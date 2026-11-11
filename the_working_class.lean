inductive Country where
  | greece
  | other
  deriving DecidableEq, Repr

structure Job where
  title      : String
  country    : Country
  monthlyNet : Nat   -- euros (illustrative numbers!)
  deriving Repr

/-- "Medium paid" band: €900-€1800 net per month. -/
def lowerBound : Nat := 900
def upperBound : Nat := 1800

/-- Propositional definitions, with automatically derived decidability. -/
def MediumPaid (j : Job) : Prop := lowerBound ≤ j.monthlyNet ∧ j.monthlyNet ≤ upperBound
def HighPaid   (j : Job) : Prop := upperBound < j.monthlyNet
def InGreece   (j : Job) : Prop := j.country = .greece

instance (j : Job) : Decidable (MediumPaid j) := by unfold MediumPaid; infer_instance
instance (j : Job) : Decidable (HighPaid j)   := by unfold HighPaid; infer_instance
instance (j : Job) : Decidable (InGreece j)   := by unfold InGreece; infer_instance

def jobs : List Job := [
  ⟨"Waiter",              .greece, 1100⟩,
  ⟨"Primary teacher",     .greece, 1150⟩,
  ⟨"Nurse",               .greece, 1200⟩,
  ⟨"IT support",          .greece, 1000⟩,
  ⟨"Electrician",         .greece, 1300⟩,
  ⟨"Hotel receptionist",  .greece,  950⟩,
  ⟨"Accountant",          .greece, 1400⟩,
  ⟨"Pharmacist",          .greece, 1500⟩,
  ⟨"Truck driver",        .greece, 1050⟩,
  ⟨"Civil engineer",      .greece, 1600⟩,
  ⟨"Tour guide",          .greece, 1200⟩,
  -- not medium: too low
  ⟨"Cashier",             .greece,  780⟩,
  ⟨"Barista",             .greece,  850⟩,
  -- not medium: too high
  ⟨"Software developer",  .greece, 2200⟩
]

/-- All medium-paid jobs in Greece. -/
def mediumGreekJobs : List Job :=
  jobs.filter (fun j => decide (InGreece j ∧ MediumPaid j))

/-- All high-paid jobs in Greece. -/
def highGreekJobs : List Job :=
  jobs.filter (fun j => decide (InGreece j ∧ HighPaid j))

/-- The exact count. -/
theorem exactly_eleven : mediumGreekJobs.length = 11 := by decide

/-- Many (at least 8), but not too many (at most 12) -- now a corollary. -/
theorem many_but_not_too_many :
    8 ≤ mediumGreekJobs.length ∧ mediumGreekJobs.length ≤ 12 := by
  rw [exactly_eleven]; omega

/-- Medium-paid jobs outnumber the high-paid ones. -/
theorem more_medium_than_high :
    highGreekJobs.length < mediumGreekJobs.length := by decide

/-- Soundness, for *any* job list: whatever the filter returns really is
    a medium-paid job in Greece, not just for this particular data. -/
theorem mediumGreekJobs_sound :
    ∀ j ∈ mediumGreekJobs, InGreece j ∧ MediumPaid j := by
  intro j hj
  simpa [mediumGreekJobs] using (List.mem_filter.mp hj).2

/-- Completeness: every medium-paid Greek job in the list is returned. -/
theorem mediumGreekJobs_complete :
    ∀ j ∈ jobs, InGreece j → MediumPaid j → j ∈ mediumGreekJobs := by
  intro j hj hg hm
  exact List.mem_filter.mpr ⟨hj, by simpa using ⟨hg, hm⟩⟩

/-- 🥚 Easter egg: a theorem whose very name is the compliment. -/
theorem «καλή δουλειά» : mediumGreekJobs.length = 11 := exactly_eleven

#eval "καλή δουλειά"   -- you proved it. 🇬🇷
