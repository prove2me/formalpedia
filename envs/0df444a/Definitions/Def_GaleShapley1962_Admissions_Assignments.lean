-- Prove2me | Definitions.Def_GaleShapley1962_Admissions_Assignments
-- name    : GaleShapley1962_Admissions_Assignments
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T02:41:16.698774+00:00
-- url     : https://prove2.me/theorems/eef597b4-0009-4ad5-8cca-0da73cd4e0b2
-- title:
--   Feasible assignments, printed stability, and applicant preference
-- statement:
--   An assignment sends each applicant to at most one college, or leaves that applicant unassigned. Feasibility requires mutual acceptability of every assigned pair and enrollment at each college no larger than its quota.
--
--   Printed instability means that there exist applicants $a,b$ and colleges $A,B$ such that $a$ is assigned to $A$, $b$ is assigned to $B$, $b$ prefers $A$ to $B$, and $A$ prefers $b$ to $a$. Printed stability is the absence of such a witness. In particular, both applicants in a witness are assigned. There is no condition concerning an unmatched applicant or a vacant place, and comparison assignments need not fill vacancies.
--
--   For an applicant, one outcome is weakly preferred to another if they are equal, or the first is an acceptable college and the second is unassignment or a strictly less preferred acceptable college. Equality includes two unassignments. On feasible assignments this gives exactly the applicant-wise comparison in the source's definition of optimality.
-- source:
--   Gale and Shapley (1962), College Admissions and the Stability of Marriage, Section 2, displayed definitions, printed p. 10 (PDF p. 2), and Section 4, printed pp. 13–14 (PDF pp. 5–6), https://doi.org/10.1080/00029890.1962.11989827

import Definitions.Def_GaleShapley1962_Admissions_Market

namespace GaleShapley1962.Admissions

/-- `none` is an unassigned applicant, not a dummy college. -/
abbrev Assignment (n m : ℕ) := Fin n → Option (Fin m)

/-- Mutual acceptability and the upper bound on each college's enrollment. -/
def Market.Feasible {n m : ℕ} (M : Market n m) (μ : Assignment n m) : Prop :=
  (∀ a c, μ a = some c → c ∈ M.permissible a) ∧
    ∀ c, (Finset.univ.filter fun a => μ a = some c).card ≤ M.quota c

/-- The literal displayed instability definition of Section 2, printed page 10:
both applicants in a witness must be assigned to actual colleges. -/
def Market.PrintedStable {n m : ℕ} (M : Market n m) (μ : Assignment n m) : Prop :=
  ¬ ∃ (a b : Fin n) (A B : Fin m),
    μ a = some A ∧ μ b = some B ∧
      listPrefers (M.applicantList b) A B ∧ listPrefers (M.collegeList A) b a

/-- Applicant weak preference on acceptable outcomes, with unassignment below
every acceptable college. Equal outcomes include two unassignments. -/
def Market.WeaklyPrefers {n m : ℕ} (M : Market n m) (a : Fin n)
    (x y : Option (Fin m)) : Prop :=
  x = y ∨ ∃ c, x = some c ∧ c ∈ M.applicantList a ∧
    (y = none ∨ ∃ d, y = some d ∧ listPrefers (M.applicantList a) c d)

instance {n m : ℕ} (M : Market n m) (μ : Assignment n m) :
    Decidable (M.Feasible μ) := by
  unfold Market.Feasible
  infer_instance

instance {n m : ℕ} (M : Market n m) (μ : Assignment n m) :
    Decidable (M.PrintedStable μ) := by
  unfold Market.PrintedStable
  infer_instance

instance {n m : ℕ} (M : Market n m) (a : Fin n) (x y : Option (Fin m)) :
    Decidable (M.WeaklyPrefers a x y) := by
  unfold Market.WeaklyPrefers
  infer_instance

end GaleShapley1962.Admissions


