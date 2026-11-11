-- Prove2me | Definitions.Def_SubquadCutReach_Faster_Tasks
-- name    : SubquadCutReach_Faster_Tasks
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T17:02:42.497192+00:00
-- url     : https://prove2.me/theorems/69510be8-239f-4930-867b-598e19d09be9
-- title:
--   Known-data input layouts and uniform protocol specifications
-- statement:
--   The task records collect the paper's source instances: arbitrary terminal pairs in oriented graphs; simple undirected graphs; fractional rules; and feasible imbalance targets with supplied orientation rules. Their fields contain no algorithm, output, running-cost assertion or correctness certificate.
--
--   $$\Pr\{Q>C_cn^{5/3}L(n)^{p_c}\}\le n^{-c}.$$
--
--   Correctness and cost predicates are properties to be proved of finite programs. Explicit memory layouts supply only allowed known data. The rounding output specification uses the source-derived vertex error four, while balanced orientation retains error one. A deterministic bounded run must halt after finitely many local steps on every tape. These interfaces keep constants uniform over all records, including their size fields.
-- source:
--   Henry Fleischmann, Sagnik Mukhopadhyay, Swagato Sanyal, STOC 2027 submission #503 (October 2026), Definitions 3.1 and 3.3, Lemmas A.3–A.5, C.2, 3.11 and Theorem 1.2; pp.2,6–7,21–27 (PDF pp.4,8–9,23–29)

import Mathlib
import Definitions.Def_SubquadCutReach_Faster_Reserve
import Definitions.Def_SubquadCutReach_Faster_Repair
import Definitions.Def_SubquadCutReach_Faster_Averaging
import Definitions.Def_SubquadCutReach_Faster_Rounding

set_option autoImplicit false
open scoped BigOperators

namespace SubquadCutReach.Faster

structure ReachCase where
  n : ℕ
  G : Digraph n
  oriented : Oriented G
  s : Fin n
  t : Fin n

structure GraphCase where
  n : ℕ
  H : SimpleGraph (Fin n)

structure RoundCase extends GraphCase where
  z : Fractional n
  valid : ValidFractional z

structure RepairCase extends GraphCase where
  b : Fin n → ℤ
  feasible : Feasible H b
  D : Rule n

structure MatchCase extends GraphCase where
  b : Fin n → ℤ
  feasible : Feasible H b

noncomputable def reachInput (i : ReachCase) : Memory := input i.n i.s.val i.t.val (fun _ => 0)

noncomputable def ReachCorrect (P : Program) (i : ReachCase) : Prop :=
  ZeroError P (outCut i.G) (reachInput i) fun m =>
    (m 0 = 0 ∨ m 0 = 1) ∧ (m 0 = 1 ↔ reachable i.G i.s i.t)

noncomputable def BalancedCorrect (P : Program) (i : GraphCase) : Prop :=
  ZeroError P (cut i.H) (input i.n 0 0 (fun _ => 0)) fun m =>
    ∀ v, |imbalance (induced i.H (outputRule i.n m)) v| ≤ 1

noncomputable def RoundCorrect (P : Program) (i : RoundCase) : Prop :=
  ZeroError P (cut i.H) (fracInput i.z) fun m =>
    Linfty (fun v => (imbalance (induced i.H (outputRule i.n m)) v : ℝ) -
      fractionalImbalance i.H i.z v) 4

noncomputable def RepairCorrect (P : Program) (i : RepairCase) : Prop :=
  ZeroError P (cut i.H) (repairInput i.b i.D) fun m =>
    imbalance (induced i.H (outputRule i.n m)) = i.b

noncomputable def FlowCorrect (P : Program) (i : RepairCase) : Prop :=
  ZeroError P (cut i.H) (repairInput i.b i.D) fun m =>
    MaximumFlow (capacity i.H i.D i.b) (outputFlow i.n m) ∧
    IntegralFlow (outputFlow i.n m)

noncomputable def MatchCorrect (P : Program) (i : MatchCase) : Prop :=
  ZeroError P (cut i.H) (targetInput i.b 0) fun m =>
    imbalance (induced i.H (outputRule i.n m)) = i.b

noncomputable def reachCosts (P : Program) (i : ReachCase) := cost P (outCut i.G) (reachInput i)
noncomputable def balancedCosts (P : Program) (i : GraphCase) :=
  cost P (cut i.H) (input i.n 0 0 (fun _ => 0))
noncomputable def roundCosts (P : Program) (i : RoundCase) := cost P (cut i.H) (fracInput i.z)
noncomputable def repairCosts (P : Program) (i : RepairCase) := cost P (cut i.H) (repairInput i.b i.D)
noncomputable def matchCosts (P : Program) (i : MatchCase) := cost P (cut i.H) (targetInput i.b 0)

/-- Known pair-family, vertex and candidate set input for Lemma 2.4. -/
noncomputable def subInput {n : ℕ} (P : Rule n) (v : ℕ) (X : Finset (Fin n)) : Memory := by
  classical
  exact input n v 0 fun i =>
    if hi : i < n*n then
      if hu : i/n < n then if hv : i%n < n then
        if P ⟨i/n,hu⟩ ⟨i%n,hv⟩ then 1 else 0 else 0 else 0
    else if hi : i-n*n < n then if (⟨i-n*n,hi⟩ : Fin n) ∈ X then 1 else 0 else 0

noncomputable def outputPairs (n : ℕ) (m : Memory) : Finset (Fin n × Fin n) := by
  classical
  exact Finset.univ.filter fun uv => uv.1 < uv.2 ∧ m (uv.1.val*n+uv.2.val : ℕ) ≠ 0

/-- Search input contains an evaluable all-pair rule, never H. -/
noncomputable def searchInput {n : ℕ} (D : Rule n) (s t : Fin n) : Memory :=
  input n s.val t.val fun i =>
    if hu : i/n < n then if hv : i%n < n then
      if D ⟨i/n,hu⟩ ⟨i%n,hv⟩ then 1 else 0 else 0 else 0

end SubquadCutReach.Faster

namespace SubquadCutReach.Faster

/-- A deterministic total query bound, with finite local time on every tape. -/
def RunsWithin {n : ℕ} (P : Program) (O : Finset (Fin n) → ℕ) (x : Memory)
    (answer : Memory → Prop) (B : ℝ) : Prop :=
  ∀ ω : ℕ → Bool, ∃ t : ℕ, (run P O x ω t).halted = true ∧
    answer (run P O x ω t).core.mem ∧ ((run P O x ω t).queries : ℝ) ≤ B

end SubquadCutReach.Faster


