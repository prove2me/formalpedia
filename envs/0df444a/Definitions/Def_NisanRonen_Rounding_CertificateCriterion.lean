-- Prove2me | Definitions.Def_NisanRonen_Rounding_CertificateCriterion
-- name    : NisanRonen_Rounding_CertificateCriterion
-- status  : Definition
-- author  : @Jie Luo
-- created : 2026-11-26T06:10:33.543481+00:00
-- url     : https://prove2.me/theorems/11482d71-edda-5659-8af6-5093f6c7570d
-- title:
--   An allocation-only criterion for the rounding mechanism
-- statement:
--   A declaration passes the optimality test when, for every in-box matrix containing that row, the chosen allocation minimizes rounded makespan with that row replaced by the true row. The allocation-only criterion tests profiles whose declarations all pass. For each comparison schedule and each occupied machine, it requires an in-box declaration matrix that keeps the machine’s row and the original allocation fixed. After truth-correcting that row, the new matrix must admit a schedule below the approximation threshold.
-- source:
--   Nisan and Ronen (2001), Algorithmic Mechanism Design, Definition 18, Definition 34, and Theorem 5.9, https://doi.org/10.1006/game.1999.0790. An allocation-only reformulation of the corrected implementation requirement.

import Definitions.Def_NisanRonen_Rounding_IsExactRoundedSolver

namespace NisanRonen.Rounding

/-- Each occupied machine has an alternative declaration profile that agrees with its own
declaration, preserves the allocation, and certifies the prescribed bound after truth correction. -/
def HasAllocationCertificates {n k : ℕ} [NeZero n] (f : List (Fin n → ℕ) → List (Fin n))
    (δ a b : ℝ) (t d : Fin n → Fin k → ℝ) (C : ℝ) : Prop :=
  ∀ i : Fin n, (∃ j, allocOf f δ d j = i) → ∃ v : Fin n → Fin k → ℝ,
    (∀ l j, a ≤ v l j ∧ v l j ≤ b) ∧ v i = d i ∧
    allocOf f δ v = allocOf f δ d ∧
    ∃ y : Fin k → Fin n,
      roundedMakespan δ y (corrStar y (Function.update v i (t i))) ≤ C


/-- Test a single declaration against every in-box profile on which it is used. The output must
minimize rounded makespan at the profile obtained by replacing this declaration by the true row. -/
def DeclarationOptimal {n k : ℕ} [NeZero n] (f : List (Fin n → ℕ) → List (Fin n))
    (δ a b : ℝ) (i : Fin n) (ti report : Fin k → ℝ) : Prop :=
  ∀ v : Fin n → Fin k → ℝ, (∀ l j, a ≤ v l j ∧ v l j ≤ b) → v i = report →
    let x := allocOf f δ v
    ∀ y : Fin k → Fin n,
      roundedMakespan δ x (corrStar x (Function.update v i ti)) ≤
        roundedMakespan δ y (corrStar y (Function.update v i ti))

/-- An allocation-only criterion for the approximation clause of the rounding mechanism. -/
def CertificateCriterion {n : ℕ} [NeZero n] (f : List (Fin n → ℕ) → List (Fin n))
    (δ a b ε : ℝ) : Prop :=
  ∀ (k : ℕ) (t d : Fin n → Fin k → ℝ),
    (∀ i j, a ≤ t i j ∧ t i j ≤ b) →
    (∀ i j, a ≤ d i j ∧ d i j ≤ b) →
    (∀ i, DeclarationOptimal f δ a b i (t i) (d i)) →
    ∀ y : Fin k → Fin n, HasAllocationCertificates f δ a b t d
      ((1 + ε) * makespan y (corrStar y t))

end NisanRonen.Rounding


