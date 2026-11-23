-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LinBase
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LinBase
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:00:21.395422+00:00
-- url     : https://prove2.me/theorems/78ee59cd-86d5-4507-aa6d-5d1bee3e919b
-- title:
--   Lin Base
-- statement:
--   Definitions and structural lemmas for Lin Base, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/LinBase.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LinDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.UnitaryGroupMassFormula.ScXuExists
open Matrix
section Pr
variable {K : Type} [Field K] {n : ℕ} (P : Matrix (Fin n) (Fin n) K)
end Pr
section Rk1
variable {R : Type} [CommRing R] {n : ℕ}
theorem one_add_smul_vecMulVec_mul (p q : Fin n → R) (c d : R) :
    (1 + c • vecMulVec p q) * (1 + d • vecMulVec p q) =
      1 + (c + d + c * d * (q ⬝ᵥ p)) • vecMulVec p q := by
  have key : vecMulVec p q * vecMulVec p q = (q ⬝ᵥ p) • vecMulVec p q := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, dotProduct,
      Finset.sum_mul]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  simp only [add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, key, smul_smul]
  first
  | (module; done)
  | (rw [add_smul, add_smul, show c * d * (q ⬝ᵥ p) = d * (c * (q ⬝ᵥ p)) by ring]; abel; done)
  | (rw [add_smul, add_smul, show c * d * (q ⬝ᵥ p) = c * (d * (q ⬝ᵥ p)) by ring]; abel; done)
def rankOneUnitGL (p q : Fin n → R) (c d : R) (h : c + d + c * d * (q ⬝ᵥ p) = 0) : GL (Fin n) R :=
  ⟨1 + c • vecMulVec p q, 1 + d • vecMulVec p q, by rw [one_add_smul_vecMulVec_mul, h, zero_smul, add_zero],
    by rw [one_add_smul_vecMulVec_mul, show d + c + d * c * (q ⬝ᵥ p) = 0 by linear_combination h, zero_smul, add_zero]⟩
end Rk1
section Good
variable {K : Type} [Field K] (O : ValuationSubring K) {n r : ℕ} (P : Matrix (Fin n) (Fin n) K)
  (Λ1 Λ2 : Submodule O (Fin n → K)) (a a' α α' : Fin r → Fin n → K)
def Good (T : GL (Fin n) K) : Prop :=
  (∀ x ∈ Λ1, (T : Matrix (Fin n) (Fin n) K) *ᵥ x ∈ Λ1 ∧
        ((T⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x ∈ Λ1) ∧
      (∀ β ∈ Λ2, (∃ β' ∈ Λ2, β' ᵥ* P = (β ᵥ* P) ᵥ* (T : Matrix (Fin n) (Fin n) K)) ∧
        (∃ β' ∈ Λ2, β' ᵥ* P = (β ᵥ* P) ᵥ* ((T⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) ∧
      (∀ i, (T : Matrix (Fin n) (Fin n) K) *ᵥ a i = a i ∧ (T : Matrix (Fin n) (Fin n) K) *ᵥ a' i = a' i ∧
        (α i ᵥ* P) ᵥ* (T : Matrix (Fin n) (Fin n) K) = α i ᵥ* P ∧
        (α' i ᵥ* P) ᵥ* (T : Matrix (Fin n) (Fin n) K) = α' i ᵥ* P)
end Good
end PI.UnitaryGroupMassFormula.ScXuExists


