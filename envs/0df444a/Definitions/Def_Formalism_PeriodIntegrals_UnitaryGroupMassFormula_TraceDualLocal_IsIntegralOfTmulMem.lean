-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TraceDualLocal_IsIntegralOfTmulMem
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TraceDualLocal_IsIntegralOfTmulMem
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:14:08.148876+00:00
-- url     : https://prove2.me/theorems/625a37c9-a97a-466c-a185-0d83dfffd104
-- title:
--   Is Integral Of Tmul Mem
-- statement:
--   Definitions and structural lemmas for Is Integral Of Tmul Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TraceDualLocal/IsIntegralOfTmulMem.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.TrDualLocW
open NumberField
open scoped TensorProduct
variable (K : Type) [Field K] [NumberField K] (ℓ : ℕ) [Fact ℓ.Prime]
def BA : Module.Basis (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] K) :=
  Algebra.TensorProduct.basis ℚ_[ℓ] (integralBasis K)
variable {K ℓ}
theorem BA_apply (i : Module.Free.ChooseBasisIndex ℤ (𝓞 K)) : BA K ℓ i = 1 ⊗ₜ integralBasis K i :=
  Algebra.TensorProduct.basis_apply _ i
theorem BA_repr_tmul (x : K) (i : Module.Free.ChooseBasisIndex ℤ (𝓞 K)) :
    (BA K ℓ).repr (1 ⊗ₜ x) i = (((integralBasis K).repr x i : ℚ) : ℚ_[ℓ]) := by
  simp [BA, Finsupp.mapRange_apply]
theorem coord_int (x : K) (hx : IsIntegral ℤ x) (i : Module.Free.ChooseBasisIndex ℤ (𝓞 K)) :
    ∃ z : ℤ, (integralBasis K).repr x i = z := by
  obtain ⟨a, rfl⟩ : ∃ a : 𝓞 K, algebraMap (𝓞 K) K a = x := ⟨⟨x, (mem_integralClosure_iff ℤ K).2 hx⟩, rfl⟩
  rw [integralBasis_repr_apply]
  exact ⟨_, rfl⟩
variable (K ℓ)
def S : Subring (ℚ_[ℓ] ⊗[ℚ] K) where
  carrier := {x | ∀ i, (BA K ℓ).repr x i ∈ PadicInt.subring ℓ}
  zero_mem' := by
    intro i
    simp
  add_mem' := by
    intro a b ha hb i
    rw [map_add, Finsupp.add_apply]
    exact add_mem (ha i) (hb i)
  neg_mem' := by
    intro a ha i
    rw [map_neg, Finsupp.neg_apply]
    exact neg_mem (ha i)
  one_mem' := by
    intro i
    rw [Algebra.TensorProduct.one_def, BA_repr_tmul]
    obtain ⟨z, hz⟩ := coord_int (1 : K) isIntegral_one i
    rw [hz, Rat.cast_intCast]
    exact intCast_mem _ z
  mul_mem' := by
    intro a b ha hb i
    have e : a * b = ∑ j, ∑ k, ((BA K ℓ).repr a j * (BA K ℓ).repr b k) • (BA K ℓ j * BA K ℓ k) := by
      conv_lhs => rw [← (BA K ℓ).sum_repr a, ← (BA K ℓ).sum_repr b]
      rw [Finset.sum_mul_sum]
      simp only [smul_mul_smul_comm]
    rw [e]
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
    refine Subring.sum_mem _ fun j _ => Subring.sum_mem _ fun k _ =>
      Subring.mul_mem _ (Subring.mul_mem _ (ha j) (hb k)) ?_
    rw [BA_apply, BA_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, BA_repr_tmul]
    have hi : IsIntegral ℤ (integralBasis K j * integralBasis K k) := by
      rw [integralBasis_apply, integralBasis_apply]
      exact (RingOfIntegers.isIntegral_coe _).mul (RingOfIntegers.isIntegral_coe _)
    obtain ⟨z, hz⟩ := coord_int _ hi i
    rw [hz, Rat.cast_intCast]
    exact intCast_mem _ z
variable {K ℓ}
end PI.TrDualLocW


