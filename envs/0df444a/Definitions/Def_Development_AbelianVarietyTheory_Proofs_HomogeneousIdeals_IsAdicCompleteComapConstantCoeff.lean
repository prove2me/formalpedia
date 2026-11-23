-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsAdicCompleteComapConstantCoeff
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsAdicCompleteComapConstantCoeff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:24:09.525947+00:00
-- url     : https://prove2.me/theorems/7285f9c2-44b4-4baf-a061-c1bd3116d3bb
-- title:
--   Is Adic Complete Comap Constant Coeff
-- statement:
--   Definitions and structural lemmas for Is Adic Complete Comap Constant Coeff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsAdicCompleteComapConstantCoeff.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
namespace GlobalTheory.ChartRing
section Eval
variable {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
theorem aeval_sub_mem_pow {J : Ideal S} {s : S} (hs : s ∈ J) {n : ℕ} {p q : Polynomial A}
    (h : ∀ i < n, p.coeff i = q.coeff i) :
    Polynomial.aeval s p - Polynomial.aeval s q ∈ J ^ n := by
  have : (Polynomial.X : Polynomial A) ^ n ∣ p - q :=
    Polynomial.X_pow_dvd_iff.2 fun i hi => by simp [h i hi]
  obtain ⟨r, hr⟩ := this
  rw [← map_sub, hr, map_mul, map_pow, Polynomial.aeval_X]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hs n)
def evalMod (A : Type*) [CommRing A] [Algebra A S] (J : Ideal S) {s : S} (hs : s ∈ J) (n : ℕ) :
    A⟦X⟧ →ₐ[A] S ⧸ J ^ n where
  toFun f := Ideal.Quotient.mk _ (Polynomial.aeval s (trunc n f))
  map_one' := by
    rw [← map_one (Ideal.Quotient.mk (J ^ n)), Ideal.Quotient.eq,
      ← map_one (Polynomial.aeval (R := A) s)]
    refine aeval_sub_mem_pow hs fun i hi => ?_
    simp [coeff_trunc, hi, Polynomial.coeff_one, coeff_one]
  map_mul' f g := by
    rw [← map_mul, ← map_mul, Ideal.Quotient.eq]
    refine aeval_sub_mem_pow hs fun i hi => ?_
    rw [coeff_trunc, if_pos hi, coeff_mul, Polynomial.coeff_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    have := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
    rw [coeff_trunc, coeff_trunc, if_pos (by omega), if_pos (by omega)]
  map_zero' := by simp
  map_add' f g := by simp
  commutes' a := by
    rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq,
      ← (Polynomial.aeval (R := A) s).commutes a]
    refine aeval_sub_mem_pow hs fun i hi => ?_
    simp [coeff_trunc, hi, Polynomial.coeff_C, coeff_C, PowerSeries.algebraMap_apply]
theorem factor_comp_evalMod (J : Ideal S) {s : S} (hs : s ∈ J) {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hle)).comp (evalMod A J hs n) =
      evalMod A J hs m := by
  refine AlgHom.ext fun f => ?_
  change Ideal.Quotient.mk _ (Polynomial.aeval s (trunc n f)) =
    Ideal.Quotient.mk _ (Polynomial.aeval s (trunc m f))
  rw [Ideal.Quotient.eq]
  refine aeval_sub_mem_pow hs fun i hi => ?_
  rw [coeff_trunc, coeff_trunc, if_pos hi, if_pos (by omega)]
def evalAdic (A : Type*) [CommRing A] [Algebra A S] (J : Ideal S) [IsAdicComplete J S] {s : S}
    (hs : s ∈ J) : A⟦X⟧ →ₐ[A] S :=
  IsAdicComplete.liftAlgHom J (evalMod A J hs) (factor_comp_evalMod J hs)
variable (J : Ideal S) [IsAdicComplete J S] {s : S} (hs : s ∈ J)
end Eval
section Division
variable {A : Type*} [CommRing A]
end Division
section Complete
variable {A : Type*} [CommRing A] (I : Ideal A)
end Complete
end GlobalTheory.ChartRing


