-- Prove2me | solution 1 for AlgebraicCurve.Pic0.sum_galois_smul_eq_zero_of_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:01:41.873201+00:00
-- url     : https://prove2.me/submissions/720b4547-a9b8-4eee-932b-378d87f1bc74

import Mathlib
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Theorems.Thm_AlgebraicCurve_Divisor_sum_galois_smul_eq_pullback_pushforward

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve.Pic0

/-- For a finite Galois cover with trivial degree-zero Picard group on the base,
the sum of the Galois translates of each degree-zero class vanishes. -/
theorem _root_.solution
    {K F E : Type*} [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
    [FiniteDimensional F E] [IsGalois F E]
    [HasPrincipalDivisors K E] [Subsingleton (Pic0 K F)] (x : Pic0 K E) :
    ∑ σ : E ≃ₐ[F] E, SemilinearAut.ofAlgAut (σ.restrictScalars K) • x = 0 := by
  classical
  obtain ⟨D, rfl⟩ := mk_surjective x
  let q : Divisor.degZero (K := K) (F := E) →+ Pic0 K E :=
    QuotientAddGroup.mk' _
  have hsum :
      (∑ σ : E ≃ₐ[F] E,
        SemilinearAut.degZeroSMulHom (SemilinearAut.ofAlgAut (σ.restrictScalars K)) D :
        Divisor.degZero (K := K) (F := E)).val =
      Divisor.pullback E (Divisor.pushforward F D.val) := by
    change (Divisor.degZero (K := K) (F := E)).subtype (∑ σ : E ≃ₐ[F] E,
      SemilinearAut.degZeroSMulHom (SemilinearAut.ofAlgAut (σ.restrictScalars K)) D) = _
    rw [map_sum]
    simp only [AddSubgroup.subtype_apply, SemilinearAut.coe_degZeroSMulHom]
    exact Divisor.sum_galois_smul_eq_pullback_pushforward D.val
  have hbase : mk (pushforwardDegZeroHom F D) = (0 : Pic0 K F) :=
    Subsingleton.elim _ _
  have hprincipal : (Divisor.pushforward F D.val).IsPrincipal := by
    exact (QuotientAddGroup.eq_zero_iff _).mp hbase
  have hpull : (Divisor.pullback E (Divisor.pushforward F D.val)).IsPrincipal :=
    Divisor.isPrincipal_pullback hprincipal
  have hzero : q (∑ σ : E ≃ₐ[F] E,
      SemilinearAut.degZeroSMulHom (SemilinearAut.ofAlgAut (σ.restrictScalars K)) D) = 0 := by
    apply (QuotientAddGroup.eq_zero_iff _).mpr
    change (∑ σ : E ≃ₐ[F] E,
      SemilinearAut.degZeroSMulHom (SemilinearAut.ofAlgAut (σ.restrictScalars K)) D).val.IsPrincipal
    rw [hsum]
    exact hpull
  rw [map_sum] at hzero
  exact hzero

end AlgebraicCurve.Pic0
