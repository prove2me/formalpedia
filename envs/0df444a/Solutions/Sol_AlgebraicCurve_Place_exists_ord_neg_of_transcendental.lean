-- Prove2me | solution 1 for AlgebraicCurve.Place.exists_ord_neg_of_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/83996e50-2b0f-5498-afc1-053fc15a60bf

import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.FieldTheory.RatFunc.Degree
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_exists_forall_ne_ofHeightOneSpectrum
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_eq_toValuationSubring
import Theorems.Thm_AlgebraicCurve_Place_exists_ord_algebraMap_eq_mul_ord
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_exists_ord_neg_of_transcendental
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"

set_option autoImplicit false

open AlgebraicCurve
open scoped nonZeroDivisors

theorem solution {K F : Type*} [Field K] [CharZero K] [Field F] [Algebra K F] (x : F) (hx : Transcendental K x) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] : ∃ v : Place K F, v.ord x < 0 := by
  classical

  have hinj : Function.Injective (Polynomial.aeval x : Polynomial K →ₐ[K] F) :=
    transcendental_iff_injective.mp hx
  have hφ : (Polynomial K)⁰ ≤ F⁰.comap (Polynomial.aeval x : Polynomial K →ₐ[K] F) := by
    intro p hp
    rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
    rw [mem_nonZeroDivisors_iff_ne_zero] at hp
    exact fun h => hp (hinj (by rw [h, map_zero]))
  set ψ : RatFunc K →ₐ[K] F := RatFunc.liftAlgHom (Polynomial.aeval x) hφ with hψ_def
  have hψX : ψ RatFunc.X = x := by
    rw [hψ_def, RatFunc.liftAlgHom_apply, RatFunc.num_X, RatFunc.denom_X, Polynomial.aeval_X,
      map_one, div_one]
  letI : Algebra (RatFunc K) F := ψ.toRingHom.toAlgebra
  haveI : IsScalarTower K (RatFunc K) F :=
    IsScalarTower.of_algebraMap_eq fun c => (ψ.commutes c).symm

  have hEle : IntermediateField.adjoin K ({x} : Set F) ≤ ψ.fieldRange :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr ⟨RatFunc.X, hψX⟩)
  haveI : Module.Finite (RatFunc K) F := by
    obtain ⟨s, hs⟩ := Module.finite_def.mp
      (inferInstance : Module.Finite (IntermediateField.adjoin K ({x} : Set F)) F)
    refine Module.finite_def.mpr ⟨s, ?_⟩
    rw [eq_top_iff]
    rintro f -
    have hf : f ∈ Submodule.span (IntermediateField.adjoin K ({x} : Set F)) (s : Set F) := by
      rw [hs]; trivial
    induction hf using Submodule.span_induction with
    | mem g hg => exact Submodule.subset_span hg
    | zero => exact Submodule.zero_mem _
    | add g h _ _ hg hh => exact Submodule.add_mem _ hg hh
    | smul e g _ hg =>
      obtain ⟨r, hr⟩ := hEle e.2
      have hsm : e • g = r • g := by
        rw [Algebra.smul_def, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
        have he' : algebraMap (IntermediateField.adjoin K ({x} : Set F)) F e = (e : F) := rfl
        rw [he', ← hr]
      rw [hsm]
      exact Submodule.smul_mem _ r hg

  haveI : CharZero (RatFunc K) :=
    charZero_of_injective_algebraMap (algebraMap K (RatFunc K)).injective
  haveI : Algebra.IsAlgebraic (RatFunc K) F := Algebra.IsAlgebraic.of_finite (RatFunc K) F
  haveI : Algebra.IsSeparable (RatFunc K) F := Algebra.IsAlgebraic.isSeparable_of_perfectField

  obtain ⟨vinf, hvinf⟩ :=
    AlgebraicCurve.RationalFunctionField.exists_forall_ne_ofHeightOneSpectrum (K := K)
  obtain ⟨w, hw⟩ := AlgebraicCurve.Place.exists_comap_eq_toValuationSubring (F' := F) vinf
  obtain ⟨e, he0, htrans⟩ :=
    AlgebraicCurve.Place.exists_ord_algebraMap_eq_mul_ord w vinf hw.symm
  refine ⟨w, ?_⟩
  have hX := htrans RatFunc.X
  have hordX : vinf.ord RatFunc.X = -1 := by
    rw [AlgebraicCurve.RationalFunctionField.ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum
      vinf hvinf RatFunc.X_ne_zero, RatFunc.intDegree_X]
  have hmapX : algebraMap (RatFunc K) F RatFunc.X = x := by
    rw [RingHom.algebraMap_toAlgebra]
    exact hψX
  rw [hmapX, hordX] at hX
  rw [hX, mul_neg_one, Left.neg_neg_iff]
  exact_mod_cast he0

end S_AlgebraicCurve_Place_exists_ord_neg_of_transcendental
end P2MW
export P2MW.S_AlgebraicCurve_Place_exists_ord_neg_of_transcendental (solution)
