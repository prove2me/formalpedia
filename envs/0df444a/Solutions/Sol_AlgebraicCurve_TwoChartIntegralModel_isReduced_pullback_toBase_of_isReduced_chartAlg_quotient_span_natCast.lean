-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.isReduced_pullback_toBase_of_isReduced_chartAlg_quotient_span_natCast
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/dbc9c440-60e7-59b8-a062-df7227cc1b5d

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_IgusaScheme
import Theorems.Thm_Algebra_isReduced_tensorProduct_of_perfectField
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_irreducible_natCast_ratLocalizedAt
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isReduced_pullback_toBase_of_isReduced_chartAlg_quotient_span_natCast

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped TensorProduct

noncomputable section

namespace RedFibreAlgebra

set_option synthInstance.maxHeartbeats 1600000

variable (p : ℕ) [Fact p.Prime]

set_option quotPrecheck false in
local notation "ℤp" => ↥(GaloisRep.ratLocalizedAt p)

scoped instance span_int_isPrime : (Ideal.span {(p : ℤ)}).IsPrime :=
  (Ideal.span_singleton_prime (by exact_mod_cast (Fact.out : p.Prime).ne_zero)).mpr
    (Nat.prime_iff_prime_int.mp Fact.out)

scoped instance dvr : IsDiscreteValuationRing ℤp :=
  GaloisRep.isDiscreteValuationRing_ratLocalizedAt p Fact.out

scoped instance isLoc : IsLocalization.AtPrime ℤp (Ideal.span {(p : ℤ)}) :=
  GaloisRep.isLocalization_ratLocalizedAt (p := p) Fact.out

theorem irreducible_p : Irreducible ((p : ℕ) : ℤp) :=
  GaloisRep.irreducible_natCast_ratLocalizedAt p Fact.out

theorem isMaximal_span_p : (Ideal.span {((p : ℕ) : ℤp)}).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible (irreducible_p p)

private theorem _root_.RedFibreAlgebra.ringHom_ext {S : Type*} [CommRing S] (f g : ℤp →+* S) : f = g :=
  IsLocalization.ringHom_ext (Ideal.span {(p : ℤ)}).primeCompl (RingHom.ext_int _ _)

p2m_export "RedFibreAlgebra" "ringHom_ext"

def φ : ℤp →+* ZMod p :=
  IsLocalization.lift (M := (Ideal.span {(p : ℤ)}).primeCompl) (S := ℤp)
    (g := Int.castRingHom (ZMod p)) (by
      rintro ⟨y, hy⟩
      have hy0 : (y : ZMod p) ≠ 0 := by
        intro h
        apply hy
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
        exact Ideal.mem_span_singleton.mpr h
      exact isUnit_iff_ne_zero.mpr hy0)

theorem φ_surjective : Function.Surjective (φ p) := ZMod.ringHom_surjective _

theorem isReduced_tensor_of_eq_zero (B : Type*) [CommRing B] [Algebra ℤp B]
    [IsReduced (B ⧸ Ideal.span {((p : ℕ) : B)})]
    (L : Type*) [Field L] [Algebra ℤp L] (hL : algebraMap ℤp L p = 0) :
    IsReduced (B ⊗[ℤp] L) := by
  let e6 : L ⊗[ℤp] B ≃ₐ[ℤp] B ⊗[ℤp] L := Algebra.TensorProduct.comm ℤp L B
  haveI : CharP L p := (CharP.charP_iff_prime_eq_zero Fact.out).mpr (by
    rw [← map_natCast (algebraMap ℤp L), hL])
  letI : Algebra ℤp (ZMod p) := (φ p).toAlgebra
  letI : Algebra (ZMod p) L := ZMod.algebra L p
  haveI : IsScalarTower ℤp (ZMod p) L :=
    IsScalarTower.of_algebraMap_eq' (ringHom_ext p _ _)

  let I : Ideal ℤp := RingHom.ker (Algebra.ofId ℤp (ZMod p))
  have hsurj : Function.Surjective (Algebra.ofId ℤp (ZMod p)) := φ_surjective p
  have hI : I = Ideal.span {((p : ℕ) : ℤp)} := by
    refine ((isMaximal_span_p p).eq_of_le (RingHom.ker_ne_top _) ?_).symm
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_natCast,
      ZMod.natCast_self]

  let e1 : (ℤp ⧸ I) ≃ₐ[ℤp] ZMod p := Ideal.quotientKerAlgEquivOfSurjective hsurj
  let e2 := Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I
  have hIB : I.map (algebraMap ℤp B) = Ideal.span {((p : ℕ) : B)} := by
    rw [hI, Ideal.map_span, Set.image_singleton, map_natCast]
  haveI r1 : IsReduced (B ⧸ I.map (algebraMap ℤp B)) := by
    let e := Ideal.quotEquivOfEq hIB
    exact isReduced_of_injective e e.injective
  haveI r2 : IsReduced (B ⊗[ℤp] (ℤp ⧸ I)) :=
    isReduced_of_injective e2.symm e2.symm.injective
  let e3 := (Algebra.TensorProduct.comm ℤp B (ℤp ⧸ I)).trans
      (Algebra.TensorProduct.congr e1 (AlgEquiv.refl (R := ℤp) (A₁ := B)))
  haveI r3 : IsReduced (ZMod p ⊗[ℤp] B) :=
    isReduced_of_injective e3.symm e3.symm.injective

  haveI r4 : IsReduced (L ⊗[ZMod p] (ZMod p ⊗[ℤp] B)) :=
    Algebra.isReduced_tensorProduct_of_perfectField (ZMod p) (ZMod p ⊗[ℤp] B) L
  let e5 := Algebra.TensorProduct.cancelBaseChange ℤp (ZMod p) (ZMod p) L B
  haveI r5 : IsReduced (L ⊗[ℤp] B) :=
    isReduced_of_injective e5.symm e5.symm.injective
  exact isReduced_of_injective e6.symm e6.symm.injective

theorem injective_algebraMap_of_ne_zero (L : Type*) [Field L] [Algebra ℤp L]
    (hL : algebraMap ℤp L p ≠ 0) : Function.Injective (algebraMap ℤp L) := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  by_contra hr0
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr0 (irreducible_p p)
  rw [map_mul, map_pow] at hr
  have hu : IsUnit (algebraMap ℤp L (u : ℤp)) := (Units.isUnit u).map _
  exact pow_ne_zero n hL ((hu.mul_right_eq_zero).mp hr)

theorem isReduced_tensor_of_ne_zero (B : Type*) [CommRing B] [Algebra ℤp B] [IsReduced B]
    (L : Type*) [Field L] [Algebra ℤp L] (hL : algebraMap ℤp L p ≠ 0) :
    IsReduced (B ⊗[ℤp] L) := by

  have key : IsReduced (L ⊗[ℤp] B) := by
    haveI : IsFractionRing ℤp ℚ := GaloisRep.isFractionRing_ratLocalizedAt p
    have hinj := injective_algebraMap_of_ne_zero p L hL
    letI : Algebra ℚ L := (IsFractionRing.lift hinj : ℚ →+* L).toAlgebra
    haveI : IsScalarTower ℤp ℚ L :=
      IsScalarTower.of_algebraMap_eq fun x => (IsFractionRing.lift_algebraMap hinj x).symm

    haveI r1 : IsReduced (B ⊗[ℤp] ℚ) :=
      isReduced_localizationPreserves (Algebra.algebraMapSubmonoid B (nonZeroDivisors ℤp))
        (B ⊗[ℤp] ℚ) inferInstance
    let e2 := Algebra.TensorProduct.comm ℤp B ℚ
    haveI r2 : IsReduced (ℚ ⊗[ℤp] B) := isReduced_of_injective e2.symm e2.symm.injective

    haveI r3 : IsReduced (L ⊗[ℚ] (ℚ ⊗[ℤp] B)) :=
      Algebra.isReduced_tensorProduct_of_perfectField ℚ (ℚ ⊗[ℤp] B) L
    let e4 := Algebra.TensorProduct.cancelBaseChange ℤp ℚ ℚ L B
    exact isReduced_of_injective e4.symm e4.symm.injective
  let e5 := Algebra.TensorProduct.comm ℤp L B
  exact isReduced_of_injective e5.symm e5.symm.injective

theorem isReduced_tensor (B : Type*) [CommRing B] [Algebra ℤp B] [IsReduced B]
    [IsReduced (B ⧸ Ideal.span {((p : ℕ) : B)})]
    (L : Type*) [Field L] [Algebra ℤp L] : IsReduced (B ⊗[ℤp] L) := by
  by_cases hL : algebraMap ℤp L p = 0
  · exact isReduced_tensor_of_eq_zero p B L hL
  · exact isReduced_tensor_of_ne_zero p B L hL

end RedFibreAlgebra
p2m_reactivate "P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isReduced_pullback_toBase_of_isReduced_chartAlg_quotient_span_natCast.RedFibreAlgebra"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isReduced_pullback_toBase_of_isReduced_chartAlg_quotient_span_natCast.RedFibreAlgebra"

noncomputable section

namespace RedFibreGeometry

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
variable (L : Type u) [CommRing L] [Algebra R L]

theorem isReduced_pullback_specMap
    (H : ∀ x : X, ∃ (B : Type u) (_ : CommRing B) (_ : Algebra R B)
      (h : Spec (.of B) ⟶ X) (_ : IsOpenImmersion h),
      h ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R B)) ∧ x ∈ Set.range h ∧
        IsReduced (B ⊗[R] L)) :
    IsReduced (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R L)))) := by
  have hst : ∀ z : ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap R L)))),
      _root_.IsReduced ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap R L)))).presheaf.stalk z) := by
    intro z
    obtain ⟨B, _, _, h, _, hh, hx, hred⟩ := H ((pullback.fst f _ : pullback f _ ⟶ X) z)

    let g := Spec.map (CommRingCat.ofHom (algebraMap R L))
    haveI : IsReduced (Spec (.of (B ⊗[R] L))) := by
      haveI : _root_.IsReduced (CommRingCat.of (B ⊗[R] L)) := hred
      infer_instance
    haveI hU : IsReduced (pullback (h ≫ f) g) :=
      isReduced_of_isOpenImmersion ((pullback.congrHom hh rfl).hom ≫ (pullbackSpecIso R B L).hom)
    let i := pullback.map (h ≫ f) g f g h (𝟙 _) (𝟙 _) (by simp) (by simp)
    have hz : z ∈ Set.range i := by
      rw [Scheme.Pullback.range_map]
      exact ⟨hx, by simp⟩
    obtain ⟨y, rfl⟩ := hz
    exact isReduced_of_injective _ (asIso <| i.stalkMap y).commRingCatIsoToRingEquiv.injective
  exact isReduced_of_isReduced_stalk _

end RedFibreGeometry
p2m_reactivate "P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isReduced_pullback_toBase_of_isReduced_chartAlg_quotient_span_natCast.RedFibreAlgebra"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isReduced_pullback_toBase_of_isReduced_chartAlg_quotient_span_natCast.RedFibreAlgebra"

noncomputable section

namespace RedFibreTwoChart

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option synthInstance.maxHeartbeats 1600000

theorem isReduced_fibre (p : ℕ) [Fact p.Prime]
    (F : Type) [Field F] [Algebra ↥(GaloisRep.ratLocalizedAt p) F] (j : F) [Fact (j ≠ 0)]
    (hFin : IsReduced (↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) F j) ⧸
      Ideal.span {((p : ℕ) : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) F j))}))
    (hInf : IsReduced (↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) F j) ⧸
      Ideal.span {((p : ℕ) : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) F j))}))
    (L : Type) [Field L] [Algebra ↥(GaloisRep.ratLocalizedAt p) L] :
    IsReduced (pullback (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) F j)
      (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) L)))) := by
  haveI := hFin
  haveI := hInf
  refine RedFibreGeometry.isReduced_pullback_specMap
    (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) F j) L fun x => ?_
  rcases AlgebraicCurve.TwoChartIntegralModel.mem_range_ιFin_or_mem_range_ιInf ↥(GaloisRep.ratLocalizedAt p) F j x with hx | hx
  · exact ⟨_, inferInstance, inferInstance, AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) F j,
      inferInstance, AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase ↥(GaloisRep.ratLocalizedAt p) F j,
      hx, RedFibreAlgebra.isReduced_tensor p _ L⟩
  · exact ⟨_, inferInstance, inferInstance, AlgebraicCurve.TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) F j,
      inferInstance, AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase ↥(GaloisRep.ratLocalizedAt p) F j,
      hx, RedFibreAlgebra.isReduced_tensor p _ L⟩

end RedFibreTwoChart
p2m_reactivate "P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isReduced_pullback_toBase_of_isReduced_chartAlg_quotient_span_natCast.RedFibreAlgebra"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isReduced_pullback_toBase_of_isReduced_chartAlg_quotient_span_natCast.RedFibreAlgebra"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

theorem solution
    (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ↥(GaloisRep.ratLocalizedAt p) F] (j : F) [Fact (j ≠ 0)]
    (hFin : IsReduced (↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) F j) ⧸
      Ideal.span {((p : ℕ) : ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) F j))}))
    (hInf : IsReduced (↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) F j) ⧸
      Ideal.span {((p : ℕ) : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) F j))}))
    (L : Type) [Field L] (toL : ↥(GaloisRep.ratLocalizedAt p) →+* L) :
    IsReduced (pullback (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) F j) (Spec.map (CommRingCat.ofHom toL))) := by
  letI : Algebra ↥(GaloisRep.ratLocalizedAt p) L := toL.toAlgebra
  exact RedFibreTwoChart.isReduced_fibre p F j hFin hInf L

end S_AlgebraicCurve_TwoChartIntegralModel_isReduced_pullback_toBase_of_isReduced_chartAlg_quotient_span_natCast
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isReduced_pullback_toBase_of_isReduced_chartAlg_quotient_span_natCast (solution)
