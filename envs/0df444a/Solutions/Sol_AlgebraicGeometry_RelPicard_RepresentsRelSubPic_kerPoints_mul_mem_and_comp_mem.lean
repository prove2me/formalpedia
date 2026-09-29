-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.RepresentsRelSubPic.kerPoints_mul_mem_and_comp_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/6f7bcf16-89d7-5cc4-9d4a-5d440fc3a9b2

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicGeometry_RigKerDualNumber
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_kerPoints_mul_mem_and_comp_mem

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_kerPoints_mul_mem_and_comp_mem.GoodReductionJacobian"

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "RelativePic0Designation schemeHomOverComp RelativeGroupLaw"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "pointGroup one mul_natural one_mul mul"
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

section ReducesToOne

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
  {T T₀ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t₀ : T₀ ⟶ Spec (CommRingCat.of R)}
  (r : T₀ ⟶ T) (hr : r ≫ t = t₀)

theorem comp_eq_one_iff (x : SchemeHomOver t f) :
    r ≫ x.1 = (L.one t₀).1 ↔ GoodReductionJacobian.schemeHomOverComp r hr x = L.one t₀ :=
  ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

include hr in

theorem comp_mul_eq_one_of_comp_eq_one (x y : SchemeHomOver t f)
    (hx : r ≫ x.1 = (L.one t₀).1) (hy : r ≫ y.1 = (L.one t₀).1) :
    r ≫ (L.mul t x y).1 = (L.one t₀).1 := by
  rw [comp_eq_one_iff L r hr] at hx hy ⊢
  rw [L.mul_natural t t₀ r hr, hx, hy, L.one_mul]

theorem hom_one (φ : SchemeHomOver f f)
    (hφ : ∀ {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s f),
      NeronModelInfra.schemeHomOverComp (L.mul s x y) φ =
        L.mul s (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ))
    {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of R)) :
    NeronModelInfra.schemeHomOverComp (L.one s) φ = L.one s := by
  letI := L.pointGroup s
  have h := hφ s (L.one s) (L.one s)
  rw [L.one_mul] at h
  have h' : (NeronModelInfra.schemeHomOverComp (L.one s) φ : SchemeHomOver s f) =
      NeronModelInfra.schemeHomOverComp (L.one s) φ * NeronModelInfra.schemeHomOverComp (L.one s) φ := h
  exact (left_eq_mul.mp h').symm ▸ rfl

include hr in

theorem comp_comp_hom_eq_one_of_comp_eq_one (φ : SchemeHomOver f f)
    (hφ : ∀ {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s f),
      NeronModelInfra.schemeHomOverComp (L.mul s x y) φ =
        L.mul s (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ))
    (x : SchemeHomOver t f) (hx : r ≫ x.1 = (L.one t₀).1) :
    r ≫ (x.1 ≫ φ.1) = (L.one t₀).1 := by
  rw [← Category.assoc, hx]
  exact congrArg Subtype.val (hom_one L φ hφ t₀)

end ReducesToOne

end GoodReductionJacobian.RelativeGroupLaw

theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (.of R))) c} {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) (A : Type u) [CommRing A] [Algebra R A] :
    letI L := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h
    let tε := Scheme.TwoAffineOpenCover.specMap R (DualNumber A)
    let t₀ := Scheme.TwoAffineOpenCover.specMap R A
    (∀ x y : SchemeHomOver tε D.toBase,
        dualNumberReduction R A ≫ x.1 = (L.one t₀).1 → dualNumberReduction R A ≫ y.1 = (L.one t₀).1 →
          dualNumberReduction R A ≫ (L.mul tε x y).1 = (L.one t₀).1) ∧
    (∀ (φ : SchemeHomOver D.toBase D.toBase),
        (∀ {T : Scheme.{u}} (s : T ⟶ Spec (.of R)) (x y : SchemeHomOver s D.toBase),
          NeronModelInfra.schemeHomOverComp (L.mul s x y) φ =
            L.mul s (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ)) →
        ∀ x : SchemeHomOver tε D.toBase, dualNumberReduction R A ≫ x.1 = (L.one t₀).1 →
          dualNumberReduction R A ≫ (x.1 ≫ φ.1) = (L.one t₀).1) := by
  refine ⟨fun x y hx hy => ?_, fun φ hφ x hx => ?_⟩
  · exact GoodReductionJacobian.RelativeGroupLaw.comp_mul_eq_one_of_comp_eq_one _ (dualNumberReduction R A)
      (dualNumberReduction_comp_specMap R A) x y hx hy
  · exact GoodReductionJacobian.RelativeGroupLaw.comp_comp_hom_eq_one_of_comp_eq_one _ (dualNumberReduction R A)
      (dualNumberReduction_comp_specMap R A) φ hφ x hx

end S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_kerPoints_mul_mem_and_comp_mem
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_kerPoints_mul_mem_and_comp_mem (solution)
