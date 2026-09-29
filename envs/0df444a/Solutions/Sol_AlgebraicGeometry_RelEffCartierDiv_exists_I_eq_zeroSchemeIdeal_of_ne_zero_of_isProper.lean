-- Prove2me | solution 1 for AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal_of_ne_zero_of_isProper
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/b6661998-cec0-5e61-88c2-c9680d37909f

import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
import Mathlib.RingTheory.FinitePresentation
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_genericPoint_notMem_support_zeroSchemeIdeal
import Theorems.Thm_AlgebraicGeometry_isReduced_of_smooth_over_field
import Theorems.Thm_AlgebraicCurve_finite_compl_of_isOpen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal_of_ne_zero_of_isProper
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry TopologicalSpace"

theorem solution
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsProper f] [SmoothOfRelativeDimension 1 f] [GeometricallyIrreducible f]
    {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ S)
    {M : (pullback f x).Modules} (hM : Scheme.Modules.IsInvertible M)
    (s : 𝟙_ (pullback f x).Modules ⟶ M) (hs : s ≠ 0) :
    ∃ (r : ℕ) (D : RelEffCartierDiv f r x), D.I = Scheme.Modules.zeroSchemeIdeal s := by
  classical

  let C : Scheme.{u} := pullback f x
  let c : C ⟶ Spec (CommRingCat.of k) := pullback.snd f x
  haveI : IsProper c := inferInstance
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange 1
  haveI : SmoothOfRelativeDimension 1 c :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) f x inferInstance
  haveI : QuasiCompact c := inferInstance

  haveI : IrreducibleSpace ↥C :=
    GeometricallyIrreducible.geometrically_irreducibleSpace (f := f) x (pullback.fst f x) c
      (IsPullback.of_hasPullback f x)
  haveI : IsReduced C :=
    isReduced_of_smooth_over_field (g := c) (SmoothOfRelativeDimension.smooth 1 c)
  haveI : IsIntegral C := isIntegral_of_irreducibleSpace_of_isReduced _

  let I : C.IdealSheafData := Scheme.Modules.zeroSchemeIdeal s
  let g : I.subscheme ⟶ Spec (CommRingCat.of k) := I.subschemeι ≫ c

  have hη : genericPoint C ∉ I.support :=
    Scheme.Modules.IsInvertible.genericPoint_notMem_support_zeroSchemeIdeal hM s hs
  have hfin : (I.support : Set C).Finite := by
    have h := AlgebraicCurve.finite_compl_of_isOpen c I.support.compl ⟨genericPoint _, hη⟩
    simpa [TopologicalSpace.Closeds.coe_compl, compl_compl] using h
  haveI : Finite ↥(I.subscheme) := by
    haveI : Finite (I.support : Set C) := hfin.to_subtype
    refine Finite.of_injective (fun z => (⟨I.subschemeι.base z, ?_⟩ : (I.support : Set C))) ?_
    · rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨z, rfl⟩
    · intro a b hab
      exact I.subschemeι.isClosedEmbedding.injective (congrArg Subtype.val hab)

  haveI : LocallyQuasiFinite g :=
    LocallyQuasiFinite.of_finite_preimage_singleton g fun y => Set.toFinite _
  haveI : IsProper g := inferInstance
  haveI hgfin : IsFinite g := IsFinite.of_isProper_of_locallyQuasiFinite g
  haveI : Flat g := inferInstance

  have hlofp : LocallyOfFinitePresentation g := by
    haveI : IsAffine I.subscheme := isAffine_of_isAffineHom g
    rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)]
    have hft : g.appTop.hom.Finite :=
      ((HasAffineProperty.iff_of_isAffine (P := @IsFinite) (f := g)).mp hgfin).2
    letI := g.appTop.hom.toAlgebra
    haveI : Module.Finite Γ(Spec (CommRingCat.of k), ⊤) Γ(I.subscheme, ⊤) := hft
    haveI : IsNoetherianRing Γ(Spec (CommRingCat.of k), ⊤) :=
      isNoetherianRing_of_ringEquiv k (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
    exact Algebra.FinitePresentation.of_finiteType.mp inferInstance

  obtain ⟨t₀⟩ : Nonempty ↥(Spec (CommRingCat.of k)) := inferInstance
  refine ⟨g.finrank t₀, ⟨I, hgfin, inferInstance, hlofp, fun t => ?_⟩, rfl⟩
  rw [Subsingleton.elim t t₀]

end S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal_of_ne_zero_of_isProper
end P2MW
export P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal_of_ne_zero_of_isProper (solution)
