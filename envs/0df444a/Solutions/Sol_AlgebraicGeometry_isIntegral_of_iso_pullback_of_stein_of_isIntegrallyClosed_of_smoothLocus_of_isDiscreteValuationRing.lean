-- Prove2me | solution 1 for AlgebraicGeometry.isIntegral_of_iso_pullback_of_stein_of_isIntegrallyClosed_of_smoothLocus_of_isDiscreteValuationRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/e805548f-6894-5825-8618-9d420248d04f

import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_AlgebraicGeometry_isProper_and_flat_and_locallyOfFinitePresentation_of_iso_pullback_specMap
import Theorems.Thm_AlgebraicGeometry_smooth_pullback_snd_specMap_of_forall_mem_smoothLocus_of_isFractionRing
import Theorems.Thm_AlgebraicGeometry_isIntegral_of_flat_of_isIntegral_pullback_specMap_of_isFractionRing
import Theorems.Thm_AlgebraicGeometry_isIntegral_pullback_specMap_of_geometricallyIntegral_pullback_snd_of_iso_pullback
import Theorems.Thm_AlgebraicGeometry_geometricallyConnected_of_bijective_algebraMap_sections
import Theorems.Thm_AlgebraicGeometry_geometricallyIntegral_of_smooth_of_geometricallyConnected
import Theorems.Thm_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isIntegral_of_iso_pullback_of_stein_of_isIntegrallyClosed_of_smoothLocus_of_isDiscreteValuationRing
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace M1B

theorem geometricallyConnected_genericFibre
    (A₀ : Type) [CommRing A₀] [IsDomain A₀]
    (X₀ : Scheme.{0}) (toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀)) [IsProper toBase₀]
    (hO : Function.Bijective (fun a : A₀ => toBase₀.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom a))) :
    GeometricallyConnected
      (pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ (FractionRing A₀))))) := by
  classical
  haveI : Module.Flat A₀ (FractionRing A₀) := IsLocalization.flat (FractionRing A₀) (nonZeroDivisors A₀)
  haveI : CompactSpace X₀ := QuasiCompact.compactSpace_of_compactSpace toBase₀
  haveI : QuasiSeparatedSpace X₀ := quasiSeparatedSpace_of_quasiSeparated toBase₀

  haveI hisoO : IsIso ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv ≫ toBase₀.appTop) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    convert hO using 1
    rfl
  have h1 := AlgebraicGeometry.isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat toBase₀ (FractionRing A₀)

  haveI hisoK : IsIso ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing A₀))).inv ≫
      (pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ (FractionRing A₀))))).appTop) :=
    h1.isIso_inl_of_isIso
  set c := pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ (FractionRing A₀)))) with hc
  haveI : CompactSpace ↑(pullback toBase₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ (FractionRing A₀))))) :=
    inferInstance
  haveI : QuasiSeparatedSpace ↑(pullback toBase₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ (FractionRing A₀))))) :=
    quasiSeparatedSpace_of_quasiSeparated c
  refine AlgebraicGeometry.geometricallyConnected_of_bijective_algebraMap_sections c (fun A' _ _ => ?_)
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (pullback.snd c (Scheme.TwoAffineOpenCover.specMap (FractionRing A₀) A')) ⊤
  haveI : Module.Flat (FractionRing A₀) A' := inferInstance
  have h2 := AlgebraicGeometry.isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat c A'
  haveI hisoA : IsIso ((Scheme.ΓSpecIso (CommRingCat.of A')).inv ≫
      (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap (FractionRing A₀) A')))).appTop) :=
    h2.isIso_inl_of_isIso
  have hbij := (ConcreteCategory.isIso_iff_bijective _).mp hisoA
  convert hbij using 1
  funext r
  rw [Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom]
  simp [Scheme.Hom.appLE, Scheme.Hom.appTop]

end M1B

theorem solution
    {L : Type} [Field L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (hA : (A : Set L) ≠ Set.univ)
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    (ι : A₀ →+* ↥A) [IsLocalHom ι] (hι : Function.Injective ι)
    (hres : Function.Surjective ((IsLocalRing.residue ↥A).comp ι))
    (halg : ∀ a : ↥A, IsAlgebraic ↥(ι.range) a)
    (X₀ : Scheme.{0}) (toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀))
    [IsIntegral X₀] [IsProper toBase₀] [Flat toBase₀] [LocallyOfFinitePresentation toBase₀]
    (hn₀ : ∀ y : X₀, IsIntegrallyClosed (X₀.presheaf.stalk y))

    (hO : Function.Bijective (fun a : A₀ => toBase₀.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom a)))

    (hgen₀ : ∀ y : X₀, (toBase₀.base y).asIdeal = ⊥ → y ∈ toBase₀.smoothLocus)

    (hsm₀ : ∀ η₀ : X₀, toBase₀.base η₀ = closedPoint A₀ → (∃ y : X₀, η₀ ⤳ y ∧ y ≠ η₀) → η₀ ∈ toBase₀.smoothLocus)
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    (iso : X ≅ Limits.pullback toBase₀ (Spec.map (CommRingCat.ofHom ι)))
    (hiso : iso.hom ≫ Limits.pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom ι)) = toBase) :
    IsIntegral X := by
  classical
  obtain ⟨hprop, hflat, hlfp⟩ := AlgebraicGeometry.isProper_and_flat_and_locallyOfFinitePresentation_of_iso_pullback_specMap A hrk hA A₀ ι hι hres halg X₀ toBase₀ hn₀ hO hgen₀ hsm₀ X toBase iso hiso
  haveI := hflat

  haveI hsmK : Smooth (pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ (FractionRing A₀))))) :=
    AlgebraicGeometry.smooth_pullback_snd_specMap_of_forall_mem_smoothLocus_of_isFractionRing (FractionRing A₀) toBase₀ hgen₀

  haveI : GeometricallyConnected (pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ (FractionRing A₀))))) :=
    M1B.geometricallyConnected_genericFibre A₀ X₀ toBase₀ hO
  have hGI : GeometricallyIntegral (pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ (FractionRing A₀))))) :=
    AlgebraicGeometry.geometricallyIntegral_of_smooth_of_geometricallyConnected _

  haveI hXL : IsIntegral ↑(pullback toBase (Spec.map (CommRingCat.ofHom (algebraMap ↥A L)))) :=
    AlgebraicGeometry.isIntegral_pullback_specMap_of_geometricallyIntegral_pullback_snd_of_iso_pullback A A₀ ι hι X₀ toBase₀ X toBase iso hiso hGI

  exact AlgebraicGeometry.isIntegral_of_flat_of_isIntegral_pullback_specMap_of_isFractionRing L toBase

end S_AlgebraicGeometry_isIntegral_of_iso_pullback_of_stein_of_isIntegrallyClosed_of_smoothLocus_of_isDiscreteValuationRing
end P2MW
export P2MW.S_AlgebraicGeometry_isIntegral_of_iso_pullback_of_stein_of_isIntegrallyClosed_of_smoothLocus_of_isDiscreteValuationRing (solution)
