-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.isLocallyFreeOfRank_pushforward_of_forall_fibre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/55d80c60-733f-5b21-b939-b38e68a4b637

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle

import Theorems.Thm_AlgebraicGeometry_RelPicard_isLocallyFreeOfRank_pushforward_of_forall_fibre_of_finiteType
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_pushforward_of_forall_exists_isPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_iso_pullback_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isPullback_snd_specMap_algebraOfHom
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finiteType_algebraOfHom
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_isLocallyFreeOfRank_pushforward_of_forall_fibre
p2m_attr_erase "instance" "AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField"
p2m_attr_erase "simp" "AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra CategoryTheory.MonoidalCategory AlgebraicGeometry.SmoothProperCurve"

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (F : (pullback c t).Modules) (hF : Scheme.Modules.IsInvertible F) (n : ℕ)
    (hfib : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F)).H1 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F)).H0 = n) :
    Scheme.Modules.IsLocallyFreeOfRank n ((Scheme.Modules.pushforward (pullback.snd c t)).obj F) := by

  refine Scheme.Modules.isLocallyFreeOfRank_pushforward_of_forall_exists_isPullback (pullback.snd c t) F n ?_
  intro y
  obtain ⟨W, hW, hyW, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens
    (show y ∈ (⊤ : T.Opens) from trivial)
  letI := Scheme.TwoAffineOpenCover.algebraOfHom t W
  haveI : Algebra.FiniteType R Γ(T, W) := Scheme.TwoAffineOpenCover.finiteType_algebraOfHom t W hW
  obtain ⟨g', hcart, -⟩ := Scheme.TwoAffineOpenCover.exists_isPullback_snd_specMap_algebraOfHom c t W hW
  refine ⟨W, hyW, Spec (CommRingCat.of Γ(T, W)),
    pullback c (Spec.map (CommRingCat.ofHom (algebraMap R Γ(T, W)))), hW.isoSpec.symm,
    pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap R Γ(T, W)))), g', hcart, ?_⟩

  refine isLocallyFreeOfRank_pushforward_of_forall_fibre_of_finiteType R c ε h𝔉 Γ(T, W)
    ((Scheme.Modules.pullback g').obj F) (hF.pullback g') n ?_

  intro k _ s 𝒲
  obtain ⟨φ, hφ, -, hmod⟩ := Scheme.Modules.exists_iso_pullback_of_isPullback (pullback.snd c t)
    (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap R Γ(T, W))))) g' hW.fromSpec hcart s
  obtain ⟨𝒱, -, -, ⟨e0⟩, ⟨e1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (fibreAt c t (s ≫ hW.fromSpec))
    (fibreAt c (Spec.map (CommRingCat.ofHom (algebraMap R Γ(T, W)))) s) φ hφ 𝒲
    (fibreModule c (Spec.map (CommRingCat.ofHom (algebraMap R Γ(T, W)))) s ((Scheme.Modules.pullback g').obj F))
    (fibreModule c t (s ≫ hW.fromSpec) F) (hmod F).some
  obtain ⟨h1, h0⟩ := hfib k (s ≫ hW.fromSpec) 𝒱
  exact ⟨e1.symm.toEquiv.subsingleton, e0.finrank_eq ▸ h0⟩

end S_AlgebraicGeometry_RelPicard_isLocallyFreeOfRank_pushforward_of_forall_fibre
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_isLocallyFreeOfRank_pushforward_of_forall_fibre (solution)
