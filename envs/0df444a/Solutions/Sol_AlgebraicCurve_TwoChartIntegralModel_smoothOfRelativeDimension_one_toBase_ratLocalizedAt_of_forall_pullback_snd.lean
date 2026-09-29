-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.smoothOfRelativeDimension_one_toBase_ratLocalizedAt_of_forall_pullback_snd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/05ba9250-7c59-546f-a257-937a25b2361b

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_AlgebraicGeometry_exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_smoothOfRelativeDimension_one_toBase_ratLocalizedAt_of_forall_pullback_snd
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

theorem solution
    (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ↥(GaloisRep.ratLocalizedAt p) F] (j : F) [Fact (j ≠ 0)]
    [Flat (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) F j)]
    [LocallyOfFinitePresentation (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) F j)]
    (hfib : ∀ (k : Type) [Field k] [IsAlgClosed k] (φ : ↥(GaloisRep.ratLocalizedAt p) →+* k),
      SmoothOfRelativeDimension 1
        (pullback.snd (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) F j) (Spec.map (CommRingCat.ofHom φ)))) :
    SmoothOfRelativeDimension 1 (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) F j) := by

  have hloc : ∀ y : ↥(TwoChartIntegralModel ↥(GaloisRep.ratLocalizedAt p) F j),
      ∃ W : (TwoChartIntegralModel ↥(GaloisRep.ratLocalizedAt p) F j).Opens, y ∈ W ∧
        SmoothOfRelativeDimension 1 (W.ι ≫ TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) F j) := by
    intro y

    obtain ⟨𝔭, h𝔭⟩ : ∃ 𝔭 : PrimeSpectrum ↥(GaloisRep.ratLocalizedAt p), (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) F j).base y = 𝔭 := ⟨_, rfl⟩
    let k : Type := AlgebraicClosure 𝔭.asIdeal.ResidueField
    let φ : ↥(GaloisRep.ratLocalizedAt p) →+* k := (algebraMap 𝔭.asIdeal.ResidueField k).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) 𝔭.asIdeal.ResidueField)
    have hker : RingHom.ker φ = 𝔭.asIdeal := by
      rw [RingHom.ker_eq_comap_bot, ← Ideal.comap_comap, ← RingHom.ker_eq_comap_bot,
        (RingHom.injective_iff_ker_eq_bot _).mp (algebraMap 𝔭.asIdeal.ResidueField k).injective,
        ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]
    have hsm := hfib k φ

    have hpt : (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) F j).base y =
        (Spec.map (CommRingCat.ofHom φ)).base (default : PrimeSpectrum k) := by
      rw [h𝔭]
      apply PrimeSpectrum.ext
      change 𝔭.asIdeal = Ideal.comap φ (default : PrimeSpectrum k).asIdeal
      rw [Ideal.eq_bot_of_prime (default : PrimeSpectrum k).asIdeal, ← RingHom.ker_eq_comap_bot, hker]
    obtain ⟨zpt, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) F j)
      (g := Spec.map (CommRingCat.ofHom φ)) y (default : PrimeSpectrum k) hpt
    exact AlgebraicGeometry.exists_mem_and_smoothOfRelativeDimension_one_of_smoothOfRelativeDimension_pullback_snd
      (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) F j) (Spec.map (CommRingCat.ofHom φ)) hsm y ⟨zpt, hz⟩
  choose W hW hsm using hloc
  exact IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension 1) W
    (top_le_iff.mp fun y _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hW y⟩) hsm

end S_AlgebraicCurve_TwoChartIntegralModel_smoothOfRelativeDimension_one_toBase_ratLocalizedAt_of_forall_pullback_snd
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_smoothOfRelativeDimension_one_toBase_ratLocalizedAt_of_forall_pullback_snd (solution)
