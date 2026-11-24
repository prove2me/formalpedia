-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_HolLineBundleToAltTransition
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_HolLineBundleToAltTransition
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:36:24.810913+00:00
-- url     : https://prove2.me/theorems/e1335d6e-41ae-419f-ad5c-94f9491a5663
-- title:
--   Hol Line Bundle To Alt Transition
-- statement:
--   Definitions and structural lemmas for Hol Line Bundle To Alt Transition, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/HolLineBundleToAltTransition.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_BergmanObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_SectionL2NormSq
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ComplexConjugate ENNReal ContDiff
noncomputable section
variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}
namespace HolLineBundle
def toIndefiniteRowSideFullHecke (L : HolLineBundle A) : IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.HolLineBundle A where
  g := L.g
  holo := L.holo
  ne_zero := L.ne_zero
  cocycle j k l x hx := (L.cocycle j k l x hx).symm
def split_model_to_place_model (L : IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.HolLineBundle A) : HolLineBundle A where
  g := L.g
  holo := L.holo
  ne_zero := L.ne_zero
  cocycle j k l x hx := (L.cocycle j k l x hx).symm
def holLineBundleEquivAlt : HolLineBundle A ≃ IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.HolLineBundle A where
  toFun := toIndefiniteRowSideFullHecke
  invFun := split_model_to_place_model
  left_inv _ := rfl
  right_inv _ := rfl
end HolLineBundle
namespace Weight
variable {L : HolLineBundle A}
theorem isWeight (W : Weight L) : IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.IsWeight L.toIndefiniteRowSideFullHecke W.φ :=
  ⟨W.smooth, W.compat⟩
def ofIsWeight {φ : Fin A.n → X → ℝ} (h : IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.IsWeight L.toIndefiniteRowSideFullHecke φ) :
    Weight L :=
  ⟨φ, h.1, h.2⟩
def split_model_to_place_model {L' : IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.HolLineBundle A} {φ : Fin A.n → X → ℝ}
    (h : IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.IsWeight L' φ) : Weight (HolLineBundle.split_model_to_place_model L') :=
  ⟨φ, h.1, h.2⟩
def equivIsWeight : Weight L ≃ {φ : Fin A.n → X → ℝ // IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.IsWeight L.toIndefiniteRowSideFullHecke φ} where
  toFun W := ⟨W.φ, W.isWeight⟩
  invFun φ := ofIsWeight φ.2
  left_inv _ := rfl
  right_inv _ := rfl
end Weight
theorem lintegral_map_chart [MeasurableSpace X] [BorelSpace X] (j : Fin A.n)
    {d : (Fin D → ℂ) → ℝ} (hd : ContinuousOn d (A.chart j).target) {g : X → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ x, g x ∂(((volume.restrict (A.chart j).target).withDensity
        fun y => ENNReal.ofReal (d y)).map (A.chart j).symm) =
      ∫⁻ y in (A.chart j).target, g ((A.chart j).symm y) * ENNReal.ofReal (d y) := by
  have hT : MeasurableSet (A.chart j).target := (A.chart j).open_target.measurableSet
  have hs : AEMeasurable (A.chart j).symm (volume.restrict (A.chart j).target) :=
    (A.chart j).continuousOn_symm.aemeasurable hT
  have hf : AEMeasurable (fun y => ENNReal.ofReal (d y)) (volume.restrict (A.chart j).target) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hd.aemeasurable hT)
  rw [lintegral_map' hg.aemeasurable (hs.mono_ac (withDensity_absolutelyContinuous _ _)),
    lintegral_withDensity_eq_lintegral_mul₀ hf
      (show AEMeasurable (fun y => g ((A.chart j).symm y)) _ from hg.comp_aemeasurable hs)]
  refine lintegral_congr fun y => ?_
  simp only [Pi.mul_apply]
  exact mul_comm _ _
namespace SmoothVolume
variable [MeasurableSpace X] [BorelSpace X]
def toIndefiniteRowSideFullHecke (dV : SmoothVolume A) : IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.SmoothVolume A where
  μ := dV.μ
  isProb := dV.isProb
  dens := dV.dens
  smooth := dV.smooth
  pos := dV.pos
  chart_eq j := Measure.ext_of_lintegral _ fun g hg => by
    rw [lintegral_map_chart j (dV.smooth j).continuousOn hg, dV.chart_lintegral j g hg]
def split_model_to_place_model (V : IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.SmoothVolume A) : SmoothVolume A where
  μ := V.μ
  isProb := V.isProb
  dens := V.dens
  smooth := V.smooth
  pos := V.pos
  chart_lintegral j g hg := by
    rw [← V.chart_eq j, lintegral_map_chart j (V.smooth j).continuousOn hg]
def holLineBundleEquivAlt : SmoothVolume A ≃ IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.SmoothVolume A where
  toFun := toIndefiniteRowSideFullHecke
  invFun := split_model_to_place_model
  left_inv _ := rfl
  right_inv _ := rfl
end SmoothVolume
variable {L : HolLineBundle A}
variable [MeasurableSpace X] [BorelSpace X]
end
end GroundTheory.Heights₂.Heights.HilbertSamuel


