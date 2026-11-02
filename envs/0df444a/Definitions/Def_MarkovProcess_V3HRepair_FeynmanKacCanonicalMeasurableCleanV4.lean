-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_FeynmanKacCanonicalMeasurableCleanV4
-- name    : MarkovProcess_V3HRepair_FeynmanKacCanonicalMeasurableCleanV4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T10:19:51.67312+00:00
-- url     : https://prove2.me/theorems/c505cd2f-8425-4a35-97e6-dbb6c9c022e8
-- title:
--   Verified MarkovProcess source repair: FeynmanKacCanonicalMeasurableCleanV4
-- statement:
--   Verified Lean 4 helper declarations for the MarkovProcess FeynmanKacCanonicalMeasurableCleanV4 module, preserving the pinned mathematical source and import dependencies.
-- source:
--   Scott Armstrong, MarkovProcess (Apache-2.0), pinned upstream 1f8060caa137731fa08029592019eeaf9d997fe5; locally verified module V3HRepaired.FeynmanKacCanonicalMeasurableCleanV4 source SHA-256 ce4f3fe75fde37bc2e66d9051fb97b2b2ce6a8784138e33b98bb90e37d9288e3. Only repaired-module import paths were converted to published Definitions.Def_MarkovProcess_V3HRepair_* names.

import Mathlib
import Definitions.Def_MarkovProcess_V3H_Trajectory_FeynmanKacFunctional_cc8a1986
import Definitions.Def_MarkovProcess_V3HRepair_ConditionalMarkovBridgeCleanV3
import Definitions.Def_MarkovProcess_V3HRepair_FeynmanKacJointMeasurableCleanV3

open MeasureTheory
open scoped NNReal
namespace MarkovProcess.ContinuousPath
variable {alpha : Type*} [TopologicalSpace alpha] [TopologicalSpace.PseudoMetrizableSpace alpha]
  [SecondCountableTopology alpha] [MeasurableSpace alpha] [BorelSpace alpha]
/-- The coordinate process is adapted to the canonical filtration. -/
theorem adapted_coordinateProcess :
    StronglyAdapted (canonicalFiltration (alpha := alpha)) (coordinateProcess (alpha := alpha)) :=
  fun t ↦ (measurable_coordinateProcess_canonicalFiltration (alpha := alpha) t).stronglyMeasurable

/-- The coordinate process is progressively measurable for the canonical filtration. -/
theorem progMeasurable_coordinateProcess :
    IsStronglyProgressive (canonicalFiltration (alpha := alpha))
      (coordinateProcess (alpha := alpha)) :=
  adapted_coordinateProcess.isStronglyProgressive_of_continuous fun omega ↦ omega.continuous

/-- The coordinate at a real time clamped to `[0, t]` is jointly measurable for the Borel
structure in time and the canonical filtration at `t`. -/
theorem measurable_clampedCoordinate (t : NNReal) :
    Measurable[(borel ℝ).prod (canonicalFiltration (alpha := alpha) t)]
      (fun p : ℝ × ContinuousPath alpha ↦ p.2 (min (Real.toNNReal p.1) t)) := by
  have htime : Measurable[(borel ℝ).prod (canonicalFiltration (alpha := alpha) t)]
      (fun p : ℝ × ContinuousPath alpha ↦ min (Real.toNNReal p.1) t) :=
    (measurable_real_toNNReal.comp measurable_fst).min measurable_const
  have hpair : Measurable[(borel ℝ).prod (canonicalFiltration (alpha := alpha) t),
      Subtype.instMeasurableSpace.prod (canonicalFiltration (alpha := alpha) t)]
      (fun p : ℝ × ContinuousPath alpha ↦
        ((⟨min (Real.toNNReal p.1) t, Set.mem_Iic.mpr (min_le_right _ _)⟩ : Set.Iic t), p.2)) :=
    (Measurable.subtype_mk htime).prodMk measurable_snd
  exact ((progMeasurable_coordinateProcess (alpha := alpha) t).comp_measurable hpair).measurable

end MarkovProcess.ContinuousPath

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace MarkovProcess.SubMarkovKernelSemigroup
noncomputable section
variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [SecondCountableTopology alpha]

/-- Measurability of a Bochner integral in a parameter, with the parameter sigma-algebra given by
a variable so that it can be instantiated at a filtration. -/
theorem stronglyMeasurable_integral_prod {Omega : Type*} {mOmega : MeasurableSpace Omega}
    (mu : Measure ℝ) [SFinite mu] {phi : ℝ × Omega → ℝ}
    (hphi : StronglyMeasurable[(borel ℝ).prod mOmega] phi) :
    StronglyMeasurable[mOmega] fun omega : Omega ↦ ∫ s, phi (s, omega) ∂mu :=
  hphi.integral_prod_left'

/-- The accumulated potential at a deterministic time is strongly measurable for the canonical
filtration at that time. -/
theorem stronglyMeasurable_feynmanKacAdditiveFunctional_canonicalFiltration {q : alpha → ℝ}
    (hq : Measurable q) (t : NNReal) :
    StronglyMeasurable[ContinuousPath.canonicalFiltration (alpha := alpha) t]
      (feynmanKacAdditiveFunctional q t) := by
  have hclamp := ContinuousPath.measurable_clampedCoordinate (alpha := alpha) t
  have hprod : StronglyMeasurable[ContinuousPath.canonicalFiltration (alpha := alpha) t]
      (fun omega : ContinuousPath alpha ↦
      ∫ s, q (omega (min (Real.toNNReal s) t))
        ∂(volume.restrict (Ioc (0 : ℝ) t))) :=
    stronglyMeasurable_integral_prod (volume.restrict (Ioc (0 : ℝ) t))
      ((hq.comp hclamp).stronglyMeasurable)
  have hfun : feynmanKacAdditiveFunctional q t = fun omega : ContinuousPath alpha ↦
      ∫ s, q (omega (min (Real.toNNReal s) t))
        ∂(volume.restrict (Ioc (0 : ℝ) t)) := by
    funext omega
    rw [feynmanKacAdditiveFunctional_apply, intervalIntegral.integral_of_le t.coe_nonneg]
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs ↦ ?_
    rw [min_eq_left (Real.toNNReal_le_iff_le_coe.mpr hs.2)]
  rw [hfun]
  exact hprod


end
end MarkovProcess.SubMarkovKernelSemigroup
#print axioms MarkovProcess.SubMarkovKernelSemigroup.stronglyMeasurable_feynmanKacAdditiveFunctional_canonicalFiltration


