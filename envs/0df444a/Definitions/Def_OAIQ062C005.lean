-- Prove2me | Definitions.Def_OAIQ062C005
-- name    : OAIQ062C005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T23:58:00.056218+00:00
-- url     : https://prove2.me/theorems/95778ca1-e0f7-4330-8c89-04a6ca9a7659
-- title:
--   Definitions bundle OAIQ062C005 of the split of OpenAI, Generalized outer-electron radii of neutral Coulomb atoms (result family 263)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.NeutralAtom.generalized_outer_radii`, carved from OpenAI's openai/math development (OpenAI, *Generalized outer-electron radii of neutral Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 229 declarations of OpenAI's Lean: 48 definitions, 4 inductive types or structures, 9 instances and 168 theorems. The definitions and types are `OAI.Coulomb.centeredSpinMeasure`, `OAI.Coulomb.coarseCubeModes`, `OAI.Coulomb.coloredObservable`, `OAI.Coulomb.configurationMeasurableEquiv`, `OAI.Coulomb.countTest`, `OAI.Coulomb.deletedLabels`, `OAI.Coulomb.formPair`, `OAI.Coulomb.gridCellDensity`, `OAI.Coulomb.gridShift`, `OAI.Coulomb.highParticleDensity`, `OAI.Coulomb.highProjection`, `OAI.Coulomb.kineticPair`, `OAI.Coulomb.lowProjection`, `OAI.Coulomb.massPair`, `OAI.Coulomb.nuclearPair`, `OAI.Coulomb.outerAppendEquiv`, `OAI.Coulomb.positiveInnerDeficit`, `OAI.Coulomb.radialShell`, `OAI.Coulomb.radialShellDensity`, `OAI.Coulomb.radialShellMoment`, `OAI.Coulomb.rawTFBregman`, `OAI.Coulomb.rawTFNegativeError`, `OAI.Coulomb.rawToTFLp`, `OAI.Coulomb.regularizedU`, `OAI.Coulomb.repulsionPair`, `OAI.Coulomb.spinCubeMeasure`, `OAI.Coulomb.spinCubeMode`, `OAI.Coulomb.spinPermEquiv`, `OAI.Coulomb.tfScalarDensity`, `OAI.NeutralAtom.PhysicalRetainedFamily`, `OAI.NeutralAtom.PhysicalRetainedFamily.toAnalytic`, `OAI.NeutralAtom.PropagationStepHypotheses`, `OAI.NeutralAtom.RetainedAnalyticFamily`, `OAI.NeutralAtom.RetainedAnalyticFamily.select`, `OAI.NeutralAtom.RetainedAnalyticSequence`, `OAI.NeutralAtom.RetainedAnalyticSequence.field`, `OAI.NeutralAtom.RetainedAnalyticSequence.reindex`, `OAI.NeutralAtom.WeakLaplacianGE`, `OAI.NeutralAtom.WeakNuclearSubsolution`, `OAI.NeutralAtom.aTF` and 12 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `CoulombRadii_FieldAnalysis_BodyCoefficient`, `CoulombRadii_FieldAnalysis_ColoredObservable`, `CoulombRadii_FieldAnalysis_ConfigurationMeasurableEquiv`, `CoulombRadii_FieldAnalysis_FermionicCoefficients`, `CoulombRadii_FieldAnalysis_Field`, `CoulombRadii_FieldAnalysis_FirstParticleDensityNonneg`, `CoulombRadii_FieldAnalysis_FlatDensityPower`, `CoulombRadii_FieldAnalysis_GridIndex`, `CoulombRadii_FieldAnalysis_GroupFermionicCoefficients`, `CoulombRadii_FieldAnalysis_HighProjection`, `CoulombRadii_FieldAnalysis_LowProjection`, `CoulombRadii_FieldAnalysis_NewtonInterior`, `CoulombRadii_FieldAnalysis_OuterJoinConfiguration`, `CoulombRadii_FieldAnalysis_PhysicalPoisson`, `CoulombRadii_FieldAnalysis_RawThomasFermiEnergy`, `CoulombRadii_FieldAnalysis_RetainedFinePower`, `CoulombRadii_FieldAnalysis_RotatedDensityPower`, `CoulombRadii_FieldAnalysis_SpinCubeEquiv`, `CoulombRadii_FieldAnalysis_SpinMode`, `CoulombRadii_FieldAnalysis_Weighted`, `CoulombRadii_FormDomain_CoreSliceRegular`, `CoulombRadii_FormDomain_ExplicitMultiplyGradient`, `CoulombRadii_FormDomain_H1Pairing`, `CoulombRadii_FormDomain_SmoothCompact`, `CoulombRadii_FormDomain_Translate`, `CoulombRadii_Localization_DeletedLabels`, `CoulombRadii_Localization_HarmonicInterior`, `CoulombRadii_Localization_HarmonicScale`, `CoulombRadii_Localization_RegularizedBounds`, `CoulombRadii_Packets_CoulombKernel`, `CoulombRadii_Packets_TailMoment`, `CoulombRadii_Propagation_InitializationBranch`, `CoulombRadii_Propagation_MaximumMollifier`, `CoulombRadii_Propagation_NearActiveMaximum`, `CoulombRadii_Propagation_PropagationAverage`, `CoulombRadii_Propagation_PropagationBarrierBounds`, `CoulombRadii_Propagation_PropagationBarrierOffset`, `CoulombRadii_Propagation_PropagationMaximum`, `CoulombRadii_Propagation_PropagationRegularity`, `CoulombRadii_Propagation_PropagationStepWeak`, `CoulombRadii_Propagation_RadialMaxSplice`, `CoulombRadii_Propagation_SmoothMaximum`, `CoulombRadii_Propagation_TfReaction`, `CoulombRadii_Propagation_WeakLocality`, `CoulombRadii_Propagation_WeakReactionMax`, `CoulombRadii_RadialBounds_NearActive`, `CoulombRadii_RadialBounds_Radial`, `CoulombRadii_RandomFields_ConditionalMatching`, `CoulombRadii_Screening_CoreCount`, `CoulombRadii_Screening_ScaledTest`, `CoulombRadii_Screening_UniformCountConsequences`, `CoulombRadii_ThomasFermi_AtomicRefinedGap`, `CoulombRadii_ThomasFermi_PatchGeometry`, `CoulombRadii_ThomasFermi_PatchResponse`, `CoulombRadii_ThomasFermi_Rescaling`, `CoulombRadii_ThomasFermi_ScaledProfile`, `CoulombRadii_ThomasFermi_TFCountTest`, `CoulombRadii_ThomasFermi_TFNegativeGap`, `CoulombRadii_ThomasFermi_TfExtendNonneg`, `CoulombRadii_Variational_Axis`, `CoulombRadii_Variational_CorrectionDensity`, `CoulombRadii_Variational_PuncturedPosition`, `CoulombRadii_Variational_RetainedAnalyticSequence`, `CoulombRadii_Variational_WeakAdd`, `CoulombRadii_Variational_WeakLaplacian`.
--
--   **Imports.** It imports the published bundle `Def_CoulombRadii`; the bundles `OAIQ062C000`, `OAIQ062C001` and `OAIQ062C002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ062C006` and `OAIQ062C007`; the statements `OAI.NeutralAtom.physical_initial_event` and `OAI.NeutralAtom.physical_normalized_inverse_point`.
-- source:
--   OpenAI, Generalized outer-electron radii of neutral Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-outer-electron-radii-of-neutral-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_CoulombRadii
import Definitions.Def_OAIQ062C000
import Definitions.Def_OAIQ062C001
import Definitions.Def_OAIQ062C002

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_FermionicCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb

open scoped Classical

noncomputable def spinPermEquiv {n : ℕ} (p : Equiv.Perm (Fin n)) : Spins n ≃ Spins n where
  toFun s := s ∘ p
  invFun s := s ∘ p.symm
  left_inv s := by ext i; simp
  right_inv s := by ext i; simp

end Coulomb

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_ConfigurationMeasurableEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb

open scoped Classical

open scoped Classical

noncomputable def configurationMeasurableEquiv (n : ℕ) :
    Configuration n ≃ᵐ (Fin n → Space) :=
  ((MeasurableEquiv.toLp 2 ((Fin n × Fin 3) → ℝ)).symm.trans
    (MeasurableEquiv.curry (Fin n) (Fin 3) ℝ)).trans
    (MeasurableEquiv.piCongrRight fun _ => MeasurableEquiv.toLp 2 (Fin 3 → ℝ))

theorem configurationMeasurableEquiv_measurePreserving (n : ℕ) :
    MeasurePreserving (configurationMeasurableEquiv n) volume volume := by
  apply MeasurePreserving.trans
    (MeasurePreserving.trans (PiLp.volume_preserving_ofLp (Fin n × Fin 3))
      (measurePreserving_uncurry (fun (_ : Fin n) (_ : Fin 3) =>
         (volume : Measure ℝ))).symm)
  exact volume_preserving_pi (fun _ => PiLp.volume_preserving_toLp (Fin 3))

end Coulomb
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_SpinMode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb
open scoped Classical
open scoped Classical
open Filter
open scoped Convolution
open ContinuousLinearMap

noncomputable def spinCubeMeasure (b : ℝ) : Measure (Fin 2 × (Fin 3 → ℝ)) :=
  Measure.count.prod (cubeMeasure b 3)

noncomputable def spinCubeMode (b : ℝ) (a : SpinMode) (x : Fin 2 × (Fin 3 → ℝ)) : ℂ :=
  spinDelta a.1 x.1 * cubeMode b a.2 x.2

end Coulomb
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_LowProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb
section LowProjection
variable {A B ι : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [SigmaFinite μ] [SigmaFinite ν]
    (v : ι → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)

noncomputable def lowProjection (s : Finset ι) (f : B × A → ℂ) (z : B × A) : ℂ :=
  ∑ i ∈ s, fiberContract (μ := μ) (v i) f z.1 * v i z.2

end LowProjection
end Coulomb

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_HighProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb

section
variable {A B ι : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [SigmaFinite μ] [SigmaFinite ν]
    (v : ι → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0)

noncomputable def highProjection (s : Finset ι) (f : B × A → ℂ) : B × A → ℂ :=
  f - lowProjection (μ := μ) v s f

end

end Coulomb
open MeasureTheory Set Filter
open scoped ENNReal NNReal

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_Weighted
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
namespace Coulomb

noncomputable def highParticleDensity {A ι : Type*} [MeasurableSpace A]
    {μ : Measure A} {n : ℕ} (v : ι → A → ℂ) (s : Finset ι)
    (f : (Fin (n+1) → A) → ℂ) (x : A) : ℝ :=
  ((n+1:ℕ):ℝ)*(∫ y : Fin n → A,
    ‖highProjection (μ := μ) v s (firstFiber f) (y,x)‖^2 ∂(Measure.pi fun _ => μ))

end Coulomb

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_FirstParticleDensityNonneg
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
namespace Coulomb

def coarseCubeModes (k : ℕ) : Finset SpinMode :=
  Finset.univ.product (Fintype.piFinset fun _ : Fin 3 => Finset.range (2^k+1))

end Coulomb

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_SpinCubeEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
namespace Coulomb
instance spinCubeMeasure_isFinite (b : ℝ) : IsFiniteMeasure (spinCubeMeasure b) := by
  unfold spinCubeMeasure
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end Coulomb

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_Translate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb

lemma mass_translate {n : ℕ} (ψ : H1Vector n) (c : Configuration n) :
    mass (ψ.translate c) = mass ψ := by
  unfold mass H1Vector.translate
  congr 1
  funext s
  exact integral_add_right_eq_self (fun x => ‖ψ.value s x‖^2) c

lemma kinetic_translate {n : ℕ} (ψ : H1Vector n) (c : Configuration n) :
    kinetic (ψ.translate c) = kinetic ψ := by
  unfold kinetic H1Vector.translate
  congr 2
  funext s
  congr 1
  funext a
  exact integral_add_right_eq_self (fun x => ‖ψ.gradient s a x‖^2) c

noncomputable def centeredSpinMeasure (R : ℝ) : Measure (Fin 2 × (Fin 3 → ℝ)) :=
  spinSpaceMeasure.restrict (centeredSpinCube R)
instance centeredSpinMeasure_sigmaFinite (R : ℝ) : SigmaFinite (centeredSpinMeasure R) := by
  unfold centeredSpinMeasure
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_SmoothCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma positionCLM_apply {n : ℕ} (i : Fin n) (x : Configuration n) :
    positionCLM i x = position x i := rfl

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Variational_Axis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
namespace NeutralAtom

theorem coordinateLaplacian_radialPower {x : Position} (hx : x ≠ 0) (p : ℝ) :
    coordinateLaplacian (radialPower p) x = 2*p*(2*p+1)*(‖x‖^2)^(p-1) := by
  have hx0 : 0 < ‖x‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  unfold coordinateLaplacian radialPower
  conv_lhs => arg 2; ext a; arg 1; arg 1; ext t; rw [norm_sq_axis_shift]
  simp only [second_deriv_quadratic_rpow hx0, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  have hpow : (‖x‖^2)^(p-2) * (‖x‖^2) = (‖x‖^2)^(p-1) := by
    rw [← Real.rpow_add_one hx0.ne']
    congr 1
    ring
  calc
    _ = 4*p*(p-1)*(‖x‖^2)^(p-2)*(∑ a : Fin 3, (x a)^2) +
        6*p*(‖x‖^2)^(p-1) := by
      rw [Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro a _
        ring
      · norm_num
        ring
    _ = _ := by
      rw [← EuclideanSpace.real_norm_sq_eq]
      calc
        _ = 4*p*(p-1)*((‖x‖^2)^(p-2) * ‖x‖^2) +
          6*p*(‖x‖^2)^(p-1) := by ring
        _ = _ := by rw [hpow]; ring

open scoped Convolution
open ContinuousLinearMap

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Variational_WeakLaplacian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
namespace NeutralAtom
open scoped Convolution
open ContinuousLinearMap

theorem coordinateLaplacian_add_at {f g : Position → ℝ} {x : Position}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    coordinateLaplacian (fun y => f y+g y) x = coordinateLaplacian f x+coordinateLaplacian g x := by
  rw [coordinateLaplacian_eq_partials (hf.add hg), coordinateLaplacian_eq_partials hf,
    coordinateLaplacian_eq_partials hg, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  have he : dirPartial (fun y => f y+g y) (axis a) =ᶠ[𝓝 x]
      fun y => dirPartial f (axis a) y+dirPartial g (axis a) y := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hy hz
    exact congrArg (fun T : Position →L[ℝ] ℝ => T (axis a))
      (fderiv_add (hy.differentiableAt (by norm_num)) (hz.differentiableAt (by norm_num)))
  have hfd : DifferentiableAt ℝ (dirPartial f (axis a)) x :=
    ((hf.fderiv_right (show (1 : WithTop ℕ∞)+1 ≤ 2 by norm_num)).clm_apply
      contDiffAt_const).differentiableAt_one
  have hgd : DifferentiableAt ℝ (dirPartial g (axis a)) x :=
    ((hg.fderiv_right (show (1 : WithTop ℕ∞)+1 ≤ 2 by norm_num)).clm_apply
      contDiffAt_const).differentiableAt_one
  change fderiv ℝ _ x (axis a) = _
  rw [he.fderiv_eq]
  exact congrArg (fun T : Position →L[ℝ] ℝ => T (axis a)) (fderiv_add hfd hgd)

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_CoulombKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
namespace NeutralAtom
open scoped Convolution
open ContinuousLinearMap

def kernelBallMass (r : ℝ) : ℝ := ∫ y in Metric.ball (0 : Position) r, coulombKernel y

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_ScaledProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
namespace NeutralAtom
open scoped Convolution
open ContinuousLinearMap

def aTF : ℝ := (12/(4*Real.pi*kTF))^2

theorem kTF_pos : 0 < kTF := by unfold kTF; positivity

def WeakLaplacianGE (f : Position → ℝ) (U : Set Position) (q : Position → ℝ) : Prop :=
  ∀ φ : Position → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
    (∀ x, 0 ≤ φ x) → (∫ x, q x*φ x) ≤ ∫ x, f x*coordinateLaplacian φ x

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Variational_CorrectionDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
namespace NeutralAtom
open scoped Convolution
open ContinuousLinearMap

def WeakNuclearSubsolution (U : Position → ℝ) (lam : ℝ) (Ω : Set Position)
    (s : Position → ℝ) : Prop :=
  ∀ φ : Position → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
    (∀ x, 0 ≤ φ x) →
    -(4*Real.pi*lam*φ 0)+(∫ x, s x*φ x) ≤ ∫ x, U x*coordinateLaplacian φ x

theorem integral_coordinateLaplacian {φ : Position → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ x, coordinateLaplacian φ x) = 0 := by
  have hh := integral_mul_coordinateLaplacian_eq
    (f := fun _ => (1:ℝ)) (fun _ _ => contDiffAt_const) hφ hc
  simpa [coordinateLaplacian] using hh

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Localization_HarmonicInterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
noncomputable section
namespace NeutralAtom

theorem dirPartial_regularizedKernel {ε : ℝ} (hε : ε ≠ 0)
    (a : Fin 3) (x : Position) :
    dirPartial (regularizedKernel ε) (axis a) x =
      -(x a)*(‖x‖^2+ε^2)^(-3/2 : ℝ) := by
  have hq : 0 < ‖x‖^2+ε^2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hε)
  have heq : (fun t : ℝ => regularizedKernel ε (x+t • axis a)) =
      fun t : ℝ => (‖x‖^2+2*t*x a+t^2+ε^2)^(-1/2 : ℝ) := by
    ext t
    rw [regularizedKernel, norm_sq_axis_shift]
  have hd : HasDerivAt (fun t : ℝ => ‖x‖^2+2*t*x a+t^2+ε^2) (2*x a) 0 := by
    convert (((hasDerivAt_const 0 (‖x‖^2)).add
      (((hasDerivAt_id 0).const_mul 2).mul_const (x a))).add
      ((hasDerivAt_id 0).pow 2)).add_const (ε^2) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | norm_num
  have hr := hd.rpow_const (p := (-1/2 : ℝ)) (Or.inl (by simpa using hq.ne'))
  have he := deriv_affine_line (v := axis a) (t := 0)
    (by simpa using (contDiff_regularizedKernel hε).differentiable (by norm_num) x)
  simp only [zero_smul, add_zero] at he
  unfold dirPartial
  rw [← he, heq]
  rw [hr.deriv]
  norm_num
  ring_nf
  all_goals simp

def cutoffHarmonicKernel (χ : Position → ℝ) (x : Position) : ℝ :=
  (coulombKernel x*coordinateLaplacian χ x +
    2*∑ a : Fin 3, coulombPartial a x*dirPartial χ (axis a) x)/(4*Real.pi)

theorem contDiff_coordinateLaplacian {χ : Position → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (coordinateLaplacian χ) := by
  have he : coordinateLaplacian χ = fun x => ∑ a : Fin 3,
      dirPartial (dirPartial χ (axis a)) (axis a) x := funext (fun x =>
    coordinateLaplacian_eq_partials
      (hχ.of_le (show (2 : WithTop ℕ∞) ≤ ∞ by exact WithTop.coe_le_coe.mpr le_top)).contDiffAt)
  rw [he]
  apply ContDiff.sum
  intro a _
  have hp : ContDiff ℝ ∞ (dirPartial χ (axis a)) :=
    contDiff_partial (n := ∞) (by simpa using hχ) (axis a)
  exact contDiff_partial (n := ∞) (by simpa using hp) (axis a)

end NeutralAtom
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Localization_RegularizedBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators ContDiff
noncomputable section
namespace NeutralAtom
lemma regularizedKernel_uniform_bound {l:ℝ} (hl:l≠0) (x:Position) :
    |regularizedKernel l x|≤(l^2)^(-1/2:ℝ) := by
  unfold regularizedKernel
  rw [abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  exact Real.rpow_le_rpow_of_nonpos (sq_pos_of_ne_zero hl) (by nlinarith [sq_nonneg ‖x‖]) (by norm_num)
lemma regularizedPartial_uniform_bound {l:ℝ} (hl:l≠0) (x:Position) (a:Fin 3) :
    |dirPartial (regularizedKernel l) (axis a) x|≤(l^2)^(-1/2:ℝ)+(l^2)^(-3/2:ℝ) := by
  let q:=‖x‖^2+l^2
  have hq:0<q:=add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hl)
  have hbase:l^2≤q:=by dsimp [q]; nlinarith [sq_nonneg ‖x‖]
  have ha:|x a|≤q+1 := by
    have H:|x a|≤‖x‖:=by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x a
    dsimp [q]
    nlinarith [sq_nonneg (‖x‖-1),sq_nonneg l]
  have he:q*q^(-3/2:ℝ)=q^(-1/2:ℝ) := by
    rw [mul_comm,←Real.rpow_add_one hq.ne']
    norm_num
  rw [dirPartial_regularizedKernel hl,abs_mul,abs_neg,
    abs_of_nonneg (Real.rpow_nonneg hq.le _)]
  change |x a| *q^(-3/2:ℝ)≤_
  calc
    _≤(q+1)*q^(-3/2:ℝ):=mul_le_mul_of_nonneg_right ha (Real.rpow_nonneg hq.le _)
    _=q^(-1/2:ℝ)+q^(-3/2:ℝ):=by rw [add_mul,he,one_mul]
    _≤_:=add_le_add (Real.rpow_le_rpow_of_nonpos (sq_pos_of_ne_zero hl) hbase (by norm_num))
      (Real.rpow_le_rpow_of_nonpos (sq_pos_of_ne_zero hl) hbase (by norm_num))
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_BodyCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Classical ContDiff
noncomputable section
namespace Coulomb

def regularizedU (l e:ℝ) (x:Space):ℝ:=NeutralAtom.regularizedKernel l x+e
lemma regularizedU_pos {l e:ℝ} (he:0<e) (x:Space):0 < regularizedU l e x :=
  add_pos_of_nonneg_of_pos (Real.rpow_nonneg (by positivity) _) he
lemma regularizedU_ge {l e:ℝ} (x:Space):e ≤ regularizedU l e x := by
  unfold regularizedU NeutralAtom.regularizedKernel
  have H:=Real.rpow_nonneg (by positivity : 0≤‖x‖^2+l^2) (-1/2:ℝ)
  linarith
lemma regularizedU_partial {l:ℝ} (hl:l≠0) (e:ℝ) (a:Fin 3) (x:Space):
    fderiv ℝ (regularizedU l e) x (EuclideanSpace.single a 1)=
      NeutralAtom.dirPartial (NeutralAtom.regularizedKernel l) (NeutralAtom.axis a) x := by
  unfold regularizedU NeutralAtom.dirPartial NeutralAtom.axis
  have hderiv := ((NeutralAtom.contDiff_regularizedKernel hl).differentiable (by simp) x).hasFDerivAt
  rw [(hderiv.add_const e).fderiv]
lemma regularizedU_smooth {l:ℝ} (hl:l≠0) (e:ℝ):ContDiff ℝ ∞ (regularizedU l e):=
  (NeutralAtom.contDiff_regularizedKernel hl).add contDiff_const

end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_GroupFermionicCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Coulomb

open scoped Classical

open scoped Classical

open Filter
open scoped Convolution
open ContinuousLinearMap

lemma thomasFermiCoefficient_pos : 0 < thomasFermiCoefficient := by
  unfold thomasFermiCoefficient
  positivity

noncomputable def gridShift {n : ℕ} (b : ℝ) (k : GridAssignment n) : Configuration n :=
  WithLp.toLp 2 (fun ij => b*(k ij : ℝ))

lemma gridShift_hasSum_integral {n : ℕ} {b : ℝ} (hb : 0 < b)
    {f : Configuration n → ℝ} (hf : Integrable f) :
    HasSum (fun k : GridAssignment n =>
        ∫ x, f (WithLp.toLp 2 x + gridShift b k)
          ∂(finiteCubeMeasure b (Fin n × Fin 3))) (∫ x, f x) := by
  have H := gridBox_hasSum_integral hb
    ((PiLp.volume_preserving_toLp (Fin n × Fin 3)).integrable_comp_of_integrable hf)
  have he := (PiLp.volume_preserving_toLp (Fin n × Fin 3)).integral_comp
    ((PiLp.homeomorph 2 (fun _ : Fin n × Fin 3 => ℝ)).symm.measurableEmbedding) f
  simpa only [Function.comp_apply, WithLp.toLp_add, gridShift, he] using H

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_GridIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace Coulomb
open scoped Classical
open scoped Classical
open Filter
open scoped Convolution
open ContinuousLinearMap

section GridIndex
variable {I : Type*}

lemma mem_gridBox_index {b : ℝ} (hb : 0 < b) (x : I → ℝ) :
    x ∈ gridBox b (gridIndex b x) := by
  rw [gridBox, Set.mem_univ_pi]
  intro i
  have hL := Int.ceil_lt_add_one (x i / b)
  have hU := Int.le_ceil (x i / b)
  constructor
  · have h : (⌈x i/b⌉ : ℝ)-1 < x i/b := by linarith
    have hh := (lt_div_iff₀ hb).mp h
    simp only [gridIndex, Int.cast_sub, Int.cast_one]
    nlinarith
  · have hh := (div_le_iff₀ hb).mp hU
    simp only [gridIndex, Int.cast_sub, Int.cast_one]
    nlinarith

end GridIndex

lemma gridBox_volume {I : Type*} [Fintype I] (b : ℝ) (k : I → ℤ) :
    volume (gridBox b k) = ENNReal.ofReal b ^ Fintype.card I := by
  simp only [gridBox, volume_pi, Measure.pi_pi, Real.volume_Ioc]
  have he (i : I) : b*((k i : ℝ)+1) - b*(k i : ℝ) = b := by ring
  simp only [he, Finset.prod_const, Finset.card_univ]

noncomputable def gridCellDensity {n : ℕ} (b : ℝ) (k : GridAssignment n)
    (y : Fin 3 → ℝ) : ℝ :=
  ∑ c : Set.range (gridCell k), (gridBox b c.val).indicator
    (fun _ => (b⁻¹)^3 *
      (Fintype.card {i : Fin n // Set.rangeFactorization (gridCell k) i = c} : ℝ)) y

lemma gridCellDensity_power_integral {n : ℕ} {b : ℝ} (hb : 0 < b)
    (k : GridAssignment n) :
    (∫ y : Fin 3 → ℝ, gridCellDensity b k y ^ (5/3 : ℝ)) =
      (b⁻¹)^2 * gridLeadingCount k := by
  let w : Set.range (gridCell k) → ℝ := fun c => (b⁻¹)^3 *
    (Fintype.card {i : Fin n // Set.rangeFactorization (gridCell k) i = c} : ℝ)
  have hd : Pairwise (fun c d : Set.range (gridCell k) =>
      Disjoint (gridBox b c.val) (gridBox b d.val)) := by
    intro c d hcd
    exact gridBox_disjoint hb (fun he => hcd (Subtype.ext he))
  have hi (c : Set.range (gridCell k)) :
      Integrable ((gridBox b c.val).indicator (fun _ => (w c)^(5/3 : ℝ))) :=
    (integrableOn_const (by rw [gridBox_volume]; finiteness)).integrable_indicator
      (gridBox_measurable b c.val)
  have he (c : Set.range (gridCell k)) :
      (∫ y, (gridBox b c.val).indicator (fun _ => (w c)^(5/3 : ℝ)) y) =
        (b⁻¹)^2 *
          (Fintype.card {i : Fin n // Set.rangeFactorization (gridCell k) i = c} : ℝ) ^
            (5/3 : ℝ) := by
    rw [integral_indicator (gridBox_measurable b c.val), integral_const]
    simp only [Measure.real, Measure.restrict_apply_univ, gridBox_volume,
      Fintype.card_fin, ENNReal.toReal_pow, ENNReal.toReal_ofReal hb.le, smul_eq_mul]
    exact cell_power_scaling hb (Nat.cast_nonneg _)
  calc
    _ = ∫ y, ∑ c : Set.range (gridCell k),
        (gridBox b c.val).indicator (fun _ => (w c)^(5/3 : ℝ)) y := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y =>
        sum_indicator_rpow_disjoint (fun c : Set.range (gridCell k) => gridBox b c.val)
          hd w (by norm_num) y)
    _ = ∑ c : Set.range (gridCell k), ∫ y,
        (gridBox b c.val).indicator (fun _ => (w c)^(5/3 : ℝ)) y :=
      integral_finsetSum _ (fun c _ => hi c)
    _ = _ := by
      simp_rw [he]
      rw [← Finset.mul_sum]
      rfl

lemma sameGridCell_eq_ite (b : ℝ) (x y : Fin 3 → ℝ) :
    sameGridCell b x y = if gridIndex b x = gridIndex b y then 1 else 0 := by
  classical
  by_cases he : gridIndex b x = gridIndex b y
  · rw [ite_eq_left he]
    have hj (j : Fin 3) : sameCell1 b (x j) (y j) = 1 := by
      rw [sameCell1_eq_ite]
      exact ite_eq_left (congrFun he j)
    simp only [sameGridCell, hj, Finset.prod_const_one]
  · rw [ite_eq_right he]
    obtain ⟨j,hj⟩ := Function.ne_iff.mp he
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rw [sameCell1_eq_ite]
    exact ite_eq_right hj

lemma gridCellDensity_sum_particles {n : ℕ} (b : ℝ) (k : GridAssignment n)
    (y : Fin 3 → ℝ) :
    gridCellDensity b k y = (b⁻¹)^3 *
      ∑ i : Fin n, (gridBox b (gridCell k i)).indicator (fun _ => (1 : ℝ)) y := by
  classical
  unfold gridCellDensity
  have he (c : Set.range (gridCell k)) :
      (gridBox b c.val).indicator
        (fun _ => (b⁻¹)^3 *
          (Fintype.card {i : Fin n // Set.rangeFactorization (gridCell k) i = c} : ℝ)) y =
      (b⁻¹)^3 *
        ((Fintype.card {i : Fin n // Set.rangeFactorization (gridCell k) i = c} : ℝ) *
          (gridBox b c.val).indicator (fun _ => (1 : ℝ)) y) := by
    by_cases hy : y ∈ gridBox b c.val
    · simp only [Set.indicator_of_mem hy, mul_one]
    · simp only [Set.indicator_of_notMem hy, mul_zero]
  simp_rw [he]
  rw [← Finset.mul_sum, sum_fiber_weight]
  rfl

lemma mem_gridBox_iff_index {I : Type*} {b : ℝ} (hb : 0 < b) (k : I → ℤ)
    (x : I → ℝ) : x ∈ gridBox b k ↔ gridIndex b x = k := by
  constructor
  · exact gridIndex_of_mem hb
  · intro he
    rw [← he]
    exact mem_gridBox_index hb x

lemma sameGridCell_eq_indicator {b : ℝ} (hb : 0 < b) (x y : Fin 3 → ℝ) :
    sameGridCell b x y = (gridBox b (gridIndex b x)).indicator (fun _ => (1 : ℝ)) y := by
  rw [sameGridCell_eq_ite]
  simp only [Set.indicator, mem_gridBox_iff_index hb, eq_comm]

lemma translatedGridDensity_eq_cell {n : ℕ} {b : ℝ} (hb : 0 < b)
    (t : Fin 3 → ℝ) (x : (Fin n × Fin 3) → ℝ) (y : Fin 3 → ℝ) :
    translatedGridDensity b t x y =
      gridCellDensity b (gridIndex b (fun ij => x ij+t ij.2)) (y+t) := by
  rw [gridCellDensity_sum_particles]
  unfold translatedGridDensity
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact sameGridCell_eq_indicator hb (fun j => x (i,j)+t j) (y+t)

lemma translatedGridDensity_power_integral {n : ℕ} {b : ℝ} (hb : 0 < b)
    (t : Fin 3 → ℝ) (x : (Fin n × Fin 3) → ℝ) :
    (∫ y : Fin 3 → ℝ, translatedGridDensity b t x y ^ (5/3 : ℝ)) =
      (b⁻¹)^2 * gridLeadingCount (gridIndex b (fun ij => x ij+t ij.2)) := by
  simp_rw [translatedGridDensity_eq_cell hb]
  calc
    _ = ∫ y, gridCellDensity b (gridIndex b (fun ij => x ij+t ij.2)) y ^ (5/3 : ℝ) :=
      integral_add_right_eq_self _ t
    _ = _ := gridCellDensity_power_integral hb _

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_FlatDensityPower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace Coulomb
open scoped Classical
open scoped Classical
open Filter
open scoped Convolution
open ContinuousLinearMap

lemma translatedGridDensity_power_integrable_translation {n : ℕ} {b : ℝ} (hb : 0 < b)
    (x : (Fin n × Fin 3) → ℝ) (y : Fin 3 → ℝ) :
    Integrable (fun t => translatedGridDensity b t x y ^ (5/3:ℝ))
      (finiteCubeMeasure b (Fin 3)) := by
  apply (integrable_const (((b⁻¹)^3*n) ^ (5/3 : ℝ))).mono'
  · exact ((Real.continuous_rpow_const (by norm_num : (0:ℝ) ≤ 5/3)).measurable.comp
      (translatedGridDensity_measurable b x y)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (translatedGridDensity_nonneg hb ..) _)]
      exact Real.rpow_le_rpow (translatedGridDensity_nonneg hb ..)
        (translatedGridDensity_le hb ..) (by norm_num))

lemma flatFineKernel_Jensen {n : ℕ} {b : ℝ} (hb : 0 < b)
    (x : (Fin n × Fin 3) → ℝ) (y : Fin 3 → ℝ) :
    (∑ i : Fin n, flatFineKernel b (y-(fun j => x (i,j)))) ^ (5/3:ℝ) ≤
      (b⁻¹)^3 * ∫ t, translatedGridDensity b t x y ^ (5/3:ℝ)
        ∂finiteCubeMeasure b (Fin 3) := by
  have := finiteCubeMeasure_neZero hb (Fin 3)
  have H := (convexOn_rpow (by norm_num : (1:ℝ) ≤ 5/3)).map_average_le
    (Real.continuous_rpow_const (by norm_num : (0:ℝ) ≤ 5/3)).continuousOn
    isClosed_Ici
    (Filter.Eventually.of_forall (fun t => translatedGridDensity_nonneg hb t x y))
    (translatedGridDensity_integrable b x y)
    (translatedGridDensity_power_integrable_translation hb x y)
  simp only [average_eq, finiteCubeMeasure_real_univ hb, Fintype.card_fin,
    ← inv_pow, smul_eq_mul, translatedGridDensity_integral hb] at H
  exact H

lemma gridCellDensity_power_integrable {n : ℕ} {b : ℝ} (hb : 0 < b)
    (k : GridAssignment n) : Integrable (fun y => gridCellDensity b k y ^ (5/3 : ℝ)) := by
  let w : Set.range (gridCell k) → ℝ := fun c => (b⁻¹)^3 *
    (Fintype.card {i : Fin n // Set.rangeFactorization (gridCell k) i = c} : ℝ)
  have hd : Pairwise (fun c d : Set.range (gridCell k) =>
      Disjoint (gridBox b c.val) (gridBox b d.val)) := by
    intro c d hcd
    exact gridBox_disjoint hb (fun he => hcd (Subtype.ext he))
  have he : (fun y => gridCellDensity b k y ^ (5/3 : ℝ)) = fun y =>
      ∑ c : Set.range (gridCell k), (gridBox b c.val).indicator
        (fun _ => (w c)^(5/3 : ℝ)) y := by
    funext y
    exact sum_indicator_rpow_disjoint (fun c : Set.range (gridCell k) => gridBox b c.val)
      hd w (by norm_num) y
  rw [he]
  apply integrable_finsetSum
  intro c _
  exact (integrableOn_const (by rw [gridBox_volume]; finiteness)).integrable_indicator
    (gridBox_measurable b c.val)

lemma translatedGridDensity_power_integrable_space {n : ℕ} {b : ℝ} (hb : 0 < b)
    (t : Fin 3 → ℝ) (x : (Fin n × Fin 3) → ℝ) :
    Integrable (fun y => translatedGridDensity b t x y ^ (5/3:ℝ)) := by
  simp_rw [translatedGridDensity_eq_cell hb]
  exact (measurePreserving_add_right volume t).integrable_comp
    (gridCellDensity_power_integrable hb _).aestronglyMeasurable |>.mpr
      (gridCellDensity_power_integrable hb _)

lemma sameCell1_measurable_pair (b : ℝ) :
    Measurable (fun p : ℝ × ℝ => sameCell1 b p.1 p.2) := by
  unfold sameCell1
  exact measurable_const.ite
    (measurableSet_eq_fun (Int.measurable_ceil.comp (measurable_fst.div_const b))
      (Int.measurable_ceil.comp (measurable_snd.div_const b))) measurable_const

lemma translatedGridDensity_measurable_pair {n : ℕ} (b : ℝ)
    (x : (Fin n × Fin 3) → ℝ) :
    Measurable (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      translatedGridDensity b p.1 x p.2) := by
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_prod
  intro j _
  have hjt : Measurable (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => p.1 j) :=
    (measurable_pi_apply (X := fun _ : Fin 3 => ℝ) j).comp measurable_fst
  have hjy : Measurable (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => p.2 j) :=
    (measurable_pi_apply (X := fun _ : Fin 3 => ℝ) j).comp measurable_snd
  exact (sameCell1_measurable_pair b).comp
    ((hjt.const_add (x (i,j))).prodMk (hjy.add hjt))

lemma translatedGridDensity_power_integrable_prod {n : ℕ} {b : ℝ} (hb : 0 < b)
    (x : (Fin n × Fin 3) → ℝ) :
    Integrable (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      translatedGridDensity b p.1 x p.2 ^ (5/3:ℝ))
      ((finiteCubeMeasure b (Fin 3)).prod volume) := by
  have hm := (translatedGridDensity_measurable_pair b x).pow_const (5/3:ℝ)
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall (fun t => translatedGridDensity_power_integrable_space hb t x)
  · have he (t : Fin 3 → ℝ) :
        (∫ y, ‖translatedGridDensity b t x y ^ (5/3:ℝ)‖) =
          (b⁻¹)^2 * gridLeadingCount (gridIndex b (fun ij => x ij+t ij.2)) := by
      simp_rw [Real.norm_of_nonneg (Real.rpow_nonneg (translatedGridDensity_nonneg hb ..) _)]
      exact translatedGridDensity_power_integral hb t x
    simp_rw [he]
    have hki : Measurable (fun t : Fin 3 → ℝ =>
        gridIndex b (fun ij : Fin n × Fin 3 => x ij+t ij.2)) := by
      apply (gridIndex_measurable b).comp
      apply Measurable.of_eval
      intro ij
      exact (measurable_pi_apply (X := fun _ : Fin 3 => ℝ) ij.2).const_add (x ij)
    have hk := (measurable_of_countable (gridLeadingCount (n := n))).comp hki
    apply (integrable_const ((b⁻¹)^2*(n:ℝ)^(5/3:ℝ))).mono'
      (hk.const_mul _).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun t => by
      dsimp only [Function.comp_apply, gridLeadingCount]
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (groupLeadingCount_nonneg _))]
      exact mul_le_mul_of_nonneg_left (groupLeadingCount_le _) (sq_nonneg _))

lemma flatFineKernel_measurable (b : ℝ) : Measurable (flatFineKernel b) := by
  apply Measurable.const_mul
  apply Finset.measurable_prod
  intro j _
  exact measurable_const.max (measurable_const.sub
    (measurable_pi_apply (X := fun _ : Fin 3 => ℝ) j).abs)

lemma flatFineKernel_power_integral_le {n : ℕ} {b : ℝ} (hb : 0 < b)
    (x : (Fin n × Fin 3) → ℝ) :
    (∫ y : Fin 3 → ℝ, (∑ i : Fin n,
      flatFineKernel b (y-(fun j => x (i,j)))) ^ (5/3:ℝ)) ≤
    (b⁻¹)^5 * ∫ t, gridLeadingCount (gridIndex b (fun ij => x ij+t ij.2))
      ∂finiteCubeMeasure b (Fin 3) := by
  have hi := translatedGridDensity_power_integrable_prod hb x
  have hr := hi.integral_prod_right.const_mul ((b⁻¹)^3)
  have hlm : Measurable (fun y : Fin 3 → ℝ => (∑ i : Fin n,
      flatFineKernel b (y-(fun j => x (i,j)))) ^ (5/3:ℝ)) := by
    apply Measurable.pow_const
    exact Finset.measurable_sum _ (fun i _ =>
      (flatFineKernel_measurable b).comp (measurable_id.sub_const _))
  have hnon (y : Fin 3 → ℝ) : 0 ≤
      (∑ i : Fin n, flatFineKernel b (y-(fun j => x (i,j)))) ^ (5/3:ℝ) :=
    Real.rpow_nonneg (Finset.sum_nonneg (fun _ _ => flatFineKernel_nonneg ..)) _
  have hl := hr.mono' hlm.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun y => by
      rw [Real.norm_of_nonneg (hnon y)]
      exact flatFineKernel_Jensen hb x y))
  calc
    _ ≤ ∫ y : Fin 3 → ℝ, (b⁻¹)^3 * ∫ t,
        translatedGridDensity b t x y ^ (5/3:ℝ) ∂finiteCubeMeasure b (Fin 3) :=
      integral_mono hl hr (fun y => flatFineKernel_Jensen hb x y)
    _ = (b⁻¹)^3 * ∫ t, (b⁻¹)^2 *
        gridLeadingCount (gridIndex b (fun ij => x ij+t ij.2))
          ∂finiteCubeMeasure b (Fin 3) := by
      rw [integral_const_mul, ← integral_integral_swap hi]
      simp_rw [translatedGridDensity_power_integral hb]
    _ = _ := by rw [integral_const_mul, ← mul_assoc, ← pow_add]

lemma flatDensityPower_nonneg {n : ℕ} (b : ℝ) (x : (Fin n × Fin 3) → ℝ) :
    0 ≤ flatDensityPower b x := by
  apply integral_nonneg
  intro y
  apply Real.rpow_nonneg
  exact Finset.sum_nonneg (fun _ _ => flatFineKernel_nonneg ..)

lemma flatDensityPower_measurable {n : ℕ} (b : ℝ) :
    Measurable (flatDensityPower (n := n) b) := by
  have hm : Measurable (fun p : ((Fin n × Fin 3) → ℝ) × (Fin 3 → ℝ) =>
      (∑ i : Fin n, flatFineKernel b (p.2-(fun j => p.1 (i,j))))^(5/3:ℝ)) := by
    apply Measurable.pow_const
    apply Finset.measurable_sum
    intro i _
    apply (flatFineKernel_measurable b).comp
    apply measurable_snd.sub
    apply Measurable.of_eval
    intro j
    exact (measurable_pi_apply (X := fun _ : Fin n × Fin 3 => ℝ) (i,j)).comp measurable_fst
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

lemma weighted_flatDensityPower_integrable {n : ℕ} {b : ℝ} (hb : 0 < b)
    {w : ((Fin n × Fin 3) → ℝ) → ℝ} (hw : Integrable w) (hw0 : ∀ x, 0 ≤ w x) :
    Integrable (fun x => flatDensityPower b x * w x) := by
  have hi := translated_count_integrable hb hw hw0
  apply (hi.integral_prod_right.const_mul ((b⁻¹)^5)).mono'
    ((flatDensityPower_measurable b).aestronglyMeasurable.mul hw.aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun x => by
    change ‖flatDensityPower b x * w x‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg (flatDensityPower_nonneg b x) (hw0 x))]
    have H := mul_le_mul_of_nonneg_right (flatFineKernel_power_integral_le hb x) (hw0 x)
    dsimp only [flatDensityPower] at *
    rw [integral_mul_const]
    nlinarith [H])

lemma weighted_flatDensityPower_le {n : ℕ} {b : ℝ} (hb : 0 < b)
    {w : ((Fin n × Fin 3) → ℝ) → ℝ} (hw : Integrable w) (hw0 : ∀ x, 0 ≤ w x) :
    (∫ x, flatDensityPower b x * w x) ≤
      (b⁻¹)^5 * ∫ t, (∫ x, gridLeadingCount (gridIndex b (fun ij => x ij+t ij.2)) * w x)
        ∂finiteCubeMeasure b (Fin 3) := by
  have hi := translated_count_integrable hb hw hw0
  calc
    _ ≤ ∫ x, (b⁻¹)^5 * ∫ t,
        gridLeadingCount (gridIndex b (fun ij => x ij+t ij.2)) * w x
          ∂finiteCubeMeasure b (Fin 3) := by
      apply integral_mono (weighted_flatDensityPower_integrable hb hw hw0)
        (hi.integral_prod_right.const_mul _)
      intro x
      dsimp only
      rw [integral_mul_const]
      exact (mul_le_mul_of_nonneg_right (flatFineKernel_power_integral_le hb x) (hw0 x)).trans_eq
        (mul_assoc ..)
    _ = _ := by rw [integral_const_mul, ← integral_integral_swap hi]

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_RotatedDensityPower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
namespace Coulomb

lemma commonIsometry_symm {n : ℕ} (L : Space ≃ₗᵢ[ℝ] Space) :
    (commonIsometry (n:=n) L).symm = commonIsometry L.symm := by
  ext x ij
  rfl

end Coulomb

open MeasureTheory Set
open scoped BigOperators Matrix ENNReal

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_CoreSliceRegular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set
open scoped BigOperators Matrix ENNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set
open scoped BigOperators ENNReal

open MeasureTheory Set
open scoped BigOperators Matrix
namespace Coulomb
instance instIsProbabilityMeasureSubtypeMatrixFinOfNatNatRealMemSubmonoidRotationRotationMeasure_1 : IsProbabilityMeasure rotationMeasure := ⟨Measure.haarMeasure_self⟩

instance instIsMulLeftInvariantSubtypeMatrixFinOfNatNatRealMemSubmonoidRotationRotationMeasure_1 : Measure.IsMulLeftInvariant rotationMeasure := by
  unfold rotationMeasure
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance instIsHaarMeasureSubtypeMatrixFinOfNatNatRealMemSubmonoidRotationRotationMeasure_1 : Measure.IsHaarMeasure rotationMeasure := by
  unfold rotationMeasure
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance instIsMulRightInvariantSubtypeMatrixFinOfNatNatRealMemSubmonoidRotationRotationMeasure_1 : Measure.IsMulRightInvariant rotationMeasure where
  map_mul_right_eq_self P := by
    have H := Measure.isMulInvariant_eq_smul_of_compactSpace
      (Measure.map (· * P) rotationMeasure) rotationMeasure
    have H1 := congrArg (fun μ : Measure Rotation => μ univ) H
    simp only [Measure.smul_apply, measure_univ, ENNReal.smul_def, smul_eq_mul, mul_one] at H1
    have H2 : (Measure.map (· * P) rotationMeasure).haarScalarFactor rotationMeasure = 1 :=
      ENNReal.coe_injective (by
        have h3 : (Measure.map (· * P) rotationMeasure) Set.univ = 1 := by
          rw [Measure.map_apply (measurable_mul_const P) MeasurableSet.univ]
          simp [measure_univ]
        rw [ENNReal.coe_one]; first | exact H1.symm | exact H1.symm.trans h3)
    rw [H2, one_smul] at H
    exact H

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_RetainedFinePower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set
open scoped BigOperators Matrix ENNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

lemma potentialForm_le_add_const {n : ℕ} (ψ : H1Vector n)
    {V W : Configuration n → ℝ} {C : ℝ}
    (hV : ∀ s, Integrable (fun x => V x*‖ψ.value s x‖^2))
    (hW : ∀ s, Integrable (fun x => W x*‖ψ.value s x‖^2))
    (h : ∀ᵐ x, V x ≤ W x+C) :
    potentialForm V ψ ≤ potentialForm W ψ + C*mass ψ := by
  have hs (s : Spins n) : (∫ x, V x*‖ψ.value s x‖^2) ≤
      (∫ x, W x*‖ψ.value s x‖^2)+C*(∫ x, ‖ψ.value s x‖^2) := by
    have hw : Integrable (fun x => ‖ψ.value s x‖^2) :=
      (ψ.value_L2 s).integrable_norm_pow (p:=2) (by decide)
    rw [←integral_const_mul, ←integral_add (hW s) (hw.const_mul C)]
    apply integral_mono_ae (hV s) ((hW s).add (hw.const_mul C))
    exact h.mono fun x hx => by simpa only [add_mul, Pi.add_apply] using mul_le_mul_of_nonneg_right hx (sq_nonneg ‖ψ.value s x‖)
  have H := Finset.sum_le_sum (s:=Finset.univ) (fun s _ => hs s)
  simpa only [potentialForm, mass, Finset.sum_add_distrib, ←Finset.mul_sum] using H

end Coulomb

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_OuterJoinConfiguration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set
open scoped BigOperators Matrix ENNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

noncomputable def outerAppendEquiv (m k : ℕ) : Spins m × Spins k ≃ Spins (k+m) :=
  (Equiv.prodComm _ _).trans (Fin.appendEquiv k m)
end Coulomb

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Localization_DeletedLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set
open scoped BigOperators Matrix ENNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

lemma sliceExpectation_mono_ae {m k : ℕ} (ψ : H1Vector (m+k))
    (f g : Spins m → Configuration m → ℝ)
    (hf : ∀ s, Integrable (fun x => mass (ψ.coreSlice s x)*f s x))
    (hg : ∀ s, Integrable (fun x => mass (ψ.coreSlice s x)*g s x))
    (h : ∀ s, ∀ᵐ x, f s x ≤ g s x) : sliceExpectation ψ f ≤ sliceExpectation ψ g := by
  exact Finset.sum_le_sum fun s _ => integral_mono_ae (hf s) (hg s)
    ((h s).mono fun x hx => mul_le_mul_of_nonneg_left hx (mass_nonneg _))

def deletedLabels {m : ℕ} (r : Configuration m → Finset (Fin m)) (x : Configuration m) : Finset (Fin m) :=
  Finset.univ \ r x
lemma deletedLabels_measurable {m : ℕ} (r : Configuration m → Finset (Fin m))
    (hr : ∀ i, MeasurableSet {x | i ∈ r x}) (i : Fin m) :
    MeasurableSet {x | i ∈ deletedLabels r x} := by
  have he : {x | i ∈ deletedLabels r x} = {x | i ∈ r x}ᶜ := by ext x; simp [deletedLabels]
  rw [he]; exact (hr i).compl
lemma retained_deleted_sum {m : ℕ} (r : Configuration m → Finset (Fin m))
    (x : Configuration m) (f : Fin m → ℝ) :
    (∑ i ∈ r x, f i) + (∑ i ∈ deletedLabels r x, f i) = ∑ i : Fin m, f i := by
  simpa only [add_comm, deletedLabels] using Finset.sum_sdiff (f:=f) (Finset.subset_univ (r x))

end Coulomb

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical SchwartzMap Pointwise

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_RawThomasFermiEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set
open scoped BigOperators Matrix ENNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical SchwartzMap Pointwise
namespace Coulomb

lemma sliceExpectation_congr_ae {m k : ℕ} (ψ : H1Vector (m+k))
    {f g : Spins m → Configuration m → ℝ} (h : ∀ s, f s =ᵐ[volume] g s) :
    sliceExpectation ψ f = sliceExpectation ψ g := by
  apply Finset.sum_congr rfl
  intro s _
  apply integral_congr_ae
  exact (h s).mono fun x hx => congrArg (mass (ψ.coreSlice s x)*·) hx

end Coulomb

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical SchwartzMap Pointwise

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_ColoredObservable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology ContDiff
noncomputable section
namespace Coulomb

def coloredObservable {n : ℕ} (F : Fin n → Configuration n → ℝ)
    (p : Fin n → Fin 2) (x : Configuration n) : ℝ :=
  ∑ i, if p i=0 then F i x else 0

end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_TfReaction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
namespace NeutralAtom
open scoped Convolution
open ContinuousLinearMap

def tfReaction (t : ℝ) : ℝ := 4*Real.pi*kTF*(max t 0)^(3/2 : ℝ)

def cutoffReaction (a : ℝ) (F : Position → ℝ) : Position → ℝ :=
  {x : Position | a ≤ ‖x‖}.indicator (fun x => tfReaction (F x))

def screenedPotential (lam : ℝ) (σ : Position → ℝ) (x : Position) : ℝ :=
  lam*coulombKernel x-potentialOf σ x

def barrierSource (a : ℝ) (U σ p : Position → ℝ) (x : Position) : ℝ :=
  (4*Real.pi)*({y : Position | ‖y‖ < a}.indicator σ x)-
    (4*Real.pi)*p x+cutoffReaction a U x

theorem tfReaction_nonneg (t : ℝ) : 0 ≤ tfReaction t := by
  have := kTF_pos
  unfold tfReaction
  positivity

theorem tfReaction_monotone : Monotone tfReaction := by
  intro x y hxy
  unfold tfReaction
  have := kTF_pos
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow (le_max_right _ _) (max_le_max hxy le_rfl)
  norm_num

theorem tfReaction_continuous : Continuous tfReaction := by
  exact continuous_const.mul ((Real.continuous_rpow_const (by norm_num : (0:ℝ)≤3/2)).comp
    (continuous_id.max continuous_const))

end NeutralAtom
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Localization_HarmonicScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
noncomputable section
namespace NeutralAtom
theorem tsupport_coordinateLaplacian_subset (φ : Position → ℝ) :
    tsupport (coordinateLaplacian φ) ⊆ tsupport φ := by
  apply closure_minimal _ (isClosed_tsupport φ)
  intro x hx
  by_contra hn
  exact hx (coordinateLaplacian_eq_zero_of_notMem_tsupport hn)

theorem coordinateLaplacian_comp_smul (f : Position → ℝ) (D : ℝ) (x : Position) :
    coordinateLaplacian (fun y => f (D • y)) x = D^2*coordinateLaplacian f (D • x) := by
  unfold coordinateLaplacian
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  have he : (fun t : ℝ => f (D • (x+t • axis a))) =
      (fun t : ℝ => (fun u : ℝ => f (D • x+u • axis a)) (D*t)) := by
    funext t
    simp only [smul_add, smul_smul]
  rw [he]
  have hed : (deriv fun t : ℝ => (fun u : ℝ => f (D • x+u • axis a)) (D*t)) =
      (fun t : ℝ => D * deriv (fun u : ℝ => f (D • x+u • axis a)) (D*t)) := by
    funext t
    exact deriv_comp_mul_left D (fun u : ℝ => f (D • x+u • axis a)) t
  rw [hed, deriv_const_mul_field, deriv_comp_mul_left]
  simp only [smul_eq_mul, mul_zero]
  ring

end NeutralAtom
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RadialBounds_Radial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory Filter
open ContinuousLinearMap
open scoped Topology BigOperators ContDiff Convolution Pointwise ENNReal
namespace NeutralAtom

def screenedField (lam : ℝ) (σ : Position → ℝ) (x : Position) : ℝ :=
  lam*coulombKernel x-potentialOf σ x

end NeutralAtom
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Variational_PuncturedPosition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory Filter
open ContinuousLinearMap
open scoped Topology BigOperators ContDiff Convolution Pointwise ENNReal
namespace NeutralAtom

def tfDensityScalar (t : ℝ) : ℝ := kTF*(max t 0)^(3/2 : ℝ)

end NeutralAtom
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Variational_RetainedAnalyticSequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory Filter
open ContinuousLinearMap
open scoped Topology BigOperators ContDiff Convolution Pointwise ENNReal
namespace NeutralAtom

theorem tfReaction_dilate {D : ℝ} (hD : 0 < D) (t : ℝ) :
    tfReaction (D^4*t) = D^6*tfReaction t := by
  have hm : max (D^4*t) 0 = D^4*max t 0 := by
    rw [mul_max_of_nonneg t 0 (pow_nonneg hD.le 4), mul_zero]
  have hr : (D^4)^(3/2 : ℝ) = D^6 := by
    rw [← Real.rpow_natCast D 4, ← Real.rpow_mul hD.le]
    norm_num
  rw [tfReaction, hm, Real.mul_rpow (pow_nonneg hD.le 4) (le_max_right t 0), hr, tfReaction]
  ring

structure RetainedAnalyticSequence where
  σ : ℕ → Position → ℝ
  U : ℕ → Position → ℝ
  p : ℕ → Position → ℝ
  lam : ℕ → ℝ
  a : ℕ → ℝ
  q : ℕ → ℝ
  Aσ : ℕ → ℝ
  Ap : ℕ → ℝ
  B : ℝ
  Ccap : ℝ
  Cinv : ℝ
  Bpos : 0 < B
  Cpos : 0 ≤ Ccap
  σi : ∀ n, Integrable (σ n)
  σp : ∀ n x, 0 ≤ σ n x
  σb : ∀ n x, σ n x ≤ Aσ n
  σmass : ∀ n, (∫ x, σ n x) = lam n
  pi : ∀ n, Integrable (p n)
  pp : ∀ n x, 0 ≤ p n x
  pb : ∀ n x, p n x ≤ Ap n
  ps : ∀ n x, a n < ‖x‖ → p n x = 0
  pm : Tendsto (fun n => ∫ x, p n x) atTop (𝓝 0)
  apos : ∀ n, 0 < a n
  alim : Tendsto a atTop (𝓝 0)
  qlim : Tendsto q atTop atTop
  aq : ∀ᶠ n in atTop, 1/(2*q n) ≤ a n
  Ucont : ∀ n, Continuous (fun x => U n x-lam n*coulombKernel x)
  Ulower : ∀ n x, a n ≤ ‖x‖ → B/‖x‖^4*(1-a n/(8*‖x‖)) ≤ U n x
  Uupper : ∀ n x, a n ≤ ‖x‖ → U n x ≤ Cinv/‖x‖^4
  Uweak : ∀ n, WeakNuclearSubsolution (U n) (lam n) Set.univ (barrierSource (a n) (U n) (σ n) (p n))
  cap : ∀ n x, a n ≤ ‖x‖ → ‖x‖ ≤ q n → screenedField (lam n) (σ n) x ≤ Ccap/‖x‖^4
  err : ∀ n x, a n ≤ ‖x‖ → ‖x‖ ≤ q n →
    |σ n x-tfDensityScalar (screenedField (lam n) (σ n) x)| ≤ ((q n)^8)⁻¹*(‖x‖^6)⁻¹

end NeutralAtom
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_Field
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory Filter
open ContinuousLinearMap
open scoped Topology BigOperators ContDiff Convolution Pointwise ENNReal
namespace NeutralAtom

def RetainedAnalyticSequence.field (d : RetainedAnalyticSequence) : ℕ → Position → ℝ :=
  fun n => screenedField (d.lam n) (d.σ n)

def RetainedAnalyticSequence.reindex (d : RetainedAnalyticSequence) (u : ℕ → ℕ)
    (hu : Tendsto u atTop atTop) : RetainedAnalyticSequence where
  σ := d.σ ∘ u
  U := d.U ∘ u
  p := d.p ∘ u
  lam := d.lam ∘ u
  a := d.a ∘ u
  q := d.q ∘ u
  Aσ := d.Aσ ∘ u
  Ap := d.Ap ∘ u
  B := d.B
  Ccap := d.Ccap
  Cinv := d.Cinv
  Bpos := d.Bpos
  Cpos := d.Cpos
  σi := fun n => d.σi (u n)
  σp := fun n => d.σp (u n)
  σb := fun n => d.σb (u n)
  σmass := fun n => d.σmass (u n)
  pi := fun n => d.pi (u n)
  pp := fun n => d.pp (u n)
  pb := fun n => d.pb (u n)
  ps := fun n => d.ps (u n)
  pm := d.pm.comp hu
  apos := fun n => d.apos (u n)
  alim := d.alim.comp hu
  qlim := d.qlim.comp hu
  aq := hu.eventually d.aq
  Ucont := fun n => d.Ucont (u n)
  Ulower := fun n => d.Ulower (u n)
  Uupper := fun n => d.Uupper (u n)
  Uweak := fun n => d.Uweak (u n)
  cap := fun n => d.cap (u n)
  err := fun n => d.err (u n)

def sommerfeldProfile (x : Position) : ℝ := aTF/‖x‖^4

def sommerfeldDensity (x : Position) : ℝ := kTF*aTF^(3/2 : ℝ)/‖x‖^6

structure RetainedAnalyticFamily (Θ : ℕ → Type*) where
  σ : ∀ n, Θ n → Position → ℝ
  U : ∀ n, Θ n → Position → ℝ
  p : ∀ n, Θ n → Position → ℝ
  lam : ℕ → ℝ
  a : ℕ → ℝ
  q : ℕ → ℝ
  ε : ℕ → ℝ
  Aσ : ∀ n, Θ n → ℝ
  Ap : ∀ n, Θ n → ℝ
  B : ℝ
  Ccap : ℝ
  Cinv : ℝ
  Bpos : 0 < B
  Cpos : 0 ≤ Ccap
  σi : ∀ n θ, Integrable (σ n θ)
  σp : ∀ n θ x, 0 ≤ σ n θ x
  σb : ∀ n θ x, σ n θ x ≤ Aσ n θ
  σmass : ∀ n θ, (∫ x, σ n θ x) = lam n
  pi : ∀ n θ, Integrable (p n θ)
  pp : ∀ n θ x, 0 ≤ p n θ x
  pb : ∀ n θ x, p n θ x ≤ Ap n θ
  ps : ∀ n θ x, a n < ‖x‖ → p n θ x = 0
  pm : ∀ n θ, (∫ x, p n θ x) ≤ ε n
  εlim : Tendsto ε atTop (𝓝 0)
  apos : ∀ n, 0 < a n
  alim : Tendsto a atTop (𝓝 0)
  qlim : Tendsto q atTop atTop
  aq : ∀ᶠ n in atTop, 1/(2*q n) ≤ a n
  Ucont : ∀ n θ, Continuous (fun x => U n θ x-lam n*coulombKernel x)
  Ulower : ∀ n θ x, a n ≤ ‖x‖ → B/‖x‖^4*(1-a n/(8*‖x‖)) ≤ U n θ x
  Uupper : ∀ n θ x, a n ≤ ‖x‖ → U n θ x ≤ Cinv/‖x‖^4
  Uweak : ∀ n θ, WeakNuclearSubsolution (U n θ) (lam n) Set.univ
    (barrierSource (a n) (U n θ) (σ n θ) (p n θ))
  cap : ∀ n θ x, a n ≤ ‖x‖ → ‖x‖ ≤ q n → screenedField (lam n) (σ n θ) x ≤ Ccap/‖x‖^4
  err : ∀ n θ x, a n ≤ ‖x‖ → ‖x‖ ≤ q n →
    |σ n θ x-tfDensityScalar (screenedField (lam n) (σ n θ) x)| ≤ ((q n)^8)⁻¹*(‖x‖^6)⁻¹

def RetainedAnalyticFamily.select {Θ : ℕ → Type*} (d : RetainedAnalyticFamily Θ)
    (u : ℕ → ℕ) (hu : Tendsto u atTop atTop) (θ : ∀ n, Θ (u n)) : RetainedAnalyticSequence where
  σ := fun n => d.σ (u n) (θ n)
  U := fun n => d.U (u n) (θ n)
  p := fun n => d.p (u n) (θ n)
  lam := d.lam ∘ u
  a := d.a ∘ u
  q := d.q ∘ u
  Aσ := fun n => d.Aσ (u n) (θ n)
  Ap := fun n => d.Ap (u n) (θ n)
  B := d.B
  Ccap := d.Ccap
  Cinv := d.Cinv
  Bpos := d.Bpos
  Cpos := d.Cpos
  σi := fun n => d.σi (u n) (θ n)
  σp := fun n => d.σp (u n) (θ n)
  σb := fun n => d.σb (u n) (θ n)
  σmass := fun n => d.σmass (u n) (θ n)
  pi := fun n => d.pi (u n) (θ n)
  pp := fun n => d.pp (u n) (θ n)
  pb := fun n => d.pb (u n) (θ n)
  ps := fun n => d.ps (u n) (θ n)
  pm := squeeze_zero (fun n => integral_nonneg (d.pp (u n) (θ n)))
    (fun n => d.pm (u n) (θ n)) (d.εlim.comp hu)
  apos := fun n => d.apos (u n)
  alim := d.alim.comp hu
  qlim := d.qlim.comp hu
  aq := hu.eventually d.aq
  Ucont := fun n => d.Ucont (u n) (θ n)
  Ulower := fun n => d.Ulower (u n) (θ n)
  Uupper := fun n => d.Uupper (u n) (θ n)
  Uweak := fun n => d.Uweak (u n) (θ n)
  cap := fun n => d.cap (u n) (θ n)
  err := fun n => d.err (u n) (θ n)

end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_TailMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
noncomputable section
namespace Coulomb

lemma screenBaseMass_antitone {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    screenBaseMass b ≤ screenBaseMass a := by
  have hb : 0 < b := ha.trans_le hab
  unfold screenBaseMass
  exact max_le_max ((inv_le_inv₀ (by positivity) (by positivity)).mpr (pow_le_pow_left₀ ha.le hab 3)) le_rfl

lemma screenMass_dyadic_bound {δ h : ℝ} (hδ : 0 ≤ δ) (hh : 0 < h) (j : ℕ) :
    screenMass δ ((2:ℝ)^j*h)/((2:ℝ)^j*h) ≤ screenMass δ h/h*(3/4:ℝ)^j := by
  have h2 : (1:ℝ) ≤ 2^j := one_le_pow₀ (by norm_num)
  have h3 : (1:ℝ) ≤ (3/2:ℝ)^j := one_le_pow₀ (by norm_num)
  have hb := screenBaseMass_antitone hh (show h ≤ (2:ℝ)^j*h by nlinarith)
  have hb' : screenBaseMass ((2:ℝ)^j*h) ≤ (3/2:ℝ)^j*screenBaseMass h :=
    hb.trans (le_mul_of_one_le_left (screenBaseMass_nonneg h) h3)
  have hp : (2:ℝ)^j ≤ ((3/2:ℝ)^j)^2 := by
    have H := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) (by norm_num : (2:ℝ) ≤ (3/2:ℝ)^2) j
    simpa only [←pow_mul,Nat.mul_comm] using H
  have hr : Real.sqrt (δ*((2:ℝ)^j*h)) ≤ (3/2:ℝ)^j*Real.sqrt (δ*h) := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity,?_⟩
    rw [mul_pow,Real.sq_sqrt (mul_nonneg hδ hh.le)]
    nlinarith [mul_le_mul_of_nonneg_right hp (mul_nonneg hδ hh.le)]
  have hm : screenMass δ ((2:ℝ)^j*h) ≤ (3/2:ℝ)^j*screenMass δ h := by
    unfold screenMass
    nlinarith
  refine (div_le_div_of_nonneg_right hm (by positivity)).trans_eq ?_
  have he : (3/2:ℝ)^j=(3/4:ℝ)^j*(2:ℝ)^j := by rw [←mul_pow]; congr 1; norm_num
  rw [he]
  field_simp

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_TfExtendNonneg
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical BigOperators Topology SchwartzMap Pointwise

open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical BigOperators Topology SchwartzMap Pointwise
namespace Coulomb

def rawTFBregman (ρ σ : Space → ℝ) : ℝ :=
  thomasFermiKineticConstant*∫ x, σ x^(5/3:ℝ)-ρ x^(5/3:ℝ)-
    (5/3:ℝ)*ρ x^(2/3:ℝ)*(σ x-ρ x)

lemma rawTFBregman_congr_ae {ρ σ ρ' σ' : Space → ℝ}
    (hρ : ρ =ᵐ[volume] ρ') (hσ : σ =ᵐ[volume] σ') :
    rawTFBregman ρ σ = rawTFBregman ρ' σ' := by
  unfold rawTFBregman
  congr 1
  apply integral_congr_ae
  filter_upwards [hρ,hσ] with x hx hy
  rw [hx,hy]

def rawToTFLp {Ω : Set Space} (σ : Space → ℝ) (hσ : MemLp σ TFExponent (volume.restrict Ω)) :
    TFLp (volume.restrict Ω) := hσ.toLp σ

lemma rawToTFLp_nonneg {Ω : Set Space} {σ : Space → ℝ}
    (hσ : MemLp σ TFExponent (volume.restrict Ω)) (hp : ∀ᵐ x ∂volume.restrict Ω, 0 ≤ σ x) :
    TFNonneg (rawToTFLp σ hσ) := by
  filter_upwards [hσ.coeFn_toLp,hp] with x hx hy
  exact hx.symm ▸ hy

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_ScaledTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology ContDiff
noncomputable section
namespace Coulomb
open NeutralAtom (dirPartial coordinateLaplacian axis)

lemma dirPartial_scaled {f : Space → ℝ} (hf : Differentiable ℝ f) (c : ℝ) (y x v : Space) :
    dirPartial (fun z => f (c • (z-y))) v x = c*dirPartial f v (c • (x-y)) := by
  have ht : HasFDerivAt (fun z : Space => c • (z-y))
      (c • ContinuousLinearMap.id ℝ Space) x := by
    convert ((hasFDerivAt_id x).sub_const y).const_smul c using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  have h := ((hf (c • (x-y))).hasFDerivAt.comp x ht).fderiv
  simp only [Function.comp_def] at h
  unfold dirPartial
  rw [h]
  simp only [ContinuousLinearMap.comp_apply,smul_apply,ContinuousLinearMap.id_apply,map_smul,smul_eq_mul]

lemma dirPartial_const_mul {f : Space → ℝ} (hf : Differentiable ℝ f) (c : ℝ) (x v : Space) :
    dirPartial (fun z => c*f z) v x = c*dirPartial f v x := by
  unfold dirPartial
  rw [((hf x).hasFDerivAt.const_mul c).fderiv]
  rfl

lemma coordinateLaplacian_scaled {f : Space → ℝ} (hf : ContDiff ℝ 2 f) (c : ℝ) (y x : Space) :
    coordinateLaplacian (fun z => f (c • (z-y))) x = c^2*coordinateLaplacian f (c • (x-y)) := by
  have hg : ContDiff ℝ 2 (fun z : Space => f (c • (z-y))) := hf.comp (by fun_prop)
  rw [NeutralAtom.coordinateLaplacian_eq_partials hg.contDiffAt,
    NeutralAtom.coordinateLaplacian_eq_partials hf.contDiffAt,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have he : dirPartial (fun z => f (c • (z-y))) (axis i) =
      fun z => c*dirPartial f (axis i) (c • (z-y)) := by
    funext z; exact dirPartial_scaled (hf.differentiable (by norm_num)) c y z _
  rw [he]
  have hp : Differentiable ℝ (dirPartial f (axis i)) :=
    (NeutralAtom.contDiff_partial (n := 1) hf (axis i)).differentiable (by norm_num)
  have hpc : Differentiable ℝ (fun z : Space => dirPartial f (axis i) (c • (z-y))) := hp.comp (by fun_prop)
  rw [dirPartial_const_mul hpc c,
    dirPartial_scaled hp c]
  ring

def countTest (y : Space) (a : ℝ) (x : Space) : ℝ := cutSeed (a⁻¹ • (x-y))
lemma countTest_smooth (y : Space) (a : ℝ) : ContDiff ℝ ∞ (countTest y a) := cutSeed_smooth.comp (by fun_prop)
lemma countTest_nonneg (y : Space) (a : ℝ) (x : Space) : 0 ≤ countTest y a x := Real.smoothTransition.nonneg _
lemma countTest_le_one (y : Space) (a : ℝ) (x : Space) : countTest y a x≤1 := Real.smoothTransition.le_one _
lemma countTest_zero (y : Space) {a : ℝ} (ha : 0<a) {x : Space} (hx : 2*a≤‖x-y‖) : countTest y a x=0 := by
  apply cutSeed_zero
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ha),←div_eq_inv_mul]
  exact (le_div_iff₀ ha).mpr hx
lemma countTest_support (y : Space) {a : ℝ} (ha : 0<a) :
    tsupport (countTest y a)⊆Metric.closedBall y (2*a) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  by_contra hn
  have hh : 2*a≤‖x-y‖ := le_of_lt (by simpa only [Metric.mem_closedBall,dist_eq_norm,not_le] using hn)
  exact hx (countTest_zero y ha hh)
lemma countTest_compact (y : Space) {a : ℝ} (ha : 0<a) : HasCompactSupport (countTest y a) :=
  (isCompact_closedBall y (2*a)).of_isClosed_subset isClosed_closure (countTest_support y ha)

end Coulomb

end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_TFCountTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology ContDiff
noncomputable section
namespace Coulomb

variable {Ω : Set Space} (hΩ : MeasurableSet Ω) [IsFiniteMeasure (volume.restrict Ω)]

omit hΩ [IsFiniteMeasure (volume.restrict Ω)] in
lemma integrable_mul_countTest {f : Space → ℝ} (hf : Integrable f) (y : Space) (a : ℝ) :
    Integrable (fun x => f x*countTest y a x) :=
  hf.mul_bdd (countTest_smooth y a).continuous.aestronglyMeasurable
    (Eventually.of_forall (fun x => by rw [Real.norm_of_nonneg (countTest_nonneg y a x)]; exact countTest_le_one y a x))

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_PhysicalPoisson
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology ContDiff
noncomputable section
namespace Coulomb

lemma coreCoulombPotential_continuousOn {k : ℕ} (u : H1Vector k)
    {A : Set Space} (hu : SpatiallySupported u A) {y : Space} {r t : ℝ}
    (hrt : r<t) (hsep : ∀ a∈A, t ≤ ‖a-y‖) :
    ContinuousOn (coreCoulombPotential u) (Metric.closedBall y r) := by
  let d := t-r
  have hd : 0<d := sub_pos.mpr hrt
  let G : Space → ℝ := fun z => ∑ s : Spins k, ∑ i : Fin k,
    ∫ x, (max d ‖position x i-z‖)⁻¹*‖u.value s x‖^2
  have hG : Continuous G := by
    apply continuous_finsetSum
    intro s hs
    apply continuous_finsetSum
    intro i hi
    apply MeasureTheory.continuous_of_dominated (bound := fun x => d⁻¹*‖u.value s x‖^2)
    · intro z
      exact (((measurable_const.max ((continuous_position i).measurable.sub measurable_const).norm).inv).aestronglyMeasurable).mul
        ((u.value_L2 s).aestronglyMeasurable.norm.pow 2)
    · intro z
      filter_upwards [] with x
      rw [Real.norm_of_nonneg (mul_nonneg (inv_nonneg.mpr (le_max_left _ _ |>.trans' hd.le)) (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_right (inv_anti₀ hd (le_max_left _ _)) (sq_nonneg _)
    · exact ((u.value_L2 s).norm.integrable_sq).const_mul _
    · filter_upwards [] with x
      exact (((continuous_const.max (continuous_const.sub continuous_id).norm).inv₀
        (fun z => ne_of_gt (hd.trans_le (le_max_left _ _)))).mul continuous_const)
  apply hG.continuousOn.congr
  intro z hz
  unfold coreCoulombPotential G
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro i hi
  apply integral_congr_ae
  filter_upwards [hu s] with x hx
  by_cases he : u.value s x=0
  · simp [he]
  · have ha : position x i∈A := (by_contra (fun hn => he (hx hn)) : x∈allPositions A) i
    have hz' : ‖z-y‖ ≤ r := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz
    have htri : ‖position x i-y‖ ≤ ‖position x i-z‖+‖z-y‖ := by
      simpa only [dist_eq_norm] using dist_triangle (position x i) z y
    have hdist : d ≤ ‖position x i-z‖ := by dsimp [d]; linarith [hsep _ ha]
    simp only [max_eq_right hdist,coulombKernel]

lemma coreCoulombPotential_weak_harmonic {k : ℕ} (u : H1Vector k)
    {A U : Set Space} (hu : SpatiallySupported u A) (hdis : Disjoint A U) :
    NeutralAtom.HasWeakLaplacian (coreCoulombPotential u) U (fun _ => 0) := by
  intro φ hφ hc ht
  have hi : Integrable (NeutralAtom.coordinateLaplacian φ) :=
    (NeutralAtom.continuous_coordinateLaplacian (hφ.of_le (by exact WithTop.coe_le_coe.mpr le_top))).integrable_of_hasCompactSupport
      (NeutralAtom.hasCompactSupport_coordinateLaplacian hc)
  rw [coreCoulombPotential_fubini u _ hi]
  simp only [zero_mul,integral_zero]
  apply Finset.sum_eq_zero
  intro s hs
  apply Finset.sum_eq_zero
  intro i hi
  apply integral_eq_zero_of_ae
  filter_upwards [hu s] with x hx
  by_cases he : u.value s x=0
  · simp [he]
  · have ha : position x i∈A := (by_contra (fun hn => he (hx hn)) : x∈allPositions A) i
    have hn : position x i∉tsupport φ := fun h => Set.disjoint_left.mp hdis ha (ht h)
    have HH := NeutralAtom.integral_translated_coulombKernel_laplacian hφ hc (position x i)
    have heq : (∫ z, coulombKernel (position x i-z)*NeutralAtom.coordinateLaplacian φ z)=0 := by
      simp_rw [coulombKernel_sub_comm (position x i)]
      change (∫ z, NeutralAtom.coulombKernel (z-position x i)*NeutralAtom.coordinateLaplacian φ z)=0
      rw [HH,image_eq_zero_of_notMem_tsupport hn]
      ring
    simp only [heq,zero_mul,Pi.zero_apply]

lemma attraction_weak_harmonic {J : ℕ} (S : Nuclei J) {U : Set Space}
    (hsep : ∀ j, S.position j∉U) :
    NeutralAtom.HasWeakLaplacian (attraction S) U (fun _ => 0) := by
  intro φ hφ hc ht
  have hL := NeutralAtom.continuous_coordinateLaplacian
    (hφ.of_le (by exact WithTop.coe_le_coe.mpr le_top))
  have hLc := NeutralAtom.hasCompactSupport_coordinateLaplacian hc
  have hts : tsupport (NeutralAtom.coordinateLaplacian φ) ⊆ tsupport φ := by
    apply closure_minimal _ (isClosed_tsupport _)
    intro x hx
    by_contra hn
    exact hx (NeutralAtom.coordinateLaplacian_eq_zero_of_notMem_tsupport hn)
  have hi (j : Fin J) : Integrable (fun x => coulombKernel (x-S.position j)*NeutralAtom.coordinateLaplacian φ x) := by
    apply NeutralAtom.integrable_mul_compact_of_continuousAt _ hL hLc
    intro x hx
    have hn : x-S.position j≠0 := sub_ne_zero.mpr (fun he => hsep j (he ▸ ht (hts hx)))
    exact ((continuous_id.sub continuous_const).norm.continuousAt).inv₀ (norm_ne_zero_iff.mpr hn)
  simp only [attraction,Finset.sum_mul,mul_assoc]
  rw [integral_finsetSum _ (fun j _ => (hi j).const_mul _)]
  simp only [zero_mul,integral_zero]
  apply Finset.sum_eq_zero
  intro j hj
  rw [integral_const_mul]
  change S.charge j*(∫ x, NeutralAtom.coulombKernel (x-S.position j)*NeutralAtom.coordinateLaplacian φ x)=0
  rw [NeutralAtom.integral_translated_coulombKernel_laplacian hφ hc,
    image_eq_zero_of_notMem_tsupport (fun h => hsep j (ht h))]
  ring

lemma attraction_continuousOn {J : ℕ} (S : Nuclei J) {U : Set Space}
    (hsep : ∀ j, S.position j∉U) : ContinuousOn (attraction S) U := by
  change ContinuousOn (fun x => ∑ j : Fin J, S.charge j * ‖x-S.position j‖⁻¹) U
  apply continuousOn_finsetSum
  intro j hj
  refine continuousOn_const.mul ?_
  refine ((continuous_id.sub continuous_const).norm.continuousOn).inv₀ ?_
  intro x hx
  exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr (fun he => hsep j ((show x=S.position j from he) ▸ hx)))

lemma coreScreenedField_continuousOn {J k : ℕ} (S : Nuclei J) (u : H1Vector k)
    {A : Set Space} (hu : SpatiallySupported u A) {y : Space} {r t : ℝ}
    (hrt : r<t) (hsep : ∀ a∈A, t ≤ ‖a-y‖)
    (hnuc : ∀ j, S.position j∉Metric.closedBall y r) :
    ContinuousOn (coreScreenedField S u) (Metric.closedBall y r) :=
  (attraction_continuousOn S hnuc).sub (coreCoulombPotential_continuousOn u hu hrt hsep)

lemma coreScreenedField_weak_harmonic {J k : ℕ} (S : Nuclei J) (u : H1Vector k)
    {A U : Set Space} (hu : SpatiallySupported u A) (hdis : Disjoint A U)
    (hnuc : ∀ j, S.position j∉U) :
    NeutralAtom.HasWeakLaplacian (coreScreenedField S u) U (fun _ => 0) := by
  intro φ hφ hc ht
  have hL := NeutralAtom.continuous_coordinateLaplacian
    (hφ.of_le (by exact WithTop.coe_le_coe.mpr le_top))
  have hLc := NeutralAtom.hasCompactSupport_coordinateLaplacian hc
  have hi : Integrable (NeutralAtom.coordinateLaplacian φ) := hL.integrable_of_hasCompactSupport hLc
  have hiC := coreCoulombPotential_mul_integrable u _ hi
  have hiA : Integrable (fun x => attraction S x*NeutralAtom.coordinateLaplacian φ x) := by
    apply NeutralAtom.integrable_mul_compact_of_continuousAt _ hL hLc
    intro x hx
    have hts : tsupport (NeutralAtom.coordinateLaplacian φ) ⊆ tsupport φ := by
      apply closure_minimal _ (isClosed_tsupport _)
      intro x hx
      by_contra hn
      exact hx (NeutralAtom.coordinateLaplacian_eq_zero_of_notMem_tsupport hn)
    have hx' : x∈tsupport φ := hts hx
    have hs (j) : x≠S.position j := fun h => hnuc j (h ▸ ht hx')
    change ContinuousAt (fun x => ∑ j : Fin J, S.charge j * ‖x-S.position j‖⁻¹) x
    apply tendsto_finsetSum
    intro j hj
    exact continuousAt_const.mul (((continuous_id.sub continuous_const).norm.continuousAt).inv₀
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hs j))))
  simp only [coreScreenedField,sub_mul]
  rw [integral_sub hiA hiC,attraction_weak_harmonic S hnuc φ hφ hc ht,
    coreCoulombPotential_weak_harmonic u hu hdis φ hφ hc ht]
  simp

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_PatchGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology ContDiff SchwartzMap Pointwise
noncomputable section
namespace Coulomb

lemma patch_continuous_field {J k : ℕ} (S : Nuclei J) (u : H1Vector k)
    {a b t : ℝ} (ha : 0<a) (hb : 0<b) (ht : t≤6*a) (y : Space)
    (hu : SpatiallySupported u {z | t≤‖z-y‖}) (hn : ∀ j, 20*a≤‖S.position j-y‖) :
    ContinuousOn (coreScreenedField S u) (Metric.ball y (t-4*b)) := by
  apply (coreScreenedField_continuousOn S u hu (r := t-4*b) (t := t) (by linarith)
    (fun z hz => hz) ?_).mono Metric.ball_subset_closedBall
  intro j hj
  have hh : ‖S.position j-y‖≤t-4*b := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hj
  linarith [hn j]

lemma patch_harmonic_field {J k : ℕ} (S : Nuclei J) (u : H1Vector k)
    {a b t : ℝ} (ha : 0<a) (hb : 0<b) (ht : t≤6*a) (y : Space)
    (hu : SpatiallySupported u {z | t≤‖z-y‖}) (hn : ∀ j, 20*a≤‖S.position j-y‖) :
    NeutralAtom.HasWeakLaplacian (coreScreenedField S u) (Metric.ball y (t-4*b)) (fun _ => 0) := by
  apply coreScreenedField_weak_harmonic S u hu
  · apply Set.disjoint_left.mpr
    intro z hz hz'
    have hh : ‖z-y‖<t-4*b := by simpa only [Metric.mem_ball,dist_eq_norm] using hz'
    change t≤‖z-y‖ at hz
    linarith
  · intro j hj
    have hh : ‖S.position j-y‖<t-4*b := by simpa only [Metric.mem_ball,dist_eq_norm] using hj
    linarith [hn j]

lemma patch_inner_ball {a b t : ℝ} (_ : 0<a) (hb : 0<b) (hsmall : 18*b≤a)
    (ht : 5*a≤t) (y : Space) : Metric.closedBall y (4*a)⊆Metric.ball y (t-4*b) := by
  intro z hz
  have hh : ‖z-y‖≤4*a := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz
  simp only [Metric.mem_ball,dist_eq_norm]
  linarith

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_UniformCountConsequences
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
noncomputable section
namespace Coulomb

lemma exists_atomic_annular_mesh {α β : ℝ} (hα : 0 < α) : ∃ t : Finset Space,
    (∀ z∈t, α ≤ ‖z‖ ∧ ‖z‖ ≤ β) ∧
    (∀ w : Space, α ≤ ‖w‖ → ‖w‖ ≤ β → ∃ z∈t, ‖w-z‖ < atomicCellScale z) := by
  let B : Set Space := {z | α ≤ ‖z‖ ∧ ‖z‖ ≤ β}
  have hc : IsCompact B := (isCompact_closedBall (0:Space) β).of_isClosed_subset
    ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const))
    (fun z hz => by simpa only [Metric.mem_closedBall,dist_zero_right] using hz.2)
  have hp (z : B) : 0 < atomicCellScale z.val := atomicCellScale_pos (by
    intro he; have H:=z.property.1; simpa [he] using hα.trans_le H)
  have hcover : B ⊆ ⋃ z : B, Metric.ball z.val (atomicCellScale z.val) := by
    intro w hw
    exact Set.mem_iUnion.mpr ⟨⟨w,hw⟩,Metric.mem_ball_self (hp ⟨w,hw⟩)⟩
  obtain ⟨t,ht⟩ := hc.elim_finite_subcover (fun z : B => Metric.ball z.val (atomicCellScale z.val))
    (fun _ => Metric.isOpen_ball) hcover
  refine ⟨t.image Subtype.val,?_,?_⟩
  · intro z hz
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hz
    exact v.property
  · intro w hw1 hw2
    obtain ⟨z,hz⟩ := Set.mem_iUnion.mp (ht ⟨hw1,hw2⟩)
    obtain ⟨hzt,hzw⟩ := Set.mem_iUnion.mp hz
    exact ⟨z.val,Finset.mem_image.mpr ⟨z,hzt,rfl⟩,by simpa only [Metric.mem_ball,dist_eq_norm] using hzw⟩

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_NewtonInterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
noncomputable section
namespace Coulomb

def radialShell (h : ℝ) : Set Space := Metric.ball 0 (2*h) \ Metric.ball 0 h

def radialShellDensity (h : ℝ) : Space → ℝ := (radialShell h).indicator (fun _ => 1)

def radialShellMoment (h : ℝ) : ℝ := ∫ y, coulombKernel y*radialShellDensity h y

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_ExplicitMultiplyGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

open scoped ENNReal Convolution

theorem observationNoiseBase_compact : HasCompactSupport observationNoiseBase := by
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Set.Icc (-1:ℝ) 1))
  intro u hu
  rw [observationNoiseBase_formula, ite_eq_right]
  intro hh
  exact hu ⟨(abs_lt.mp hh).1.le, (abs_lt.mp hh).2.le⟩

theorem observationNoiseBase_integrable : Integrable observationNoiseBase :=
  observationNoiseBase_contDiff.continuous.integrable_of_hasCompactSupport
    observationNoiseBase_compact

theorem observationNoiseBase_integral_pos : 0 < ∫ u, observationNoiseBase u := by
  apply integral_pos_of_integrable_nonneg_nonzero
    observationNoiseBase_contDiff.continuous observationNoiseBase_integrable
    observationNoiseBase_nonneg (x := 0)
  exact (expNegInvGlue.pos_of_pos (by norm_num : (0:ℝ) < 1-0^2)).ne'

theorem observationNoiseDensity_nonneg (u : ℝ) : 0 ≤ observationNoiseDensity u :=
  mul_nonneg (inv_nonneg.mpr observationNoiseBase_integral_pos.le)
    (observationNoiseBase_nonneg u)

theorem observationNoiseDensity_integrable : Integrable observationNoiseDensity :=
  observationNoiseBase_integrable.const_mul _

theorem observationNoiseDensity_mass : (∫ u, observationNoiseDensity u) = 1 := by
  unfold observationNoiseDensity
  rw [integral_const_mul, observationNoiseNormalizer]
  exact inv_mul_cancel₀ observationNoiseBase_integral_pos.ne'

instance observationNoiseLaw_probability : IsProbabilityMeasure observationNoiseLaw := by
  constructor
  rw [observationNoiseLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal observationNoiseDensity_integrable
      (Filter.Eventually.of_forall observationNoiseDensity_nonneg), observationNoiseDensity_mass]
  norm_num

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_H1Pairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Classical ContDiff
noncomputable section
namespace Coulomb

def massPair {n:ℕ} (u v:H1Vector n) : ℝ := ∑ s,∫ x,inner ℝ (u.value s x) (v.value s x)
def kineticPair {n:ℕ} (u v:H1Vector n) : ℝ := (1/2:ℝ)*∑ s,∑ a,∫ x,inner ℝ (u.gradient s a x) (v.gradient s a x)
def nuclearPair {M n:ℕ} (S:Nuclei M) (u v:H1Vector n) : ℝ :=
  ∑ s,∫ x,(∑ i,attraction S (position x i))*inner ℝ (u.value s x) (v.value s x)
def repulsionPair {n:ℕ} (u v:H1Vector n) : ℝ :=
  ∑ s,∫ x,pairPotential x*inner ℝ (u.value s x) (v.value s x)
def formPair {M n:ℕ} (S:Nuclei M) (u v:H1Vector n) : ℝ := kineticPair u v-nuclearPair S u v+repulsionPair u v
end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_SmoothMaximum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
namespace NeutralAtom

lemma coordinateLaplacian_comp_scalar {f : Position → ℝ} {h : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hh : ContDiff ℝ 2 h) (x : Position) :
    coordinateLaplacian (fun y => h (f y)) x=
      deriv (deriv h) (f x)*(∑ a : Fin 3, (deriv (fun t : ℝ => f (x+t • axis a)) 0)^2)+
      deriv h (f x)*coordinateLaplacian f x := by
  unfold coordinateLaplacian
  have H (a : Fin 3) : ContDiff ℝ 2 (fun t : ℝ => f (x+t • axis a)) :=
    hf.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  simp_rw [second_deriv_comp_scalar (H _) hh,zero_smul,add_zero]
  rw [Finset.sum_add_distrib,Finset.mul_sum,Finset.mul_sum]

lemma coordinateLaplacian_softMax_lower {e : ℝ} (he : 0<e) {f g : Position → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : Position) :
    softWeight e (f x-g x)*coordinateLaplacian f x+
      (1-softWeight e (f x-g x))*coordinateLaplacian g x≤
      coordinateLaplacian (fun y => softMax e (f y) (g y)) x := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by exact WithTop.coe_le_coe.mpr le_top)
  have hg2 : ContDiff ℝ 2 g := hg.of_le (by exact WithTop.coe_le_coe.mpr le_top)
  have hs2 : ContDiff ℝ 2 (softPlus e) := (contDiff_softPlus he).of_le (by exact WithTop.coe_le_coe.mpr le_top)
  unfold softMax
  have hcomp : ContDiff ℝ 2 (fun y => softPlus e (f y-g y)) := hs2.comp (hf2.sub hg2)
  rw [coordinateLaplacian_add_at hg2.contDiffAt hcomp.contDiffAt,
    coordinateLaplacian_comp_scalar (hf2.sub hg2) hs2,second_deriv_softPlus he,
    (softPlus_hasDerivAt he _).deriv,coordinateLaplacian_sub hf2 hg2]
  have H : 0≤e^2/(2*(softAbs e (f x-g x))^3)*
      (∑ a : Fin 3, (deriv (fun t : ℝ => f (x+t • axis a)-g (x+t • axis a)) 0)^2) := by
    apply mul_nonneg
    · have hp := softAbs_pos he (f x-g x)
      positivity
    · exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  nlinarith

end NeutralAtom

end
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
namespace NeutralAtom

lemma softWeight_response_tendsto {e a b q r : ℕ → ℝ} {A B Q R : ℝ}
    (he : Tendsto e atTop (𝓝 0)) (hep : ∀ n,0<e n)
    (ha : Tendsto a atTop (𝓝 A)) (hb : Tendsto b atTop (𝓝 B))
    (hq : Tendsto q atTop (𝓝 Q)) (hr : Tendsto r atTop (𝓝 R))
    (htie : A=B → Q=R) :
    Tendsto (fun n => softWeight (e n) (a n-b n)*q n+
      (1-softWeight (e n) (a n-b n))*r n) atTop (𝓝 (if B≤ A then Q else R)) := by
  have h1 : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  rcases lt_trichotomy A B with h|h|h
  · rw [ite_eq_right (not_le.mpr h)]
    have hw := softWeight_tendsto_of_gt he ha hb h
    simpa using (hw.mul hq).add ((h1.sub hw).mul hr)
  · have hQR := htie h
    rw [ite_eq_left h.ge,hQR]
    rw [hQR] at hq
    apply (show Tendsto (fun n => min (q n) (r n)) atTop (𝓝 R) by simpa using hq.min hr).squeeze
      (show Tendsto (fun n => max (q n) (r n)) atTop (𝓝 R) by simpa using hq.max hr)
    · intro n; exact (convex_pair_bounds (softWeight_bounds (hep n) _).1 (softWeight_bounds (hep n) _).2).1
    · intro n; exact (convex_pair_bounds (softWeight_bounds (hep n) _).1 (softWeight_bounds (hep n) _).2).2
  · rw [ite_eq_left h.le]
    have hw := softWeight_tendsto_of_lt he ha hb h
    simpa using (hw.mul hq).add ((h1.sub hw).mul hr)

end NeutralAtom

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_MaximumMollifier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter ContinuousLinearMap
open scoped BigOperators Topology ContDiff Convolution
namespace NeutralAtom

lemma maximumMollify_tendsto {f : Position → ℝ} (hf : Continuous f) (x : Position) :
    Tendsto (fun n => maximumMollify n f x) atTop (𝓝 (f x)) := by
  have H := ContDiffBump.convolution_tendsto_right_of_continuous (μ:=volume)
    maximumBump_rOut_tendsto hf x
  simpa only [continuous_convolution_comm,maximumMollify] using H

lemma maximumMollify_ae_tendsto {f : Position → ℝ} (hf : LocallyIntegrable f volume) :
    ∀ᵐ x, Tendsto (fun n => maximumMollify n f x) atTop (𝓝 (f x)) := by
  have H := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (μ:=volume)
    maximumBump_rOut_tendsto (K:=2) (Eventually.of_forall (fun n => by dsimp [maximumBump]; linarith)) hf
  simpa only [continuous_convolution_comm,maximumMollify] using H

lemma maximumMollify_abs_le {f : Position → ℝ} (hf : LocallyIntegrable f volume)
    {A : ℝ} {U : Set Position} (hA : ∀ y∈U, |f y|≤A) (n : ℕ) {x : Position}
    (hx : Metric.closedBall x (maximumBump n).rOut⊆U) : |maximumMollify n f x|≤A := by
  let φ := maximumBump n
  have hi := (φ.hasCompactSupport_normed (μ:=volume)).convolutionExists_right (lsmul ℝ ℝ) hf φ.continuous_normed x
  change Integrable (fun y => f y*φ.normed volume (x-y)) volume at hi
  change |∫ y, f y*φ.normed volume (x-y)|≤A
  calc
    _ ≤ ∫ y, |f y*φ.normed volume (x-y)| := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun y => f y*φ.normed volume (x-y))
    _ ≤ ∫ y, A*φ.normed volume (x-y) := by
      have hin : Integrable (fun y => |f y*φ.normed volume (x-y)|) volume := hi.norm
      apply integral_mono hin ((integrable_normed_bump_reflect φ x).const_mul A)
      intro y
      change |f y*φ.normed volume (x-y)|≤A*φ.normed volume (x-y)
      rw [abs_mul,abs_of_nonneg (φ.nonneg_normed _)]
      by_cases hy : φ.normed volume (x-y)=0
      · simp [hy]
      · apply mul_le_mul_of_nonneg_right _ (φ.nonneg_normed _)
        exact hA y (hx (normed_bump_reflect_tsupport φ x (subset_closure hy)))
    _ = A := by rw [integral_const_mul,integral_sub_left_eq_self,φ.integral_normed,mul_one]

lemma maximumMollify_abs_le_ball {f : Position → ℝ} (hf : LocallyIntegrable f volume)
    {A R : ℝ} (hA : ∀ y∈Metric.closedBall (0:Position) (R+1), |f y|≤A)
    (n : ℕ) {x : Position} (hx : x∈Metric.closedBall 0 R) : |maximumMollify n f x|≤A := by
  apply maximumMollify_abs_le hf hA n
  intro y hy
  simp only [Metric.mem_closedBall] at *
  have h := dist_triangle y x 0
  exact h.trans (add_le_add (hy.trans (maximumBump_rOut_le_one n)) hx |>.trans_eq (add_comm 1 R))

end NeutralAtom

end
open MeasureTheory Set Filter ContinuousLinearMap
open scoped BigOperators Topology ContDiff Convolution
namespace NeutralAtom

lemma weakLaplacianGE_maximumMollify_local {f q : Position → ℝ} {U : Set Position}
    (hf : LocallyIntegrable f volume) (hw : WeakLaplacianGE f U q) (n : ℕ) (x : Position)
    (hx : Metric.closedBall x (maximumBump n).rOut ⊆ U) :
    maximumMollify n q x ≤ coordinateLaplacian (maximumMollify n f) x := by
  let φ := maximumBump n
  have ht := normed_bump_reflect_tsupport φ x
  have hc : HasCompactSupport (fun y => φ.normed volume (x-y)) :=
    (isCompact_closedBall x φ.rOut).of_isClosed_subset (isClosed_tsupport _) ht
  have hs : ContDiff ℝ ∞ (fun y => φ.normed volume (x-y)) :=
    φ.contDiff_normed.comp (contDiff_const.sub contDiff_id)
  have H := hw _ hs hc (ht.trans hx) (fun y => φ.nonneg_normed _)
  unfold maximumMollify
  rw [coordinateLaplacian_convolution hf (maximumBump n).contDiff_normed (maximumBump n).hasCompactSupport_normed]
  simpa only [coordinateLaplacian_reflect,convolution_def,lsmul_apply,smul_eq_mul] using H

theorem WeakLaplacianGE.max_tied {f g q r : Position → ℝ} {U : Set Position}
    (hU : IsOpen U) (hf : Continuous f) (hg : Continuous g)
    (hq : LocallyIntegrable q volume) (hr : LocallyIntegrable r volume)
    (hbq : ∀ R : ℝ, ∃ C : ℝ, ∀ x ∈ Metric.closedBall 0 R, |q x| ≤ C)
    (hbr : ∀ R : ℝ, ∃ C : ℝ, ∀ x ∈ Metric.closedBall 0 R, |r x| ≤ C)
    (hwf : WeakLaplacianGE f U q) (hwg : WeakLaplacianGE g U r)
    (htie : ∀ x, f x=g x → q x=r x) :
    WeakLaplacianGE (fun x => max (f x) (g x)) U (fun x => if g x ≤ f x then q x else r x) := by
  intro φ hφ hc ht hp
  obtain ⟨R,hR⟩ := hc.isBounded.subset_closedBall (0:Position)
  obtain ⟨A,hA⟩ := (isCompact_closedBall (0:Position) (R+1)).exists_bound_of_continuousOn hf.continuousOn
  obtain ⟨B,hB⟩ := (isCompact_closedBall (0:Position) (R+1)).exists_bound_of_continuousOn hg.continuousOn
  obtain ⟨Q,hQ⟩ := hbq (R+1)
  obtain ⟨S,hS⟩ := hbr (R+1)
  let e : ℕ → ℝ := fun n => (maximumBump n).rOut
  have he : ∀ n, 0 < e n := fun n => (maximumBump n).rOut_pos
  have hF (n : ℕ) := maximumMollify_contDiff hf.locallyIntegrable n
  have hG (n : ℕ) := maximumMollify_contDiff hg.locallyIntegrable n
  have hQn (n : ℕ) := maximumMollify_contDiff hq n
  have hSn (n : ℕ) := maximumMollify_contDiff hr n
  let p : ℕ → Position → ℝ := fun n x => softWeight (e n) (maximumMollify n f x-maximumMollify n g x)
  let v : ℕ → Position → ℝ := fun n x => softMax (e n) (maximumMollify n f x) (maximumMollify n g x)
  let a : ℕ → Position → ℝ := fun n x => p n x*maximumMollify n q x+(1-p n x)*maximumMollify n r x
  have hpc (n : ℕ) : Continuous (p n) := (continuous_softWeight (he n)).comp ((hF n).continuous.sub (hG n).continuous)
  have hvc (n : ℕ) : ContDiff ℝ ∞ (v n) := contDiff_softMax (he n) (hF n) (hG n)
  have hac (n : ℕ) : Continuous (a n) := ((hpc n).mul (hQn n).continuous).add ((continuous_const.sub (hpc n)).mul (hSn n).continuous)
  have hbv (n : ℕ) (x : Position) (hx : x ∈ tsupport φ) : |v n x| ≤ A+B+1 := by
    have H := softMax_abs_le (he n).le
      (maximumMollify_abs_le_ball hf.locallyIntegrable hA n (hR hx))
      (maximumMollify_abs_le_ball hg.locallyIntegrable hB n (hR hx))
    have hle : e n ≤ 1 := maximumBump_rOut_le_one n
    linarith
  have hba (n : ℕ) (x : Position) (hx : x ∈ tsupport φ) : |a n x| ≤ Q+S := by
    exact convex_pair_abs_le (softWeight_bounds (he n) _).1 (softWeight_bounds (he n) _).2
      (maximumMollify_abs_le_ball hq hQ n (hR hx))
      (maximumMollify_abs_le_ball hr hS n (hR hx))
  have hva (x : Position) : Tendsto (fun n => v n x) atTop (𝓝 (max (f x) (g x))) :=
    softMax_tendsto maximumBump_rOut_tendsto (maximumMollify_tendsto hf x) (maximumMollify_tendsto hg x)
  have haa : ∀ᵐ x, Tendsto (fun n => a n x) atTop (𝓝 (if g x ≤ f x then q x else r x)) := by
    filter_upwards [maximumMollify_ae_tendsto hq,maximumMollify_ae_tendsto hr] with x hx hy
    exact softWeight_response_tendsto maximumBump_rOut_tendsto he (maximumMollify_tendsto hf x)
      (maximumMollify_tendsto hg x) hx hy (htie x)
  have hla := tendsto_integral_compact_mul hac hφ.continuous hc hba haa
  have hlv := tendsto_integral_compact_mul (fun n => (hvc n).continuous)
    (contDiff_coordinateLaplacian hφ).continuous (hasCompactSupport_coordinateLaplacian hc)
    (fun n x hx => hbv n x (tsupport_coordinateLaplacian_subset φ hx)) (Eventually.of_forall hva)
  apply le_of_tendsto_of_tendsto hla hlv
  obtain ⟨δ,hδ,hδU⟩ := hc.exists_cthickening_subset_open hU ht
  have hn : ∀ᶠ n in atTop, e n < δ := maximumBump_rOut_tendsto.eventually (gt_mem_nhds hδ)
  filter_upwards [hn] with n hn
  have hlocal (x : Position) (hx : x ∈ tsupport φ) : Metric.closedBall x (maximumBump n).rOut ⊆ U :=
    (Metric.closedBall_subset_closedBall hn.le).trans ((Metric.closedBall_subset_cthickening hx δ).trans hδU)
  have hpoint (x : Position) (hx : x ∈ tsupport φ) : a n x ≤ coordinateLaplacian (v n) x := by
    apply le_trans _ (coordinateLaplacian_softMax_lower (he n) (hF n) (hG n) x)
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left (weakLaplacianGE_maximumMollify_local hf.locallyIntegrable hwf n x (hlocal x hx))
        (softWeight_bounds (he n) _).1
    · exact mul_le_mul_of_nonneg_left (weakLaplacianGE_maximumMollify_local hg.locallyIntegrable hwg n x (hlocal x hx))
        (sub_nonneg.mpr (softWeight_bounds (he n) _).2)
  rw [integral_mul_coordinateLaplacian_eq (fun x _ => (hvc n).contDiffAt.of_le (by exact WithTop.coe_le_coe.mpr le_top)) hφ hc]
  apply integral_mono
    (integrable_mul_compact_of_continuousAt (fun x _ => (hac n).continuousAt) hφ.continuous hc)
    (integrable_mul_compact_of_continuousAt (fun x _ => (contDiff_coordinateLaplacian (hvc n)).continuous.continuousAt) hφ.continuous hc)
  intro x
  change a n x*φ x ≤ coordinateLaplacian (v n) x*φ x
  by_cases hx : x ∈ tsupport φ
  · exact mul_le_mul_of_nonneg_right (hpoint x hx) (hp x)
  · simp [image_eq_zero_of_notMem_tsupport hx]

end NeutralAtom

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_WeakReactionMax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
namespace NeutralAtom

theorem WeakLaplacianGE.max_reaction {f g b : Position → ℝ} {F : Position → ℝ → ℝ}
    {U : Set Position} (hU : IsOpen U) (hf : Continuous f) (hg : Continuous g)
    (hq : LocallyIntegrable (fun x => b x+F x (f x)) volume)
    (hr : LocallyIntegrable (fun x => b x+F x (g x)) volume)
    (hbq : ∀ R : ℝ, ∃ C : ℝ, ∀ x ∈ Metric.closedBall 0 R, |b x+F x (f x)| ≤ C)
    (hbr : ∀ R : ℝ, ∃ C : ℝ, ∀ x ∈ Metric.closedBall 0 R, |b x+F x (g x)| ≤ C)
    (hwf : WeakLaplacianGE f U (fun x => b x+F x (f x)))
    (hwg : WeakLaplacianGE g U (fun x => b x+F x (g x))) :
    WeakLaplacianGE (fun x => max (f x) (g x)) U (fun x => b x+F x (max (f x) (g x))) := by
  have H := WeakLaplacianGE.max_tied hU hf hg hq hr hbq hbr hwf hwg (fun x h => by rw [h])
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  by_cases h : g x ≤ f x
  · simp [h]
  · simp [h,max_eq_right (le_of_not_ge h)]

lemma cutoffReaction_offset_ball_bound {a Z : ℝ} (ha : 0 < a)
    {f : Position → ℝ} (hf : Continuous f) (R : ℝ) :
    ∃ C : ℝ, ∀ x ∈ Metric.closedBall 0 R,
      |cutoffReaction a (fun y => Z*coulombKernel y+f y) x| ≤ C := by
  obtain ⟨D,hD⟩ := (isCompact_closedBall (0:Position) R).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨tfReaction (|Z|/a+D),?_⟩
  intro x hx
  by_cases haX : a ≤ ‖x‖
  · have hn : 0 < ‖x‖ := ha.trans_le haX
    have hZ : Z*coulombKernel x ≤ |Z|/a := by
      unfold coulombKernel
      calc
        Z*‖x‖⁻¹ ≤ |Z| *‖x‖⁻¹ := mul_le_mul_of_nonneg_right (le_abs_self _) (inv_nonneg.mpr hn.le)
        _ ≤ |Z| *a⁻¹ := mul_le_mul_of_nonneg_left (inv_anti₀ ha haX) (abs_nonneg _)
        _ = |Z|/a := by rw [div_eq_mul_inv]
    have h := tfReaction_monotone (show Z*coulombKernel x+f x ≤ |Z|/a+D by
      have H : f x ≤ D := (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hD x hx)
      linarith)
    simpa [cutoffReaction, haX, abs_of_nonneg (tfReaction_nonneg _)] using h
  · simpa [cutoffReaction, haX] using tfReaction_nonneg (|Z|/a+D)

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem WeakLaplacianGE.average {F Q : Ω → Position → ℝ} {U : Set Position}
    (hF : Measurable (Function.uncurry F)) (hQ : Measurable (Function.uncurry Q))
    (hbF : ∀ R : ℝ, ∃ C : ℝ, ∀ o x, x ∈ Metric.closedBall 0 R → |F o x| ≤ C)
    (hbQ : ∀ R : ℝ, ∃ C : ℝ, ∀ o x, x ∈ Metric.closedBall 0 R → |Q o x| ≤ C)
    (hw : ∀ᵐ o ∂μ, WeakLaplacianGE (F o) U (Q o)) :
    WeakLaplacianGE (fun x => ∫ o, F o x ∂μ) U (fun x => ∫ o, Q o x ∂μ) := by
  intro φ hφ hc ht hp
  rw [integral_average_test hQ hbQ hφ.continuous hc,
    integral_average_test hF hbF (contDiff_coordinateLaplacian hφ).continuous
      (hasCompactSupport_coordinateLaplacian hc)]
  apply integral_mono_ae
    (joint_compact_test_integrable hQ hbQ hφ.continuous hc).integral_prod_left
    (joint_compact_test_integrable hF hbF (contDiff_coordinateLaplacian hφ).continuous
      (hasCompactSupport_coordinateLaplacian hc)).integral_prod_left
  filter_upwards [hw] with o ho
  exact ho φ hφ hc ht hp

theorem tfReaction_integral_le {f : Ω → ℝ} (hf : Integrable f μ)
    (hr : Integrable (fun o => (max (f o) 0)^(3/2:ℝ)) μ) :
    tfReaction (∫ o, f o ∂μ) ≤ ∫ o, tfReaction (f o) ∂μ := by
  have hpos : Integrable (fun o => max (f o) 0) μ := hf.sup (integrable_const 0)
  have hm : max (∫ o, f o ∂μ) 0 ≤ ∫ o, max (f o) 0 ∂μ := max_le
    (integral_mono hf hpos (fun o => le_max_left _ _))
    (integral_nonneg (fun o => le_max_right _ _))
  have hJ := (convexOn_rpow (by norm_num : (1:ℝ) ≤ 3/2)).map_integral_le
    (Real.continuous_rpow_const (by norm_num : (0:ℝ) ≤ 3/2)).continuousOn isClosed_Ici
    (Eventually.of_forall (fun o => (show max (f o) 0 ∈ Ici (0:ℝ) from (show 0 ≤ max (f o) 0 from le_max_right _ _)))) hpos hr
  unfold tfReaction
  rw [integral_const_mul]
  apply mul_le_mul_of_nonneg_left _ (by have := kTF_pos; positivity)
  exact (Real.rpow_le_rpow (le_max_right _ _) hm (by norm_num)).trans hJ

end NeutralAtom

end
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
namespace NeutralAtom

lemma nuclear_offset_test_identity {f φ : Position → ℝ} (hf : Continuous f)
    (Z : ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ x, (Z*coulombKernel x+f x)*coordinateLaplacian φ x)=
      -(4*Real.pi*Z*φ 0)+(∫ x, f x*coordinateLaplacian φ x) := by
  have hL := (contDiff_coordinateLaplacian hφ).continuous
  have hLc := hasCompactSupport_coordinateLaplacian hc
  have hiK : Integrable (fun x => coulombKernel x*coordinateLaplacian φ x) := by
    simpa only [smul_eq_mul] using
      locallyIntegrable_coulombKernel.integrable_smul_right_of_hasCompactSupport hL hLc
  have hiF := integrable_mul_compact_of_continuousAt (fun x _ => hf.continuousAt) hL hLc
  simp_rw [add_mul]
  rw [integral_add (by simpa only [mul_assoc] using hiK.const_mul Z) hiF]
  simp_rw [mul_assoc Z]
  rw [integral_const_mul,integral_coulombKernel_laplacian hφ hc]
  ring

theorem weakNuclearSubsolution_offset_iff {f q : Position → ℝ} {Z : ℝ} {U : Set Position}
    (hf : Continuous f) :
    WeakNuclearSubsolution (fun x => Z*coulombKernel x+f x) Z U q ↔ WeakLaplacianGE f U q := by
  constructor <;> intro h φ hφ hc ht hp
  · have H := h φ hφ hc ht hp
    rw [nuclear_offset_test_identity hf Z hφ hc] at H
    linarith
  · rw [nuclear_offset_test_identity hf Z hφ hc]
    linarith [h φ hφ hc ht hp]

theorem WeakNuclearSubsolution.max_reaction {f g b : Position → ℝ} {Z : ℝ}
    {F : Position → ℝ → ℝ} {U : Set Position}
    (hU : IsOpen U) (hf : Continuous f) (hg : Continuous g)
    (hq : LocallyIntegrable (fun x => b x+F x (Z*coulombKernel x+f x)) volume)
    (hr : LocallyIntegrable (fun x => b x+F x (Z*coulombKernel x+g x)) volume)
    (hbq : ∀ R : ℝ, ∃ C : ℝ, ∀ x ∈ Metric.closedBall 0 R,
      |b x+F x (Z*coulombKernel x+f x)| ≤ C)
    (hbr : ∀ R : ℝ, ∃ C : ℝ, ∀ x ∈ Metric.closedBall 0 R,
      |b x+F x (Z*coulombKernel x+g x)| ≤ C)
    (hwf : WeakNuclearSubsolution (fun x => Z*coulombKernel x+f x) Z U
      (fun x => b x+F x (Z*coulombKernel x+f x)))
    (hwg : WeakNuclearSubsolution (fun x => Z*coulombKernel x+g x) Z U
      (fun x => b x+F x (Z*coulombKernel x+g x))) :
    WeakNuclearSubsolution (fun x => Z*coulombKernel x+max (f x) (g x)) Z U
      (fun x => b x+F x (Z*coulombKernel x+max (f x) (g x))) := by
  apply (weakNuclearSubsolution_offset_iff (hf.max hg)).2
  exact WeakLaplacianGE.max_reaction (F := fun x t => F x (Z*coulombKernel x+t))
    hU hf hg hq hr hbq hbr
    ((weakNuclearSubsolution_offset_iff (Z:=Z) hf).1 hwf)
    ((weakNuclearSubsolution_offset_iff (Z:=Z) hg).1 hwg)

end NeutralAtom

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_WeakLocality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Manifold
namespace NeutralAtom

lemma coordinateLaplacian_finset_sum {ι : Type*} (s : Finset ι) (f : ι → Position → ℝ)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (x : Position) :
    coordinateLaplacian (fun y => ∑ i ∈ s, f i y) x=∑ i ∈ s, coordinateLaplacian (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coordinateLaplacian]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [coordinateLaplacian_add_at ((hf i).of_le (by exact WithTop.coe_le_coe.mpr le_top)).contDiffAt
      ((ContDiff.sum (s:=s) (fun j _ => hf j)).of_le (by exact WithTop.coe_le_coe.mpr le_top)).contDiffAt,ih]

theorem WeakLaplacianGE.of_local {f q : Position → ℝ} {U : Set Position}
    (hf : LocallyIntegrable f volume) (hq : LocallyIntegrable q volume)
    (hlocal : ∀ x ∈ U, ∃ V : Set Position, x ∈ V ∧ IsOpen V ∧ WeakLaplacianGE f V q) :
    WeakLaplacianGE f U q := by
  classical
  intro φ hφ hc ht hp
  choose V hmem hopen hweak using (fun x : tsupport φ => hlocal x.val (ht x.property))
  have hcover : tsupport φ ⊆ ⋃ x : tsupport φ, V x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩,hmem ⟨x,hx⟩⟩
  obtain ⟨s,hs⟩ := hc.elim_finite_subcover V hopen hcover
  let W : s → Set Position := fun i => V i.val
  have hW : tsupport φ ⊆ ⋃ i : s, W i := by
    intro x hx
    obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp (hs hx)
    exact mem_iUnion.mpr ⟨⟨i,hi⟩,hxi⟩
  obtain ⟨P,hP⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I:=𝓘(ℝ,Position))
    (isClosed_tsupport φ) W (fun i => hopen i.val) hW
  let ψ : s → Position → ℝ := fun i x => P i x*φ x
  have hψc (i : s) : ContDiff ℝ ∞ (ψ i) := by
    exact (contMDiff_iff_contDiff.mp (P i).contMDiff).mul hφ
  have hψs (i : s) : HasCompactSupport (ψ i) := hc.mul_left
  have hψt (i : s) : tsupport (ψ i) ⊆ W i :=
    (tsupport_mul_subset_left).trans (hP i)
  have hsum : (fun x => ∑ i : s, ψ i x)=φ := by
    funext x
    by_cases hx : x ∈ tsupport φ
    · have H := P.sum_eq_one hx
      rw [finsum_eq_sum_of_fintype] at H
      simp only [ψ,←Finset.sum_mul,H,one_mul]
    · simp [ψ,image_eq_zero_of_notMem_tsupport hx]
  have hiq (i : s) : Integrable (fun x => q x*ψ i x) := by
    simpa only [smul_eq_mul] using hq.integrable_smul_right_of_hasCompactSupport
      (hψc i).continuous (hψs i)
  have hif (i : s) : Integrable (fun x => f x*coordinateLaplacian (ψ i) x) := by
    simpa only [smul_eq_mul] using hf.integrable_smul_right_of_hasCompactSupport
      (contDiff_coordinateLaplacian (hψc i)).continuous (hasCompactSupport_coordinateLaplacian (hψs i))
  have H := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    hweak i.val (ψ i) (hψc i) (hψs i) (hψt i)
      (fun x => mul_nonneg (P.nonneg i x) (hp x)))
  rw [←integral_finsetSum _ (fun i _ => hiq i),←integral_finsetSum _ (fun i _ => hif i)] at H
  have hsume x : (∑ i : s, ψ i x)=φ x := congrFun hsum x
  simpa only [←Finset.mul_sum,←coordinateLaplacian_finset_sum Finset.univ ψ hψc,hsum,hsume] using H

end NeutralAtom

end
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
namespace NeutralAtom

lemma cutoffReaction_offset_locallyIntegrable {a Z : ℝ} (ha : 0<a)
    {f : Position → ℝ} (hf : Continuous f) :
    LocallyIntegrable (cutoffReaction a (fun x => Z*coulombKernel x+f x)) volume := by
  apply locallyIntegrable_of_ball_bounds
  · exact (tfReaction_continuous.measurable.comp ((measurable_const.mul
      measurable_coulombKernel).add hf.measurable)).indicator
      (isClosed_le continuous_const continuous_norm).measurableSet
  · exact cutoffReaction_offset_ball_bound ha hf

lemma WeakLaplacianGE.mono_source_on {f q r : Position → ℝ} {U : Set Position}
    (hw : WeakLaplacianGE f U q) (hq : LocallyIntegrable q volume)
    (hr : LocallyIntegrable r volume) (hle : ∀ᵐ x, x ∈ U → r x≤q x) :
    WeakLaplacianGE f U r := by
  intro φ hφ hc ht hp
  apply le_trans _ (hw φ hφ hc ht hp)
  have hi (g : Position → ℝ) (hg : LocallyIntegrable g volume) :
      Integrable (fun x => g x*φ x) := by
    simpa only [smul_eq_mul] using hg.integrable_smul_right_of_hasCompactSupport hφ.continuous hc
  apply integral_mono_ae (hi r hr) (hi q hq)
  filter_upwards [hle] with x hx
  by_cases h : x ∈ tsupport φ
  · exact mul_le_mul_of_nonneg_right (hx (ht h)) (hp x)
  · simp [image_eq_zero_of_notMem_tsupport h]

theorem WeakNuclearSubsolution.max_cutoffTF {f g b : Position → ℝ} {a Z : ℝ}
    {U : Set Position} (ha : 0<a) (hU : IsOpen U) (hf : Continuous f) (hg : Continuous g)
    (hb : Measurable b)
    (hbb : ∀ R : ℝ, ∃ C : ℝ, ∀ x ∈ Metric.closedBall 0 R, |b x| ≤ C)
    (hwf : WeakNuclearSubsolution (fun x => Z*coulombKernel x+f x) Z U
      (fun x => b x+cutoffReaction a (fun y => Z*coulombKernel y+f y) x))
    (hwg : WeakNuclearSubsolution (fun x => Z*coulombKernel x+g x) Z U
      (fun x => b x+cutoffReaction a (fun y => Z*coulombKernel y+g y) x)) :
    WeakNuclearSubsolution (fun x => Z*coulombKernel x+max (f x) (g x)) Z U
      (fun x => b x+cutoffReaction a (fun y => Z*coulombKernel y+max (f y) (g y)) x) := by
  have hbi := locallyIntegrable_of_ball_bounds hb hbb
  apply WeakNuclearSubsolution.max_reaction (F := fun x t => if a≤‖x‖ then tfReaction t else 0)
    hU hf hg
  · exact hbi.add (cutoffReaction_offset_locallyIntegrable ha hf)
  · exact hbi.add (cutoffReaction_offset_locallyIntegrable ha hg)
  · intro R
    obtain ⟨C,hC⟩ := hbb R
    obtain ⟨D,hD⟩ := cutoffReaction_offset_ball_bound (Z:=Z) ha hf R
    exact ⟨C+D,fun x hx => (abs_add_le _ _).trans (add_le_add (hC x hx) (hD x hx))⟩
  · intro R
    obtain ⟨C,hC⟩ := hbb R
    obtain ⟨D,hD⟩ := cutoffReaction_offset_ball_bound (Z:=Z) ha hg R
    exact ⟨C+D,fun x hx => (abs_add_le _ _).trans (add_le_add (hC x hx) (hD x hx))⟩
  · exact hwf
  · exact hwg

theorem WeakNuclearSubsolution.finset_max_cutoffTF {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (f : ι → Position → ℝ) {b : Position → ℝ}
    {a Z : ℝ} {U : Set Position} (ha : 0<a) (hU : IsOpen U)
    (hf : ∀ i∈s, Continuous (f i)) (hb : Measurable b)
    (hbb : ∀ R : ℝ, ∃ C : ℝ, ∀ x ∈ Metric.closedBall 0 R, |b x| ≤ C)
    (hw : ∀ i∈s, WeakNuclearSubsolution (fun x => Z*coulombKernel x+f i x) Z U
      (fun x => b x+cutoffReaction a (fun y => Z*coulombKernel y+f i y) x)) :
    WeakNuclearSubsolution (fun x => Z*coulombKernel x+s.sup' hs (fun i => f i x)) Z U
      (fun x => b x+cutoffReaction a (fun y => Z*coulombKernel y+s.sup' hs (fun i => f i y)) x) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact False.elim (Finset.not_nonempty_empty hs)
  | @insert i s hi ih =>
    by_cases hne : s.Nonempty
    · have hf' : ∀ j∈s, Continuous (f j) := fun j hj => hf j (Finset.mem_insert_of_mem hj)
      have h := WeakNuclearSubsolution.max_cutoffTF ha hU (hf i (Finset.mem_insert_self _ _))
        (Continuous.finset_sup'_apply hne hf') hb hbb
        (hw i (Finset.mem_insert_self _ _))
        (ih hne hf' (fun j hj => hw j (Finset.mem_insert_of_mem hj)))
      simpa only [Finset.sup'_insert hne] using h
    · have he := Finset.not_nonempty_iff_eq_empty.mp hne
      subst s
      simpa using hw i (Finset.mem_insert_self _ _)

end NeutralAtom

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RadialBounds_NearActive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
noncomputable section
namespace NeutralAtom

theorem finite_max_near_active {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (f : ι → Position → ℝ) (hf : ∀ i∈s, Continuous (f i))
    {x₀ : Position} {O : Set Position} (hO : IsOpen O) (hx₀ : x₀∈O)
    {η : ℝ} (hη : 0<η) :
    ∃ t : Finset ι, ∃ ht : t.Nonempty, t⊆s ∧
      (∀ i∈s, i∈t ↔ s.sup' hs (fun j => f j x₀)-f i x₀≤η) ∧
      ∃ U : Set Position, x₀∈U ∧ IsOpen U ∧ U⊆O ∧
        (∀ x∈U, s.sup' hs (fun j => f j x)=t.sup' ht (fun j => f j x)) ∧
        (∀ i∈t, ∀ x∈U, s.sup' hs (fun j => f j x)-f i x<2*η) := by
  classical
  let M : Position → ℝ := fun x => s.sup' hs (fun j => f j x)
  have hM : Continuous M := Continuous.finset_sup'_apply hs hf
  obtain ⟨i₀,hi₀,hmax⟩ := Finset.exists_mem_eq_sup' hs (fun i => f i x₀)
  let t := s.filter (fun i => M x₀-f i x₀≤η)
  have hti₀ : i₀∈t := by
    simp only [t,Finset.mem_filter]
    exact ⟨hi₀,by dsimp only [M]; rw [hmax]; linarith⟩
  have ht : t.Nonempty := ⟨i₀,hti₀⟩
  have hts : t⊆s := Finset.filter_subset _ s
  let V : ι → Set Position := fun i => if i∈t then {x | M x-f i x<2*η}
    else {x | f i x<f i₀ x}
  have hV (i) (hi : i∈s) : IsOpen (V i) := by
    dsimp only [V]
    split_ifs
    · exact isOpen_lt (hM.sub (hf i hi)) continuous_const
    · exact isOpen_lt (hf i hi) (hf i₀ hi₀)
  have hxV (i) (hi : i∈s) : x₀∈V i := by
    dsimp only [V]
    split_ifs with hit
    · have hh := (Finset.mem_filter.mp hit).2
      change M x₀-f i x₀<2*η
      linarith
    · have hh : ¬M x₀-f i x₀≤η := by simpa only [t,Finset.mem_filter,hi,true_and] using hit
      change f i x₀<f i₀ x₀
      dsimp only [M] at hh
      rw [hmax] at hh
      linarith
  let U := O∩⋂ i∈s, V i
  refine ⟨t,ht,hts,?_,U,?_,?_,inter_subset_left,?_,?_⟩
  · intro i hi
    simp only [t,Finset.mem_filter,hi,true_and,M]
  · exact ⟨hx₀,mem_iInter₂.mpr (fun i hi => hxV i hi)⟩
  · exact hO.inter (isOpen_biInter_finset fun i hi => hV i hi)
  · intro x hx
    apply le_antisymm
    · apply Finset.sup'_le
      intro i hi
      by_cases hit : i∈t
      · exact Finset.le_sup' (fun j => f j x) hit
      · have hh := mem_iInter₂.mp hx.2 i hi
        have hh' : f i x<f i₀ x := by simpa only [V,ite_eq_right hit,mem_ofPred_eq] using hh
        exact hh'.le.trans (Finset.le_sup' (fun j => f j x) hti₀)
    · exact Finset.sup'_mono (fun j => f j x) hts ht
  · intro i hi x hx
    have hh := mem_iInter₂.mp hx.2 i (hts hi)
    simpa only [V,ite_eq_left hi,mem_ofPred_eq,M] using hh

end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_PatchResponse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap
noncomputable section
namespace Coulomb

def tfScalarDensity (v : ℝ) : ℝ :=
  (max v 0/(thomasFermiKineticConstant*(5/3:ℝ)))^(3/2:ℝ)

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_NearActiveMaximum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
namespace NeutralAtom

lemma WeakLaplacianGE.congr_on {f g q r : Position → ℝ} {U : Set Position}
    (hw : WeakLaplacianGE f U q) (he : ∀ x∈U, f x=g x) (hq : ∀ x∈U, q x=r x) :
    WeakLaplacianGE g U r := by
  intro φ hφ hc ht hp
  have H := hw φ hφ hc ht hp
  have hleft : (fun x => q x*φ x)=(fun x => r x*φ x) := by
    funext x
    by_cases hx : x∈tsupport φ
    · rw [hq x (ht hx)]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have hright : (fun x => f x*coordinateLaplacian φ x)=(fun x => g x*coordinateLaplacian φ x) := by
    funext x
    by_cases hx : x∈tsupport φ
    · rw [he x (ht hx)]
    · simp [coordinateLaplacian_eq_zero_of_notMem_tsupport hx]
  simpa only [hleft,hright] using H

lemma WeakLaplacianGE.mono_domain {f q : Position → ℝ} {U V : Set Position}
    (hw : WeakLaplacianGE f U q) (hVU : V⊆U) : WeakLaplacianGE f V q :=
  fun φ hφ hc ht hp => hw φ hφ hc (ht.trans hVU) hp

theorem WeakNuclearSubsolution.near_active_cutoffTF {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (f q : ι → Position → ℝ)
    {b : Position → ℝ} {a Z η : ℝ} {U : Set Position}
    (ha : 0<a) (hη : 0<η) (hU : IsOpen U)
    (hf : ∀ i∈s, Continuous (f i)) (hq : ∀ i∈s, LocallyIntegrable (q i) volume)
    (hb : Measurable b)
    (hbb : ∀ R : ℝ, ∃ C : ℝ, ∀ x ∈ Metric.closedBall 0 R, |b x| ≤ C)
    (hw : ∀ i∈s, WeakNuclearSubsolution (fun x => Z*coulombKernel x+f i x) Z U (q i))
    (hcompare : ∀ i∈s, ∀ x∈U, s.sup' hs (fun j => f j x)-f i x<2*η →
      b x+cutoffReaction a (fun y => Z*coulombKernel y+f i y) x≤q i x) :
    WeakNuclearSubsolution (fun x => Z*coulombKernel x+s.sup' hs (fun i => f i x)) Z U
      (fun x => b x+cutoffReaction a (fun y => Z*coulombKernel y+s.sup' hs (fun i => f i y)) x) := by
  classical
  let M : Position → ℝ := fun x => s.sup' hs (fun i => f i x)
  have hM : Continuous M := Continuous.finset_sup'_apply hs hf
  have hbi : LocallyIntegrable b volume := locallyIntegrable_of_ball_bounds hb hbb
  apply (weakNuclearSubsolution_offset_iff hM).2
  apply WeakLaplacianGE.of_local hM.locallyIntegrable
    (hbi.add (cutoffReaction_offset_locallyIntegrable ha hM))
  intro x₀ hx₀
  obtain ⟨t,ht,hts,_,V,hxV,hV,hVU,hmax,hnear⟩ :=
    finite_max_near_active s hs f hf hU hx₀ hη
  have hft (i) (hi : i∈t) : Continuous (f i) := hf i (hts hi)
  have hwt (i) (hi : i∈t) : WeakNuclearSubsolution (fun x => Z*coulombKernel x+f i x) Z V
      (fun x => b x+cutoffReaction a (fun y => Z*coulombKernel y+f i y) x) := by
    apply (weakNuclearSubsolution_offset_iff (hft i hi)).2
    apply (((weakNuclearSubsolution_offset_iff (hft i hi)).1 (hw i (hts hi))).mono_domain hVU).mono_source_on
      (hq i (hts hi)) (hbi.add (cutoffReaction_offset_locallyIntegrable ha (hft i hi)))
    exact Eventually.of_forall (fun x hx => hcompare i (hts hi) x (hVU hx) (hnear i hi x hx))
  have H := WeakNuclearSubsolution.finset_max_cutoffTF t ht f ha hV hft hb hbb hwt
  have H' := (weakNuclearSubsolution_offset_iff (Continuous.finset_sup'_apply ht hft)).1 H
  refine ⟨V,hxV,hV,H'.congr_on (fun x hx => (hmax x hx).symm) ?_⟩
  intro x hx
  dsimp only [M]
  unfold cutoffReaction
  by_cases haX : a ≤ ‖x‖
  · simp [Pi.add_apply, Set.indicator, haX, hmax x hx]
  · simp [Pi.add_apply, Set.indicator, haX]

lemma laplacian_propagationBarrier {x : Position} (hx : x≠0) (B r : ℝ) :
    coordinateLaplacian (propagationBarrier B r) x=
      B/‖x‖^6*(12-5*r/(2*‖x‖)) := by
  have hcp (p : ℝ) : ContDiffAt ℝ 2 (radialPower p) x :=
    (contDiffOn_radialPower p 2).contDiffAt (isOpen_punctured.mem_nhds hx)
  unfold propagationBarrier
  rw [coordinateLaplacian_const_mul]
  have he : (fun y => radialPower (-2) y-r/8*radialPower (-(5/2:ℝ)) y)=
      (fun y => radialPower (-2) y+(-r/8)*radialPower (-(5/2:ℝ)) y) := by
    funext y
    ring
  rw [he,coordinateLaplacian_add_at (hcp (-2)) (contDiffAt_const.mul (hcp (-(5/2:ℝ)))),
    coordinateLaplacian_const_mul]
  simp only [coordinateLaplacian_radialPower hx]
  have h7 : (‖x‖^2)^(-(7/2:ℝ))=(‖x‖^7)⁻¹ := by
    exact radialPower_half_nat 7 x
  norm_num [show (-(5/2:ℝ))-1=-(7/2:ℝ) by ring,Real.rpow_neg_natCast,h7]
  have hn := norm_ne_zero_iff.mpr hx
  field_simp
  ring

end NeutralAtom

end
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
namespace NeutralAtom

lemma tfScalarDensity_eq_kTF (v : ℝ) :
    Coulomb.tfScalarDensity v=kTF*(max v 0)^(3/2:ℝ) := by
  have hπ : 0<3*Real.pi^2 := by positivity
  have hcf : Coulomb.thomasFermiKineticConstant*(5/3:ℝ)=(3*Real.pi^2)^(2/3:ℝ)/2 := by
    unfold Coulomb.thomasFermiKineticConstant
    ring
  unfold Coulomb.tfScalarDensity
  rw [hcf,Real.div_rpow (le_max_right _ _) (by positivity),
    Real.div_rpow (Real.rpow_nonneg hπ.le _) (by norm_num),←Real.rpow_mul hπ.le]
  norm_num
  unfold kTF
  field_simp

lemma tfReaction_eq_scalar (v : ℝ) : tfReaction v=4*Real.pi*Coulomb.tfScalarDensity v := by
  rw [tfScalarDensity_eq_kTF]
  unfold tfReaction
  ring

end NeutralAtom

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_PropagationBarrierBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
namespace NeutralAtom

lemma WeakLaplacianGE.of_classical {f q : Position → ℝ} {U : Set Position}
    (hf : ∀ x ∈ U, ContDiffAt ℝ 2 f x) (hq : LocallyIntegrableOn q U)
    (hle : ∀ x ∈ U, q x ≤ coordinateLaplacian f x) : WeakLaplacianGE f U q := by
  intro φ hφ hc ht hp
  rw [integral_mul_coordinateLaplacian_eq (fun x hx => hf x (ht hx)) hφ hc]
  apply integral_mono (integrable_mul_test_on hq hφ.continuous hc ht)
    (integrable_mul_compact_of_continuousAt
      (fun x hx => continuousAt_coordinateLaplacian (hf x (ht hx))) hφ.continuous hc)
  intro x
  by_cases hx : x ∈ tsupport φ
  · exact mul_le_mul_of_nonneg_right (hle x (ht hx)) (hp x)
  · simp only [image_eq_zero_of_notMem_tsupport hx,mul_zero,le_refl]

lemma WeakLaplacianGE.to_nuclear_away {f q : Position → ℝ} {U : Set Position}
    (hw : WeakLaplacianGE f U q) (h0 : (0:Position) ∉ U) (Z : ℝ) :
    WeakNuclearSubsolution f Z U q := by
  intro φ hφ hc ht hp
  have hz := image_eq_zero_of_notMem_tsupport (show (0:Position) ∉ tsupport φ from fun h => h0 (ht h))
  simpa only [hz,mul_zero,neg_zero,zero_add] using hw φ hφ hc ht hp

lemma WeakNuclearSubsolution.congr_on {f g q r : Position → ℝ} {U : Set Position} {Z : ℝ}
    (hw : WeakNuclearSubsolution f Z U q) (he : ∀ x ∈ U, f x=g x) (hq : ∀ x ∈ U, q x=r x) :
    WeakNuclearSubsolution g Z U r := by
  intro φ hφ hc ht hp
  have H := hw φ hφ hc ht hp
  have hleft : (fun x => q x*φ x)=(fun x => r x*φ x) := by
    funext x
    by_cases hx : x ∈ tsupport φ
    · rw [hq x (ht hx)]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have hright : (fun x => f x*coordinateLaplacian φ x)=(fun x => g x*coordinateLaplacian φ x) := by
    funext x
    by_cases hx : x ∈ tsupport φ
    · rw [he x (ht hx)]
    · simp [coordinateLaplacian_eq_zero_of_notMem_tsupport hx]
  simpa only [hleft,hright] using H

lemma WeakNuclearSubsolution.mono_domain {f q : Position → ℝ} {U V : Set Position} {Z : ℝ}
    (hw : WeakNuclearSubsolution f Z U q) (hVU : V ⊆ U) : WeakNuclearSubsolution f Z V q :=
  fun φ hφ hc ht hp => hw φ hφ hc (ht.trans hVU) hp

lemma WeakNuclearSubsolution.of_local {f q : Position → ℝ} {U : Set Position} {Z : ℝ}
    (hf : Continuous f) (hq : LocallyIntegrable q volume)
    (hw : ∀ x ∈ U, ∃ V : Set Position, x ∈ V ∧ IsOpen V ∧
      WeakNuclearSubsolution (fun y => Z*coulombKernel y+f y) Z V q) :
    WeakNuclearSubsolution (fun x => Z*coulombKernel x+f x) Z U q := by
  apply (weakNuclearSubsolution_offset_iff hf).2
  apply WeakLaplacianGE.of_local hf.locallyIntegrable hq
  intro x hx
  obtain ⟨V,hxV,hV,hWV⟩ := hw x hx
  exact ⟨V,hxV,hV,(weakNuclearSubsolution_offset_iff hf).1 hWV⟩

lemma WeakLaplacianGE.sub_const {f q : Position → ℝ} {U : Set Position}
    (hf : Continuous f) (hw : WeakLaplacianGE f U q) (c : ℝ) :
    WeakLaplacianGE (fun x => f x-c) U q := by
  intro φ hφ hc ht hp
  have hi := integrable_mul_compact_of_continuousAt (fun x _ => hf.continuousAt)
    (contDiff_coordinateLaplacian hφ).continuous (hasCompactSupport_coordinateLaplacian hc)
  have hi' : Integrable (fun x => c*coordinateLaplacian φ x) := ((contDiff_coordinateLaplacian hφ).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_coordinateLaplacian hc)).const_mul c
  simp_rw [sub_mul]
  rw [integral_sub hi hi',integral_const_mul,integral_coordinateLaplacian hφ hc,mul_zero,sub_zero]
  exact hw φ hφ hc ht hp

lemma WeakNuclearSubsolution.sub_offset_const {f q : Position → ℝ} {U : Set Position} {Z : ℝ}
    (hf : Continuous f) (hw : WeakNuclearSubsolution (fun x => Z*coulombKernel x+f x) Z U q) (c : ℝ) :
    WeakNuclearSubsolution (fun x => Z*coulombKernel x+(f x-c)) Z U q :=
  (weakNuclearSubsolution_offset_iff (hf.sub continuous_const)).2
    (((weakNuclearSubsolution_offset_iff hf).1 hw).sub_const hf c)

end NeutralAtom

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_PropagationBarrierOffset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
namespace NeutralAtom

lemma propagationBarrierOffset_eq {B R Z : ℝ} {x : Position} (hx : R≤‖x‖) :
    Z*coulombKernel x+propagationBarrierOffset B R Z x=propagationBarrier B R x := by
  rw [propagationBarrierOffset,max_eq_right hx,propagationBarrier_eq]
  unfold coulombKernel
  ring

end NeutralAtom

end
section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
namespace NeutralAtom

def propagationRHS (r d μ p u : ℝ) : ℝ :=
  propagationCoreSource r d μ p+(if r≤d then tfReaction u else 0)

lemma propagation_old_source {bad : Prop} {r R d μ p u l : ℝ}
    (hrR : r≤R) (hR : 0<R) (hl : 0≤l)
    (hgain : ¬bad → r≤d → d<R → 4*Real.pi*μ≤tfReaction u) :
    propagationRHS R d μ (propagationStepError bad r R d μ p) (u-l/R^4)≤
      propagationRHS r d μ p u := by
  classical
  by_cases hdr : d < r
  · have hdR : d<R := hdr.trans_le hrR
    simp [propagationRHS,propagationCoreSource,propagationStepError,hdr,hdR,
      not_le_of_gt hdr,not_le_of_gt hdR]
  · have hrd : r≤d := le_of_not_gt hdr
    by_cases hdR : d<R
    · by_cases hb : bad
      · simp [propagationRHS,propagationCoreSource,propagationStepError,hdr,hdR,hrd,
          not_le_of_gt hdR,hb]
        nlinarith only [tfReaction_nonneg u]
      · have H := hgain hb hrd hdR
        simp only [propagationRHS,propagationCoreSource,propagationStepError,hb,false_and,
          ite_false,add_zero,hdR,ite_eq_left,not_le_of_gt hdR,hdr,hrd]
        nlinarith only [H]
    · have hRd : R≤d := le_of_not_gt hdR
      have H := tfReaction_monotone (show u-l/R^4≤u by
        have : 0≤l/R^4 := div_nonneg hl (pow_pos hR 4).le
        linarith only [this])
      simp only [propagationRHS,propagationCoreSource,propagationStepError,hdR,and_false,
        ite_false,add_zero,hdr,hRd,hrd,ite_eq_left]
      linarith only [H]

lemma propagation_physical_source {r R d μ p H l : ℝ} {_ : ℝ} {bad : Prop}
    (hμ : 0≤μ) (hp : 0≤p)
    (houter : R≤d → tfReaction (H-l/R^4)≤4*Real.pi*μ) :
    propagationRHS R d μ (propagationStepError bad r R d μ p) (H-l/R^4)≤4*Real.pi*μ := by
  have he := propagationStepError_nonneg (bad:=bad) (r:=r) (R:=R) (d:=d) hμ hp
  have hπ : 0<4*Real.pi := by positivity
  by_cases hdR : d<R
  · simp only [propagationRHS,propagationCoreSource,hdR,ite_eq_left,not_le_of_gt hdR,ite_false,add_zero]
    nlinarith only [he,hπ]
  · have hRd := le_of_not_gt hdR
    have H := houter hRd
    simp only [propagationRHS,propagationCoreSource,hdR,ite_false,hRd,ite_eq_left,zero_sub]
    nlinarith only [he,hπ,H]

lemma propagation_barrier_source {r R d μ p v : ℝ} {bad : Prop}
    (hRd : R≤d) (hμ : 0≤μ) (hp : 0≤p) :
    propagationRHS R d μ (propagationStepError bad r R d μ p) v≤tfReaction v := by
  have he := propagationStepError_nonneg (bad:=bad) (r:=r) (R:=R) (d:=d) hμ hp
  have hπ : 0<4*Real.pi := by positivity
  simp only [propagationRHS,propagationCoreSource,hRd,ite_eq_left,not_lt_of_ge hRd,ite_false,zero_sub]
  nlinarith only [he,hπ]

lemma propagationRHS_eq {r Z : ℝ} (f μ p : Position → ℝ) (x : Position) :
    propagationRHS r ‖x‖ (μ x) (p x) (Z*coulombKernel x+f x)=
      propagationCoreSource r ‖x‖ (μ x) (p x)+
        cutoffReaction r (fun y => Z*coulombKernel y+f y) x := by
  simp [propagationRHS,cutoffReaction,Set.indicator]

end NeutralAtom

end
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_RadialMaxSplice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators Topology Classical
noncomputable section
namespace NeutralAtom

lemma radialMaxSplice_outer {α β c e : ℝ} {f g : Position → ℝ}
    (hαe : α≤e) (hβc : β ≤ c)
    (hupp : ∀ x,e≤‖x‖ → ‖x‖ ≤ c → f x≤g x)
    {x : Position} (hx : e<‖x‖) : radialMaxSplice α β f g x=g x := by
  unfold radialMaxSplice
  have hn : ¬‖x‖<α := not_lt_of_ge (hαe.trans hx.le)
  rw [ite_eq_right hn]
  split_ifs with hβ
  · exact max_eq_right (hupp x hx.le (hβ.le.trans hβc))
  · rfl

lemma continuous_radialMaxSplice {α β a b c e : ℝ} {f g : Position → ℝ}
    (hbα : b<α) (hαa : α<a) (hae : a≤e) (heβ : e<β) (hβc : β < c)
    (hf : Continuous f) (hg : Continuous g)
    (hlow : ∀ x,b≤‖x‖ → ‖x‖≤a → g x≤f x)
    (hupp : ∀ x,e≤‖x‖ → ‖x‖ ≤ c → f x≤g x) :
    Continuous (radialMaxSplice α β f g) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hxa : ‖x‖<a
  · apply hf.continuousAt.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hxa] with y hy
    exact radialMaxSplice_inner hbα.le (hae.trans heβ.le) hlow hy
  · by_cases hex : e<‖x‖
    · apply hg.continuousAt.congr_of_eventuallyEq
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hex] with y hy
      exact radialMaxSplice_outer (hαa.le.trans hae) hβc.le hupp hy
    · have hxb : b<‖x‖ := (hbα.trans hαa).trans_le (le_of_not_gt hxa)
      have hxc : ‖x‖ < c := (le_of_not_gt hex).trans_lt (heβ.trans hβc)
      apply (hf.max hg).continuousAt.congr_of_eventuallyEq
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hxb,
        (isOpen_lt continuous_norm continuous_const).mem_nhds hxc] with y hy hy'
      exact radialMaxSplice_middle hαa.le heβ.le hlow hupp ⟨hy,hy'⟩

end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

lemma propagationPairOffset_continuous (bad : Prop) (R l1 l2 : ℝ) {u H : Position → ℝ}
    (hu : Continuous u) (hH : Continuous H) : Continuous (propagationPairOffset bad R l1 l2 u H) := by
  change Continuous (fun x => if bad then u x-l1/R^4 else max (u x-l1/R^4) (H x-l2/R^4))
  by_cases hb : bad
  · simp only [ite_eq_left hb]
    exact hu.sub continuous_const
  · simp only [ite_eq_right hb]
    exact (hu.sub continuous_const).max (hH.sub continuous_const)

lemma propagation_old_lower_overlap {B r R Z l1 : ℝ} (hB : 0<B) (hr : 0 < r)
    (hR : R=2*r) (hl1 : l1≤propagationGamma B) {u : Position → ℝ} {x : Position}
    (hx : R≤‖x‖) (hx' : ‖x‖≤(11/10)*R)
    (hu : propagationBarrier B r x≤Z*coulombKernel x+u x) :
    propagationBarrierOffset B R Z x≤u x-l1/R^4 := by
  have hRp : 0<R := by rw [hR]; positivity
  have H := propagationBarrier_gap hB hr (by simpa only [hR] using hx) (by simpa only [hR] using hx')
  rw [←hR] at H
  have Hl := div_le_div_of_nonneg_right hl1 (pow_pos hRp 4).le
  have he := propagationBarrierOffset_eq (B:=B) (Z:=Z) hx
  linarith only [hu,H,Hl,he]

lemma propagation_splice_overlaps {bad : Prop} {B C r R Z L l1 l2 : ℝ}
    {u H : Position → ℝ} (hB : 0<B) (hr : 0 < r) (hR : R=2*r) (hL : 2<L)
    (hl2 : 0≤l2) (hl21 : l2≤l1) (hlγ : l1≤propagationGamma B) (hCL : C≤l2*L^4)
    (hu : ∀ x,r≤‖x‖ → propagationBarrier B r x≤Z*coulombKernel x+u x ∧
      Z*coulombKernel x+u x≤C/‖x‖^4)
    (hH : ¬bad → ∀ x,r≤‖x‖ → ‖x‖≤2*L*R → Z*coulombKernel x+H x≤C/‖x‖^4) :
    (∀ x,(26/25)*R≤‖x‖ → ‖x‖≤(27/25)*R →
      propagationBarrierOffset B R Z x≤propagationPairOffset bad R l1 l2 u H x) ∧
    (∀ x,L*R≤‖x‖ → ‖x‖≤2*L*R →
      propagationPairOffset bad R l1 l2 u H x≤propagationBarrierOffset B R Z x) := by
  have hRp : 0<R := by rw [hR]; positivity
  constructor
  · intro x hx hx'
    have hRx : R≤‖x‖ := by linarith only [hx,hRp]
    have hrx : r≤‖x‖ := by rw [hR] at hRx; linarith only [hRx,hr]
    exact (propagation_old_lower_overlap hB hr hR hlγ hRx
      (by linarith only [hx',hRp]) (hu x hrx).1).trans (le_propagationPairOffset bad R l1 l2 u H x)
  · intro x hx hx'
    have hRx : R≤‖x‖ := by nlinarith only [hx,mul_pos (show 0<L-1 by linarith) hRp]
    have hrx : r≤‖x‖ := by rw [hR] at hRx; linarith only [hRx,hr]
    have hb := propagationBarrier_positive hB hRp hRx
    have he := propagationBarrierOffset_eq (B:=B) (Z:=Z) hRx
    have hC1 : C≤l1*L^4 := hCL.trans (mul_le_mul_of_nonneg_right hl21 (pow_nonneg (by linarith) _))
    have hv1 := propagation_shift_cap_nonpos hRp (by linarith : 0<L) (hl2.trans hl21) hx hC1 (hu x hrx).2
    have hv1' : u x-l1/R^4≤propagationBarrierOffset B R Z x := by linarith only [hv1,hb,he]
    unfold propagationPairOffset
    split_ifs with hbad
    · exact hv1'
    · have hv2 := propagation_shift_cap_nonpos hRp (by linarith : 0<L) hl2 hx hCL (hH hbad x hrx hx')
      exact max_le hv1' (by linarith only [hv2,hb,he])

lemma propagationNextOffset_continuous {bad : Prop} {B C r R Z L l1 l2 : ℝ}
    {u H : Position → ℝ} (hB : 0<B) (hr : 0 < r) (hR : R=2*r) (hL : 2<L)
    (hl2 : 0≤l2) (hl21 : l2≤l1) (hlγ : l1≤propagationGamma B) (hCL : C≤l2*L^4)
    (huc : Continuous u) (hHc : Continuous H)
    (hu : ∀ x,r≤‖x‖ → propagationBarrier B r x≤Z*coulombKernel x+u x ∧
      Z*coulombKernel x+u x≤C/‖x‖^4)
    (hH : ¬bad → ∀ x,r≤‖x‖ → ‖x‖≤2*L*R → Z*coulombKernel x+H x≤C/‖x‖^4) :
    Continuous (propagationNextOffset bad B R Z L l1 l2 u H) := by
  have hRp : 0<R := by rw [hR]; positivity
  obtain ⟨hlow,hupp⟩ := propagation_splice_overlaps hB hr hR hL hl2 hl21 hlγ hCL hu hH
  apply continuous_radialMaxSplice
    (b:=(26/25)*R) (a:=(27/25)*R) (e:=L*R) (c:=2*L*R)
  · linarith only [hRp]
  · linarith only [hRp]
  · nlinarith only [mul_pos (show 0<L-27/25 by linarith) hRp]
  · nlinarith only [mul_pos (show 0<L by linarith) hRp]
  · nlinarith only [mul_pos (show 0<L by linarith) hRp]
  · exact propagationPairOffset_continuous bad R l1 l2 huc hHc
  · exact propagationBarrierOffset_continuous B Z hRp
  · exact hlow
  · exact hupp

end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_PropagationMaximum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

def propagationCandidateSources (r R Z : ℝ) (u μ p b : Position → ℝ) : Fin 3 → Position → ℝ :=
  ![fun x => propagationRHS r ‖x‖ (μ x) (p x) (Z*coulombKernel x+u x),
    fun x => 4*Real.pi*μ x,cutoffReaction R (fun x => Z*coulombKernel x+b x)]

end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_PropagationRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

lemma propagationRHS_locallyIntegrable {r Z : ℝ} {u μ p : Position → ℝ} (hr : 0 < r)
    (hu : Continuous u) (hμ : Measurable μ) (hp : Measurable p)
    (hbμ : ∀ D : ℝ,∃ M : ℝ,∀ x∈Metric.closedBall 0 D,|μ x|≤M)
    (hbp : ∀ D : ℝ,∃ P : ℝ,∀ x∈Metric.closedBall 0 D,|p x|≤P) :
    LocallyIntegrable (fun x => propagationRHS r ‖x‖ (μ x) (p x) (Z*coulombKernel x+u x)) volume := by
  have H : LocallyIntegrable (fun x => propagationCoreSource r ‖x‖ (μ x) (p x)+
      cutoffReaction r (fun y => Z*coulombKernel y+u y) x) volume := (locallyIntegrable_of_ball_bounds (propagationCoreSource_measurable (r:=r) hμ hp)
    (propagationCoreSource_ball_bounds (r:=r) hbμ hbp)).add (cutoffReaction_offset_locallyIntegrable (Z:=Z) hr hu)
  simpa only [propagationRHS_eq] using H

end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

theorem WeakNuclearSubsolution.radialMaxSplice {α β a b c e Z : ℝ}
    {f g : Position → ℝ} {q : Position → ℝ → ℝ}
    (hbα : b<α) (hαa : α<a) (hae : a≤e) (heβ : e<β) (hβc : β < c)
    (hf : Continuous f) (hg : Continuous g)
    (hlow : ∀ x,b≤‖x‖ → ‖x‖≤a → g x≤f x)
    (hupp : ∀ x,e≤‖x‖ → ‖x‖ ≤ c → f x≤g x)
    (hqi : LocallyIntegrable (fun x => q x (radialMaxSplice α β f g x)) volume)
    (hinner : WeakNuclearSubsolution (fun x => Z*coulombKernel x+f x) Z {x | ‖x‖<a} (fun x => q x (f x)))
    (hmiddle : WeakNuclearSubsolution (fun x => Z*coulombKernel x+max (f x) (g x)) Z
      {x | b<‖x‖ ∧ ‖x‖ < c} (fun x => q x (max (f x) (g x))))
    (houter : WeakNuclearSubsolution (fun x => Z*coulombKernel x+g x) Z {x | e<‖x‖} (fun x => q x (g x))) :
    WeakNuclearSubsolution (fun x => Z*coulombKernel x+radialMaxSplice α β f g x) Z univ
      (fun x => q x (radialMaxSplice α β f g x)) := by
  apply WeakNuclearSubsolution.of_local
    (continuous_radialMaxSplice hbα hαa hae heβ hβc hf hg hlow hupp) hqi
  intro x hx
  by_cases hxa : ‖x‖<a
  · refine ⟨{y | ‖y‖<a},hxa,isOpen_lt continuous_norm continuous_const,?_⟩
    apply hinner.congr_on
    · intro y hy
      rw [radialMaxSplice_inner hbα.le (hae.trans heβ.le) hlow hy]
    · intro y hy
      rw [radialMaxSplice_inner hbα.le (hae.trans heβ.le) hlow hy]
  · by_cases hex : e<‖x‖
    · refine ⟨{y | e<‖y‖},hex,isOpen_lt continuous_const continuous_norm,?_⟩
      apply houter.congr_on
      · intro y hy
        rw [radialMaxSplice_outer (hαa.le.trans hae) hβc.le hupp hy]
      · intro y hy
        rw [radialMaxSplice_outer (hαa.le.trans hae) hβc.le hupp hy]
    · have hxb : b<‖x‖ := (hbα.trans hαa).trans_le (le_of_not_gt hxa)
      have hxc : ‖x‖ < c := (le_of_not_gt hex).trans_lt (heβ.trans hβc)
      refine ⟨{y | b<‖y‖ ∧ ‖y‖ < c},⟨hxb,hxc⟩,
        (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const),?_⟩
      apply hmiddle.congr_on
      · intro y hy
        rw [radialMaxSplice_middle hαa.le heβ.le hlow hupp hy]
      · intro y hy
        rw [radialMaxSplice_middle hαa.le heβ.le hlow hupp hy]

end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

structure PropagationStepHypotheses (bad : Prop) (B C r R Z L l1 l2 e ξ hl hh : ℝ)
    (u H μ p : Position → ℝ) : Prop where
  B_pos : 0<B
  r_pos : 0 < r
  R_eq : R=2*r
  L_large : 2<L
  l2_nonneg : 0≤l2
  l2_le_l1 : l2≤l1
  l1_le_gamma : l1≤propagationGamma B
  cap_large : B≤C
  upper_overlap : C≤l2*L^4
  e_pos : 0<e
  xi_nonneg : 0≤ξ
  xi_lt_l2 : ξ<l2
  gain_gap : 16*ξ+2*e<l1-l2
  height_lower : hl≤(7/8:ℝ)*B-2*e*(2*L)^4
  height_upper : C≤hh
  u_cont : Continuous u
  H_cont : Continuous H
  mu_nonneg : ∀ x,0≤μ x
  p_nonneg : ∀ x,0≤p x
  mu_measurable : Measurable μ
  p_measurable : Measurable p
  mu_bounds : ∀ D : ℝ,∃ M : ℝ,∀ x∈Metric.closedBall 0 D,|μ x|≤M
  p_bounds : ∀ D : ℝ,∃ P : ℝ,∀ x∈Metric.closedBall 0 D,|p x|≤P
  u_weak : WeakNuclearSubsolution (fun x => Z*coulombKernel x+u x) Z univ
    (fun x => propagationRHS r ‖x‖ (μ x) (p x) (Z*coulombKernel x+u x))
  H_weak : WeakNuclearSubsolution (fun x => Z*coulombKernel x+H x) Z univ (fun x => 4*Real.pi*μ x)
  barrier_small : 4*Real.pi*kTF*Real.sqrt B≤19/2
  old_caps : ∀ x,r≤‖x‖ → propagationBarrier B r x≤Z*coulombKernel x+u x ∧
    Z*coulombKernel x+u x≤C/‖x‖^4
  physical_cap : ¬bad → ∀ x,r≤‖x‖ → ‖x‖≤2*L*R → Z*coulombKernel x+H x≤C/‖x‖^4
  inverse : ¬bad → ∀ x,r≤‖x‖ → ‖x‖≤2*L*R → ∀ h∈Icc hl hh,
    (‖x‖^6*μ x≤Coulomb.tfScalarDensity h → ‖x‖^4*(Z*coulombKernel x+H x)≤h+ξ) ∧
    (Coulomb.tfScalarDensity h≤‖x‖^6*μ x → h-ξ≤‖x‖^4*(Z*coulombKernel x+H x))

namespace PropagationStepHypotheses
variable {bad : Prop} {B C r R Z L l1 l2 e ξ hl hh : ℝ} {u H μ p : Position → ℝ}
variable (d : PropagationStepHypotheses bad B C r R Z L l1 l2 e ξ hl hh u H μ p)
include d

lemma R_pos : 0<R := by rw [d.R_eq]; exact mul_pos (by norm_num) d.r_pos
lemma L_pos : 0<L := lt_trans (by norm_num) d.L_large
lemma old_le_new : r≤R := by rw [d.R_eq]; linarith only [d.r_pos]

lemma next_continuous : Continuous (propagationNextOffset bad B R Z L l1 l2 u H) :=
  propagationNextOffset_continuous d.B_pos d.r_pos d.R_eq d.L_large d.l2_nonneg d.l2_le_l1
    d.l1_le_gamma d.upper_overlap d.u_cont d.H_cont d.old_caps d.physical_cap

lemma step_error_measurable : Measurable (fun x => propagationStepError bad r R ‖x‖ (μ x) (p x)) :=
  propagationStepError_measurable bad r R d.mu_measurable d.p_measurable
lemma step_error_bounds : ∀ D : ℝ,∃ K : ℝ,∀ x∈Metric.closedBall 0 D,
    |propagationStepError bad r R ‖x‖ (μ x) (p x)|≤K :=
  propagationStepError_ball_bounds d.mu_bounds d.p_bounds

end PropagationStepHypotheses
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Variational_WeakAdd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

lemma WeakLaplacianGE.add {f g q r : Position → ℝ} {U : Set Position}
    (hf : Continuous f) (hg : Continuous g)
    (hq : LocallyIntegrable q volume) (hr : LocallyIntegrable r volume)
    (hwf : WeakLaplacianGE f U q) (hwg : WeakLaplacianGE g U r) :
    WeakLaplacianGE (fun x => f x+g x) U (fun x => q x+r x) := by
  intro φ hφ hc ht hp
  have hL := (contDiff_coordinateLaplacian hφ).continuous
  have hLc := hasCompactSupport_coordinateLaplacian hc
  have hif := integrable_mul_compact_of_continuousAt (fun x _ => hf.continuousAt) hL hLc
  have hig := integrable_mul_compact_of_continuousAt (fun x _ => hg.continuousAt) hL hLc
  have hiq := integrable_mul_test_on (hq.locallyIntegrableOn U) hφ.continuous hc ht
  have hir := integrable_mul_test_on (hr.locallyIntegrableOn U) hφ.continuous hc ht
  simp_rw [add_mul]
  rw [integral_add hiq hir,integral_add hif hig]
  exact add_le_add (hwf φ hφ hc ht hp) (hwg φ hφ hc ht hp)

lemma WeakLaplacianGE.quadratic (a : ℝ) :
    WeakLaplacianGE (fun x : Position => a*‖x‖^2) univ (fun _ => 6*a) := by
  apply WeakLaplacianGE.of_classical
    (fun _ _ => (contDiff_const.mul (contDiff_norm_sq ℝ)).contDiffAt)
    (continuous_const.locallyIntegrable.locallyIntegrableOn univ)
  intro x hx
  simpa only [sub_zero] using (coordinateLaplacian_quadratic (0:Position) x a).ge

lemma WeakLaplacianGE.zero : WeakLaplacianGE (fun _ : Position => (0:ℝ)) univ (fun _ => 0) := by
  intro φ hφ hc ht hp
  simp

end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_InitializationBranch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

lemma initialPropagationOffset_continuous (bad : Prop) (Z r a : ℝ) {H : Position → ℝ}
    (hc : Continuous H) : Continuous (initialPropagationOffset bad Z r a H) := by
  unfold initialPropagationOffset
  by_cases hb : bad
  · simp only [ite_eq_left hb]
    fun_prop
  · simp only [ite_eq_right hb]
    exact (hc.sub continuous_const).add (continuous_const.mul (continuous_norm.pow 2))

lemma initialPropagationOffset_base_weak {bad : Prop} {Z r a : ℝ} {H μ : Position → ℝ}
    (hH : Continuous H) (hμ : LocallyIntegrable μ volume)
    (hw : WeakNuclearSubsolution (fun x => Z*coulombKernel x+H x) Z univ (fun x => 4*Real.pi*μ x)) :
    WeakNuclearSubsolution (fun x => Z*coulombKernel x+initialPropagationOffset bad Z r a H x) Z univ
      (fun x => 4*Real.pi*(if bad then 0 else μ x)+6*a) := by
  apply (weakNuclearSubsolution_offset_iff (initialPropagationOffset_continuous bad Z r a hH)).2
  have hc : Continuous (fun x => if bad then (0:ℝ) else H x) := by
    by_cases hb : bad <;> simp only [hb,ite_true,ite_false]
    · exact continuous_const
    · exact hH
  have hq : LocallyIntegrable (fun x => 4*Real.pi*(if bad then 0 else μ x)) volume := by
    by_cases hb : bad
    · simp only [ite_eq_left hb,mul_zero]
      exact continuous_const.locallyIntegrable
    · simp only [ite_eq_right hb]
      exact hμ.smul (4*Real.pi)
  have hb : WeakLaplacianGE (fun x => if bad then (0:ℝ) else H x) univ
      (fun x => 4*Real.pi*(if bad then 0 else μ x)) := by
    by_cases hb : bad
    · simpa only [ite_eq_left hb,mul_zero] using WeakLaplacianGE.zero
    · simpa only [ite_eq_right hb] using (weakNuclearSubsolution_offset_iff hH).1 hw
  exact WeakLaplacianGE.add (hc.sub continuous_const)
    (continuous_const.mul (continuous_norm.pow 2)) hq continuous_const.locallyIntegrable
    (hb.sub_const hc ((7/10:ℝ)*Z/r)) (WeakLaplacianGE.quadratic a)

lemma initialPropagationOffset_upper {bad : Prop} {Z r a : ℝ} {H : Position → ℝ}
    (hZ : 0≤Z) (hr : 0 < r) (ha : 0≤a) (hquad : 4*a*r^2≤(1/20:ℝ)*Z/r)
    (hH : ∀ x,H x≤0) {x : Position} (hx : r≤‖x‖) (hx' : ‖x‖≤2*r) :
    Z*coulombKernel x+initialPropagationOffset bad Z r a H x≤2*Z/r := by
  have hd := hr.trans_le hx
  have hpot : (if bad then (0:ℝ) else H x)≤0 := by split_ifs; rfl; exact hH x
  have hker : Z*coulombKernel x≤Z/r := by
    change Z*‖x‖⁻¹≤Z/r
    rw [←div_eq_mul_inv]
    exact div_le_div_of_nonneg_left hZ hr hx
  have hsq := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg x) hx' 2) ha
  unfold initialPropagationOffset
  have hZr : 0≤Z/r := div_nonneg hZ hr.le
  simp only [mul_div_assoc] at hquad ⊢
  nlinarith only [hpot,hker,hsq,hquad,hZr]

lemma initialPropagationOffset_weak {bad : Prop} {Z r a : ℝ} {H μ : Position → ℝ}
    (hZ : 0≤Z) (hr : 0 < r) (ha : 0≤a) (hquad : 4*a*r^2≤(1/20:ℝ)*Z/r)
    (hreaction : tfReaction (2*Z/r)≤6*a)
    (hH : Continuous H) (hHnonpos : ∀ x,H x≤0)
    (hμ : Measurable μ) (hμnonneg : ∀ x,0≤μ x)
    (hbμ : ∀ D : ℝ,∃ C : ℝ,∀ x∈Metric.closedBall 0 D,|μ x|≤C)
    (hw : WeakNuclearSubsolution (fun x => Z*coulombKernel x+H x) Z univ (fun x => 4*Real.pi*μ x)) :
    WeakNuclearSubsolution (fun x => Z*coulombKernel x+initialPropagationOffset bad Z r a H x) Z
      {x | ‖x‖<2*r}
      (fun x => propagationRHS r ‖x‖ (μ x) (initialPropagationError bad r μ x)
        (Z*coulombKernel x+initialPropagationOffset bad Z r a H x)) := by
  have hc := initialPropagationOffset_continuous bad Z r a hH
  have hμi := locallyIntegrable_of_ball_bounds hμ hbμ
  have Hbase := (initialPropagationOffset_base_weak (bad:=bad) (r:=r) (a:=a) hH hμi hw).mono_domain
    (subset_univ {x : Position | ‖x‖<2*r})
  have hqi : LocallyIntegrable (fun x => 4*Real.pi*(if bad then 0 else μ x)+6*a) volume := by
    by_cases hb : bad
    · simpa only [ite_eq_left hb,mul_zero,zero_add] using (continuous_const.locallyIntegrable : LocallyIntegrable (fun _ : Position => 6*a) volume)
    · simp only [ite_eq_right hb]
      have hscaled : LocallyIntegrable (fun x => 4*Real.pi*μ x) volume := hμi.smul (4*Real.pi)
      exact hscaled.add (continuous_const.locallyIntegrable : LocallyIntegrable (fun _ : Position => 6*a) volume)
  apply (weakNuclearSubsolution_offset_iff hc).2
  apply ((weakNuclearSubsolution_offset_iff hc).1 Hbase).mono_source_on hqi
    (propagationRHS_locallyIntegrable hr hc hμ (initialPropagationError_measurable bad r hμ)
      hbμ (initialPropagationError_ball_bounds hbμ))
  exact Eventually.of_forall (fun x hx => by
    have hcore := initial_core_source bad r μ x (hμnonneg x)
    unfold propagationRHS
    by_cases hxr : r≤‖x‖
    · rw [ite_eq_left hxr]
      have hreact := (tfReaction_monotone (initialPropagationOffset_upper (bad:=bad) hZ hr ha hquad hHnonpos hxr
        (le_of_lt hx))).trans hreaction
      exact add_le_add hcore hreact
    · rw [ite_eq_right hxr,add_zero]
      linarith only [hcore,ha])

end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

lemma initialPropagationOffset_lower {bad : Prop} {Z r a : ℝ} {H : Position → ℝ}
    (hZ : 0 ≤ Z) (hr : 0 < r) (ha : 0 ≤ a)
    (hH : ¬bad → ∀ x,r ≤ ‖x‖ → ‖x‖ ≤ 2*r → -(1/10:ℝ)*Z/r ≤ H x)
    {x : Position} (hx : r ≤ ‖x‖) (hx' : ‖x‖ ≤ (53/50)*r) :
    (7/50:ℝ)*(Z/r) ≤ Z*coulombKernel x+initialPropagationOffset bad Z r a H x := by
  have hd := hr.trans_le hx
  have hpot : -(1/10:ℝ)*(Z/r) ≤ if bad then (0:ℝ) else H x := by
    split_ifs with hb
    · have hh : 0 ≤ Z/r := div_nonneg hZ hr.le
      linarith only [hh]
    · simpa only [mul_div_assoc] using hH hb x hx (by linarith only [hx',hr])
  have hker : (50/53:ℝ)*(Z/r) ≤ Z*coulombKernel x := by
    have hh := div_le_div_of_nonneg_left hZ hd hx'
    change Z/((53/50)*r) ≤ Z/‖x‖ at hh
    change (50/53:ℝ)*(Z/r) ≤ Z*‖x‖⁻¹
    convert hh using 1 <;> field_simp
  have hquad : 0 ≤ a*‖x‖^2 := mul_nonneg ha (sq_nonneg _)
  have hZr := div_nonneg hZ hr.le
  unfold initialPropagationOffset
  simp only [mul_div_assoc]
  linarith only [hpot,hker,hquad,hZr]

lemma initialPropagationOffset_nonpos {bad : Prop} {Z r a : ℝ} {H : Position → ℝ}
    (hZ : 0 ≤ Z) (hr : 0 < r) (ha : 0 ≤ a) (hquad : 4*a*r^2 ≤ (1/20:ℝ)*Z/r)
    (hH : ∀ x,H x ≤ 0) {x : Position} (hx : (19/10)*r ≤ ‖x‖) (hx' : ‖x‖ ≤ 2*r) :
    Z*coulombKernel x+initialPropagationOffset bad Z r a H x ≤ 0 := by
  have hd : 0<‖x‖ := (by positivity : (0:ℝ)<(19/10)*r).trans_le hx
  have hpot : (if bad then (0:ℝ) else H x) ≤ 0 := by split_ifs; rfl; exact hH x
  have hker : Z*coulombKernel x ≤ (10/19:ℝ)*(Z/r) := by
    have hh := div_le_div_of_nonneg_left hZ (by positivity : (0:ℝ)<(19/10)*r) hx
    change Z/‖x‖ ≤ Z/((19/10)*r) at hh
    change Z*‖x‖⁻¹ ≤ (10/19:ℝ)*(Z/r)
    convert hh using 1 <;> field_simp
  have hsq := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg x) hx' 2) ha
  have hZr := div_nonneg hZ hr.le
  unfold initialPropagationOffset
  simp only [mul_div_assoc] at hquad ⊢
  nlinarith only [hpot,hker,hsq,hquad,hZr]

lemma initialPropagationOffset_low_overlap {bad : Prop} {B Z r a : ℝ} {H : Position → ℝ}
    (hB : 0<B) (hZ : 0 ≤ Z) (hr : 0 < r) (ha : 0 ≤ a) (hBZ : B ≤ (1/10:ℝ)*Z*r^3)
    (hH : ¬bad → ∀ x,r ≤ ‖x‖ → ‖x‖ ≤ 2*r → -(1/10:ℝ)*Z/r ≤ H x)
    {x : Position} (hx : r ≤ ‖x‖) (hx' : ‖x‖ ≤ (53/50)*r) :
    propagationBarrierOffset B r Z x ≤ initialPropagationOffset bad Z r a H x := by
  have hbar := (propagationBarrier_two_sided hB.le hr hx).2
  have hh : B/‖x‖^4 ≤ B/r^4 := div_le_div_of_nonneg_left hB.le (pow_pos hr 4)
    (pow_le_pow_left₀ hr.le hx 4)
  have hBr : B/r^4 ≤ (1/10:ℝ)*(Z/r) := by
    apply (div_le_iff₀ (pow_pos hr 4)).mpr
    calc
      B ≤ (1/10:ℝ)*Z*r^3 := hBZ
      _ = (1/10:ℝ)*(Z/r)*r^4 := by field_simp
  have hlow := initialPropagationOffset_lower hZ hr ha hH hx hx'
  have hZr := div_nonneg hZ hr.le
  have he := propagationBarrierOffset_eq (B:=B) (Z:=Z) hx
  linarith only [hbar,hh,hBr,hlow,hZr,he]

lemma initialPropagationOffset_high_overlap {bad : Prop} {B Z r a : ℝ} {H : Position → ℝ}
    (hB : 0<B) (hZ : 0 ≤ Z) (hr : 0 < r) (ha : 0 ≤ a) (hquad : 4*a*r^2 ≤ (1/20:ℝ)*Z/r)
    (hH : ∀ x,H x ≤ 0) {x : Position} (hx : (19/10)*r ≤ ‖x‖) (hx' : ‖x‖ ≤ 2*r) :
    initialPropagationOffset bad Z r a H x ≤ propagationBarrierOffset B r Z x := by
  have hxr : r ≤ ‖x‖ := by linarith only [hx,hr]
  have hp := propagationBarrier_positive hB hr hxr
  have hn := initialPropagationOffset_nonpos (bad:=bad) hZ hr ha hquad hH hx hx'
  have he := propagationBarrierOffset_eq (B:=B) (Z:=Z) hxr
  linarith only [hp,hn,he]

lemma initialNextOffset_continuous {bad : Prop} {B Z r a : ℝ} {H : Position → ℝ}
    (hB : 0<B) (hZ : 0 ≤ Z) (hr : 0 < r) (ha : 0 ≤ a) (hBZ : B ≤ (1/10:ℝ)*Z*r^3)
    (hquad : 4*a*r^2 ≤ (1/20:ℝ)*Z/r) (hH : Continuous H) (hHnonpos : ∀ x,H x ≤ 0)
    (hHlow : ¬bad → ∀ x,r ≤ ‖x‖ → ‖x‖ ≤ 2*r → -(1/10:ℝ)*Z/r ≤ H x) :
    Continuous (initialNextOffset bad B Z r a H) := by
  apply continuous_radialMaxSplice (a:=(53/50)*r) (b:=r) (e:=(19/10)*r) (c:=2*r)
  · linarith only [hr]
  · linarith only [hr]
  · linarith only [hr]
  · linarith only [hr]
  · linarith only [hr]
  · exact initialPropagationOffset_continuous bad Z r a hH
  · exact propagationBarrierOffset_continuous B Z hr
  · exact fun x hx hx' => initialPropagationOffset_low_overlap hB hZ hr ha hBZ hHlow hx hx'
  · exact fun x hx hx' => initialPropagationOffset_high_overlap hB hZ hr ha hquad hHnonpos hx hx'

end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_PropagationAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
noncomputable section
namespace NeutralAtom
section Average
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [MeasurableSpace Ω] in
lemma cutoffReaction_offset_uniform_bound {a Z : ℝ} (ha : 0<a) {f : Ω → Position → ℝ}
    (hb : ∀ R : ℝ, ∃ C : ℝ, ∀ o x, x ∈ Metric.closedBall 0 R → |f o x| ≤ C) :
    ∀ R : ℝ, ∃ C : ℝ, ∀ o x, x ∈ Metric.closedBall 0 R →
      |cutoffReaction a (fun y => Z*coulombKernel y+f o y) x| ≤ C := by
  intro R
  obtain ⟨D,hD⟩ := hb R
  refine ⟨tfReaction (|Z|/a+D),?_⟩
  intro o x hx
  by_cases haX : a ≤ ‖x‖
  · have hn : 0 < ‖x‖ := ha.trans_le haX
    have hZ : Z*coulombKernel x ≤ |Z|/a := by
      unfold coulombKernel
      calc
        Z*‖x‖⁻¹ ≤ |Z| *‖x‖⁻¹ := mul_le_mul_of_nonneg_right (le_abs_self _) (inv_nonneg.mpr hn.le)
        _ ≤ |Z| *a⁻¹ := mul_le_mul_of_nonneg_left (inv_anti₀ ha haX) (abs_nonneg _)
        _ = |Z|/a := by rw [div_eq_mul_inv]
    have h := tfReaction_monotone (show Z*coulombKernel x+f o x ≤ |Z|/a+D by
      have H : f o x ≤ D := (le_abs_self _).trans (hD o x hx)
      linarith)
    simpa [cutoffReaction, haX, abs_of_nonneg (tfReaction_nonneg _)] using h
  · simpa [cutoffReaction, haX] using tfReaction_nonneg (|Z|/a+D)

lemma cutoffReaction_offset_joint_measurable {a Z : ℝ} {f : Ω → Position → ℝ}
    (hm : Measurable (Function.uncurry f)) :
    Measurable (fun z : Ω × Position => cutoffReaction a (fun y => Z*coulombKernel y+f z.1 y) z.2) := by
  have h : Measurable (fun z : Ω × Position => tfReaction (Z*coulombKernel z.2+f z.1 z.2)) :=
    tfReaction_continuous.measurable.comp ((measurable_const.mul
    (measurable_coulombKernel.comp measurable_snd)).add hm)
  exact h.ite ((isClosed_le continuous_const continuous_norm).measurableSet.preimage measurable_snd)
    measurable_const

lemma cutoffReaction_average_le {a Z : ℝ} {f : Ω → Position → ℝ}
    (hm : Measurable (Function.uncurry f))
    (hb : ∀ R : ℝ, ∃ C : ℝ, ∀ o x, x ∈ Metric.closedBall 0 R → |f o x| ≤ C)
    (x : Position) :
    cutoffReaction a (fun y => Z*coulombKernel y+∫ o, f o y ∂μ) x ≤
      ∫ o, cutoffReaction a (fun y => Z*coulombKernel y+f o y) x ∂μ := by
  by_cases haX : a ≤ ‖x‖
  · simp only [cutoffReaction, Set.indicator, Set.mem_ofPred_eq, haX, ↓reduceIte]
    have hi := integrable_section_of_ball_bounds (μ:=μ) hm hb x
    have hi' : Integrable (fun o => Z*coulombKernel x+f o x) μ :=
      (integrable_const (Z*coulombKernel x)).add hi
    have hpow : Integrable (fun o => (max (Z*coulombKernel x+f o x) 0)^(3/2:ℝ)) μ := by
      obtain ⟨C,hC⟩ := hb ‖x‖
      have hB : 0≤|Z*coulombKernel x|+max C 0 := add_nonneg (abs_nonneg _) (le_max_right _ _)
      apply (integrable_const ((|Z*coulombKernel x|+max C 0)^(3/2:ℝ))).mono'
        ((Real.continuous_rpow_const (by norm_num : (0:ℝ)≤3/2)).measurable.comp
          (((measurable_const.add (hm.comp (measurable_id.prodMk measurable_const))).max measurable_const))).aestronglyMeasurable
      filter_upwards [] with o
      change ‖(max (Z*coulombKernel x+f o x) 0)^(3/2:ℝ)‖ ≤ _
      rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (le_max_right _ _) _)]
      apply Real.rpow_le_rpow (le_max_right _ _) _ (by norm_num)
      apply max_le _ hB
      have H := hC o x (by simp)
      linarith [le_abs_self (Z*coulombKernel x),le_abs_self (f o x), le_max_left C 0]
    have H := tfReaction_integral_le hi' hpow
    simpa [integral_add (integrable_const _) hi] using H
  · simp [cutoffReaction,haX]

end Average
end NeutralAtom

end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_PropagationStepWeak
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom
namespace PropagationStepHypotheses
variable {bad : Prop} {B C r R Z L l1 l2 e ξ hl hh : ℝ} {u H μ p : Position → ℝ}
variable (d : PropagationStepHypotheses bad B C r R Z L l1 l2 e ξ hl hh u H μ p)
include d

lemma lower_pair {x : Position} (hx : R≤‖x‖) (hx' : ‖x‖≤(11/10)*R) :
    propagationBarrier B R x≤Z*coulombKernel x+propagationPairOffset bad R l1 l2 u H x := by
  have Hold := propagation_old_lower_overlap d.B_pos d.r_pos d.R_eq d.l1_le_gamma hx hx'
    (d.old_caps x (d.old_le_new.trans hx)).1
  have H' := Hold.trans (le_propagationPairOffset bad R l1 l2 u H x)
  have he := propagationBarrierOffset_eq (B:=B) (Z:=Z) hx
  linarith only [H',he]

end PropagationStepHypotheses
end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom
namespace PropagationStepHypotheses
variable {bad : Prop} {B C r R Z L l1 l2 e ξ hl hh : ℝ} {u H μ p : Position → ℝ}
variable (d : PropagationStepHypotheses bad B C r R Z L l1 l2 e ξ hl hh u H μ p)
include d

lemma pair_cap {x : Position} (hx : R≤‖x‖) (hx' : ‖x‖≤2*L*R) :
    Z*coulombKernel x+propagationPairOffset bad R l1 l2 u H x≤C/‖x‖^4 := by
  have h1 : 0≤l1/R^4 := div_nonneg (d.l2_nonneg.trans d.l2_le_l1) (pow_pos d.R_pos 4).le
  have h2 : 0≤l2/R^4 := div_nonneg d.l2_nonneg (pow_pos d.R_pos 4).le
  have hu := (d.old_caps x (d.old_le_new.trans hx)).2
  by_cases hb : bad
  · simp only [propagationPairOffset,ite_eq_left hb]
    linarith only [hu,h1]
  · have hH := d.physical_cap hb x (d.old_le_new.trans hx) hx'
    simp only [propagationPairOffset,ite_eq_right hb]
    rw [add_max]
    exact max_le (by linarith only [hu,h1]) (by linarith only [hH,h2])

lemma next_caps {x : Position} (hx : R≤‖x‖) :
    propagationBarrier B R x≤Z*coulombKernel x+propagationNextOffset bad B R Z L l1 l2 u H x ∧
    Z*coulombKernel x+propagationNextOffset bad B R Z L l1 l2 u H x≤C/‖x‖^4 := by
  have hp := (propagationBarrier_two_sided d.B_pos.le d.R_pos hx).2
  have hbc : propagationBarrier B R x≤C/‖x‖^4 := hp.trans
    (div_le_div_of_nonneg_right d.cap_large (pow_nonneg (norm_nonneg x) 4))
  have he := propagationBarrierOffset_eq (B:=B) (Z:=Z) hx
  unfold propagationNextOffset radialMaxSplice
  split_ifs with ha hb
  · have hx' : ‖x‖≤(11/10)*R := by linarith only [ha,d.R_pos]
    exact ⟨d.lower_pair hx hx',d.pair_cap hx (by
      have H := mul_pos (show 0<2*L-11/10 by linarith only [d.L_large]) d.R_pos
      nlinarith only [hx',H])⟩
  · rw [add_max]
    exact ⟨he ▸ le_max_right _ _, max_le (d.pair_cap hx (by
      have H := mul_pos d.L_pos d.R_pos
      nlinarith only [hb,H])) (by rwa [he])⟩
  · rw [he]
    exact ⟨le_rfl,hbc⟩

lemma next_outer {x : Position} (hx : L*R<‖x‖) :
    Z*coulombKernel x+propagationNextOffset bad B R Z L l1 l2 u H x=propagationBarrier B R x := by
  obtain ⟨_,hup⟩ := propagation_splice_overlaps d.B_pos d.r_pos d.R_eq d.L_large d.l2_nonneg
    d.l2_le_l1 d.l1_le_gamma d.upper_overlap d.old_caps d.physical_cap
  have hα : (53/50)*R≤L*R := by
    have H := mul_pos (show 0<L-53/50 by linarith only [d.L_large]) d.R_pos
    nlinarith only [H]
  have hβ : (3/2)*L*R≤2*L*R := by nlinarith only [mul_pos d.L_pos d.R_pos]
  have hRx : R≤‖x‖ := by
    have H := mul_pos (show 0<L-1 by linarith only [d.L_large]) d.R_pos
    nlinarith only [hx,H]
  rw [propagationNextOffset,radialMaxSplice_outer hα hβ hup hx]
  exact propagationBarrierOffset_eq hRx

lemma next_error_nonneg (x : Position) :
    0≤propagationStepError bad r R ‖x‖ (μ x) (p x) :=
  propagationStepError_nonneg (d.mu_nonneg x) (d.p_nonneg x)

lemma next_error_support (hs : ∀ x,r≤‖x‖ → p x=0) :
    ∀ x,R≤‖x‖ → propagationStepError bad r R ‖x‖ (μ x) (p x)=0 := by
  intro x hx
  simp [propagationStepError,not_lt_of_ge hx,hs x (d.old_le_new.trans hx)]

end PropagationStepHypotheses
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_TFNegativeGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical BigOperators Topology
noncomputable section
namespace Coulomb

def rawTFNegativeError (Φ ρ σ : Space → ℝ) : ℝ :=
  ∫ x, max ((∫ z, coulombKernel (x-z)*ρ z)-Φ x) 0*σ x

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_ConditionalMatching
attribute [-instance] _root_.OAI.NeutralAtom.observationNoise_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal ContDiff
namespace NeutralAtom

instance allObservationNoiseLaw_probability (n J : ℕ) :
    IsProbabilityMeasure (allObservationNoiseLaw n J) := by
  unfold allObservationNoiseLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance observationLaw_probability {n J : ℕ} (ν : Measure (Configuration n))
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (observationLaw J ν) := by
  unfold observationLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end NeutralAtom

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_CoreCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

def positiveInnerDeficit {n : ℕ} (Z : ℝ) (A : Set Space) (x : Configuration n) : ℝ :=
  max (Z-localCount A x) 0

end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_AtomicRefinedGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace Coulomb

lemma atomic_patch_nucleus_distance {J : ℕ} (S : Nuclei J)
    (hatom : ∀ i, S.position i=0) (y : Space) (j : Fin J) :
    20*atomicCellScale y ≤ ‖S.position j-y‖ := by
  rw [hatom j,zero_sub,norm_neg]
  unfold atomicCellScale
  nlinarith [norm_nonneg y]

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_Rescaling
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory Filter
open ContinuousLinearMap
open scoped Topology BigOperators ContDiff Convolution Pointwise ENNReal
namespace NeutralAtom

theorem coulombKernel_smul {D : ℝ} (hD : 0 < D) (x : Position) :
    coulombKernel (D • x) = D⁻¹*coulombKernel x := by
  simp only [coulombKernel, norm_smul, Real.norm_eq_abs, abs_of_pos hD, mul_inv_rev, mul_comm]

theorem potentialOf_scaledDensity {D : ℝ} (hD : 0 < D) (σ : Position → ℝ) (x : Position) :
    potentialOf (scaledDensity D σ) x = D^4*potentialOf σ (D • x) := by
  have h := Measure.integral_comp_smul_of_nonneg volume
    (fun y => coulombKernel (D • x-y)*σ y) D (hR := hD.le)
  simp only [Position, finrank_euclideanSpace_fin, smul_eq_mul] at h
  simp_rw [← smul_sub, coulombKernel_smul hD, mul_assoc, integral_const_mul] at h
  unfold potentialOf scaledDensity
  simp_rw [show ∀ y, coulombKernel (x-y)*(D^6*σ (D • y)) =
    D^6*(coulombKernel (x-y)*σ (D • y)) by intro y; ring, integral_const_mul]
  field_simp [hD.ne'] at h ⊢
  nlinarith [h]

theorem screenedField_scaledDensity {D : ℝ} (hD : 0 < D) (lam : ℝ)
    (σ : Position → ℝ) (x : Position) :
    screenedField (D^3*lam) (scaledDensity D σ) x =
      D^4*screenedField lam σ (D • x) := by
  rw [screenedField, screenedField, potentialOf_scaledDensity hD,
    coulombKernel_smul hD]
  field_simp

theorem WeakNuclearSubsolution.dilate {U q : Position → ℝ} {lam : ℝ}
    {D : ℝ} (hD : 0 < D) (hw : WeakNuclearSubsolution U lam Set.univ q) :
    WeakNuclearSubsolution (fun x => D^4*U (D • x)) (D^3*lam) Set.univ
      (scaledDensity D q) := by
  intro φ hφ hc _ht hφp
  let e : Position ≃ₜ Position := Homeomorph.smul (Units.mk0 D⁻¹ (inv_ne_zero hD.ne'))
  let ψ : Position → ℝ := fun x => φ (D⁻¹ • x)
  have hψ : ContDiff ℝ ∞ ψ := hφ.comp (contDiff_id.const_smul D⁻¹)
  have hψc : HasCompactSupport ψ := hc.comp_homeomorph e
  have hid (x : Position) : D⁻¹ • (D • x) = x := by
    rw [smul_smul, inv_mul_cancel₀ hD.ne', one_smul]
  have hLap (x : Position) : coordinateLaplacian ψ (D • x) =
      (D⁻¹)^2*coordinateLaplacian φ x := by
    change coordinateLaplacian (fun y => φ (D⁻¹ • y)) (D • x) = _
    rw [coordinateLaplacian_comp_smul, hid]
  have hleft := Measure.integral_comp_smul_of_nonneg volume
    (fun x => U x*coordinateLaplacian ψ x) D (hR := hD.le)
  have hright := Measure.integral_comp_smul_of_nonneg volume
    (fun x => q x*ψ x) D (hR := hD.le)
  simp only [Position, finrank_euclideanSpace_fin, smul_eq_mul] at hleft hright
  simp_rw [hLap, show ∀ x, U (D • x)*((D⁻¹)^2*coordinateLaplacian φ x) =
    (D⁻¹)^2*(U (D • x)*coordinateLaplacian φ x) by intro x; ring,
    integral_const_mul] at hleft
  simp only [ψ, hid] at hright
  have hwe := mul_le_mul_of_nonneg_left
    (hw ψ hψ hψc (Set.subset_univ _) (fun x => hφp _)) (pow_nonneg hD.le 3)
  have hψ0 : ψ 0 = φ 0 := by simp [ψ]
  rw [hψ0] at hwe
  have hli : D^4*(∫ x, U (D • x)*coordinateLaplacian φ x) =
      D^3*(∫ x, U x*coordinateLaplacian ψ x) := by
    field_simp [hD.ne'] at hleft
    rw [← hleft]
    ring
  have hri : D^6*(∫ x, q (D • x)*φ x) = D^3*(∫ x, q x*ψ x) := by
    field_simp [hD.ne'] at hright
    simp only [one_div] at hright
    change (∫ x, q (D • x)*φ x)*D^3 = (∫ x, q x*ψ x) at hright
    rw [← hright]
    ring
  simp only [scaledDensity, mul_assoc, integral_const_mul]
  rw [hli, hri]
  linarith

theorem barrierSource_dilate {D : ℝ} (hD : 0 < D) (r : ℝ)
    (U σ p : Position → ℝ) (x : Position) :
    barrierSource (r/D) (fun y => D^4*U (D • y))
      (scaledDensity D σ) (scaledDensity D p) x =
        scaledDensity D (barrierSource r U σ p) x := by
  have hlt : ‖D • x‖ < r ↔ ‖x‖ < r/D := by
    rw [lt_div_iff₀ hD, norm_smul, Real.norm_eq_abs, abs_of_pos hD, mul_comm]
  have hle : r ≤ ‖D • x‖ ↔ r/D ≤ ‖x‖ := by
    rw [div_le_iff₀ hD, norm_smul, Real.norm_eq_abs, abs_of_pos hD, mul_comm]
  simp only [barrierSource, cutoffReaction, scaledDensity, Set.indicator_apply,
    Set.mem_ofPred_eq, hlt, hle, tfReaction_dilate hD]
  split_ifs <;> ring

theorem WeakNuclearSubsolution.dilate_barrier {D : ℝ} (hD : 0 < D)
    {U σ p : Position → ℝ} {lam r : ℝ}
    (hw : WeakNuclearSubsolution U lam Set.univ (barrierSource r U σ p)) :
    WeakNuclearSubsolution (fun x => D^4*U (D • x)) (D^3*lam) Set.univ
      (barrierSource (r/D) (fun x => D^4*U (D • x))
        (scaledDensity D σ) (scaledDensity D p)) := by
  simpa only [show barrierSource (r/D) (fun x => D^4*U (D • x))
      (scaledDensity D σ) (scaledDensity D p) =
        scaledDensity D (barrierSource r U σ p) from funext (barrierSource_dilate hD r U σ p)]
    using hw.dilate hD

theorem tfDensityScalar_dilate {D : ℝ} (hD : 0 < D) (t : ℝ) :
    tfDensityScalar (D^4*t) = D^6*tfDensityScalar t := by
  have hm : max (D^4*t) 0 = D^4*max t 0 := by
    rw [mul_max_of_nonneg t 0 (pow_nonneg hD.le 4), mul_zero]
  have hr : (D^4)^(3/2 : ℝ) = D^6 := by
    rw [← Real.rpow_natCast D 4, ← Real.rpow_mul hD.le]
    norm_num
  rw [tfDensityScalar, hm, Real.mul_rpow (pow_nonneg hD.le 4) (le_max_right t 0), hr,
    tfDensityScalar]
  ring

theorem screened_comparison_dilate {D r q C δ lam : ℝ} (hD : 0 < D)
    {σ : Position → ℝ}
    (hbound : ∀ y, r ≤ ‖y‖ → ‖y‖ ≤ q*D →
      screenedField lam σ y ≤ C/‖y‖^4 ∧
      |σ y-tfDensityScalar (screenedField lam σ y)| ≤ δ/‖y‖^6)
    (x : Position) (hx : r/D ≤ ‖x‖) (hxq : ‖x‖ ≤ q) :
    screenedField (D^3*lam) (scaledDensity D σ) x ≤ C/‖x‖^4 ∧
      |scaledDensity D σ x-tfDensityScalar
        (screenedField (D^3*lam) (scaledDensity D σ) x)| ≤ δ/‖x‖^6 := by
  have hxl : r ≤ ‖D • x‖ := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hD, mul_comm] using
      (div_le_iff₀ hD).mp hx
  have hxu : ‖D • x‖ ≤ q*D := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hD, mul_comm] using
      mul_le_mul_of_nonneg_left hxq hD.le
  obtain ⟨hc,he⟩ := hbound _ hxl hxu
  rw [screenedField_scaledDensity hD, tfDensityScalar_dilate hD]
  constructor
  · have hh := mul_le_mul_of_nonneg_left hc (pow_nonneg hD.le 4)
    rwa [mul_inverse_power_dilate hD] at hh
  · have hh := mul_le_mul_of_nonneg_left he (pow_nonneg hD.le 6)
    rw [mul_inverse_power_dilate hD] at hh
    simpa only [scaledDensity, ← mul_sub, abs_mul, abs_of_nonneg (pow_nonneg hD.le 6)] using hh

structure PhysicalRetainedFamily (Θ : ℕ → Type*) where
  μ : ∀ n, Θ n → Position → ℝ
  u : ∀ n, Θ n → Position → ℝ
  p : ∀ n, Θ n → Position → ℝ
  Z : ℕ → ℕ
  s : ℕ → ℝ
  r : ℕ → ℝ
  q : ℕ → ℕ
  Aμ : ∀ n, Θ n → ℝ
  Ap : ∀ n, Θ n → ℝ
  B : ℝ
  Ccap : ℝ
  Cinv : ℝ
  Bpos : 0 < B
  Cpos : 0 ≤ Ccap
  sp : ∀ n, 0 < s n
  rp : ∀ n, 0 < r n
  slim : Tendsto s atTop (𝓝 0)
  qlim : Tendsto q atTop atTop
  rlo : ∀ n, 1/(2*(q n : ℝ)) ≤ r n/s n
  rhi : ∀ n, r n/s n ≤ ((q n : ℝ))⁻¹
  μi : ∀ n θ, Integrable (μ n θ)
  μp : ∀ n θ x, 0 ≤ μ n θ x
  μb : ∀ n θ x, μ n θ x ≤ Aμ n θ
  μmass : ∀ n θ, (∫ x, μ n θ x) = (Z n : ℝ)
  pi : ∀ n θ, Integrable (p n θ)
  pp : ∀ n θ x, 0 ≤ p n θ x
  pb : ∀ n θ x, p n θ x ≤ Ap n θ
  ps : ∀ n θ x, r n < ‖x‖ → p n θ x = 0
  pm : ∀ n θ, (∫ x, p n θ x) ≤ 1
  ucont : ∀ n θ, Continuous (fun x => u n θ x-(Z n : ℝ)*coulombKernel x)
  ubounds : ∀ n θ x, r n ≤ ‖x‖ →
    B/‖x‖^4*(1-r n/(8*‖x‖)) ≤ u n θ x ∧ u n θ x ≤ Cinv/‖x‖^4
  uweak : ∀ n θ, WeakNuclearSubsolution (u n θ) (Z n : ℝ) Set.univ
    (barrierSource (r n) (u n θ) (μ n θ) (p n θ))
  band : ∀ n θ x, r n ≤ ‖x‖ → ‖x‖ ≤ (q n : ℝ)*s n →
    screenedField (Z n : ℝ) (μ n θ) x ≤ Ccap/‖x‖^4 ∧
    |μ n θ x-tfDensityScalar (screenedField (Z n : ℝ) (μ n θ) x)| ≤
      (((q n : ℝ)^8)⁻¹)/‖x‖^6

theorem continuous_scaled_offset {D z : ℝ} (hD : 0 < D) {u : Position → ℝ}
    (hu : Continuous (fun x => u x-z*coulombKernel x)) :
    Continuous (fun x => D^4*u (D • x)-(D^3*z)*coulombKernel x) := by
  have he : (fun x => D^4*u (D • x)-(D^3*z)*coulombKernel x) =
      fun x => D^4*(u (D • x)-z*coulombKernel (D • x)) := by
    funext x
    simp only [coulombKernel, norm_smul, Real.norm_eq_abs, abs_of_pos hD, mul_inv_rev]
    field_simp
  rw [he]
  exact (hu.comp (continuous_const_smul D)).const_mul _

def PhysicalRetainedFamily.toAnalytic {Θ : ℕ → Type*} (d : PhysicalRetainedFamily Θ) :
    RetainedAnalyticFamily Θ where
  σ := fun n θ => scaledDensity (d.s n) (d.μ n θ)
  U := fun n θ x => d.s n^4*d.u n θ (d.s n • x)
  p := fun n θ => scaledDensity (d.s n) (d.p n θ)
  lam := fun n => d.s n^3*(d.Z n : ℝ)
  a := fun n => d.r n/d.s n
  q := fun n => (d.q n : ℝ)
  ε := fun n => d.s n^3
  Aσ := fun n θ => d.s n^6*d.Aμ n θ
  Ap := fun n θ => d.s n^6*d.Ap n θ
  B := d.B
  Ccap := d.Ccap
  Cinv := d.Cinv
  Bpos := d.Bpos
  Cpos := d.Cpos
  σi := fun n θ => scaledDensity_integrable (d.sp n) (d.μi n θ)
  σp := fun n θ => scaledDensity_nonneg (d.μp n θ)
  σb := fun n θ => scaledDensity_bound (d.μb n θ)
  σmass := fun n θ => by rw [integral_scaledDensity (d.sp n), d.μmass]
  pi := fun n θ => scaledDensity_integrable (d.sp n) (d.pi n θ)
  pp := fun n θ => scaledDensity_nonneg (d.pp n θ)
  pb := fun n θ => scaledDensity_bound (d.pb n θ)
  ps := fun n θ => scaledDensity_support (d.sp n) (d.ps n θ)
  pm := fun n θ => by
    rw [integral_scaledDensity (d.sp n)]
    exact (mul_le_mul_of_nonneg_left (d.pm n θ) (pow_nonneg (d.sp n).le 3)).trans_eq
      (mul_one _)
  εlim := by simpa using d.slim.pow 3
  apos := fun n => div_pos (d.rp n) (d.sp n)
  alim := by
    apply squeeze_zero (fun n => (div_pos (d.rp n) (d.sp n)).le) d.rhi
    exact tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp d.qlim)
  qlim := tendsto_natCast_atTop_atTop.comp d.qlim
  aq := Eventually.of_forall d.rlo
  Ucont := fun n θ => continuous_scaled_offset (d.sp n) (d.ucont n θ)
  Ulower := fun n θ x hx => (barrier_bounds_dilate (d.sp n) (d.ubounds n θ) x hx).1
  Uupper := fun n θ x hx => (barrier_bounds_dilate (d.sp n) (d.ubounds n θ) x hx).2
  Uweak := fun n θ => (d.uweak n θ).dilate_barrier (d.sp n)
  cap := fun n θ x hx hxq => (screened_comparison_dilate (d.sp n) (d.band n θ) x hx hxq).1
  err := fun n θ x hx hxq => by
    simpa only [div_eq_mul_inv] using
      (screened_comparison_dilate (d.sp n) (d.band n θ) x hx hxq).2

end NeutralAtom
end

end

end OAI
end


