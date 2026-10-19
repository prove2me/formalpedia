-- Prove2me | Definitions.Def_OAIQWHLE000
-- name    : OAIQWHLE000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-19T01:37:52.173731+00:00
-- url     : https://prove2.me/theorems/f50dcc4c-8301-4039-a022-96f32ecfcee2
-- title:
--   OpenAI Hénon–Lane–Emden split: definitions bundle
-- statement:
--   The definitions bundle of the split of OpenAI's proof of the subcritical Hénon–Lane–Emden conjecture (`OAI.HenonLaneEmden.main_nonexistence`). It holds OpenAI's Lean definitions and instances from the modules listed below of `lean/OAI/Analysis/HenonEmden` (OpenAI, *The Subcritical Hénon–Lane–Emden Conjecture*, OpenAI Math Release, September 24, 2026, result family 370, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a. Among them are:
--   - the convolution and mollifier notation (`HenonLaneEmden.WeakPDE.convolve`, `HenonLaneEmden.WeakPDE.standardBump`) and the raw Newtonian potential `HenonLaneEmden.WeakPDE.rawPotential`;
--   - the sources and energies (`source`, `weightedEnergy`, `weightedEnergyN`), the scaling exponents and dilations (`alpha`, `beta`, `dilation`);
--   - the cutoff of the paper's (3.2) (`eta`, `w`, `d`, `X`, with their profiles);
--   - the Newton kernel and the interaction measure (`newtonKernel`, `newtonDenom`, `interaction`), and the localization and pressure functionals (`localQ`, `radialPressure`, `fluxFactor`, `radialFactor`, `directionalFactor`);
--   - the cap and component weights of Section 5 (`weight`, `lineWeight`, `layerMeasure`, `endpointAverage`) and the directional integrals (`positionIntegral`, `endpointIntegral`, `lossIntegral`, `capPressureIntegral`, `capMismatchIntegral`, `pairMismatchIntegral`);
--   - the explicit constants of the estimates (`sourceConstant`, `sourceBallConstant`, `uniformMassConstant`, `lossCoefficient`, `lowLevelConstant`, `endpointConstant`, and others).
--
--   It also contains the four lemmas that definitions and instances use in their bodies (`norm_unit`, `inner_transverse`, `join_surjective`, `IsSolution.swap`) and the σ-finiteness instances of the layer, source and interaction measures. It proves no named theorem and imports no statement.
--
--   The definitions of the published statement (`Space`, `IsSolution`, `Subcritical`) are not repeated: the bundle imports them from the published bundle `Def_HenonEmden`.
--
--   Modules: `AdaptiveCaps.lean`, `AngularBounds.lean`, `AngularIntegration.lean`, `AngularLoss.lean`, `AngularMeasurability.lean`, `CapGeometry.lean`, `CapOscillation.lean`, `CapWeights.lean`, `Components.lean`, `ComponentWeights.lean`, `Cutoff.lean`, `Endpoints.lean`, `Energy.lean`, `FarInteraction.lean`, `FarLocalization.lean`, `GlobalLoss.lean`, `Gradients.lean`, `Interaction.lean`, `Intervals.lean`, `LayerAssembly.lean`, `LayerIntegration.lean`, `LayerPressure.lean`, `LayerSplit.lean`, `LineCoordinates.lean`, `LocalizationIntegral.lean`, `MassGrowth.lean`, `Mollification.lean`, `NearLocalization.lean`, `NewtonBounds.lean`, `NewtonPotential.lean`, `OriginBounds.lean`, `PairPressure.lean`, `PairRecovery.lean`, `PressureEstimate.lean`, `RadialGeometry.lean`, `RadialJoint.lean`, `RelativeLocalization.lean`, `RootRecovery.lean`, `Scaling.lean`, `SourceEndpoints.lean`, `SourceMass.lean`, `Sources.lean`, `SpatialComponents.lean`, `SpatialEndpoints.lean`, `SpatialPressure.lean`, `SphereCaps.lean`, `SphereMean.lean`, `Tonelli.lean`, `UniformBounds.lean`, `WeakForm.lean`, `WeightedEnergy.lean`.
--
--   The theorems of the development are proved in the ten solutions of this split. Three prove the published classical statements of potential theory, each stated with Mathlib's definitions only: Liouville's theorem for nonnegative harmonic distributions (`OAI.HenonLaneEmden.WeakPDE.harmonic_distribution_nonneg_constant`), the lower bound for the Newtonian potential (`OAI.HenonLaneEmden.WeakPDE.weak_newton_lower`) and the Riesz decomposition (`OAI.HenonLaneEmden.WeakPDE.potential_constant`). Six prove intermediate statements of OpenAI's argument, and the last proves `OAI.HenonLaneEmden.main_nonexistence` from them.
-- source:
--   OpenAI, The Subcritical Hénon–Lane–Emden Conjecture, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 370; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Subcritical-Henon-Lane-Emden-Conjecture-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/HenonEmden at commit adc7f12

import Mathlib
import Definitions.Def_HenonEmden

section
-- module Solutions.OAIQW_HenonLaneEmden.LineCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section LineCoordinates

open MeasureTheory Set Metric
open scoped InnerProductSpace
noncomputable section
namespace HenonLaneEmden.LineCoordinates

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def transverse (e : sphere (0:E) 1) : Submodule ℝ E := (ℝ ∙ (e : E))ᗮ
omit [InnerProductSpace ℝ E] in
lemma norm_unit (e : sphere (0:E) 1) : ‖(e:E)‖ = 1 := by
  simpa only [mem_sphere,dist_zero_right] using e.2
lemma inner_transverse (e : sphere (0:E) 1) (z : transverse e) : inner ℝ (e:E) (z:E) = 0 :=
  Submodule.mem_orthogonal_singleton_iff_inner_right.mp z.2

def join (e : sphere (0:E) 1) : WithLp 2 (transverse e × ℝ) →ₗᵢ[ℝ] E where
  toFun z := z.fst.1 + z.snd • (e:E)
  map_add' z z' := by simp only [WithLp.add_fst,WithLp.add_snd,Submodule.coe_add,add_smul]; abel
  map_smul' r z := by
    simp only [WithLp.smul_fst,WithLp.smul_snd,Submodule.coe_smul_of_tower,smul_eq_mul,
      smul_add,smul_smul,RingHom.id_apply]
  norm_map' z := by
    change ‖(z.fst:E)+z.snd • (e:E)‖ = ‖z‖
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_add_sq_real,real_inner_comm,inner_smul_left,inner_transverse,mul_zero,mul_zero,add_zero,
      norm_smul,norm_unit,mul_one,Real.norm_eq_abs,sq_abs,WithLp.prod_norm_sq_eq_of_L2,
      Real.norm_eq_abs,sq_abs]
    rfl

lemma join_surjective (e : sphere (0:E) 1) : Function.Surjective (join e) := by
  intro x
  let t := inner ℝ (e:E) x
  have hz : x-t • (e:E) ∈ transverse e := by
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    simp only [inner_sub_right,inner_smul_right,real_inner_self_eq_norm_sq,norm_unit,one_pow,mul_one,t,sub_self]
  refine ⟨WithLp.toLp 2 (⟨x-t • (e:E),hz⟩,t),?_⟩
  change (x-t • (e:E))+t • (e:E) = x
  abel

def isometry (e : sphere (0:E) 1) : WithLp 2 (transverse e × ℝ) ≃ₗᵢ[ℝ] E :=
  LinearIsometryEquiv.ofSurjective (join e) (join_surjective e)

@[simp] lemma isometry_apply (e : sphere (0:E) 1) (z : WithLp 2 (transverse e × ℝ)) :
    isometry e z = (z.fst:E)+z.snd • (e:E) := rfl

variable [MeasurableSpace E] [BorelSpace E]

def measurableEquiv (e : sphere (0:E) 1) : (transverse e × ℝ) ≃ᵐ E :=
  (MeasurableEquiv.toLp 2 _).trans (isometry e).toMeasurableEquiv

@[simp] lemma measurableEquiv_apply (e : sphere (0:E) 1) (z : transverse e × ℝ) :
    measurableEquiv e z = (z.1:E)+z.2 • (e:E) := rfl

end HenonLaneEmden.LineCoordinates
end
end LineCoordinates

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.WeakForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uE2

section WeakForm



open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace HenonLaneEmden.WeakPDE
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

noncomputable def dir (f : E → ℝ) (e : E) : E → ℝ := fun x => fderiv ℝ f x e

end HenonLaneEmden.WeakPDE

end WeakForm

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.SphereMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uS uE uE2

section SphereMean

open Set Filter Topology MeasureTheory
open scoped ContDiff
open Set Filter Topology
open scoped RealInnerProductSpace ContDiff
open Set Filter Topology
open scoped ContDiff
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal
noncomputable section

open Set Filter Topology MeasureTheory

namespace HenonLaneEmden.SphereCalculus
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

abbrev UnitSphere (E : Type uE2) [NormedAddCommGroup E] := Metric.sphere (0:E) 1

noncomputable def mean (u : E → ℝ) (r : ℝ) : ℝ :=
  ∫ θ : UnitSphere E, u (r • θ.1) ∂(volume : Measure E).toSphere
noncomputable def meanD (u : E → ℝ) (r : ℝ) : ℝ :=
  ∫ θ : UnitSphere E, fderiv ℝ u (r • θ.1) θ.1 ∂(volume : Measure E).toSphere
noncomputable def meanDD (u : E → ℝ) (r : ℝ) : ℝ :=
  ∫ θ : UnitSphere E, fderiv ℝ (fderiv ℝ u) (r • θ.1) θ.1 θ.1
    ∂(volume : Measure E).toSphere

end HenonLaneEmden.SphereCalculus

end
end SphereMean

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.Mollification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uE2 uι uE3

section Mollification

open Set Filter Topology MeasureTheory
open scoped ContDiff
open Set Filter Topology
open scoped RealInnerProductSpace ContDiff
open Set Filter Topology
open scoped ContDiff
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal
open Set Filter Topology MeasureTheory
open Set Filter Topology
open MeasureTheory
noncomputable section


open scoped Convolution
namespace HenonLaneEmden.WeakPDE
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

noncomputable def convolve (f g : E → ℝ) : E → ℝ := f ⋆[ContinuousLinearMap.mul ℝ ℝ] g

end HenonLaneEmden.WeakPDE

namespace HenonLaneEmden.WeakPDE
variable {E : Type uE3} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

noncomputable def standardBump (j : ℕ) : ContDiffBump (0:E) :=
  ⟨1/((j:ℝ)+1),2/((j:ℝ)+1),by positivity,by
    apply (div_lt_div_iff_of_pos_right (by positivity : (0:ℝ)<j+1)).mpr
    norm_num⟩

end HenonLaneEmden.WeakPDE

end
end Mollification

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.Scaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section Scaling

open Set Filter Topology MeasureTheory
open scoped ContDiff
open Set Filter Topology
open scoped RealInnerProductSpace ContDiff
open Set Filter Topology
open scoped ContDiff
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal
open Set Filter Topology MeasureTheory
open Set Filter Topology
open MeasureTheory
open scoped Convolution
noncomputable section

open Set Filter Topology
namespace HenonLaneEmden


noncomputable def alpha (p q A B : ℝ) := (2+A+p*(2+B))/(p*q-1)
noncomputable def beta (p q A B : ℝ) := (2+B+q*(2+A))/(p*q-1)

noncomputable def dilation {n : ℕ} (u : Space n → ℝ) (a R : ℝ) : Space n → ℝ :=
  fun x => R^a*u (R • x)

end HenonLaneEmden

end
end Scaling

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.Sources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Sources

open Set Filter Topology MeasureTheory
open scoped ContDiff
open Set Filter Topology
open scoped RealInnerProductSpace ContDiff
open Set Filter Topology
open scoped ContDiff
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal
open Set Filter Topology MeasureTheory
open Set Filter Topology
open MeasureTheory
open scoped Convolution
open Set Filter Topology
noncomputable section


open MeasureTheory Set Filter Topology
open scoped ContDiff
namespace HenonLaneEmden

noncomputable def source {n : ℕ} (u : Space n → ℝ) (q B : ℝ) (x : Space n) : ℝ :=
  if x = 0 then 0 else ‖x‖^B*(u x)^q

end HenonLaneEmden

end
end Sources

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.OriginBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section OriginBounds

open Set Filter Topology MeasureTheory
open scoped ContDiff
open Set Filter Topology
open scoped RealInnerProductSpace ContDiff
open Set Filter Topology
open scoped ContDiff
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal
open Set Filter Topology MeasureTheory
open Set Filter Topology
open MeasureTheory
open scoped Convolution
open Set Filter Topology
open MeasureTheory Set Filter Topology
open scoped ContDiff
noncomputable section


namespace HenonLaneEmden
open SphereCalculus

lemma IsSolution.swap {n : ℕ} {p q A B : ℝ} {u v : Space n → ℝ}
    (h : IsSolution n p q A B u v) : IsSolution n q p B A v u :=
  ⟨h.continuous_v,h.continuous_u,h.regular_v,h.regular_u,
    h.positive_v,h.positive_u,h.equation_v,h.equation_u⟩

end HenonLaneEmden

end
end OriginBounds

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.NewtonBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section NewtonBounds

open Set Filter Topology MeasureTheory
open scoped ContDiff
open Set Filter Topology
open scoped RealInnerProductSpace ContDiff
open Set Filter Topology
open scoped ContDiff
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal
open Set Filter Topology MeasureTheory
open Set Filter Topology
open MeasureTheory
open scoped Convolution
open Set Filter Topology
open MeasureTheory Set Filter Topology
open scoped ContDiff
noncomputable section


namespace HenonLaneEmden
open WeakPDE

noncomputable def sphereArea (n : ℕ) : ℝ := ((volume : Measure (Space n)).toSphere univ).toReal
noncomputable def newtonDenom (n : ℕ) : ℝ := ((n:ℝ)-2)*sphereArea n

end HenonLaneEmden

end
end NewtonBounds

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.NewtonPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uE2 uE3 uE4

section NewtonPotential

open Set Filter Topology MeasureTheory
open scoped ContDiff
open Set Filter Topology
open scoped RealInnerProductSpace ContDiff
open Set Filter Topology
open scoped ContDiff
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal
open Set Filter Topology MeasureTheory
open Set Filter Topology
open MeasureTheory
open scoped Convolution
open Set Filter Topology
open MeasureTheory Set Filter Topology
open scoped ContDiff
noncomputable section


namespace HenonLaneEmden.WeakPDE
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

noncomputable def rawPotential (g : E → ℝ) (x : E) : ℝ :=
  ∫ y, ‖x-y‖^(2-(Module.finrank ℝ E:ℝ))*g y

end HenonLaneEmden.WeakPDE

end
end NewtonPotential

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.SourceMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section SourceMass

open Set Filter Topology MeasureTheory
open scoped ContDiff
open Set Filter Topology
open scoped RealInnerProductSpace ContDiff
open Set Filter Topology
open scoped ContDiff
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal
open Set Filter Topology MeasureTheory
open Set Filter Topology
open MeasureTheory
open scoped Convolution
open Set Filter Topology
open MeasureTheory Set Filter Topology
open scoped ContDiff
noncomputable section


namespace HenonLaneEmden
open WeakPDE
noncomputable def sourceMass {n : ℕ} (u : Space n → ℝ) (q B R : ℝ) : ℝ :=
  ∫ x in Metric.ball (0:Space n) R, source u q B x
noncomputable def lowerMass {n : ℕ} (u : Space n → ℝ) (q B R : ℝ) : ℝ :=
  (2*R)^(2-(n:ℝ))/newtonDenom n*sourceMass u q B R
noncomputable def weightMass (n : ℕ) (B : ℝ) : ℝ :=
  ∫ x in Metric.ball (0:Space n) 1, ‖x‖^B
noncomputable def ballConstant (n : ℕ) : ℝ := 2^(2-(n:ℝ))/newtonDenom n

end HenonLaneEmden

end
end SourceMass

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.MassGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section MassGrowth

open Set Filter Topology MeasureTheory
open scoped ContDiff
open Set Filter Topology
open scoped RealInnerProductSpace ContDiff
open Set Filter Topology
open scoped ContDiff
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal
open Set Filter Topology MeasureTheory
open Set Filter Topology
open MeasureTheory
open scoped Convolution
open Set Filter Topology
open MeasureTheory Set Filter Topology
open scoped ContDiff
noncomputable section


namespace HenonLaneEmden
noncomputable def sourceConstant (n : ℕ) (p q A B : ℝ) : ℝ :=
  ((ballConstant n*weightMass n A)*(ballConstant n*weightMass n B)^p)^(1/(1-p*q)) / ballConstant n

end HenonLaneEmden

end
end MassGrowth

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.CapGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section CapGeometry

open MeasureTheory MeasureTheory.Measure Set Metric
open scoped ENNReal Pointwise
noncomputable section
namespace HenonLaneEmden.CapGeometry

/-- Radial bands in the positive-radius factor of polar coordinates. -/
def band (a b : ℝ) : Set (Ioi (0:ℝ)) := {r | a < r.1 ∧ r.1 < b}

end HenonLaneEmden.CapGeometry
end
end CapGeometry

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.CapWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uT

section CapWeights

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden.CapWeights

variable {T : Type uT} [MetricSpace T]

/-- A Lipschitz tent profile suffices for the pressure argument; no derivative
of the profile is used in the layer or interval integration. -/
def profile (θ : T) (l : ℝ) (e : T) : ℝ := max (1-dist e θ/l) 0

variable [MeasurableSpace T] [BorelSpace T] (σ : Measure T) [IsFiniteMeasure σ] [CompactSpace T]

def normalizer (θ : T) (l : ℝ) : ℝ := ∫ e, profile θ l e ∂σ

/-- Every cap is normalized exactly, with no rotational-invariance assumption. -/
def normalized (θ : T) (l : ℝ) (e : T) : ℝ := profile θ l e / normalizer σ θ l

end HenonLaneEmden.CapWeights
end
end CapWeights

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.SphereCaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section SphereCaps

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden.CapWeights

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

def lowerConstant : ℝ := (μ (ball (0:E) 1)).toReal /
  (4^Module.finrank ℝ E * 2^(Module.finrank ℝ E-1)) / 2^(Module.finrank ℝ E)
def upperConstant : ℝ := 4^Module.finrank ℝ E*(μ (ball (0:E) 1)).toReal

end HenonLaneEmden.CapWeights
end
end SphereCaps

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.Cutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section Cutoff

open MeasureTheory Set Metric Filter Topology
noncomputable section
namespace HenonLaneEmden.Cutoff

/-- The positive-part powers used by the compact cutoff. -/
def posPow (k : ℕ) (r : ℝ) : ℝ := (max r 0)^k

def m (n : ℕ) := n+3
def k (n : ℕ) := n*(m n+1)
def N (n : ℕ) := k n+n+2

def gapProfile (r : ℝ) : ℝ := min 1 (max (2-r) 0)
def baseProfile (r : ℝ) : ℝ := max (1-posPow 3 (r-1)) 0
def etaProfile (n : ℕ) (r : ℝ) : ℝ := posPow (N n) (1-posPow 3 (r-1))
def derivativeProfile (n : ℕ) (r : ℝ) : ℝ :=
  -(3*(N n:ℝ)*(max (r-1) 0)^2*(baseProfile r)^(N n-1))
def wProfile (n : ℕ) (r : ℝ) : ℝ := -r*derivativeProfile n r

def secondProfile (n : ℕ) (r : ℝ) : ℝ :=
  -6*(N n:ℝ)*max (r-1) 0*(baseProfile r)^(N n-1) +
    9*(N n:ℝ)*(N n-1)*((max (r-1) 0)^4)*(baseProfile r)^(N n-2)

def derivativeConstant (n : ℕ) : ℝ := 3*(N n:ℝ)*3^(N n-1)
def secondConstant (n : ℕ) : ℝ := (6*(N n:ℝ)+9*(N n:ℝ)*(N n-1))*3^(N n-2)
def wDerivativeConstant (n : ℕ) : ℝ := derivativeConstant n+2*secondConstant n

def wDerivativeProfile (n : ℕ) (r : ℝ) : ℝ := -derivativeProfile n r-r*secondProfile n r

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def d (x : E) : ℝ := gapProfile ‖x‖
def eta (n : ℕ) (x : E) : ℝ := etaProfile n ‖x‖
def w (n : ℕ) (x : E) : ℝ := -(fderiv ℝ (eta n : E → ℝ) x x)
def X (n : ℕ) (x : E) : E := eta n x • x

end HenonLaneEmden.Cutoff
end
end Cutoff

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.AdaptiveCaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section AdaptiveCaps

open MeasureTheory Set Metric NormedSpace
noncomputable section
namespace HenonLaneEmden.AdaptiveCap
open Cutoff CapWeights

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

def direction (x : E) (hx : x ≠ 0) : sphere (0:E) 1 :=
  ⟨NormedSpace.normalize x, by simpa only [mem_sphere,dist_zero_right] using NormedSpace.norm_normalize hx⟩

def weight (κ : ℝ) (e : sphere (0:E) 1) (x : E) : ℝ := by
  classical
  exact if hx : x ≠ 0 ∧ 0 < d x then
    w (Module.finrank ℝ E) x * normalized μ.toSphere (direction x hx.1) (κ*d x) e
  else 0

def boundConstant (κ : ℝ) : ℝ :=
  (6*(N (Module.finrank ℝ E):ℝ)*3^(N (Module.finrank ℝ E)-1)) /
    (lowerConstant μ * κ^(Module.finrank ℝ E-1))

end HenonLaneEmden.AdaptiveCap
end
end AdaptiveCaps

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.CapOscillation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section CapOscillation

open MeasureTheory Set Metric
noncomputable section
namespace HenonLaneEmden.AdaptiveCap
open Cutoff CapWeights
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

def normalizedOscConstant : ℝ :=
  2/(lowerConstant μ/2^(Module.finrank ℝ E-1))+
    2*(2^(Module.finrank ℝ E)*upperConstant μ)/(lowerConstant μ/2^(Module.finrank ℝ E-1))^2

def oscillationConstant (κ : ℝ) : ℝ :=
  wDerivativeConstant (Module.finrank ℝ E)*2^(N (Module.finrank ℝ E)-2) /
      (lowerConstant μ*κ^(Module.finrank ℝ E-1)) +
  (6*(N (Module.finrank ℝ E):ℝ)*3^(N (Module.finrank ℝ E)-1))*
    2^(N (Module.finrank ℝ E)-1)*normalizedOscConstant μ*6/κ^(Module.finrank ℝ E)

end HenonLaneEmden.AdaptiveCap
end
end CapOscillation

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.Components
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX

section Components
open MeasureTheory Set Filter Topology
open scoped ENNReal
open Classical
namespace HenonLaneEmden.LineComponents

variable {X : Type uX} [TopologicalSpace X]

/-- All points of the closed segment between the base point `0` and `r`
remain in the open line layer. -/
def SegmentInside (U : Set (X × ℝ)) (p : X) (r : ℝ) : Prop :=
  ∀ s ∈ uIcc 0 r, (p,s) ∈ U

/-- The rational definition makes joint measurability independent of coordinates
on the direction-dependent transverse hyperplanes. -/
noncomputable def forwardExit (U : Set (X × ℝ)) (p : X) : ℝ≥0∞ :=
  ⨆ r : ℚ, if SegmentInside U p (r : ℝ) then ENNReal.ofReal (r : ℝ) else 0

noncomputable def backwardExit (U : Set (X × ℝ)) (p : X) : ℝ≥0∞ :=
  ⨆ r : ℚ, if SegmentInside U p (-(r : ℝ)) then ENNReal.ofReal (r : ℝ) else 0

noncomputable def componentLength (U : Set (X × ℝ)) (p : X) : ℝ≥0∞ :=
  forwardExit U p + backwardExit U p

noncomputable def componentInf (U : Set (X × ℝ)) (value : X × ℝ → ℝ) (p : X) : ℝ≥0∞ :=
  ⨅ r : ℚ, if SegmentInside U p (r : ℝ) then ENNReal.ofReal (value (p,(r : ℝ))) else ⊤

noncomputable def componentWeight (U : Set (X × ℝ)) (h d : X × ℝ → ℝ)
    (δ : ℝ) (p : X) : ℝ≥0∞ :=
  if (p,0) ∈ U ∧ componentLength U p ≠ ⊤ ∧
      componentLength U p ≤ ENNReal.ofReal (2*δ) * componentInf U d p
  then componentInf U h p else 0

end HenonLaneEmden.LineComponents
end Components

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.ComponentWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX uP

section ComponentWeights
open MeasureTheory Set Filter Topology
open scoped ENNReal
open Classical
namespace HenonLaneEmden.LineComponents
variable {X : Type uX} [TopologicalSpace X]

/-- The family that observes a single real layer relative to a moving basepoint. -/
def shiftedLayer (U : Set ℝ) : Set (ℝ × ℝ) := {z | z.1+z.2 ∈ U}

noncomputable def setInf (f : ℝ → ℝ) (I : Set ℝ) : ℝ≥0∞ :=
  ⨅ y ∈ I, ENNReal.ofReal (f y)

/-- The component weight, including the zero continuation when
the set is empty or the length condition fails. -/
noncomputable def setWeight (h d : ℝ → ℝ) (δ : ℝ) (I : Set ℝ) : ℝ≥0∞ :=
  if I.Nonempty ∧ volume I ≠ ⊤ ∧ volume I ≤ ENNReal.ofReal (2*δ)*setInf d I
  then setInf h I else 0

section Parameter
variable {P : Type uP} [TopologicalSpace P]

def relativeLayer (U : Set (P × ℝ)) : Set ((P × ℝ) × ℝ) :=
  {z | (z.1.1,z.1.2+z.2) ∈ U}

end Parameter

end HenonLaneEmden.LineComponents
end ComponentWeights

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.SpatialComponents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section SpatialComponents

open MeasureTheory Set Metric
noncomputable section
namespace HenonLaneEmden.SpatialComponents
open Cutoff AdaptiveCap LineComponents
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

def lineLayer (f : E → ℝ) : Set ((sphere (0:E) 1 × (E × ℝ)) × ℝ) :=
  {z | 0 < z.1.2.2 ∧ z.1.2.2 < f (z.1.2.1+z.2 • z.1.1.1)}
def lineWeight (f : E → ℝ) (κ δ : ℝ) (p : sphere (0:E) 1 × (E × ℝ)) : ℝ :=
  (componentWeight (lineLayer f) (fun z => weight μ κ z.1.1 (z.1.2.1+z.2 • z.1.1.1))
    (fun z => d (z.1.2.1+z.2 • z.1.1.1)) δ p).toReal

end HenonLaneEmden.SpatialComponents
end
end SpatialComponents

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.Intervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Intervals
open MeasureTheory Set Filter Topology
namespace HenonLaneEmden.IntervalGeometry


/-- Integral over the segment of half-length `r` centered at `x`. -/
noncomputable def segmentIntegral (k : ℝ → ℝ) (r x : ℝ) : ℝ :=
  ∫ t in x - r..x + r, k t




/-- Restricted Newton kernel; `c` is its (positive) normalization. -/
noncomputable def kernel (n : ℕ) (l c h : ℝ) : ℝ :=
  c * (l ^ 2 + h ^ 2) ^ ((2 - (n : ℝ)) / 2)




noncomputable def boxIntegral (a b c d : ℝ) (F : ℝ → ℝ → ℝ) : ℝ :=
  ∫ x in a..b, ∫ y in c..d, F x y

end HenonLaneEmden.IntervalGeometry
end Intervals

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.LayerPressure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section LayerPressure


open Set MeasureTheory
open scoped ENNReal NNReal Topology

namespace HenonLaneEmden.LayerPressure

/-- The actual (nonempty) connected components of an open real line layer. -/
def components (U : Set ℝ) : Set (Set ℝ) := connectedComponentIn U '' U

open IntervalGeometry

open LineComponents

noncomputable def lineWeight (U : Set ℝ) (h d : ℝ → ℝ) (δ x : ℝ) : ℝ :=
  (setWeight h d δ (connectedComponentIn U x)).toReal

noncomputable def leftAverage (U : Set ℝ) (k : ℝ → ℝ) (x y : ℝ) : ℝ :=
  (k (sInf (connectedComponentIn U x)-y)+k (sSup (connectedComponentIn U x)-y))/2

noncomputable def rightAverage (V : Set ℝ) (k : ℝ → ℝ) (x y : ℝ) : ℝ :=
  (k (x-sInf (connectedComponentIn V y))+k (x-sSup (connectedComponentIn V y)))/2

end HenonLaneEmden.LayerPressure
end LayerPressure

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.Endpoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uP uP2 uP3 uP4 uP5 uP6 uP7 uP8

section Endpoints

open Set MeasureTheory Filter Topology
open scoped ENNReal
open Classical
namespace HenonLaneEmden.LineComponents

/-- Relative endpoints are chosen by measurable rational exits. On the only
components whose weight is positive they are the genuine finite endpoints. -/
noncomputable def lowerEndpoint {P : Type uP} (U : Set (P × ℝ)) (p : P × ℝ) : ℝ :=
  p.2 - (backwardExit (relativeLayer U) p).toReal
noncomputable def upperEndpoint {P : Type uP2} (U : Set (P × ℝ)) (p : P × ℝ) : ℝ :=
  p.2 + (forwardExit (relativeLayer U) p).toReal

end HenonLaneEmden.LineComponents
end Endpoints

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.SpatialEndpoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section SpatialEndpoints

open MeasureTheory Set Metric
noncomputable section
namespace HenonLaneEmden.SpatialComponents
open Cutoff AdaptiveCap LineComponents
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

def lowerOffset (f : E → ℝ) (p : sphere (0:E) 1 × (E × ℝ)) : ℝ :=
  -(backwardExit (lineLayer f) p).toReal
def upperOffset (f : E → ℝ) (p : sphere (0:E) 1 × (E × ℝ)) : ℝ :=
  (forwardExit (lineLayer f) p).toReal
def lowerPoint (f : E → ℝ) (p : sphere (0:E) 1 × (E × ℝ)) : E :=
  p.2.1+lowerOffset f p • p.1.1
def upperPoint (f : E → ℝ) (p : sphere (0:E) 1 × (E × ℝ)) : E :=
  p.2.1+upperOffset f p • p.1.1

end HenonLaneEmden.SpatialComponents
end
end SpatialEndpoints

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.SourceEndpoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section SourceEndpoints

open MeasureTheory Set Metric
noncomputable section
namespace HenonLaneEmden.SpatialComponents
open Cutoff AdaptiveCap

 def endpointConstant (q B : ℝ) : ℝ := 2*(|-B/q| *2^|-B/q-1| *2^|-B/q|)

def endpointAverage {n : ℕ} (u : Space n → ℝ) (f : Space n → ℝ)
    (z : sphere (0:Space n) 1 × (Space n × ℝ)) : ℝ :=
  (u (lowerPoint f z)+u (upperPoint f z))/2

end HenonLaneEmden.SpatialComponents
end
end SourceEndpoints

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.Tonelli
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section Tonelli

open MeasureTheory Set Function
open scoped ENNReal
namespace HenonLaneEmden.LayerTonelli

variable {E : Type uE} [MeasurableSpace E]

/-- The literal positive source subgraph; no integrability is implicit. -/
def sourceSubgraph (f : E → ℝ) : Set (E × ℝ) := {z | 0 < z.2 ∧ z.2 < f z.1}

noncomputable def layerMeasure (μ : Measure E) (f : E → ℝ) : Measure (E × ℝ) :=
  (μ.prod volume).restrict (sourceSubgraph f)

instance layerMeasure_sfinite (μ : Measure E) [SFinite μ] (f : E → ℝ) :
    SFinite (layerMeasure μ f) := inferInstanceAs (SFinite ((μ.prod volume).restrict _))

/-- Newton potentials are kept as nonnegative extended integrals until their
finiteness has separately been supplied by the PDE. -/
noncomputable def potential (μ : Measure E) (k : E × E → ℝ≥0∞) (g : E → ℝ) (x : E) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (g y)*k (x,y) ∂μ

end HenonLaneEmden.LayerTonelli
end Tonelli

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.LayerSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uZ uA uB uC uA2 uB2 uC2 uA3 uB3 uC3

section LayerSplit

open MeasureTheory Set
open scoped ENNReal
namespace HenonLaneEmden.LayerTonelli

variable {Z : Type uZ} [MeasurableSpace Z]

def tripleSwap {A : Type uA} {B : Type uB} {C : Type uC} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] :
    (A × B) × C ≃ᵐ (A × C) × B :=
  MeasurableEquiv.prodAssoc.trans
    ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl A) MeasurableEquiv.prodComm).trans
      MeasurableEquiv.prodAssoc.symm)

@[simp] lemma tripleSwap_apply {A : Type uA2} {B : Type uB2} {C : Type uC2} [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] (x : (A × B) × C) :
    tripleSwap x = ((x.1.1,x.2),x.1.2) := rfl

def parameterLayer (f : Z × ℝ → ℝ) : Set ((Z × ℝ) × ℝ) :=
  {z | 0 < z.1.2 ∧ z.1.2 < f (z.1.1,z.2)}

noncomputable def parameterLayerMeasure (μ : Measure Z) (f : Z × ℝ → ℝ) :
    Measure ((Z × ℝ) × ℝ) :=
  ((μ.prod volume).prod volume).restrict (parameterLayer f)

instance parameterLayerMeasure_sfinite (μ : Measure Z) [SFinite μ] (f : Z × ℝ → ℝ) :
    SFinite (parameterLayerMeasure μ f) := inferInstanceAs (SFinite (Measure.restrict _ _))

end HenonLaneEmden.LayerTonelli
end LayerSplit

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.LayerAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uZ

section LayerAssembly

open MeasureTheory Set
open scoped ENNReal
namespace HenonLaneEmden.LayerPressure
open LineComponents IntervalGeometry LayerTonelli

variable {Z : Type uZ} [NormedAddCommGroup Z] [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]


noncomputable def sourceWeight (f h d : Z × ℝ → ℝ) (δ : ℝ) (a : (Z × ℝ) × ℝ) : ℝ :=
  lineWeight {s | ((a.1.1,a.2),s) ∈ parameterLayer f} (fun s => h (a.1.1,s))
    (fun s => d (a.1.1,s)) δ a.1.2

noncomputable def sourceLower (f : Z × ℝ → ℝ) (a : (Z × ℝ) × ℝ) : Z × ℝ :=
  (a.1.1,lowerEndpoint (parameterLayer f) ((a.1.1,a.2),a.1.2))
noncomputable def sourceUpper (f : Z × ℝ → ℝ) (a : (Z × ℝ) × ℝ) : Z × ℝ :=
  (a.1.1,upperEndpoint (parameterLayer f) ((a.1.1,a.2),a.1.2))

noncomputable def splitKernel (n : ℕ) (C : ℝ) (z : (Z × ℝ) × (Z × ℝ)) : ℝ :=
  kernel n ‖z.1.1-z.2.1‖ C (z.1.2-z.2.2)
noncomputable def splitDirection (z : (Z × ℝ) × (Z × ℝ)) : ℝ :=
  (z.1.2-z.2.2)^2/(‖z.1.1-z.2.1‖^2+(z.1.2-z.2.2)^2)

noncomputable def pairLeft (n : ℕ) (C : ℝ) (f g h d : Z × ℝ → ℝ) (δ : ℝ)
    (z : ((Z × ℝ) × ℝ) × ((Z × ℝ) × ℝ)) : ℝ :=
  (sourceWeight f h d δ z.1+sourceWeight g h d δ z.2)*splitKernel n C (z.1.1,z.2.1)

noncomputable def pairRight (n : ℕ) (C : ℝ) (f g h d : Z × ℝ → ℝ) (δ : ℝ)
    (z : ((Z × ℝ) × ℝ) × ((Z × ℝ) × ℝ)) : ℝ :=
  sourceWeight f h d δ z.1 *
    ((splitKernel n C (sourceLower f z.1,z.2.1)+splitKernel n C (sourceUpper f z.1,z.2.1))/2) +
  sourceWeight g h d δ z.2 *
    ((splitKernel n C (z.1.1,sourceLower g z.2)+splitKernel n C (z.1.1,sourceUpper g z.2))/2) +
  (((n:ℝ)-2)*h z.1.1*splitDirection (z.1.1,z.2.1)+
    |sourceWeight f h d δ z.1-sourceWeight g h d δ z.2|)*splitKernel n C (z.1.1,z.2.1)

end HenonLaneEmden.LayerPressure
end LayerAssembly

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.UniformBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section UniformBounds

open MeasureTheory Set Filter
open scoped ENNReal
namespace HenonLaneEmden.UniformTail

variable {E : Type uE} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]


noncomputable def tailNumber (C a s : ℝ) : ℝ :=
  2^a*(C*2^s*8^(s-a)/(1-2^(s-a)))

end HenonLaneEmden.UniformTail

namespace HenonLaneEmden
open UniformTail

noncomputable def sourceMeasure {n : ℕ} (u : Space n → ℝ) (q B : ℝ) : Measure (Space n) :=
  volume.withDensity (fun x => ENNReal.ofReal (source u q B x))


instance sourceMeasure_sigmaFinite {n : ℕ} (u : Space n → ℝ) (q B : ℝ) :
    SigmaFinite (sourceMeasure u q B) := by unfold sourceMeasure; infer_instance

noncomputable def kernelMass (n : ℕ) : ℝ :=
  ∫ x in Metric.ball (0:Space n) 12, ‖x‖^(2-(n:ℝ))

noncomputable def uniformTailConstant (n : ℕ) (p q A B : ℝ) : ℝ :=
  tailNumber (sourceConstant n p q A B) ((n:ℝ)-2) ((n:ℝ)-2-alpha p q A B)

noncomputable def uniformMassConstant (n : ℕ) (p q A B : ℝ) : ℝ :=
  (kernelMass n*(sourceConstant n p q A B*8^((n:ℝ)-2-alpha p q A B)) +
    uniformTailConstant n p q A B * (volume (Metric.ball (0:Space n) 4)).toReal) / newtonDenom n

end HenonLaneEmden
end UniformBounds

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.Energy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Energy
open MeasureTheory Set Filter Topology Metric
open scoped ENNReal
namespace HenonLaneEmden

noncomputable def energyDensity {n : ℕ} (u : Space n → ℝ) (q B : ℝ) (x : Space n) : ℝ :=
  ‖x‖^B*(u x)^(q+1)

end HenonLaneEmden
end Energy

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.Interaction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Interaction

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden
open LayerTonelli

/-- The Newton kernel, including its harmless diagonal convention. -/
def newtonKernel (n : ℕ) (z : Space n × Space n) : ℝ :=
  (newtonDenom n)⁻¹*‖z.1-z.2‖^(2-(n:ℝ))

@[fun_prop] lemma measurable_newtonKernel (n : ℕ) : Measurable (newtonKernel n) := by
  unfold newtonKernel; fun_prop

def interaction {n : ℕ} (f g : Space n → ℝ) : Measure (Space n × Space n) :=
  (volume.prod volume).withDensity (fun z => ENNReal.ofReal (f z.1)*ENNReal.ofReal (g z.2)*
    ENNReal.ofReal (newtonKernel n z))

instance interaction_sigmaFinite {n : ℕ} (f g : Space n → ℝ) : SigmaFinite (interaction f g) := by
  unfold interaction
  apply SigmaFinite.withDensity_of_ne_top
  filter_upwards [] with z
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top

end HenonLaneEmden
end
end Interaction

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.SpatialPressure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX uY uX2 uY2 uX3 uY3 uX4 uY4 uE

section SpatialPressure

open MeasureTheory Set Metric
open scoped ENNReal InnerProductSpace
noncomputable section
namespace HenonLaneEmden.SpatialComponents
open Cutoff AdaptiveCap LineComponents LineCoordinates LayerTonelli
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

def coordinateLayerEquiv (e : sphere (0:E) 1) : ((transverse e × ℝ) × ℝ) ≃ᵐ (E × ℝ) :=
  MeasurableEquiv.prodCongr (measurableEquiv e) (MeasurableEquiv.refl ℝ)

end HenonLaneEmden.SpatialComponents
end
end SpatialPressure

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.PairPressure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uE2 uE3 uE4

section PairPressure

open MeasureTheory Set Metric
open scoped ENNReal InnerProductSpace
noncomputable section
namespace HenonLaneEmden
open LineCoordinates

def directionalFactor {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : sphere (0:E) 1) (z : E × E) : ℝ :=
  (inner ℝ (e:E) (z.1-z.2))^2/‖z.1-z.2‖^2

@[fun_prop] lemma measurable_directionalFactor {E : Type uE2} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] (e : sphere (0:E) 1) : Measurable (directionalFactor e) := by
  unfold directionalFactor; fun_prop

namespace SpatialComponents
open Cutoff AdaptiveCap LineComponents LayerTonelli

def spatialPairLeft {n : ℕ} (f g : Space n → ℝ) (κ δ : ℝ) (e : sphere (0:Space n) 1)
    (z : (Space n × ℝ) × (Space n × ℝ)) : ℝ :=
  (lineWeight volume f κ δ (e,z.1)+lineWeight volume g κ δ (e,z.2))*newtonKernel n (z.1.1,z.2.1)

def spatialPairRight {n : ℕ} (f g : Space n → ℝ) (κ δ : ℝ) (e : sphere (0:Space n) 1)
    (z : (Space n × ℝ) × (Space n × ℝ)) : ℝ :=
  lineWeight volume f κ δ (e,z.1)*
    ((newtonKernel n (lowerPoint f (e,z.1),z.2.1)+newtonKernel n (upperPoint f (e,z.1),z.2.1))/2)+
  lineWeight volume g κ δ (e,z.2)*
    ((newtonKernel n (z.1.1,lowerPoint g (e,z.2))+newtonKernel n (z.1.1,upperPoint g (e,z.2)))/2)+
  (((n:ℝ)-2)*weight volume κ e z.1.1*directionalFactor e (z.1.1,z.2.1)+
    |lineWeight volume f κ δ (e,z.1)-lineWeight volume g κ δ (e,z.2)|)*newtonKernel n (z.1.1,z.2.1)

end SpatialComponents
end HenonLaneEmden
end
end PairPressure

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.PairRecovery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section PairRecovery

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden.SpatialComponents
open Cutoff AdaptiveCap LayerTonelli

def positionIntegral {n : ℕ} (u f : Space n → ℝ) (κ δ : ℝ) (e : sphere (0:Space n) 1) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (lineWeight volume f κ δ (e,z)*u z.1) ∂layerMeasure volume f

def endpointIntegral {n : ℕ} (u f : Space n → ℝ) (κ δ : ℝ) (e : sphere (0:Space n) 1) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (lineWeight volume f κ δ (e,z)*endpointAverage u f (e,z)) ∂layerMeasure volume f

def lossIntegral {n : ℕ} (u f : Space n → ℝ) (κ δ : ℝ) (e : sphere (0:Space n) 1) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal ((weight volume κ e z.1-lineWeight volume f κ δ (e,z))*u z.1) ∂layerMeasure volume f

def capPressureIntegral {n : ℕ} (f g : Space n → ℝ) (κ : ℝ) (e : sphere (0:Space n) 1) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (((n:ℝ)-2)*weight volume κ e z.1*directionalFactor e z) ∂interaction f g

def pairMismatchIntegral {n : ℕ} (f g : Space n → ℝ) (κ δ : ℝ) (e : sphere (0:Space n) 1) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (|lineWeight volume f κ δ (e,z.1)-lineWeight volume g κ δ (e,z.2)| *
    newtonKernel n (z.1.1,z.2.1)) ∂(layerMeasure volume f).prod (layerMeasure volume g)

def capMismatchIntegral {n : ℕ} (f g : Space n → ℝ) (κ : ℝ) (e : sphere (0:Space n) 1) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (|weight volume κ e z.1-weight volume κ e z.2|) ∂interaction f g

end HenonLaneEmden.SpatialComponents
end
end PairRecovery

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.RootRecovery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section RootRecovery

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden.SpatialComponents
open Cutoff AdaptiveCap LayerTonelli

def sourceRoot {n : ℕ} (q B : ℝ) (z : Space n × ℝ) : ℝ := (z.2/‖z.1‖^B)^(1/q)
@[fun_prop] lemma measurable_sourceRoot (n : ℕ) (q B : ℝ) : Measurable (sourceRoot (n:=n) q B) := by
  unfold sourceRoot; fun_prop

end HenonLaneEmden.SpatialComponents
end
end RootRecovery

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.WeightedEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section WeightedEnergy

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden
open Cutoff AdaptiveCap

def weightedEnergy {n : ℕ} (χ u : Space n → ℝ) (q B : ℝ) : ℝ :=
  ∫ x, χ x*source u q B x*u x

def weightedEnergyN {n : ℕ} (χ u : Space n → ℝ) (q B : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (χ x*source u q B x*u x)

end HenonLaneEmden
end
end WeightedEnergy

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.AngularIntegration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uΩ

section AngularIntegration

open MeasureTheory Set Metric
noncomputable section
namespace HenonLaneEmden.Angular
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  (μ : Measure E) [μ.IsAddHaarMeasure]
open LineComponents

def rayConstant (n : ℕ) : ℝ := 2^(n+1)*(n:ℝ)

end HenonLaneEmden.Angular

end
end AngularIntegration

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.LayerIntegration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section LayerIntegration

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden.SpatialComponents
open Cutoff AdaptiveCap LineComponents Angular

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

def averagedLoss (f : E → ℝ) (κ δ : ℝ) (z : E × ℝ) : ℝ :=
  ∫ e : sphere (0:E) 1, weight μ κ e z.1-lineWeight μ f κ δ (e,z) ∂μ.toSphere

end HenonLaneEmden.SpatialComponents
end
end LayerIntegration

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.GlobalLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section GlobalLoss

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden.SpatialComponents
open Cutoff AdaptiveCap LineComponents Angular LayerTonelli
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

def lossCoefficient (κ δ M P : ℝ) : ℝ :=
  oscillationConstant μ κ*δ*μ.toSphere.real univ+
    (boundConstant μ κ*rayConstant (Module.finrank ℝ E)*M)/δ^(Module.finrank ℝ E)/P

def lowLevelConstant (n : ℕ) : ℝ := 6*(N n:ℝ)*3^(N n-1)

end HenonLaneEmden.SpatialComponents
end
end GlobalLoss

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.RadialGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uE2 uE3 uE4 uE5

section RadialGeometry

open MeasureTheory Set Metric NormedSpace
open scoped ENNReal InnerProductSpace
noncomputable section
namespace HenonLaneEmden
open Cutoff AdaptiveCap CapWeights

def radialFactor {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (z : E × E) : ℝ :=
  (inner ℝ z.1 (z.1-z.2))^2/(‖z.1‖^2*‖z.1-z.2‖^2)

def fluxFactor {E : Type uE2} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (n : ℕ) (z : E × E) : ℝ :=
  inner ℝ (z.1-z.2) (X n z.1-X n z.2)/‖z.1-z.2‖^2

end HenonLaneEmden
end
end RadialGeometry

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.NearLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uE2

section NearLocalization

open Set Metric
open scoped InnerProductSpace
noncomputable section
namespace HenonLaneEmden
open Cutoff AdaptiveCap

@[fun_prop] lemma measurable_radialFactor (n : ℕ) : Measurable (radialFactor : Space n × Space n → ℝ) := by
  unfold radialFactor; fun_prop

def pairGap {n : ℕ} (z : Space n × Space n) : ℝ := max (d z.1) (d z.2)
def localError {n : ℕ} (z : Space n × Space n) : ℝ :=
  |fluxFactor n z-eta n z.1+w n z.1*radialFactor z|+|eta n z.1-eta n z.2|
def closeConstant (n : ℕ) : ℝ := (2*secondConstant n+4*derivativeConstant n)*2^(N n)

end HenonLaneEmden
end
end NearLocalization

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.FarInteraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section FarInteraction

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden
open Cutoff

def farWeight {n : ℕ} (δ j : ℝ) (z : Space n × Space n) : ℝ :=
  if 0 < d z.1 ∧ δ*d z.1^(m n) ≤ ‖z.1-z.2‖ then d z.1^j else 0

def truncatedConstant (n : ℕ) (p q A B : ℝ) : ℝ :=
  max ((newtonDenom n)⁻¹*(sourceConstant n p q A B*8^((n:ℝ)-2-alpha p q A B)+
    uniformTailConstant n p q A B)) 0

def farConstant (n : ℕ) (p q A B δ : ℝ) : ℝ :=
  truncatedConstant n p q A B*δ^(2-(n:ℝ))*
    max (sourceConstant n q p B A*2^((n:ℝ)-2-alpha q p B A)) 0

end HenonLaneEmden
end
end FarInteraction

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.FarLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section FarLocalization

open MeasureTheory Set Metric
open scoped InnerProductSpace
noncomputable section
namespace HenonLaneEmden
open Cutoff AdaptiveCap

def farLocalConstant (n : ℕ) : ℝ := 2*3^(N n)+2*derivativeConstant n

end HenonLaneEmden
end
end FarLocalization

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.Gradients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uE2 uE3 uE4 uE5 uE6

section Gradients
open Set Filter Topology MeasureTheory MeasureTheory.Measure
open scoped RealInnerProductSpace ContDiff ENNReal Convolution Pointwise
noncomputable section
open HenonLaneEmden.WeakPDE HenonLaneEmden.SphereCalculus

namespace HenonLaneEmden.WeakPDE
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

noncomputable def kernelDir (e x : E) : ℝ :=
  (2-(Module.finrank ℝ E:ℝ))*‖x‖^(-(Module.finrank ℝ E:ℝ))*⟪x,e⟫

end HenonLaneEmden.WeakPDE

end
end Gradients

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.RadialJoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section RadialJoint

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal InnerProductSpace
noncomputable section
namespace HenonLaneEmden
open WeakPDE Cutoff

@[fun_prop] lemma measurable_joint_kernelDir (n : ℕ) :
    Measurable (fun z : Space n × Space n => kernelDir z.1 (z.1-z.2)) := by
  unfold kernelDir
  exact (measurable_const.mul ((measurable_fst.sub measurable_snd).norm.pow_const _)).mul (by fun_prop)

end HenonLaneEmden
end
end RadialJoint

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.LocalizationIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section LocalizationIntegral

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden
open Cutoff

def localFarSum {n : ℕ} (δ : ℝ) (z : Space n × Space n) : ℝ :=
  farWeight δ (N n-1:ℕ) z+δ⁻¹*farWeight δ ((N n:ℝ)-(m n:ℝ)) z+
    farWeight δ (N n-1:ℕ) z.swap+δ⁻¹*farWeight δ ((N n:ℝ)-(m n:ℝ)) z.swap

def localizationConstant (n : ℕ) (p q A B δ : ℝ) : ℝ :=
  farLocalConstant n*(1+δ⁻¹)*(farConstant n p q A B δ+farConstant n q p B A δ)

end HenonLaneEmden
end
end LocalizationIntegral

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.AngularBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section AngularBounds

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden
open Cutoff AdaptiveCap SpatialComponents

def radialPressure {n : ℕ} (f g : Space n → ℝ) : ℝ :=
  ((n:ℝ)-2)*(∫ z : Space n × Space n, w n z.1*radialFactor z ∂interaction f g)

end HenonLaneEmden
end
end AngularBounds

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.AngularMeasurability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section AngularMeasurability

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden
open Cutoff AdaptiveCap SpatialComponents LayerTonelli

def sphereMass (n : ℕ) : ℝ := (volume : Measure (Space n)).toSphere.real univ

end HenonLaneEmden
end
end AngularMeasurability

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.AngularLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section AngularLoss

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden
open Cutoff AdaptiveCap SpatialComponents LayerTonelli

def sourceBallConstant (n : ℕ) (p q A B : ℝ) : ℝ :=
  max (sourceConstant n p q A B*4^((n:ℝ)-2-alpha p q A B)) 0+
    max (sourceConstant n q p B A*4^((n:ℝ)-2-alpha q p B A)) 0

end HenonLaneEmden
end
end AngularLoss

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.PressureEstimate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section PressureEstimate

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden
open Cutoff AdaptiveCap SpatialComponents LayerTonelli Angular

def pressureGeomCoefficient (n : ℕ) : ℝ := 12*(N n:ℝ)*((n:ℝ)-2)
def pressureSmallCoefficient (n : ℕ) (p q A B κ : ℝ) : ℝ :=
  3*sphereMass n*oscillationConstant (volume : Measure (Space n)) κ+
    6*(N n:ℝ)*(endpointConstant q B+endpointConstant p A)
def pressureHighCoefficient (n : ℕ) (p q A B κ δ : ℝ) : ℝ :=
  2*(boundConstant (volume : Measure (Space n)) κ*rayConstant n*sourceBallConstant n p q A B)/δ^n
def pressureConstant (n : ℕ) (p q A B κ δ P : ℝ) : ℝ :=
  sphereMass n*boundConstant (volume : Measure (Space n)) κ*
    (farConstant n p q A B δ+farConstant n q p B A δ)+
  2*lowLevelConstant n*P*(max (uniformMassConstant n p q A B) 0+max (uniformMassConstant n q p B A) 0)

end HenonLaneEmden
end
end PressureEstimate

end OAI
end

section
-- module Solutions.OAIQW_HenonLaneEmden.RelativeLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section RelativeLocalization

open MeasureTheory Set Metric
noncomputable section
namespace HenonLaneEmden
open Cutoff

def localQ {n : ℕ} (f g : Space n → ℝ) : ℝ :=
  ∫ z : Space n × Space n, fluxFactor n z-eta n z.1+w n z.1*radialFactor z ∂interaction f g

end HenonLaneEmden
end
end RelativeLocalization

end OAI
end


