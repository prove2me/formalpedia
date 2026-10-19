-- Prove2me | Definitions.Def_OAIQWGP000
-- name    : OAIQWGP000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-19T00:18:02.236449+00:00
-- url     : https://prove2.me/theorems/5896b56f-42fa-4e69-bdc0-63db613f48cf
-- title:
--   OpenAI Gaussian propeller split: definitions bundle
-- statement:
--   The definitions bundle of the split of OpenAI's proof of the Gaussian propeller bound (`OAI.GaussianPropeller.all_partitions`). It holds OpenAI's Lean definitions and structures from the modules listed below of `lean/OAI/Probability/GaussianPropeller` (OpenAI, *The Gaussian propeller bound in every dimension*, OpenAI Math Release, September 24, 2026, result family 096, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a. Examples are the standard normal density and distribution function `Quantile.φ`, `Quantile.Φ` and the quantile function `Quantile.q`; the cone probabilities `EhrhardCone.cone`, `EhrhardCone.shifted`, `EhrhardCone.prob`; the one-dimensional tail `OneCell.density`, `OneCell.tail` and the functions `ProbabilityBounds.p`, `ProbabilityBounds.loss`; the optimality notions `Reduction.Optimal`, `Reduction.MinimalOptimal`, `Reduction.activeCount`; and the structure `Reduction.Configuration`. It also contains the lemmas those definitions use in their bodies. Two port edits for this Mathlib fall in the bundle: `Set.orderIsoOfEq` is `OrderIso.setCongr` here (in `Quantile.cdfIso`), and in one `convert … using 1` step the closer now runs on every goal (`<;> first | rfl | …`).
--
--   The definitions of the published statement (`Space`, `gaussian`, `IsPartition`, `centroid`, `value`, `coord`, `propeller`, `AllPartitions`) are not repeated: the bundle imports them from the published bundle `Def_GaussianPropeller`. It imports no other bundle.
--
--   Modules: `Moments.lean`, `Dual.lean`, `Deletion.lean`, `Translation.lean`, `HeatConvolution.lean`, `Quantile.lean`, `QuantileCalculus.lean`, `HeatMaximum.lean`, `SmoothedConcavity.lean`, `SoftMinimum.lean`, `ConeConcavity.lean`, `OneCell.lean`, `Mills.lean`, `Taylor.lean`, `ProbabilityBounds.lean`, `Attainment.lean`, `PairIntegral.lean`, `ResidualBounds.lean`, `Polar.lean`, `CapIntegral.lean`, `Coordinates.lean`, `CapBounds.lean`, `CapNumeric.lean`, `Geometry.lean`, `QuarticCertificates.lean`, `CapCertificates.lean`, `Scalar.lean`, `Configuration.lean`.
--
--   The theorems that the definitions do not need are proved in the eight solutions of this split. Three prove named results published as standalone statements: the concavity of the Gaussian quantile of shifted cone probabilities (an Ehrhard-type inequality), and two classical bounds on Mills' ratio. Four prove intermediate statements of OpenAI's argument, and the last proves `OAI.GaussianPropeller.all_partitions` from them. The proofs use two published general results instead of re-proving them: Gaussian integration by parts (`HighDimProb.RandomProcesses.gaussian_linear_integration_by_parts`) and the Cameron–Martin density formula (`HairerSPDE.map_add_eq_withDensity`). The split exists because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, The Gaussian propeller bound in every dimension, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 096; Apache License 2.0); definitions carved from lean/OAI/Probability/GaussianPropeller at commit adc7f12

import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_HairerSPDE_CameronMartin

section
-- module Solutions.OAIQW_GaussianPropeller.Moments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uF

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace GaussianPropeller

open scoped RealInnerProductSpace

@[simp] theorem centroid_empty (d : ℕ) : centroid (∅ : Set (Space d)) = 0 := by
  simp [centroid]

end GaussianPropeller

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.Dual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace GaussianPropeller
open scoped RealInnerProductSpace

namespace Reduction

abbrev Tuple (d k : ℕ) := PiLp 2 (fun _ : Fin k => Space d)

variable {d k : ℕ} [NeZero k]

noncomputable def scoreMax (v : Fin k → Space d) (x : Space d) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => ⟪v i, x⟫)

noncomputable def width (v : Tuple d k) : ℝ := ∫ x, scoreMax v.ofLp x ∂gaussian d

def scoreCell (v : Fin k → Space d) (i : Fin k) : Set (Space d) :=
  {x | (∀ j, ⟪v j, x⟫ ≤ ⟪v i, x⟫) ∧ (∀ j, j < i → ⟪v j, x⟫ < ⟪v i, x⟫)}

noncomputable def moments (A : Fin k → Set (Space d)) : Tuple d k :=
  WithLp.toLp 2 (fun i => centroid (A i))

def Optimal (A : Fin k → Set (Space d)) : Prop :=
  IsPartition A ∧ ∀ B : Fin k → Set (Space d), IsPartition B → value B ≤ value A

noncomputable def activeLabels (A : Fin k → Set (Space d)) : Finset (Fin k) :=
  Finset.univ.filter (fun i => gaussian d (A i) ≠ 0)

noncomputable def activeCount (A : Fin k → Set (Space d)) : ℕ := (activeLabels A).card

def MinimalOptimal (A : Fin k → Set (Space d)) : Prop :=
  Optimal A ∧ ∀ B : Fin k → Set (Space d), Optimal B → activeCount A ≤ activeCount B

def merge (A : Fin k → Set (Space d)) (i j : Fin k) (l : Fin k) : Set (Space d) :=
  if l = i then A i ∪ A j else if l = j then ∅ else A l

def closedCell (z : Fin k → Space d) (i : Fin k) : Set (Space d) :=
  {x | ∀ j, ⟪z j, x⟫ ≤ ⟪z i, x⟫}

end Reduction

end GaussianPropeller

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.Deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal

open scoped RealInnerProductSpace

namespace GaussianPropeller.Reduction

variable {d k : ℕ} [NeZero k]

omit [NeZero k] in
lemma erase_univ_nonempty (hk : 2 ≤ k) (i : Fin k) :
    (Finset.univ.erase i).Nonempty := by
  classical
  apply Finset.card_pos.mp
  simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  omega

noncomputable def omittedMax (hk : 2 ≤ k) (z : Fin k → Space d)
    (i : Fin k) (x : Space d) : ℝ :=
  (Finset.univ.erase i).sup' (erase_univ_nonempty hk i) (fun j => ⟪z j,x⟫)

noncomputable def recentered (z : Fin k → Space d) (i : Fin k) : Tuple d k :=
  WithLp.toLp 2 (fun j => if j = i then 0 else z j + ((k:ℝ)-1)⁻¹ • z i)

end GaussianPropeller.Reduction

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.Translation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uX uY uι

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace

namespace GaussianPropeller.Translation

noncomputable def stdDensity {ι : Type uι} [Fintype ι]
    (x : EuclideanSpace ℝ ι) : ℝ := ∏ i, gaussianPDFReal 0 1 (x i)

end GaussianPropeller.Translation

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.HeatConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uV uι

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology

namespace GaussianPropeller.HeatConvolution
variable {ι : Type uι} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "γ" => stdGaussian E

noncomputable def heat {V : Type uV} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : E → V) (t : ℝ) (x : E) : V := ∫ z, F (x+Real.sqrt t • z) ∂γ

end GaussianPropeller.HeatConvolution

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.Quantile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace GaussianPropeller.Quantile

noncomputable def φ (x : ℝ) : ℝ := (Real.sqrt (2*Real.pi))⁻¹ * Real.exp (-x^2/2)
noncomputable def Φ (x : ℝ) : ℝ := ∫ y in Iic x, φ y

lemma φ_pos (x : ℝ) : 0 < φ x := by unfold φ; positivity
lemma φ_neg (x : ℝ) : φ (-x) = φ x := by simp [φ]
lemma integrable_φ : Integrable φ := by
  unfold φ
  have h := integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2)
  simpa only [φ, show ∀ x : ℝ, -x^2/2 = -(1/2:ℝ)*x^2 by intro x; ring] using
    h.const_mul ((Real.sqrt (2*Real.pi))⁻¹)
lemma integral_φ : ∫ x, φ x = 1 := by
  unfold φ
  rw [integral_const_mul]
  simp_rw [show ∀ x : ℝ, -x^2/2 = -(1/2:ℝ)*x^2 by intro x; ring]
  rw [integral_gaussian]
  have hp : Real.pi/(1/2:ℝ) = 2*Real.pi := by ring
  rw [hp, inv_mul_cancel₀ (by positivity)]
lemma hasDerivAt_φ (x : ℝ) : HasDerivAt φ (-x*φ x) x := by
  unfold φ
  convert ((((hasDerivAt_pow 2 x).neg.div_const 2).exp).const_mul
    ((Real.sqrt (2*Real.pi))⁻¹)) using 1 <;> first | rfl | ring1 | (norm_num <;> ring1)
lemma continuous_φ : Continuous φ := by exact continuous_iff_continuousAt.mpr fun x =>
  (hasDerivAt_φ x).continuousAt
lemma hasDerivAt_Φ (x : ℝ) : HasDerivAt Φ (φ x) x := by
  have heq : Φ = fun a => Φ 0 + ∫ t in (0:ℝ)..a, φ t := by
    funext a
    have hi := intervalIntegral.integral_Iic_sub_Iic
      (a := 0) (b := a) integrable_φ.integrableOn integrable_φ.integrableOn
    change Φ a-Φ 0 = _ at hi
    linarith only [hi]
  rw [heq]
  exact (intervalIntegral.integral_hasDerivAt_right integrable_φ.intervalIntegrable
    continuous_φ.stronglyMeasurable.stronglyMeasurableAtFilter continuous_φ.continuousAt).const_add _
lemma continuous_Φ : Continuous Φ := continuous_iff_continuousAt.mpr fun x =>
  (hasDerivAt_Φ x).continuousAt
lemma strictMono_Φ : StrictMono Φ := strictMono_of_deriv_pos (fun x => by
    rw [(hasDerivAt_Φ x).deriv]; exact φ_pos x)
lemma Φ_pos (x : ℝ) : 0 < Φ x := by
  apply (setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ (fun x => (φ_pos x).le))
    integrable_φ.integrableOn).mpr
  simp [Function.support, ne_of_gt (φ_pos _)]
lemma Φ_eq_one_sub_tail (x : ℝ) : Φ x = 1 - ∫ y in Ioi x, φ y := by
  have h := integral_add_compl measurableSet_Iic integrable_φ (s := Iic x)
  rw [compl_Iic, integral_φ] at h
  unfold Φ
  linarith only [h]
lemma Φ_neg (x : ℝ) : Φ (-x) = 1-Φ x := by
  have h := integral_comp_neg_Iic (-x) φ
  simp only [φ_neg, neg_neg] at h
  change Φ (-x) = (∫ y in Ioi x, φ y) at h
  rw [h, Φ_eq_one_sub_tail]
  ring
lemma Φ_lt_one (x : ℝ) : Φ x < 1 := by
  have h := Φ_pos (-x)
  rw [Φ_neg] at h
  linarith only [h]
lemma Φ_mem (x : ℝ) : Φ x ∈ Ioo (0:ℝ) 1 := ⟨Φ_pos x, Φ_lt_one x⟩
lemma tendsto_Φ_atTop : Tendsto Φ atTop (𝓝 1) := by
  have ht := tendsto_integral_Ioi_zero (f := φ) (μ := volume) tendsto_id
  convert ht.const_sub 1 using 1
  · exact funext Φ_eq_one_sub_tail
  · norm_num
lemma tendsto_Φ_atBot : Tendsto Φ atBot (𝓝 0) := by
  have ht := tendsto_Φ_atTop.comp tendsto_neg_atBot_atTop
  have hh := ht.const_sub 1
  simpa only [Function.comp_def, Φ_neg, sub_sub_cancel, sub_self] using hh
lemma range_Φ : range Φ = Ioo (0:ℝ) 1 := by
  apply Subset.antisymm
  · rintro _ ⟨x,rfl⟩; exact Φ_mem x
  · have hh := isPreconnected_univ.intermediate_value_Ioo
      (l₁ := atBot) (l₂ := atTop) (by simp) (by simp) continuous_Φ.continuousOn
      tendsto_Φ_atBot tendsto_Φ_atTop
    simpa only [image_univ] using hh

noncomputable def cdfIso : ℝ ≃o Ioo (0:ℝ) 1 :=
  (strictMono_Φ.orderIso Φ).trans (OrderIso.setCongr _ _ range_Φ)
noncomputable def q (p : ℝ) : ℝ :=
  if h : p ∈ Ioo (0:ℝ) 1 then cdfIso.symm ⟨p,h⟩ else 0

noncomputable def I (p : ℝ) : ℝ := φ (q p)
end GaussianPropeller.Quantile

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.QuantileCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uι

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

open scoped RealInnerProductSpace

namespace GaussianPropeller.SmoothCDF
open GaussianPropeller.Quantile
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def grad (f : E → ℝ) (g : E → E) (x : E) : E := φ (f x) • g x
noncomputable def hess (f : E → ℝ) (g : E → E) (K : E → E →L[ℝ] E) (x : E) : E →L[ℝ] E :=
  φ (f x) • K x - (f x*φ (f x)) • ((innerSL ℝ (g x)).smulRight (g x))

end GaussianPropeller.SmoothCDF

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.HeatMaximum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uι

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace

open Set Filter
open scoped Topology RealInnerProductSpace

namespace GaussianPropeller.HeatMaximum

section Spatial
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def deficit (v : E → ℝ) (a b σ : ℝ) (x y : E) : ℝ :=
  v (a • x+b • y)-a*v x-b*v y+σ*(1+a*‖x‖^2+b*‖y‖^2)

end Spatial
end GaussianPropeller.HeatMaximum

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.SmoothedConcavity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace

open scoped NNReal
namespace GaussianPropeller.EhrhardSmooth
open GaussianPropeller.Quantile GaussianPropeller.HeatConvolution
variable {ι : Type uι} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

noncomputable def qheat (f : E → ℝ) (t : ℝ) (x : E) : ℝ := q (heat (fun y => Φ (f y)) t x)

end GaussianPropeller.EhrhardSmooth

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.SoftMinimum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uι

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal

open Set Filter
open scoped Topology RealInnerProductSpace NNReal
namespace GaussianPropeller.SoftMin

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type uι} [Fintype ι] [Nonempty ι]

noncomputable def Z (v : ι → E) (x : E) : ℝ := ∑ i, Real.exp (-⟪v i,x⟫)
noncomputable def weight (v : ι → E) (x : E) (i : ι) : ℝ := Real.exp (-⟪v i,x⟫)/Z v x
noncomputable def value (v : ι → E) (x : E) : ℝ := -Real.log (Z v x)
noncomputable def grad (v : ι → E) (x : E) : E := ∑ i, weight v x i • v i
noncomputable def hess (v : ι → E) (x : E) : E →L[ℝ] E :=
  ∑ i, (weight v x i) • ((innerSL ℝ (grad v x-v i)).smulRight (v i))

end GaussianPropeller.SoftMin

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.ConeConcavity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX uι uκ

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal

namespace GaussianPropeller.EhrhardCone
open GaussianPropeller.Quantile GaussianPropeller.EhrhardSmooth
variable {ι : Type uι} {κ : Type uκ} [Fintype ι] [Fintype κ] [Nonempty κ]
local notation "E" => EuclideanSpace ℝ ι
local notation "γ" => stdGaussian E

def cone (v : κ → E) : Set E := {y | ∀ i, 0 ≤ ⟪v i,y⟫}
def shifted (v : κ → E) (x : E) : Set E := {y | x+y ∈ cone v}
noncomputable def prob (v : κ → E) (x : E) : ℝ := (γ).real (shifted v x)

end GaussianPropeller.EhrhardCone

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.OneCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace

namespace GaussianPropeller.OneCell

noncomputable def Q (x : ℝ) : ℝ := x+x^3/2-x^5/24+x^7/240-x^9/2688+x^11/3456
noncomputable def P (x : ℝ) : ℝ := (398943/1000000:ℝ)*Q x-x^2/2
noncomputable def P' (x : ℝ) : ℝ := (398943/1000000:ℝ)*
  (1+3*x^2/2-5*x^4/24+7*x^6/240-9*x^8/2688+11*x^10/3456)-x
noncomputable def P'' (x : ℝ) : ℝ := (398943/1000000:ℝ)*
  (3*x-5*x^3/6+7*x^5/40-3*x^7/112+55*x^9/1728)-1

noncomputable def density (x : ℝ) : ℝ := Real.exp (-x^2/2)
noncomputable def gaussianConst : ℝ := (Real.sqrt (2*Real.pi))⁻¹
noncomputable def tail (a : ℝ) : ℝ := ∫ x in Ioi a, density x

noncomputable def densityUpper (x : ℝ) : ℝ := 1-x^2/2+x^4/8-x^6/48+x^8/384
noncomputable def densityLower (x : ℝ) : ℝ := 1-x^2/2+x^4/8-x^6/48
noncomputable def densityPrimitive (x : ℝ) : ℝ := x-x^3/6+x^5/40-x^7/336+x^9/3456
noncomputable def densityLowerPrimitive (x : ℝ) : ℝ := x-x^3/6+x^5/40-x^7/336

end GaussianPropeller.OneCell

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.Mills
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace

namespace GaussianPropeller.Mills
open OneCell

noncomputable def barrier (x : ℝ) : ℝ := (3*x+Real.sqrt (x^2+8))/4
noncomputable def barrier' (x : ℝ) : ℝ := (3+x/Real.sqrt (x^2+8))/4

noncomputable def lambda (x : ℝ) : ℝ := density x / tail x
noncomputable def G (x : ℝ) : ℝ := lambda x * (lambda x-x)

end GaussianPropeller.Mills

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.Taylor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace

open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace GaussianPropeller.Taylor
noncomputable def E (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n+1), (-1:ℝ)^k*x^k/(Nat.factorial k)
noncomputable def J (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n+1), (-1:ℝ)^k*x^(2*k+1)/((2:ℝ)^k*(Nat.factorial k)*(2*k+1))

end GaussianPropeller.Taylor

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.ProbabilityBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace GaussianPropeller.ProbabilityBounds
open OneCell Mills Taylor
noncomputable def p (x : ℝ) : ℝ := gaussianConst*tail x

noncomputable def loss (x : ℝ) : ℝ := p x^2*G x

end GaussianPropeller.ProbabilityBounds

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.Attainment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology

namespace GaussianPropeller.Reduction

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

noncomputable def axis0 (d : ℕ) (hd : 2 ≤ d) : Space d :=
  EuclideanSpace.single ⟨0, by omega⟩ 1
noncomputable def axis1 (d : ℕ) (hd : 2 ≤ d) : Space d :=
  EuclideanSpace.single ⟨1, by omega⟩ 1

noncomputable def sectorScores (d : ℕ) (hd : 2 ≤ d) : Tuple d 3 :=
  WithLp.toLp 2 ![(2 * Real.sqrt 3) • axis0 d hd,
    (-Real.sqrt 3) • axis0 d hd + (3 : ℝ) • axis1 d hd,
    (-Real.sqrt 3) • axis0 d hd - (3 : ℝ) • axis1 d hd]

end GaussianPropeller.Reduction

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.PairIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology

open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal

namespace GaussianPropeller.PairIntegral

noncomputable def triangle (s u v : ℝ) : ℝ≥0∞ :=
  if u ≤ s then if v ≤ s then ENNReal.ofReal (max (s+u+v) 0) else 0 else 0

end GaussianPropeller.PairIntegral

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.ResidualBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal

namespace GaussianPropeller.Reduction

open scoped RealInnerProductSpace

variable {d k : ℕ} [NeZero k]

omit [NeZero k] in
@[simp] theorem mem_activeLabels (A : Fin k → Set (Space d)) (i : Fin k) :
    i ∈ activeLabels A ↔ gaussian d (A i) ≠ 0 := by
  classical
  simp [activeLabels]

noncomputable def residualCoefficient (z y : Space d) : ℝ := -⟪z,y⟫ / ‖z‖^2
noncomputable def residualVector (z y : Space d) : Space d := y + residualCoefficient z y • z

end GaussianPropeller.Reduction

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.Polar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal

open Metric

namespace GaussianPropeller.Polar
open Real
noncomputable def radial (n : ℕ) (b : ℝ) : ℝ := ∫ r in Ioi (0:ℝ), r^n * exp (-b*r^2)

end GaussianPropeller.Polar

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.CapIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric

namespace GaussianPropeller.Cap
open OneCell ProbabilityBounds Polar
open scoped Topology

variable {n : ℕ}
abbrev CE (n : ℕ) := EuclideanSpace ℝ (Fin n)

noncomputable def capP (n : ℕ) (a : ℝ) : ℝ := ∫ y : CE n, p (a*‖y‖) ∂stdGaussian (CE n)
noncomputable def capM (n : ℕ) (a : ℝ) : ℝ := gaussianConst * ∫ y : CE n, density (a*‖y‖) ∂stdGaussian (CE n)

end GaussianPropeller.Cap

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.Coordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric

open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal

namespace GaussianPropeller.Coords
abbrev CS (n : ℕ) := EuclideanSpace ℝ (Fin n)

noncomputable def split (n : ℕ) (x : CS (n+1)) : ℝ × CS n :=
  (x 0, WithLp.toLp 2 (fun i => x i.succ))
noncomputable def join (n : ℕ) (y : ℝ × CS n) : CS (n+1) :=
  WithLp.toLp 2 (Fin.cons y.1 y.2.ofLp)

lemma split_join (n : ℕ) (y : ℝ × CS n) : split n (join n y)=y := by
  rcases y with ⟨s,y⟩
  simp [split,join]

lemma join_split (n : ℕ) (x : CS (n+1)) : join n (split n x)=x := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [join,split]

lemma continuous_split (n : ℕ) : Continuous (split n) := by
  unfold split
  apply Continuous.prodMk (by fun_prop)
  exact (PiLp.continuous_toLp 2 _).comp (by fun_prop)

lemma continuous_join (n : ℕ) : Continuous (join n) := by
  unfold join
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp only [Fin.cons_zero, Fin.cons_succ]
  · fun_prop
  · fun_prop

noncomputable def splitEquiv (n : ℕ) : CS (n+1) ≃ᵐ ℝ × CS n where
  toFun := split n
  invFun := join n
  left_inv := join_split n
  right_inv := split_join n
  measurable_toFun := (continuous_split n).measurable
  measurable_invFun := (continuous_join n).measurable

end GaussianPropeller.Coords

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.CapBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal

namespace GaussianPropeller.Cap
open Coords OneCell ProbabilityBounds Polar
open scoped Topology
variable {n : ℕ}

noncomputable def coneCap (n : ℕ) (a : ℝ) : Set (CE (n+1)) :=
  {x | a*‖(split n x).2‖ < x 0}

end GaussianPropeller.Cap

namespace GaussianPropeller.Cap
open OneCell ProbabilityBounds Polar
open scoped Topology

noncomputable def sphereTail (b:ℝ) := ∫ u in b..1, Real.sqrt (1-u^2)

end GaussianPropeller.Cap

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.CapNumeric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal

namespace GaussianPropeller.CapNumeric
open Real Set
noncomputable def Q (t:ℝ) := (4/15:ℝ)-t/35-t^2/504
noncomputable def U (t:ℝ) := (1-t)*t^2*Real.sqrt (2*t)*Q t
noncomputable def R (t:ℝ) := (4/3:ℝ)-31*t/15+67*t^2/280+11*t^3/504

end GaussianPropeller.CapNumeric

namespace GaussianPropeller.Cap
open OneCell ProbabilityBounds Polar CapNumeric

noncomputable def sphereGap (b:ℝ) := ∫ u in b..1, (u-b)*Real.sqrt (1-u^2)

noncomputable def gapPrim (t s:ℝ) := Real.sqrt (2*s)*
    (2*t*s/3-(2/5+t/10)*s^2+(1/14-t/112)*s^3+s^4/144)

end GaussianPropeller.Cap

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.Geometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uι

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal

namespace GaussianPropeller.Geometry

open scoped RealInnerProductSpace

section InnerProduct
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def unitVector (w : E) : E := ‖w‖⁻¹ • w

end InnerProduct

end GaussianPropeller.Geometry

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.QuarticCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal

namespace GaussianPropeller.FourCertificates
open OneCell ProbabilityBounds Mills Taylor

noncomputable def quartic (r:ℝ) := (3/5:ℝ)*r^4+(237/500:ℝ)*r^2+(3679/40000:ℝ)
noncomputable def small (r:ℝ) := (217/500:ℝ)*r+(3/20:ℝ)*r^2
noncomputable def large (r:ℝ) := (13/20:ℝ)*r^2+(9/100:ℝ)

end GaussianPropeller.FourCertificates

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.CapCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal

namespace GaussianPropeller.FourCertificates
noncomputable def affine (r:ℝ) := (108/125:ℝ)*r^2+(143/5000:ℝ)

end GaussianPropeller.FourCertificates

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.Scalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal

namespace GaussianPropeller
namespace Scalar

def charge (A u : ℝ) : ℝ := 0.415 * u - (A - 0.15) * u ^ 2

noncomputable def finalBudget (A k t : ℝ) : ℝ :=
  charge A (Real.sqrt (2.6 * t)) + k * charge A t

noncomputable def smallRoot (A k : ℝ) : ℝ :=
  (0.415 - Real.sqrt (0.415 ^ 2 - 4 * (A - 0.15) * (1 - A) / k)) /
    (2 * (A - 0.15))

noncomputable def threshold (A : ℝ) : ℝ := 0.415 / (A - 0.15)

noncomputable def clipCoeff (A : ℝ) : ℝ := (A - 0.15) * 0.42 / (threshold A + 0.42)

structure Regime (A : ℝ) (k : ℕ) : Prop where
  A_lower : 0.884 ≤ A
  A_upper : A < 1
  k_lower : 2 ≤ k
  root_lower : 0.066 < smallRoot A k
  root_upper : smallRoot A k < 0.12
  root_eq : (k : ℝ) * charge A (smallRoot A k) = 1 - A
  root_cap : 2.6 * smallRoot A k < (threshold A) ^ 2
  root_slope : (A - 0.15) * (0.42 + smallRoot A k) < 0.415
  cap_charge : 1 - A < (k : ℝ) * charge A 0.42
  tail_end_charge : charge A 0.066 ≤ charge A 0.45
  base_charge_pos : 0 < charge A 0.066
  four_margin : 1 - A < clipCoeff A *
      (4 * (threshold A) ^ 2 - 1 + ((k : ℝ) - 1) * 0.066 ^ 2) +
      ((k : ℝ) - 1) * charge A 0.066
  third_margin : 1 - A < charge A 0.23 + (k : ℝ) * charge A 0.066
  final_margin : 1 - A < finalBudget A k 0.066

structure RadiusData (m : ℕ) (A : ℝ) where
  r : ℕ → ℝ
  δ : ℕ → ℝ
  pos : ∀ i < m, 0 < r i
  ordered : AntitoneOn r (Set.Iio m)
  cap : ∀ i < m, r i ≤ 2 / 3
  norm : ∑ i ∈ Finset.range m, r i ^ 2 = 1
  nonneg : ∀ i < m, 0 ≤ δ i
  lower : ∀ i < m, charge A (r i) ≤ δ i
  budget : ∑ i ∈ Finset.range m, δ i = 1 - A

end Scalar

end GaussianPropeller

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.Configuration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal RealInnerProductSpace

namespace GaussianPropeller.Reduction
open OneCell ProbabilityBounds
open scoped RealInnerProductSpace

structure Configuration (d k:ℕ) where
  z : Fin k→Space d
  P : Fin k→ℝ
  zero : ∑ j,z j=0
  norm : ∑ j,‖z j‖^2=1
  pos : ∀ j,z j≠0
  order : Antitone (fun j=>‖z j‖)
  obtuse : Pairwise (fun j l=>⟪z j,z l⟫<0)
  cap : ∀ j,‖z j‖≤2/3
  probability : ∑ j,P j=1
  half : ∀ j,P j≤1/2
  quadratic : ∀ j,(if k=5 then (0.929:ℝ) else 0.884)*‖z j‖^2≤P j
  linear : ∀ j,0.415*‖z j‖+0.15*‖z j‖^2≤P j
  pair : ∀ i j l, i≠j → i≠l →
      ‖residualVector (z i) (z j)‖^2*‖residualVector (z i) (z l)‖^2-
      ⟪residualVector (z i) (z j),residualVector (z i) (z l)⟫^2≤
      (3/Real.pi)^2*‖z i‖^2*(1+residualCoefficient (z i) (z j))^2*
      (1+residualCoefficient (z i) (z l))^2
  cap3 : k=4 → ∀ j,‖z j‖≤(8/3:ℝ)*P j*(1-P j)
  loss4 : k=4 → ∀ j,∃ x≥(0:ℝ),p x=P j ∧
      (9/(8*Real.pi))*‖z j‖^2/(1+Real.sqrt (1-(4/3:ℝ)*‖z j‖^2))≤loss x

end GaussianPropeller.Reduction

end OAI
end


