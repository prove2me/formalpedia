-- Prove2me | Definitions.Def_OAIQWRLC000
-- name    : OAIQWRLC000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-19T01:25:52.40566+00:00
-- url     : https://prove2.me/theorems/9fffb429-1d44-449b-b812-186d9f59b70c
-- title:
--   OpenAI repeated localization split: definitions bundle
-- statement:
--   This is the definitions bundle for the split of OpenAI's proof of `OAI.RepeatedLocalization.repeated_localization`. That theorem concerns adaptive experiments with exact Gaussian observations of an unknown point of a small cube. After $t$ rounds of $N$-way choices there is a valid dyadic disclosure of the unknown whose mutual information is $O((n+1)t)$ and whose expected final localization level is $O(t)$.
--
--   The bundle holds OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Probability/GaussianInformation/Dyadic` and `lean/OAI/Probability/Localization` (OpenAI, *Localization costs and information growth for exact Gaussian observations*, OpenAI Math Release, September 27, 2026, result family 140, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a. Among them are:
--   - the entropy function `xlog` and the information functionals `infoContribution` and `finiteInformation`;
--   - dyadic spread and the block channel;
--   - the information constants;
--   - the history states, posterior channels and refinements of the realization argument.
--
--   The bundle also holds the lemmas that these definitions use in their bodies, and OpenAI's `@[simp]` lemmas about them.
--
--   The definitions of the published statement are not repeated. These are coordinates, cells, Gaussian blocks, rules, disclosures and the experiment laws. The bundle imports them from the published bundle `Def_GaussianInformation`. It imports no other bundle.
--
--   Modules (OpenAI paths): `Dyadic/BoxKernels`, `Dyadic/ChannelEntropy`, `Dyadic/ChannelProducts`, `Dyadic/ChartGeometry`, `Dyadic/ConditionalMoments`, `Dyadic/Entropy`, `Dyadic/GaussianImages`, `Dyadic/GramVolume`, `Dyadic/GridSpread`, `Dyadic/HeavyCells`, `Dyadic/LabelBounds`, `Dyadic/MixtureBounds`, `Dyadic/PosteriorChannels`, `Dyadic/ProjectionMoments`, `Dyadic/ProjectionTests`, `Dyadic/Realization`, `Dyadic/RealizationStep`, `Dyadic/Refinement`, `Dyadic/RefinementCost`, `Dyadic/ReplicaMoments`, `Dyadic/ScoreBounds`, `Dyadic/StateExpectation`, `Dyadic/StateInformation`, `Localization/Cells`, `Localization/Experiment`.
-- source:
--   OpenAI, Localization costs and information growth for exact Gaussian observations, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 140; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Localization-costs-and-information-growth-for-exact-Gaussian-observations-September-27-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability/GaussianInformation/Dyadic and lean/OAI/Probability/Localization at commit adc7f12

import Mathlib
import Definitions.Def_GaussianInformation

section
-- module Solutions.OAIQW_RepeatedLocalization.Compat
namespace OAI
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
end OAICompat434


end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.Localization_Experiment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

lemma continuous_chart (n : ℕ) : Continuous (@chart n) := by
  apply continuous_pi
  intro a
  refine Fin.lastCases ?_ (fun j => ?_) a
  · simp only [chart, Fin.lastCases_last]
    fun_prop
  · simp only [chart, Fin.lastCases_castSucc]
    fun_prop

lemma continuous_exactLabel (n : ℕ) :
    Continuous (fun Xz : GaussianBlock n × Coordinate n => exactLabel Xz.1 Xz.2) := by
  apply continuous_pi
  intro row
  unfold exactLabel
  apply continuous_finsetSum
  intro coordinate _
  exact ((continuous_apply coordinate).comp ((continuous_apply row).comp continuous_fst)).mul
    ((continuous_apply coordinate).comp ((continuous_chart n).comp continuous_snd))

lemma measurable_initialCube (n : ℕ) : MeasurableSet (initialCube n) := by
  apply MeasurableSet.univ_pi
  intro _
  exact measurableSet_Ico

lemma volume_initialCube (n : ℕ) :
    volume (initialCube n) = ENNReal.ofReal ((1 / Real.sqrt n) ^ n) := by
  unfold initialCube
  rw [Real.volume_pi_Ico]
  have hw : 1 / (2 * Real.sqrt n) - -1 / (2 * Real.sqrt n) = 1 / Real.sqrt n := by
    ring
  simp only [hw, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact (ENNReal.ofReal_pow (by positivity) n).symm

lemma volume_initialCube_pos {n : ℕ} (hn : 0 < n) :
    0 < volume (initialCube n) := by
  rw [volume_initialCube]
  exact ENNReal.ofReal_pos.mpr (pow_pos (by positivity) n)

lemma volume_initialCube_ne_top (n : ℕ) : volume (initialCube n) ≠ ∞ := by
  rw [volume_initialCube]
  exact ENNReal.ofReal_ne_top

lemma cubePrior_isProbabilityMeasure {n : ℕ} (hn : 0 < n) :
    IsProbabilityMeasure (cubePrior n) := by
  exact cond_isProbabilityMeasure_of_finite
    (ne_of_gt (volume_initialCube_pos hn)) (volume_initialCube_ne_top n)

instance gaussianBlockLaw_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (gaussianBlockLaw n) := by
  unfold gaussianBlockLaw
  infer_instance

lemma BlockRule.prob_le_one {n N : ℕ} (rule : BlockRule n N)
    (data : GaussianBlock n × Label n) (w : Fin N) : rule.prob data w ≤ 1 := by
  rw [← rule.sum_one data]
  exact Finset.single_le_sum (fun i _ => rule.nonneg data i) (Finset.mem_univ w)

lemma measurable_actualRule {n N : ℕ} (rule : BlockRule n N) (w : Fin N) :
    Measurable (fun Xz : GaussianBlock n × Coordinate n =>
      rule.prob (Xz.1, exactLabel Xz.1 Xz.2) w) :=
  (rule.measurable_prob w).comp
    (measurable_fst.prodMk (continuous_exactLabel n).measurable)

lemma integrable_actualRule {n N : ℕ} (rule : BlockRule n N)
    (z : Coordinate n) (w : Fin N) :
    Integrable (fun X => rule.prob (X, exactLabel X z) w) (gaussianBlockLaw n) := by
  apply (integrable_const (1 : ℝ)).mono'
  · exact ((measurable_actualRule rule w).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun X => by
      rw [Real.norm_eq_abs, abs_of_nonneg (rule.nonneg _ w)]
      exact rule.prob_le_one _ w)

lemma measurable_blockProbability {n N : ℕ} (rule : BlockRule n N) (w : Fin N) :
    Measurable (fun z => blockProbability rule z w) := by
  exact (measurable_actualRule rule w).stronglyMeasurable.integral_prod_left'.measurable

lemma blockProbability_nonneg {n N : ℕ} (rule : BlockRule n N)
    (z : Coordinate n) (w : Fin N) : 0 ≤ blockProbability rule z w := by
  exact integral_nonneg (fun X => rule.nonneg _ w)

lemma blockProbability_sum {n N : ℕ} (rule : BlockRule n N) (z : Coordinate n) :
    ∑ w, blockProbability rule z w = 1 := by
  unfold blockProbability
  rw [← integral_finsetSum _ (fun w _ => integrable_actualRule rule z w)]
  simp [rule.sum_one]

lemma measurable_historyLikelihood {n N t : ℕ} (rules : Rules n N t) (w : History N t) :
    Measurable (fun z => historyLikelihood rules z w) := by
  exact Finset.measurable_prod _ (fun i _ => measurable_blockProbability (rules i (past w i)) (w i))

lemma historyLikelihood_nonneg {n N t : ℕ} (rules : Rules n N t)
    (z : Coordinate n) (w : History N t) : 0 ≤ historyLikelihood rules z w := by
  exact Finset.prod_nonneg (fun i _ => blockProbability_nonneg _ _ _)

end RepeatedLocalization

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.Localization_Cells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

noncomputable def cellWidth (n J : ℕ) : ℝ := 1 / (Real.sqrt n * (2 : ℝ)^J)
noncomputable def cellLower {n : ℕ} (Q : Cell n) (i : Fin n) : ℝ :=
  -1 / (2 * Real.sqrt n) + (Q.2 i : ℝ) / (Real.sqrt n * (2 : ℝ)^Q.1)
noncomputable def cellCenter {n : ℕ} (Q : Cell n) : Coordinate n :=
  fun i => cellLower Q i + cellWidth n Q.1 / 2

lemma cellSet_eq_pi {n : ℕ} (Q : Cell n) :
    cellSet Q = Set.pi univ (fun i => Ico (cellLower Q i) (cellLower Q i + cellWidth n Q.1)) := by
  ext z
  simp only [cellSet, mem_ofPred_eq, mem_pi, mem_univ, true_implies, mem_Ico]
  congr! 3
  simp only [cellLower, cellWidth]
  ring

lemma volume_cellSet {n : ℕ} (Q : Cell n) :
    volume (cellSet Q) = ENNReal.ofReal ((cellWidth n Q.1)^n) := by
  rw [cellSet_eq_pi, Real.volume_pi_Ico]
  simp only [add_sub_cancel_left, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact (ENNReal.ofReal_pow (by unfold cellWidth; positivity) n).symm

lemma cellSet_subset_initialCube {n : ℕ} (hn : 0 < n) (Q : Cell n) :
    cellSet Q ⊆ initialCube n := by
  intro z hz i hi
  have hd : 0 < Real.sqrt (n : ℝ) * (2 : ℝ)^Q.1 := by positivity
  have hidx : (Q.2 i : ℝ) + 1 ≤ (2 : ℝ)^Q.1 := by exact_mod_cast (Q.2 i).isLt
  have hl : 0 ≤ (Q.2 i : ℝ) / (Real.sqrt n * (2 : ℝ)^Q.1) := by positivity
  have hu : ((Q.2 i : ℝ) + 1) / (Real.sqrt n * (2 : ℝ)^Q.1) ≤ 1 / Real.sqrt n := by
    apply (div_le_iff₀ hd).mpr
    have hs : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hn)).ne'
    have he : 1 / Real.sqrt n * (Real.sqrt n * (2 : ℝ)^Q.1) = (2 : ℝ)^Q.1 := by field_simp
    rwa [he]
  have hw : -1 / (2 * Real.sqrt n) + 1 / Real.sqrt n = 1 / (2 * Real.sqrt n) := by ring
  exact ⟨(by linarith [(hz i).1]), (hz i).2.trans_le (by linarith)⟩

lemma cubePrior_cellSet {n : ℕ} (hn : 0 < n) (Q : Cell n) :
    cubePrior n (cellSet Q) = ENNReal.ofReal ((1 / 2 : ℝ)^(n * Q.1)) := by
  unfold cubePrior
  rw [cond_apply (measurable_initialCube n), inter_eq_right.mpr (cellSet_subset_initialCube hn Q),
    volume_initialCube, volume_cellSet]
  have hp : 0 < (1 / Real.sqrt n)^n := by positivity
  rw [← ENNReal.ofReal_inv_of_pos hp, ← ENNReal.ofReal_mul (inv_nonneg.mpr hp.le)]
  congr 1
  unfold cellWidth
  have hs : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hn)).ne'
  simp only [one_div, inv_pow, inv_inv, mul_inv_rev ]
  rw [← mul_pow]
  have hc : Real.sqrt n * (((2 : ℝ)^Q.1)⁻¹ * (Real.sqrt n)⁻¹) = ((2 : ℝ)^Q.1)⁻¹ := by field_simp
  rw [hc, inv_pow, ← pow_mul, Nat.mul_comm Q.1 n]

noncomputable def cellIndex {n : ℕ} (J : ℕ) (z : Coordinate n) : Fin n → Fin (2^J) :=
  fun i => ⟨⌊(z i + 1 / (2 * Real.sqrt n)) * (Real.sqrt n * (2 : ℝ)^J)⌋₊ % 2^J,
    Nat.mod_lt _ (pow_pos (by norm_num) J)⟩

noncomputable def cellAt {n : ℕ} (J : ℕ) (z : Coordinate n) : Cell n := ⟨J, cellIndex J z⟩

noncomputable def childCell {n : ℕ} (Q : Cell n) (l : ℕ) (a : Fin n → Fin (2^l)) : Cell n :=
  ⟨Q.1 + l, fun i => ⟨(Q.2 i).val * 2^l + (a i).val, by
    rw [pow_add]
    have h1 := (Q.2 i).isLt
    have h2 := (a i).isLt
    nlinarith⟩⟩

noncomputable def ancestorCell {n : ℕ} (Q : Cell n) (J : ℕ) (hJ : J ≤ Q.1) : Cell n :=
  ⟨J,fun i => ⟨(Q.2 i).val / 2^(Q.1-J),by
    apply (Nat.div_lt_iff_lt_mul (by positivity : 0 < 2^(Q.1-J))).mpr
    rw [← pow_add,Nat.add_sub_of_le hJ]
    exact (Q.2 i).isLt⟩⟩

lemma cellSet_root (n : ℕ) : cellSet (rootCell n) = initialCube n := by
  ext z
  simp only [cellSet,rootCell,initialCube,Fin.val_zero,Nat.cast_zero,zero_div,add_zero,
    pow_zero,mul_one,zero_add,Set.mem_ofPred_eq,Set.mem_pi,Set.mem_univ,forall_true_left,Set.mem_Ico]
  have he : -1/(2*Real.sqrt n)+1/Real.sqrt n = 1/(2*Real.sqrt n) := by ring
  rw [he]

end RepeatedLocalization

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_GridSpread
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
namespace RepeatedLocalization

def euclideanGridCell {n : ℕ} (base : Fin n → ℝ) (h : ℝ) (a : Fin n → ℤ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ i, base i + h * a i ≤ x i ∧ x i < base i + h * (a i + 1)}

end RepeatedLocalization

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_ChartGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
namespace RepeatedLocalization

noncomputable def eCoordinate {n : ℕ} (z : Coordinate n) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 z
noncomputable def eChart {n : ℕ} (z : Coordinate n) : EuclideanSpace ℝ (Fin (n+1)) :=
  WithLp.toLp 2 (chart z)

noncomputable def firstCoordinates {n : ℕ} (v : EuclideanSpace ℝ (Fin (n+1))) :
    EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => v i.castSucc)

noncomputable def normalizedChart {n : ℕ} (Q : Cell n) (z : Coordinate n) :
    EuclideanSpace ℝ (Fin (n+1)) := (2 : ℝ)^Q.1 • (eChart z - eChart (cellCenter Q))

noncomputable def normalizedGridBase {n : ℕ} (Q : Cell n) : Fin n → ℝ :=
  fun i => (2 : ℝ)^Q.1 * (cellLower Q i - cellCenter Q i)

def DyadicSpread {n : ℕ} (μ : Measure (Coordinate n)) (Q : Cell n) (B : ℝ) : Prop :=
  ∀ (l : ℕ) (R : Cell n), R.1 = Q.1 + l → cellSet R ⊆ cellSet Q →
    μ (cellSet R) ≤ ENNReal.ofReal (B * (2 : ℝ)^(-(n : ℝ)*l/2))

noncomputable def gridConstant : ℝ := 3 * (Real.exp 1 * Real.sqrt Real.pi)
noncomputable def tubeConstant : ℝ := 13 * max 1 gridConstant

end RepeatedLocalization

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_ConditionalMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace RepeatedLocalization
open Metric

noncomputable def tubeWeightConstant (n : ℕ) (B : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (B * tubeConstant^n) ^ (1/2 : ℝ)

end RepeatedLocalization

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_BoxKernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace RepeatedLocalization

noncomputable def closedBox {k : ℕ} (c : Fin k → ℝ) (η : ℝ) : Set (Fin k → ℝ) :=
  {u | ∀ i, |u i-c i| ≤ η}

noncomputable def boxScale (k : ℕ) (η : ℝ) : ℝ≥0∞ := (ENNReal.ofReal ((2*η)^k))⁻¹

noncomputable def boxKernel {k : ℕ} (η : ℝ) (c u : Fin k → ℝ) : ℝ≥0∞ :=
  (closedBox c η).indicator (fun _ => boxScale k η) u

end RepeatedLocalization

open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_GramVolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
namespace RepeatedLocalization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def gramTriangular {q : ℕ} (f : Fin q → E) : Matrix (Fin q) (Fin q) ℝ :=
  fun i j => (if i = j then 1 else 0) +
    (if i < j then ⟪gramSchmidt ℝ f i, f j⟫ / ‖gramSchmidt ℝ f i‖ ^ 2 else 0)

end RepeatedLocalization

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_ReplicaMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
namespace RepeatedLocalization
open Metric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def replicaPlane {q : ℕ} (b : E) (f : Fin q → E) : AffineSubspace ℝ E :=
  AffineSubspace.mk' b (Submodule.span ℝ (range f))

noncomputable def gramInverseProduct {q : ℕ} (k : ℕ) (f : Fin q → E) : ℝ≥0∞ :=
  ∏ i, (ENNReal.ofReal ‖gramSchmidt ℝ f i‖)⁻¹ ^ k

end RepeatedLocalization

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_GaussianImages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace RepeatedLocalization
open Matrix WithLp
open scoped MatrixOrder RealInnerProductSpace

noncomputable def rowMatrix {q d : ℕ} (f : Fin q → EuclideanSpace ℝ (Fin d)) :
    Matrix (Fin q) (Fin d) ℝ := fun i j => f i j

end RepeatedLocalization

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_ProjectionMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace RepeatedLocalization
open Metric Matrix WithLp

noncomputable def gaussianRows (k d : ℕ) : Measure (Fin k → Fin d → ℝ) :=
  Measure.pi (fun _ => Measure.pi (fun _ => gaussianReal 0 1))

noncomputable def projectVector {k d : ℕ} (X : Fin k → Fin d → ℝ)
    (v : EuclideanSpace ℝ (Fin d)) : Fin k → ℝ := fun r => ∑ j, X r j * v j

noncomputable def smoothedProjection {α : Type*} [MeasurableSpace α] {k d : ℕ}
    (μ : Measure α) (a : α → EuclideanSpace ℝ (Fin d)) (η : ℝ)
    (p : (Fin k → Fin d → ℝ) × (Fin k → ℝ)) : ℝ≥0∞ :=
  ∫⁻ z, boxKernel η (projectVector p.1 (a z)) p.2 ∂μ

end RepeatedLocalization

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_MixtureBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace RepeatedLocalization

noncomputable def smoothingWidth (j : ℕ) : ℝ := 1 / ((j:ℝ)+1)

noncomputable def boxAverage {T : Type*} {k : ℕ} (η : ℝ)
    (g : T × (Fin k → ℝ) → ℝ≥0∞) (p : T × (Fin k → ℝ)) : ℝ≥0∞ :=
  ∫⁻ u, boxKernel η p.2 u * g (p.1,u)

noncomputable def mixtureDensity {T E : Type*} [MeasurableSpace E] {k : ℕ}
    (μ : Measure E) (b : T × E → Fin k → ℝ) (η : ℝ) (p : T × (Fin k → ℝ)) : ℝ≥0∞ :=
  ∫⁻ z, boxKernel η (b (p.1,z)) p.2 ∂μ

noncomputable def exactMixtureLaw {T E : Type*} [MeasurableSpace T] [MeasurableSpace E]
    {k : ℕ} (σ : Measure T) (μ : Measure E) (b : T × E → Fin k → ℝ) :
    Measure (T × (Fin k → ℝ)) := (σ.prod μ).map (fun q => (q.1,b q))

end RepeatedLocalization

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_ProjectionTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace RepeatedLocalization

noncomputable def weightedProjectionMoment (n k m : ℕ) (B : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((2:ℝ)^(k*(m-1))) *
    (1 + tubeWeightConstant n B * ENNReal.ofReal ((2:ℝ)^(k+1)))^(m-1)

end RepeatedLocalization

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_Entropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace RepeatedLocalization
noncomputable def xlog (x : ℝ) : ℝ := x * Real.log x

noncomputable def scoreMass {α : Type*} [MeasurableSpace α] (μ : Measure α) (p : α → ℝ) : ℝ :=
  ∫ x, p x ∂μ

noncomputable def infoContribution {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (p : α → ℝ) : ℝ :=
  (∫ x, xlog (p x) ∂μ) - xlog (scoreMass μ p)

end RepeatedLocalization

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_ScoreBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace RepeatedLocalization
noncomputable def finiteInformation {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (μ : Measure α) (p : ι → α → ℝ) : ℝ := ∑ i,infoContribution μ (p i)

end RepeatedLocalization

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_LabelBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace RepeatedLocalization

noncomputable def goodLabels (k : ℕ) : Set (Fin k → ℝ) := {u | ∑ i,(u i)^2 ≤ (16:ℝ)*k}

noncomputable def labelVolumeConstant : ℝ := 4*Real.exp 1*Real.sqrt Real.pi

noncomputable def averagedScores {α β ι : Type*} [MeasurableSpace β]
    (ν : Measure β) (f : β × α → ι → ℝ) (i : ι) (x : α) : ℝ := ∫ y,f (y,x) i ∂ν

noncomputable def goodRegion (k d : ℕ) : Set ((Fin k → Fin d → ℝ) × (Fin k → ℝ)) :=
  Set.univ ×ˢ goodLabels k

noncomputable def blockInformationConstant : ℝ := 2*Real.log (4*tubeConstant*labelVolumeConstant)+3

end RepeatedLocalization

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_HeavyCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace RepeatedLocalization

noncomputable def heavyThreshold (n j : ℕ) : ℝ := (2:ℝ)^(-(n:ℝ)*j/2)

lemma heavyThreshold_pos (n j : ℕ) : 0 < heavyThreshold n j := Real.rpow_pos_of_pos (by norm_num) _

noncomputable def deepHeavyDepth {n : ℕ} (μ : Measure (Coordinate n))
    (Q : Cell n) (D : ℕ) (z : Coordinate n) : ℕ :=
  (Finset.range (D+1)).sup' Finset.nonempty_range_add_one (fun j =>
    if heavyThreshold n j ≤ μ.real (cellSet (cellAt (Q.1+j) z)) then j else 0)

noncomputable def deepHeavyCell {n : ℕ} (μ : Measure (Coordinate n))
    (Q : Cell n) (D : ℕ) (z : Coordinate n) : Cell n := by
  classical
  exact if z ∈ cellSet Q then cellAt (Q.1+deepHeavyDepth μ Q D z) z else Q

lemma heavyThreshold_sq (n j : ℕ) : (heavyThreshold n j)^2 = (1/2:ℝ)^(n*j) := by
  rw [heavyThreshold,← Real.rpow_natCast,← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  have he : (-(n:ℝ)*(j:ℝ)/2)*(2:ℝ) = -(↑(n*j):ℝ) := by push_cast; ring
  norm_num only [Nat.cast_ofNat]
  rw [he,Real.rpow_neg (by norm_num),Real.rpow_natCast]
  simp only [one_div,inv_pow]

end RepeatedLocalization

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_PosteriorChannels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace RepeatedLocalization
noncomputable def scorePosterior {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (p : α → ℝ) : Measure α :=
  μ.withDensity (fun x => ENNReal.ofReal (p x/scoreMass μ p))

structure FiniteChannel (α ι : Type*) [MeasurableSpace α] [Fintype ι] where
  prob : ι → α → ℝ
  measurable : ∀ i,Measurable (prob i)
  nonneg : ∀ i x,0 ≤ prob i x
  total : ∀ x,∑ i,prob i x = 1

namespace FiniteChannel
variable {α ι κ : Type*} [MeasurableSpace α] [Fintype ι] [Fintype κ]

def bind (p : FiniteChannel α ι) (q : ι → FiniteChannel α κ) : FiniteChannel α (ι × κ) where
  prob i x := p.prob i.1 x*(q i.1).prob i.2 x
  measurable i := (p.measurable i.1).mul ((q i.1).measurable i.2)
  nonneg i x := mul_nonneg (p.nonneg i.1 x) ((q i.1).nonneg i.2 x)
  total x := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum,FiniteChannel.total,mul_one]
    exact p.total x

open scoped Classical in
noncomputable def deterministic [MeasurableSpace κ] [MeasurableSingletonClass κ]
    (f : α → κ) (hf : Measurable f) : FiniteChannel α κ where
  prob i x := if f x = i then 1 else 0
  measurable i := measurable_const.piecewise (hf (measurableSet_singleton i)) measurable_const
  nonneg i x := by split_ifs <;> norm_num
  total x := by
    classical
    simp

end FiniteChannel

namespace FiniteChannel
variable {α ι κ : Type*} [MeasurableSpace α] [Fintype ι] [Fintype κ]

open scoped Classical in
noncomputable def coarsen (p : FiniteChannel α ι) (f : ι → κ) : FiniteChannel α κ where
  prob j x := ∑ i,if f i = j then p.prob i x else 0
  measurable j := Finset.measurable_sum _ (fun i _ => by by_cases h : f i = j <;> simp [h,p.measurable])
  nonneg j x := Finset.sum_nonneg (fun i _ => by split_ifs; exact p.nonneg _ _; exact le_refl _)
  total x := by
    classical
    rw [Finset.sum_comm]
    simp [p.total]

end FiniteChannel

end RepeatedLocalization

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_ChannelProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace RepeatedLocalization

namespace FiniteChannel
variable {α ι : Type*} [MeasurableSpace α] [Fintype ι] {κ : ι → Type*} [∀ i,Fintype (κ i)]

def dbind (p : FiniteChannel α ι) (q : ∀ i,FiniteChannel α (κ i)) : FiniteChannel α (Sigma κ) where
  prob i x := p.prob i.1 x*(q i.1).prob i.2 x
  measurable i := (p.measurable i.1).mul ((q i.1).measurable i.2)
  nonneg i x := mul_nonneg (p.nonneg i.1 x) ((q i.1).nonneg i.2 x)
  total x := by
    rw [Fintype.sum_sigma]
    simp_rw [← Finset.mul_sum,FiniteChannel.total,mul_one]
    exact p.total x

end FiniteChannel

end RepeatedLocalization

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_RefinementCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace RepeatedLocalization

noncomputable def depthGeometric (j : ℕ) : ℝ := (1/2:ℝ)^(j+1)

structure HeavyRefinement (n : ℕ) (μ : Measure (Coordinate n)) (Q : Cell n) where
  Index : Type
  [finiteIndex : Fintype Index]
  channel : FiniteChannel (Coordinate n) Index
  cell : Index → Cell n
  B : Index → ℝ
  B_one : ∀ i, 1 ≤ B i
  select : Coordinate n → Index
  select_fiber : ∀ i, MeasurableSet {z | select z = i}
  chosen : ∀ i z, 0 < channel.prob i z → select z = i
  cell_subset : ∀ i, cellSet (cell i) ⊆ cellSet Q
  select_mem : ∀ z ∈ cellSet Q, z ∈ cellSet (cell (select z))
  level_ge : ∀ i,Q.1 ≤ (cell i).1
  support : ∀ i,0 < scoreMass μ (channel.prob i) →
    scorePosterior μ (channel.prob i) (cellSet (cell i)) = 1
  spread : ∀ i,0 < scoreMass μ (channel.prob i) →
    DyadicSpread (scorePosterior μ (channel.prob i)) (cell i) (B i)
  entropy_bound : finiteInformation μ channel.prob ≤
    ((n:ℝ)/2+1)*Real.log 2*(∑ i,scoreMass μ (channel.prob i)*((cell i).1-Q.1:ℕ))+Real.log 2
  concentration_bound : (∑ i,scoreMass μ (channel.prob i)*Real.log (B i)) ≤
    Real.log 2*(∑ i,scoreMass μ (channel.prob i)*((cell i).1-Q.1:ℕ))+Real.log 2+1

attribute [instance] HeavyRefinement.finiteIndex

end RepeatedLocalization

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_ChannelEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace RepeatedLocalization

namespace FiniteChannel
variable {α ι : Type*} [MeasurableSpace α] [Fintype ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

noncomputable def law (p : FiniteChannel α ι) (μ : Measure α) : Measure (α × ι) :=
  (μ.prod Measure.count).withDensity (fun x => ENNReal.ofReal (p.prob x.2 x.1))

noncomputable def outputLaw (p : FiniteChannel α ι) (μ : Measure α) : Measure ι :=
  Measure.count.withDensity (fun i => ENNReal.ofReal (scoreMass μ (p.prob i)))

noncomputable def likelihoodRatio (p : FiniteChannel α ι) (μ : Measure α) (x : α × ι) : ℝ :=
  p.prob x.2 x.1/scoreMass μ (p.prob x.2)

end FiniteChannel

end RepeatedLocalization

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_StateExpectation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace RepeatedLocalization
namespace FiniteChannel
variable {α ι : Type*} [MeasurableSpace α] [Fintype ι]

noncomputable def expectation (p : FiniteChannel α ι) (μ : Measure α) (f : ι → ℝ) : ℝ :=
  ∑ i,scoreMass μ (p.prob i)*f i

end FiniteChannel

structure AnalysisState (n : ℕ) where
  Index : Type
  [finiteIndex : Fintype Index]
  channel : FiniteChannel (Coordinate n) Index
  cell : Index → Cell n
  B : Index → ℝ
  B_one : ∀ i,1 ≤ B i
  support : ∀ i,0 < scoreMass (cubePrior n) (channel.prob i) →
    scorePosterior (cubePrior n) (channel.prob i) (cellSet (cell i)) = 1
  spread : ∀ i,0 < scoreMass (cubePrior n) (channel.prob i) →
    DyadicSpread (scorePosterior (cubePrior n) (channel.prob i)) (cell i) (B i)

attribute [instance] AnalysisState.finiteIndex

namespace AnalysisState
variable {n : ℕ}
noncomputable def information (s : AnalysisState n) : ℝ := finiteInformation (cubePrior n) s.channel.prob
noncomputable def depth (s : AnalysisState n) : ℝ := s.channel.expectation (cubePrior n) (fun i => (s.cell i).1)
noncomputable def concentration (s : AnalysisState n) : ℝ := s.channel.expectation (cubePrior n) (fun i => Real.log (s.B i))
noncomputable def potential (s : AnalysisState n) : ℝ :=
  s.information+s.concentration-((n:ℝ)/2+2)*Real.log 2*s.depth

end AnalysisState

lemma scorePosterior_one {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] :
    scorePosterior μ (fun _ => 1) = μ := by simp [scorePosterior,scoreMass]

lemma cubePrior_spread_root {n : ℕ} (hn : 0 < n) : DyadicSpread (cubePrior n) (rootCell n) 1 := by
  intro j R hR hsub
  have hlev : R.1 = j := by simpa [rootCell] using hR
  rw [cubePrior_cellSet hn,hlev,one_mul]
  change ENNReal.ofReal ((1/2:ℝ)^(n*j)) ≤ ENNReal.ofReal (heavyThreshold n j)
  apply ENNReal.ofReal_le_ofReal
  rw [← heavyThreshold_sq]
  have hle : heavyThreshold n j ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg _
    have hj0 : (0:ℝ) ≤ j := Nat.cast_nonneg _
    nlinarith [mul_nonneg hn0 hj0]
  have hp := (heavyThreshold_pos n j).le
  nlinarith

noncomputable def initialState {n : ℕ} (hn : 0 < n) : AnalysisState n := by
  letI := cubePrior_isProbabilityMeasure hn
  let p : FiniteChannel (Coordinate n) Unit := {
    prob := fun _ _ => 1
    measurable := fun _ => measurable_const
    nonneg := fun _ _ => zero_le_one
    total := fun _ => by simp }
  exact {
    Index := Unit
    channel := p
    cell := fun _ => rootCell n
    B := fun _ => 1
    B_one := fun _ => le_refl _
    support := fun _ _ => by
      change scorePosterior (cubePrior n) (fun _ => 1) (cellSet (rootCell n)) = 1
      rw [scorePosterior_one,cubePrior_cellSet hn]; simp [rootCell]
    spread := fun _ _ => by
      change DyadicSpread (scorePosterior (cubePrior n) (fun _ => 1)) (rootCell n) 1
      rw [scorePosterior_one]; exact cubePrior_spread_root hn }

def appendHistoryEquiv (N t : ℕ) : (History N t × Fin N) ≃ History N (t+1) :=
  (Equiv.prodComm _ _).trans (Fin.snocEquiv (fun _ => Fin N))

lemma appendHistoryEquiv_apply {N t : ℕ} (w : History N t) (v : Fin N) :
    appendHistoryEquiv N t (w,v) = Fin.snoc (α := fun _ : Fin (t+1) => Fin N) w v := rfl

def initRules {n N t : ℕ} (rules : Rules n N (t+1)) : Rules n N t :=
  fun i => rules i.castSucc

lemma past_snoc_castSucc {N t : ℕ} (w : History N t) (v : Fin N) (i : Fin t) :
    past (Fin.snoc (α := fun _ : Fin (t+1) => Fin N) w v) i.castSucc = past w i := by
  funext j
  change Fin.snoc (α := fun _ : Fin (t+1) => Fin N) w v (Fin.castSucc ⟨j.val,Nat.lt_trans j.isLt i.isLt⟩) = _
  exact Fin.snoc_castSucc (α := fun _ : Fin (t+1) => Fin N) v w ⟨j.val,Nat.lt_trans j.isLt i.isLt⟩

lemma past_snoc_last {N t : ℕ} (w : History N t) (v : Fin N) :
    past (Fin.snoc (α := fun _ : Fin (t+1) => Fin N) w v) (Fin.last t) = w := by
  funext j
  change Fin.snoc (α := fun _ : Fin (t+1) => Fin N) w v j.castSucc = _
  simp

lemma historyLikelihood_snoc {n N t : ℕ} (rules : Rules n N (t+1))
    (z : Coordinate n) (w : History N t) (v : Fin N) :
    historyLikelihood rules z (Fin.snoc (α := fun _ : Fin (t+1) => Fin N) w v) =
      historyLikelihood (initRules rules) z w * blockProbability (rules (Fin.last t) w) z v := by
  rw [historyLikelihood,Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc,Fin.snoc_last,past_snoc_castSucc,past_snoc_last]
  rfl

lemma historyLikelihood_sum {n N t : ℕ} (rules : Rules n N t) (z : Coordinate n) :
    ∑ w,historyLikelihood rules z w = 1 := by
  induction t with
  | zero => simp [historyLikelihood]
  | succ t ih =>
    rw [← Equiv.sum_comp (appendHistoryEquiv N t),Fintype.sum_prod_type]
    simp_rw [appendHistoryEquiv_apply,historyLikelihood_snoc,← Finset.mul_sum,blockProbability_sum,mul_one]
    exact ih (initRules rules)

noncomputable def blockChannel {n N : ℕ} (rule : BlockRule n N) : FiniteChannel (Coordinate n) (Fin N) where
  prob := fun w z => blockProbability rule z w
  measurable := measurable_blockProbability rule
  nonneg := fun w z => blockProbability_nonneg rule z w
  total := blockProbability_sum rule

noncomputable def historyChannel {n N t : ℕ} (rules : Rules n N t) : FiniteChannel (Coordinate n) (History N t) where
  prob := fun w z => historyLikelihood rules z w
  measurable := measurable_historyLikelihood rules
  nonneg := fun w z => historyLikelihood_nonneg rules z w
  total := historyLikelihood_sum rules

end RepeatedLocalization

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_StateInformation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace RepeatedLocalization

def UniformBlockCost (n N : ℕ) (L : ℝ) : Prop :=
  ∀ (μ : Measure (Coordinate n)), IsProbabilityMeasure μ → ∀ (Q : Cell n) (B : ℝ),
    μ (cellSet Q) = 1 → 1 ≤ B → DyadicSpread μ Q B → ∀ rule : BlockRule n N,
      finiteInformation μ (blockChannel rule).prob ≤ L+Real.log B

end RepeatedLocalization

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_Refinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace RepeatedLocalization
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

structure ExtensionWitness {n N : ℕ} (s : AnalysisState n)
    (q : s.Index → FiniteChannel (Coordinate n) (Fin N))
    (s' : AnalysisState n) (f : s'.Index → s.Index × Fin N) where
  choose : (s.Index × Fin N) → Coordinate n → s'.Index
  choose_fiber : ∀ i j, MeasurableSet {z | choose i z = j}
  erase_choose : ∀ i z, f (choose i z) = i
  chosen : ∀ j z, 0 < s'.channel.prob j z → choose (f j) z = j
  positive_parent : ∀ j z, 0 < s'.channel.prob j z → 0 < s.channel.prob (f j).1 z
  contains : ∀ i z, z ∈ cellSet (s.cell i.1) → z ∈ cellSet (s'.cell (choose i z))
  subset : ∀ j, cellSet (s'.cell j) ⊆ cellSet (s.cell (f j).1)

end RepeatedLocalization

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_Realization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace RepeatedLocalization
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

lemma through_last {N t : ℕ} (w : History N (t+1)) : through w (Fin.last t) = w := by
  funext j
  rfl

instance AnalysisState.indexMeasurableSpace {n : ℕ} (s : AnalysisState n) : MeasurableSpace s.Index := ⊤

instance AnalysisState.indexMeasurableSingleton {n : ℕ} (s : AnalysisState n) : MeasurableSingletonClass s.Index := ⟨fun _ => trivial⟩

structure Realization {n N t : ℕ} (s : AnalysisState n) (f : s.Index → History N t) where
  Q : Disclosure n N t
  Qmeas : ∀ i, Measurable (fun zh : Coordinate n × History N (i.val+1) => Q i zh.1 zh.2)
  Qfinite : ∀ i, (Set.range (fun zh : Coordinate n × History N (i.val+1) => Q i zh.1 zh.2)).Finite
  read : Coordinate n → History N t → s.Index
  read_meas : Measurable (fun zw : Coordinate n × History N t => read zw.1 zw.2)
  erase_read : ∀ z w, f (read z w) = w
  chosen : ∀ j z, 0 < s.channel.prob j z → read z (f j) = j
  trace : s.Index → Fin t → Cell n
  trace_read : ∀ z w i, trace (read z w) i = Q i z (through w i)
  trace_cube : ∀ j i, cellSet (trace j i) ⊆ initialCube n
  trace_below : ∀ j i, cellSet (s.cell j) ⊆ cellSet (trace j i)
  trace_nested : ∀ k (i j : Fin t), i ≤ j → cellSet (trace k j) ⊆ cellSet (trace k i)
  cell_cube : ∀ j, cellSet (s.cell j) ⊆ initialCube n
  read_mem : ∀ z ∈ initialCube n, ∀ w, z ∈ cellSet (s.cell (read z w))
  depth_read : ∀ z w, finalLevel Q (z,w) = (s.cell (read z w)).1

noncomputable def initialRealization {n N : ℕ} (hn : 0 < n) :
    Realization (initialState hn) (fun _ => (Fin.elim0 : History N 0)) where
  Q := fun i => Fin.elim0 i
  Qmeas := fun i => Fin.elim0 i
  Qfinite := fun i => Fin.elim0 i
  read := fun _ _ => ()
  read_meas := measurable_const
  erase_read := fun _ _ => Subsingleton.elim _ _
  chosen := fun j _ _ => by change () = (j : Unit); exact Subsingleton.elim _ _
  trace := fun _ i => Fin.elim0 i
  trace_read := fun _ _ i => Fin.elim0 i
  trace_cube := fun _ i => Fin.elim0 i
  trace_below := fun _ i => Fin.elim0 i
  trace_nested := fun _ i => Fin.elim0 i
  cell_cube := fun _ => by change cellSet (rootCell n) ⊆ initialCube n; rw [cellSet_root]
  read_mem := fun z hz _ => by change z ∈ cellSet (rootCell n); rwa [cellSet_root]
  depth_read := fun _ _ => by simp [finalLevel,initialState,rootCell]

lemma ExtensionWitness.choose_meas {n N : ℕ} {s s' : AnalysisState n}
    {q : s.Index → FiniteChannel (Coordinate n) (Fin N)} {g : s'.Index → s.Index × Fin N}
    (E : ExtensionWitness s q s' g) : Measurable (fun iz : (s.Index × Fin N) × Coordinate n => E.choose iz.1 iz.2) := by
  apply measurable_from_prod_countable_right
  intro i
  apply measurable_to_countable
  intro z
  exact E.choose_fiber i (E.choose i z)

end RepeatedLocalization

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Dyadic_RealizationStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace RepeatedLocalization
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

lemma through_init {N t : ℕ} (w : History N (t+1)) (i : Fin t) :
    through (Fin.init w) i = through w i.castSucc := by
  funext j
  rfl

noncomputable def extendRealization {n N t : ℕ} {s s' : AnalysisState n}
    {f : s.Index → History N t} {q : s.Index → FiniteChannel (Coordinate n) (Fin N)}
    {g : s'.Index → s.Index × Fin N} (R : Realization s f) (E : ExtensionWitness s q s' g) :
    Realization s' (fun j => Fin.snoc (α := fun _ : Fin (t+1) => Fin N) (f (g j).1) (g j).2) := by
  classical
  let rd := fun (z : Coordinate n) (w : History N (t+1)) => E.choose (R.read z (Fin.init w),w (Fin.last t)) z
  have hrd : Measurable (fun zw : Coordinate n × History N (t+1) => rd zw.1 zw.2) := by
    apply E.choose_meas.comp (f := fun zw : Coordinate n × History N (t+1) => ((R.read zw.1 (Fin.init zw.2),zw.2 (Fin.last t)),zw.1))
    exact ((R.read_meas.comp (measurable_fst.prodMk ((measurable_of_countable (fun w : History N (t+1) => Fin.init w)).comp measurable_snd))).prodMk
      ((measurable_of_countable (fun w : History N (t+1) => w (Fin.last t))).comp measurable_snd)).prodMk measurable_fst
  have herase (z : Coordinate n) (w : History N (t+1)) :
      g (rd z w) = (R.read z (Fin.init w),w (Fin.last t)) := E.erase_choose _ _
  let Q : Disclosure n N (t+1) := Fin.lastCases (fun z w => s'.cell (rd z w)) R.Q
  let tr : s'.Index → Fin (t+1) → Cell n := fun j => Fin.snoc (R.trace (g j).1) (s'.cell j)
  refine {
    Q := Q
    Qmeas := ?_
    Qfinite := ?_
    read := rd
    read_meas := hrd
    erase_read := ?_
    chosen := ?_
    trace := tr
    trace_read := ?_
    trace_cube := ?_
    trace_below := ?_
    trace_nested := ?_
    cell_cube := fun j => (E.subset j).trans (R.cell_cube (g j).1)
    read_mem := ?_
    depth_read := ?_ }
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Q,Fin.lastCases_last]
      change Measurable (fun zw : Coordinate n × History N (t+1) => s'.cell (rd zw.1 zw.2))
      exact (measurable_of_countable s'.cell).comp hrd
    · simp only [Q,Fin.lastCases_castSucc]
      change Measurable (fun zw : Coordinate n × History N (j.val+1) => R.Q j zw.1 zw.2)
      exact R.Qmeas j
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Q,Fin.lastCases_last]
      change (Set.range (fun zw : Coordinate n × History N (t+1) => s'.cell (rd zw.1 zw.2))).Finite
      apply (Set.finite_range s'.cell).subset
      rintro c ⟨zw,rfl⟩
      exact ⟨rd zw.1 zw.2,rfl⟩
    · simp only [Q,Fin.lastCases_castSucc]
      change (Set.range (fun zh : Coordinate n × History N (j.val+1) => R.Q j zh.1 zh.2)).Finite
      exact R.Qfinite j
  · intro z w
    rw [herase,R.erase_read]
    exact Fin.snoc_init_self w
  · intro j z hz
    dsimp only [rd]
    rw [Fin.init_snoc,Fin.snoc_last,R.chosen (g j).1 z (E.positive_parent j z hz)]
    exact E.chosen j z hz
  · intro z w i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [tr,Q,through_last]
    · simp only [tr,Q,Fin.snoc_castSucc,Fin.lastCases_castSucc]
      rw [herase]
      simpa only [through_init] using R.trace_read z (Fin.init w) j
  · intro j i
    refine Fin.lastCases ?_ (fun k => ?_) i
    · simp only [tr,Fin.snoc_last]
      exact (E.subset j).trans (R.cell_cube _)
    · simp only [tr,Fin.snoc_castSucc]
      exact R.trace_cube _ k
  · intro j i
    refine Fin.lastCases ?_ (fun k => ?_) i
    · simp only [tr,Fin.snoc_last]
      exact Subset.rfl
    · simp only [tr,Fin.snoc_castSucc]
      exact (E.subset j).trans (R.trace_below _ k)
  · intro k i j
    refine Fin.lastCases ?_ (fun a => ?_) i
    · refine Fin.lastCases ?_ (fun b => ?_) j
      · intro _; exact Subset.rfl
      · intro h; exact False.elim (by have := b.isLt; change t ≤ b.val at h; omega)
    · refine Fin.lastCases ?_ (fun b => ?_) j
      · intro _
        simp only [tr,Fin.snoc_last,Fin.snoc_castSucc]
        exact (E.subset k).trans (R.trace_below _ a)
      · intro h
        simpa only [tr,Fin.snoc_castSucc] using R.trace_nested (g k).1 a b h
  · intro z hz w
    exact E.contains _ z (R.read_mem z hz (Fin.init w))
  · intro z w
    simp only [finalLevel,show 0 < t+1 by omega,dite_eq_left]
    change (Q (Fin.last t) z (through w (Fin.last t))).1 = (s'.cell (rd z w)).1
    rw [through_last]
    simp only [Q,Fin.lastCases_last]

end RepeatedLocalization

end OAI
end


