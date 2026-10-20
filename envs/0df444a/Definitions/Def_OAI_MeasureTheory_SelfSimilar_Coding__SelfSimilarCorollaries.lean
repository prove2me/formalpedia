-- Prove2me | Definitions.Def_OAI_MeasureTheory_SelfSimilar_Coding__SelfSimilarCorollaries
-- name    : OAI_MeasureTheory_SelfSimilar_Coding__SelfSimilarCorollaries
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T13:49:52.302656+00:00
-- url     : https://prove2.me/theorems/1a2fa5d4-fbef-410f-b18d-d4105490d5cf
-- title:
--   The symbolic coding of a self-similar measure
-- statement:
--   These notions belong to a formal proof of the dimension formula for self-similar measures on the line. Let $f_i(x)=r_ix+b_i$ with $0<|r_i|<1$ and weights $w_i>0$ summing to $1$, and let $\mu=\sum_iw_i\,(f_i)_*\mu$ be the self-similar probability measure. The formula states $\underline{\dim}_H\mu=\min(1,h/\chi)$. Here $h$ is the entropy rate of the random walk on composed affine maps, with exact overlaps allowed, $\chi=-\sum_iw_i\log_2|r_i|$ is the Lyapunov exponent, and $\underline{\dim}_H\mu$ is the infimum of $\dim_HE$ over sets of positive measure. The proof identifies the dimension with an exponent of the symbolic coding, compares entropies of $\mu$ on dyadic grids, and rules out a strict gap by an entropy-increase argument for convolutions.
--
--   For a sequence $\omega$ of letters:
--
--   1. **Slopes and terms.** $\mathrm{slope}_n(\omega)=\prod_{j<n}r_{\omega_j}$ and $\mathrm{term}_n(\omega)=\mathrm{slope}_n(\omega)\,b_{\omega_n}$.
--   2. **Coding map.** The point
--   $$
--   \pi(\omega)=\sum_{n\ge0}\mathrm{slope}_n(\omega)\,b_{\omega_n}=\lim_nf_{\omega_0}\circ\cdots\circ f_{\omega_{n-1}}(0),
--   $$
--   a convergent series since $|r_i|\le c<1$; the map is measurable.
--   3. **Measures.** The symbol law $\sum_iw_i\delta_i$, the Bernoulli address measure (its infinite product), and the law of $\mu$ as the pushforward of the address measure by $\pi$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/Coding.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/Coding.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SelfSimilarCorollaries mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Model
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Boundary__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TranslationGain__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FairPairs__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ProductLaw__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_GridCoupling__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteRefinement__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SumsetBound__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WordTypes__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_DigitSumset__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Bernoulli__SelfSimilarCorollaries

namespace OAI

universe uι

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
namespace EntropyRateDimension
namespace Coding
open Filter Set
open scoped Topology

variable {ι : Type uι} [Fintype ι] [Nonempty ι]

def shift (ω : ℕ → ι) (n : ℕ) : ι := ω (n+1)

def slope (S : System ι) (ω : ℕ → ι) (n : ℕ) : ℝ :=
  ∏ j ∈ Finset.range n, S.ratio (ω j)

def term (S : System ι) (ω : ℕ → ι) (n : ℕ) : ℝ :=
  slope S ω n * S.offset (ω n)

noncomputable def point (S : System ι) (ω : ℕ → ι) : ℝ := ∑' n, term S ω n

omit [Nonempty ι] in
theorem slope_zero (S : System ι) (ω : ℕ → ι) : slope S ω 0 = 1 := by simp [slope]

omit [Nonempty ι] in
theorem slope_succ (S : System ι) (ω : ℕ → ι) (n : ℕ) :
    slope S ω (n+1) = slope S ω n * S.ratio (ω n) := by
  simp [slope, Finset.prod_range_succ]

omit [Nonempty ι] in
theorem abs_slope_le (S : System ι) (ω : ℕ → ι) {c : ℝ}
    (hc : 0 ≤ c) (hr : ∀ i, |S.ratio i| ≤ c) (n : ℕ) :
    |slope S ω n| ≤ c^n := by
  induction n with
  | zero => simp [slope_zero]
  | succ n ih =>
    rw [slope_succ, abs_mul, pow_succ]
    exact mul_le_mul ih (hr _) (abs_nonneg _) (pow_nonneg hc _)

omit [Nonempty ι] in
theorem abs_term_le (S : System ι) (ω : ℕ → ι) {c T : ℝ}
    (hc : 0 ≤ c) (_hT : 0 ≤ T) (hr : ∀ i, |S.ratio i| ≤ c)
    (ht : ∀ i, |S.offset i| ≤ T) (n : ℕ) : |term S ω n| ≤ c^n*T := by
  rw [term, abs_mul]
  exact mul_le_mul (abs_slope_le S ω hc hr n) (ht _) (abs_nonneg _) (pow_nonneg hc n)

theorem term_summable (S : System ι) (ω : ℕ → ι) : Summable (term S ω) := by
  obtain ⟨c,T,hc,hc1,hT,hr,ht⟩ := S.exists_uniform_bounds
  apply Summable.of_norm_bounded ((summable_geometric_of_lt_one hc.le hc1).mul_right T)
  intro n
  simpa only [Real.norm_eq_abs] using abs_term_le S ω hc.le hT hr ht n

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

omit [Nonempty ι] in
theorem slope_measurable (S : System ι) (n : ℕ) : Measurable (fun ω => slope S ω n) := by
  apply Finset.measurable_prod
  intro j hj
  exact (measurable_of_finite _).comp (measurable_pi_apply j)

omit [Nonempty ι] in
theorem term_measurable (S : System ι) (n : ℕ) : Measurable (fun ω => term S ω n) :=
  (slope_measurable S n).mul ((measurable_of_finite _).comp (measurable_pi_apply n))

theorem point_measurable (S : System ι) : Measurable (point S) := by
  apply measurable_of_tendsto_metrizable
    (fun n => Finset.measurable_sum (s := Finset.range n) (fun j _ => term_measurable S j))
  apply tendsto_pi_nhds.mpr
  intro ω
  exact (term_summable S ω).hasSum.tendsto_sum_nat

noncomputable def symbolMeasure (S : System ι) : Measure ι :=
  ∑ i, ENNReal.ofReal (S.weight i) • Measure.dirac i

instance symbolMeasure_probability (S : System ι) : IsProbabilityMeasure (symbolMeasure S) where
  measure_univ := by
    simp only [symbolMeasure, Measure.finsetSum_apply, Measure.smul_apply,
      Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => S.weight_nonneg i), S.weight_sum]
    simp

noncomputable def addressMeasure (S : System ι) : Measure (ℕ → ι) :=
  Measure.infinitePi fun _ : ℕ => symbolMeasure S

instance addressMeasure_probability (S : System ι) : IsProbabilityMeasure (addressMeasure S) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi fun _ : ℕ => symbolMeasure S))

noncomputable def law (S : System ι) : Measure ℝ := (addressMeasure S).map (point S)

instance law_probability (S : System ι) : IsProbabilityMeasure (law S) :=
  (Measure.isProbabilityMeasure_map_iff (point_measurable S).aemeasurable).2 inferInstance

end Coding
end EntropyRateDimension

end

end OAI


