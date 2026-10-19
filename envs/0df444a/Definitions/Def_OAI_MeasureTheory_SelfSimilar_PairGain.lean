-- Prove2me | Definitions.Def_OAI_MeasureTheory_SelfSimilar_PairGain
-- name    : OAI_MeasureTheory_SelfSimilar_PairGain
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T03:30:49.676438+00:00
-- url     : https://prove2.me/theorems/5eb7d8bb-ec98-4a5e-91f7-acc6d637bc60
-- title:
--   Shifted laws, windows and finite convolutions
-- statement:
--   These notions belong to a formal proof of the dimension formula for self-similar measures on the line. Let $f_i(x)=r_ix+b_i$ with $0<|r_i|<1$ and weights $w_i>0$ summing to $1$, and let $\mu=\sum_iw_i\,(f_i)_*\mu$ be the self-similar probability measure. The formula states $\underline{\dim}_H\mu=\min(1,h/\chi)$. Here $h$ is the entropy rate of the random walk on composed affine maps, with exact overlaps allowed, $\chi=-\sum_iw_i\log_2|r_i|$ is the Lyapunov exponent, and $\underline{\dim}_H\mu$ is the infimum of $\dim_HE$ over sets of positive measure. The proof identifies the dimension with an exponent of the symbolic coding, compares entropies of $\mu$ on dyadic grids, and rules out a strict gap by an entropy-increase argument for convolutions.
--
--   1. **Shifts and windows.** The translate $\mu(\cdot-b)$, and the window $\bar H_s(\mu)-\bar H_t(\mu)$ of averaged grid entropies between scales $s$ and $t$.
--   2. **Pair law.** $\frac12\bigl(\mu(\cdot-x)+\mu(\cdot-y)\bigr)$.
--   3. **Finite convolution.** For a finite law $\nu$ and scale $a$,
--   $$
--   \nu_a*\mu=\sum_x\nu(x)\,\mu(\cdot-ax).
--   $$
--   4. **Decomposition.** For feasible edge weights $w$ in a band, the residual mass $\nu(x)-\mathrm{incident}_w(x)$, and the decomposition of $\nu_a*\mu$ into pair laws on edges and single translates on residuals.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/PairGain.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/PairGain.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SelfSimilar mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Boundary
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TranslationGain
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FairPairs
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ProductLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_GridCoupling
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteRefinement
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SumsetBound
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WordTypes
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_DigitSumset
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Bernoulli
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Coding
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_InvariantLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallRatios
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallIntegrability
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_CodingIntegrals
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ErgodicAverages
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TriangularAverages
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallLimits
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RadiusGrowth
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RadialLimit
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ExactDimension
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_UpperBound
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Conditioning

namespace OAI

universe uα uβ

namespace EntropyRateDimension.MeasureEntropy
open MeasureTheory
open scoped BigOperators ENNReal

noncomputable def shiftLaw (μ : Measure ℝ) (b : ℝ) : Measure ℝ := μ.map (fun x => x+b)

instance shiftLaw_probability (μ : Measure ℝ) [IsProbabilityMeasure μ] (b : ℝ) :
    IsProbabilityMeasure (shiftLaw μ b) :=
  (Measure.isProbabilityMeasure_map_iff (measurable_id.add_const b).aemeasurable).2 inferInstance

noncomputable def window (μ : Measure ℝ) (s t : ℝ) : ℝ := averaged μ s-averaged μ t

noncomputable def pairLaw (μ : Measure ℝ) (x y : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1/2 : ℝ) • shiftLaw μ x+ENNReal.ofReal (1/2 : ℝ) • shiftLaw μ y

instance pairLaw_probability (μ : Measure ℝ) [IsProbabilityMeasure μ] (x y : ℝ) :
    IsProbabilityMeasure (pairLaw μ x y) := by
  constructor
  simpa [pairLaw,Measure.add_apply,Measure.smul_apply,measure_univ] using ENNReal.inv_two_add_inv_two

noncomputable def finiteConv (ν : FairPairs.Law) (a : ℝ) (μ : Measure ℝ) : Measure ℝ :=
  ∑ x : ν.support, ENNReal.ofReal (ν.prob x) • shiftLaw μ (a*x)

instance finiteConv_probability (ν : FairPairs.Law) (a : ℝ) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (finiteConv ν a μ) :=
  mixture_probability _ _ (fun x => (ν.prob_pos x x.property).le) ν.subtype_sum

end EntropyRateDimension.MeasureEntropy

namespace EntropyRateDimension.FairPairs
open MeasureTheory MeasureEntropy
open scoped BigOperators ENNReal

noncomputable def residual {ν : Law} {ℓ : ℤ} (w : ν.edges ℓ → ℝ) (x : ν.support) : ℝ :=
  ν.prob x-incident w x

noncomputable def decompositionWeight {ν : Law} {ℓ : ℤ} (w : ν.edges ℓ → ℝ) :
    ν.edges ℓ ⊕ ν.support → ℝ := Sum.elim w (residual w)

noncomputable def decompositionLaw {ν : Law} {ℓ : ℤ} (μ : Measure ℝ) (a : ℝ) :
    ν.edges ℓ ⊕ ν.support → Measure ℝ := Sum.elim
      (fun e => pairLaw μ (a*e.val.1) (a*e.val.2))
      (fun x => shiftLaw μ (a*x))

instance decompositionLaw_probability {ν : Law} {ℓ : ℤ} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a : ℝ) (z : ν.edges ℓ ⊕ ν.support) : IsProbabilityMeasure (decompositionLaw μ a z) := by
  cases z <;> dsimp [decompositionLaw] <;> infer_instance

end EntropyRateDimension.FairPairs

namespace EntropyRateDimension.MeasureEntropy
open MeasureTheory FairPairs
open scoped BigOperators ENNReal

end EntropyRateDimension.MeasureEntropy

end OAI


