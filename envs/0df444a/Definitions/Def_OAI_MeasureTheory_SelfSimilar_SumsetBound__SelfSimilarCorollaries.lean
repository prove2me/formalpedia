-- Prove2me | Definitions.Def_OAI_MeasureTheory_SelfSimilar_SumsetBound__SelfSimilarCorollaries
-- name    : OAI_MeasureTheory_SelfSimilar_SumsetBound__SelfSimilarCorollaries
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T13:39:36.15399+00:00
-- url     : https://prove2.me/theorems/45821891-daa3-4dff-b202-45106130a955
-- title:
--   Band costs, sumsets and grid entropy of finite laws
-- statement:
--   These notions belong to a formal proof of the dimension formula for self-similar measures on the line. Let $f_i(x)=r_ix+b_i$ with $0<|r_i|<1$ and weights $w_i>0$ summing to $1$, and let $\mu=\sum_iw_i\,(f_i)_*\mu$ be the self-similar probability measure. The formula states $\underline{\dim}_H\mu=\min(1,h/\chi)$. Here $h$ is the entropy rate of the random walk on composed affine maps, with exact overlaps allowed, $\chi=-\sum_iw_i\log_2|r_i|$ is the Lyapunov exponent, and $\underline{\dim}_H\mu$ is the infimum of $\dim_HE$ over sets of positive measure. The proof identifies the dimension with an exponent of the symbolic coding, compares entropies of $\mu$ on dyadic grids, and rules out a strict gap by an entropy-increase argument for convolutions.
--
--   For a finite law $\nu$:
--
--   1. **Band support and cost.** The bands of all distances between support points, and the cost $\sum_\ell2^{1-\ell}\,\mathrm{cap}_\ell(\nu)$ over bands with $2^{-\ell}\le R$.
--   2. **Partition entropy.** For $k$ independent samples and a labelling $g$, the conditional entropy of the labels given the sum of the samples.
--   3. **Refinement cost.** $\frac{352k^4}{R}\,\mathrm{cost}_R(\nu)\log2$.
--   4. **Sumset.** The set of sums $x_1+\dots+x_k$ of $k$ support points.
--   5. **Shannon and grid entropy in bits.** $H(\nu)/\log2$ and the entropy of $\lfloor x/\rho\rfloor$ in bits:
--   $$
--   H_\rho(\nu)=\frac1{\log2}\,H\bigl(\lfloor x/\rho\rfloor\bigr).
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/SumsetBound.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/SumsetBound.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uβ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace FairPairs

open FiniteEntropy

noncomputable def Law.bandSupport (ν : Law) : Finset ℤ := by
  classical
  exact (ν.support ×ˢ ν.support).image (fun e => bandIndex |e.2-e.1|)

noncomputable def Law.bandCost (ν : Law) (R : ℝ) : ℝ := by
  classical
  exact ∑ ℓ ∈ ν.bandSupport.filter (fun ℓ => (2 : ℝ)^(-ℓ) ≤ R),
    (2 : ℝ)^(1-ℓ)*capacity ν ℓ

theorem Law.subtype_sum (ν : Law) : ∑ a : ν.support, ν.prob a = 1 := by
  simpa only [Finset.sum_coe_sort] using ν.prob_sum

noncomputable def Law.partitionEntropy (ν : Law) (k : ℕ) (g : ℝ → List ℤ) : ℝ := by
  classical
  exact conditionalEntropy Finset.univ
    (ProductLaw.weight (fun _ : Fin k => fun a : ν.support => ν.prob a))
    (fun x i => g (x i)) (fun x => ∑ i, (x i : ℝ))

noncomputable def Law.refinementCost (ν : Law) (k : ℕ) (R : ℝ) : ℝ :=
  (352*k^4/R)*ν.bandCost R*Real.log 2

noncomputable def Law.sumset (ν : Law) (k : ℕ) : Finset ℝ := by
  classical
  exact Finset.univ.image (fun x : Fin k → ν.support => ∑ i, (x i : ℝ))

noncomputable def Law.shannonEntropy (ν : Law) : ℝ := entropy ν.support ν.prob / Real.log 2

noncomputable def Law.gridEntropy (ν : Law) (ρ : ℝ) : ℝ := by
  classical
  exact observableEntropy ν.support ν.prob (fun x => ⌊x/ρ⌋) / Real.log 2

end FairPairs

end EntropyRateDimension
end

end OAI


