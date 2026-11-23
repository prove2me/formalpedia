-- Prove2me | Definitions.Def_BwSC_LowerBound_Supplement_Gap
-- name    : BwSC_LowerBound_Supplement_Gap
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T09:42:19.077457+00:00
-- url     : https://prove2.me/theorems/f480c935-65dd-42cb-a7dd-6b6599c3cd90
-- title:
--   Appendix A — actual unique-best gap and both instance-dependent rates
-- statement:
--   Let $\nu$ be an environment with arm means $\mu_i$. If the best arm $k^*$ is unique and there is another arm, define its actual gap by
--   $$\Delta(\nu)=\min_{j\ne k^*}(\mu_{k^*}-\mu_j).$$
--   For tied optima and for one arm set $\Delta(\nu)=0$. The gap-weighted worst-case regret is $\sup_{\nu\in\mathcal E_K}\Delta(\nu)R^\pi_\nu(K,T)$, with $\mathcal E_K$ the normalized sub-Gaussian class. Write $q=q(S,K)$ and $r=r(S,K)$ for the published phase indices. The rate numerators are
--   $$A_\Delta=\frac{(K-r)^{2-1/(q+1)}}K T^{1/(q+1)},\qquad B_{\Delta,u}=K^{1-1/(q+1)}T^{1/(q+1)},\qquad B_{\Delta,l}=K^{1-1/(q+2)}T^{1/(q+2)}.$$
--   These are the exact terms printed in Theorems 6 and 7. In particular the second upper-bound term uses $q+1$, while the second lower-bound term uses $q+2$.
--
--   **Formalization Note** The minimum is taken over a nonempty finite set after choosing the unique best arm; it never uses an empty real infimum. Tie environments contribute zero to the extended-real supremum. Theorem 6 assumes $\Delta(\nu)>0$ only in its multi-arm clause; the one-arm clause asserts zero regret. No numerical lower bound on the gap is imposed.
-- source:
--   Simchi-Levi & Xu, arXiv:1905.10825v4, pp. 38–39, positive-gap convention and Theorems 6–7

import Mathlib
import Definitions.Def_BwSC_LowerBound_Supplement_Environment

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace BwSC.LowerBound.Supplement

/-- Unique optimal action, as assumed in Appendix A, p. 38. -/
def UniqueBest {K : ℕ} (ν : StochasticBandit K) (i : Fin K) : Prop :=
  ∀ j, j ≠ i → banditArmMean ν j < banditArmMean ν i

/-- The actual gap of the environment, Appendix A, p. 38. It is the
minimum best-minus-other mean when there is a unique best and another arm.
For a tie or a one-arm environment it is zero. No empty real infimum is used. -/
noncomputable def sourceGap {K : ℕ} (ν : StochasticBandit K) : ℝ := by
  classical
  exact if hb : ∃ i, UniqueBest ν i then
    let i := Classical.choose hb
    let others := Finset.univ.erase i
    if hn : others.Nonempty then
      others.inf' hn (fun j => banditArmMean ν i - banditArmMean ν j)
    else 0
  else 0

/-- Theorem 7, p. 39: take the supremum over environments and their actual
gaps, not over an unrelated free variable Δ. Ties contribute zero. -/
noncomputable def gapWeightedWorstRegret {K : ℕ} (π : BanditPolicy K) (T : ℕ) : EReal :=
  ⨆ ν : {ν : StochasticBandit K // AdmissibleEnvironment ν},
    (sourceGap ν.val * banditRegret ν.val π T : ℝ)

/-- First term in both Theorems 6 and 7, before division by Δ. -/
noncomputable def gapRateA (K S T : ℕ) : ℝ :=
  ((K : ℝ) - (rIdx S K : ℝ)) ^ (2 - 1 / ((qIdx S K : ℝ) + 1)) / K *
    (T : ℝ) ^ (1 / ((qIdx S K : ℝ) + 1))

/-- Second term of Theorem 6, exactly as printed (q+1). -/
noncomputable def gapRateBUpper (K S T : ℕ) : ℝ :=
  (K : ℝ) ^ (1 - 1 / ((qIdx S K : ℝ) + 1)) *
    (T : ℝ) ^ (1 / ((qIdx S K : ℝ) + 1))

/-- Second term of Theorem 7, exactly as printed (q+2). -/
noncomputable def gapRateBLower (K S T : ℕ) : ℝ :=
  (K : ℝ) ^ (1 - 1 / ((qIdx S K : ℝ) + 2)) *
    (T : ℝ) ^ (1 / ((qIdx S K : ℝ) + 2))

end BwSC.LowerBound.Supplement


