-- Prove2me | Definitions.Def_FragileBandit_CauchyTail_Supplement_PathwiseConvergence
-- name    : FragileBandit_CauchyTail_Supplement_PathwiseConvergence
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T00:04:09.812376+00:00
-- url     : https://prove2.me/theorems/2dd34a07-b973-4c46-9d14-e9bd104bf823
-- title:
--   Definition 4 for the Gaussian design — convergence on every convergent reward path
-- statement:
--   For the unit-variance Gaussian design family, every real number is an allowed mean and
--
--   $$d_P(u,v)=\frac{(u-v)^2}{2}.$$
--
--   `IsGaussianPathwiseConvergent` is the instance of Definition 4 used in the counterexample. For every real reward table, every compatible policy path, and every vector of pairwise distinct limits $c_i$ of the local empirical averages, each non-best arm satisfies
--
--   $$\frac{N_i(T)}{\log T}\longrightarrow\frac{1}{d_P(c_i,\max_j c_j)}.$$
--
--   The divergence is the published $d_P$ evaluated at the fixed Gaussian base. The property ranges over all real tables, rather than only paths under the proposed counterexample's law.
--
--   **Formalization Note** A compatible path selects only actions with nonzero conditional probability. The unique-ranking convention is expressed by injectivity of the limit vector, and the optimal arm is omitted as in (22). Counts divided by $\log T$ and their limits are compared in $[0,+\infty]$. The definition implements only the Gaussian design instance needed for the existential refutation; it does not purport to extend the source's divergence to boundary means of other design families. The Gaussian mean domain is all of $\mathbb R$, so the published parameter choice is always evaluated inside its domain.
-- source:
--   Fan and Glynn, The Fragility of Optimized Bandit Algorithms, arXiv:2109.13595v8, p.20, Definition 4, (22)

import Mathlib
import Definitions.Def_FragileBandit_CauchyTail_Supplement_TailEncoding
import Definitions.Def_FragileBandit_CauchyTail_Supplement_RestedProcess

set_option autoImplicit false

namespace FragileBandit.CauchyTail.Supplement

open MeasureTheory ProbabilityTheory Filter BanditAlgorithm
open scoped ENNReal Topology

/-- The Gaussian-design instance of Definition 4, used by the counterexample.
Every real table is admitted because the design mean domain is all of ℝ.
The policy property is pointwise across tables and possible action paths, rather than
an almost-sure assertion only under the counterexample's law. -/
def IsGaussianPathwiseConvergent {K : ℕ} (π : BanditPolicy K) : Prop :=
  ∀ (x : RewardTable K) (a : ℕ → Fin K) (c : Fin K → ℝ),
    IsPolicyPath π x a → Function.Injective c →
    (∀ i, Tendsto (fun n : ℕ => rewardSum x i n / (n : ℝ)) atTop (𝓝 (c i))) →
    ∀ b : Fin K, (∀ j, c j ≤ c b) → ∀ i : Fin K, i ≠ b →
      Tendsto (fun T : ℕ => ENNReal.ofReal
        ((armPullCount i (realizedHistory x a T) : ℝ) / Real.log T)) atTop
        (𝓝 ((dP (gaussianReal 0 1) (c i) (c b))⁻¹))

end FragileBandit.CauchyTail.Supplement


