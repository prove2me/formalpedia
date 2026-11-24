-- Prove2me | Definitions.Def_RobustPrefLearn_MTP_Supplement_Information
-- name    : RobustPrefLearn_MTP_Supplement_Information
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T00:12:31.339275+00:00
-- url     : https://prove2.me/theorems/43ebbc6c-0f25-44fb-833c-78b93e0d2658
-- title:
--   Equations (26)–(27), p. 45 — extended KL divergence and general Chernoff information
-- statement:
--   For the testing model of Appendix B.1, write $H(\theta)=\{i:\theta\in H_i\}$. The alternative parameters share no true hypothesis with $\theta$:
--   $$A(\theta)=\{\theta':\forall i\in H(\theta),\ \theta'\notin H_i\}.$$
--   For positive normalized masses $a_x=f_\theta(x\mid S)$ and $b_x=f_{\theta'}(x\mid S)$, set
--   $$D_S(\theta\Vert\theta')=\sum_x\bigl[a_x\log(a_x/b_x)-a_x+b_x\bigr],\qquad D_\lambda(\theta\Vert\theta')=\sum_S\lambda(S)D_S(\theta\Vert\theta').$$
--   Each corrected summand is nonnegative, and the normalization terms cancel, giving the KL divergence printed in (26), including its possible infinite value. The information is
--   $$I_*(\theta)=\sup_{\lambda\in\Delta(\mathcal S)}\inf_{\theta'\in A(\theta)}D_\lambda(\theta\Vert\theta').$$
--   This is the denominator in the general testing lower bound and supports arbitrary discrete outcome spaces.
--
--   **Formalization Note** Divergences, distributions and information take values in $[0,\infty]$. An empty alternative set has infimum $+\infty$, an empty simplex has supremum zero, and divergent nonnegative series have value $+\infty$. The hypotheses of the testing theorem supply positivity and normalization. The bar on the source's $\overline H(\theta')$ is retained.
-- source:
--   Feng, Caldentey & Ryan, SSRN 3215614, Appendix B.2, equations (26)–(27), p. 45

import Mathlib
import Definitions.Def_RobustPrefLearn_MTP_Supplement_Testing

open scoped ENNReal

namespace RobustPrefLearn.MTP.Supplement

universe u v w

/-- (26), p.45. For positive probability masses the summands are nonnegative
by `log r ≤ r − 1`; the correction `−f+g` sums to zero. This is KL even when
it is infinite, unlike the real-valued tsum of signed log-likelihood terms. -/
noncomputable def testingDivS {Θ : Type u} {S : Type v} {X : Type w} {I : ℕ}
    (M : TestingModel Θ S X I) (θ θ' : Θ) (s : S) : ℝ≥0∞ :=
  ∑' x, ENNReal.ofReal (M.mass θ s x * Real.log (M.mass θ s x / M.mass θ' s x)
    - M.mass θ s x + M.mass θ' s x)

/-- Δ(𝒮), discrete probability distributions on arbitrary experiment types.
This is the weight-function interface to Mathlib's `PMF`. -/
def testingSimplex (S : Type v) : Set (S → ℝ≥0∞) := {lam | ∑' s, lam s = 1}

noncomputable def testingDivLam {Θ : Type u} {S : Type v} {X : Type w} {I : ℕ}
    (M : TestingModel Θ S X I) (lam : S → ℝ≥0∞) (θ θ' : Θ) : ℝ≥0∞ :=
  ∑' s, lam s * testingDivS M θ θ' s

/-- A(θ), p.45: every hypothesis true at θ is false at θ'. The bar in the
rendered source is essential; overlapping true-hypothesis sets are excluded. -/
def testingAlt {Θ : Type u} {S : Type v} {X : Type w} {I : ℕ}
    (M : TestingModel Θ S X I) (θ : Θ) : Set Θ :=
  {θ' | ∀ i, θ ∈ M.H i → θ' ∉ M.H i}

/-- (27), p.45. Empty alternatives give infinity; unbounded divergences
retain infinity. No real sSup/sInf default is used. -/
noncomputable def testingInfo {Θ : Type u} {S : Type v} {X : Type w} {I : ℕ}
    (M : TestingModel Θ S X I) (θ : Θ) : ℝ≥0∞ :=
  ⨆ lam ∈ testingSimplex S, ⨅ θ' ∈ testingAlt M θ, testingDivLam M lam θ θ'

end RobustPrefLearn.MTP.Supplement


