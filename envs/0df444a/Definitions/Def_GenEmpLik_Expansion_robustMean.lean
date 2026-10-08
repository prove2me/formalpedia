-- Prove2me | Definitions.Def_GenEmpLik_Expansion_robustMean
-- name    : GenEmpLik_Expansion_robustMean
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T03:01:39.547245+00:00
-- url     : https://prove2.me/theorems/6f2018f4-ceb3-4344-b2ba-f7dd0eda1bff
-- title:
--   Robust mean $\sup\{E_P[Z] : D_f(P\|\widehat P_n)\le\rho/n\}$ of a sample
-- statement:
--   Let $z=(z_1,\dots,z_n)\in\mathbb R^n$ be a sample with empirical distribution $\widehat P_n$, let $f$ be a divergence function and $\rho\ge0$. A distribution $P\ll\widehat P_n$ is a weight vector $p\in\mathbb R^n$ with $p\ge0$ and $\sum_i p_i=1$, and its divergence from $\widehat P_n$ is $D_f(P\|\widehat P_n)=\sum_{i=1}^n\frac1n f(np_i)$. The **robust mean** of the sample is
--
--   $$
--   \sup_{P:\,D_f(P\|\widehat P_n)\le\rho/n} E_P[Z]\;=\;\sup\Big\{\sum_{i=1}^n p_iz_i \;:\; p\ge0,\ \sum_{i=1}^n p_i=1,\ \sum_{i=1}^n \tfrac1n f(np_i)\le\tfrac\rho n\Big\}.
--   $$
--
--   It is the upper endpoint of the generalized empirical likelihood confidence interval for the mean, and the quantity whose expansion is the goal of the mission.
--
--   **Formalization Note** The feasible set is the published `PhiDivRobust.Counterpart.probUncertaintySet f (fun _ => 1/n) (ρ/n)`, whose divergence is the published `phiDiv`. The supremum is Lean's real `sSup`; for $n>0$ and $\rho\ge0$ the set of values is non-empty (it contains the uniform weights, since $f(1)=0$) and bounded (it lies in the simplex), so `sSup` is the true supremum. Distributions not absolutely continuous with respect to $\widehat P_n$ are excluded, as in the paper's definitions (4) and (15).
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, p. 7, Lemma 1, (8); p. 32, (32)

import Mathlib
import Definitions.Def_PhiDivRobust_Counterpart_uncertaintySet

namespace GenEmpLik.Expansion

/-- The robust mean `sup { E_P[Z] : D_f(P ‖ P̂_n) ≤ ρ/n }` of the sample `z = (z₁, …, zₙ)`
(Duchi, Glynn & Namkoong, arXiv:1610.03425v3, p. 7, (8); the ball of (31)–(32), p. 32).
A distribution `P ≪ P̂_n` is a weight vector `p` on the sample, and
`D_f(P ‖ P̂_n) = ∑ᵢ (1/n) f(n pᵢ)` is the published `phiDiv f p (fun _ => 1/n)`, so the ball is the
published `probUncertaintySet f (fun _ => 1/n) (ρ/n) = {p ≥ 0 | ∑ pᵢ = 1, ∑ᵢ (1/n) f(n pᵢ) ≤ ρ/n}`.
For `0 < n` and `0 ≤ ρ` the set of values is non-empty (it contains the uniform vector, as
`f 1 = 0`) and bounded (it lies in the simplex), so the real `sSup` is the supremum. -/
noncomputable def robustMean {n : ℕ} (f : ℝ → EReal) (ρ : ℝ) (z : Fin n → ℝ) : ℝ :=
  sSup ((fun p : Fin n → ℝ => ∑ i, p i * z i) ''
    PhiDivRobust.Counterpart.probUncertaintySet f (fun _ => (1 : ℝ) / n) (ρ / n))

end GenEmpLik.Expansion


