-- Prove2me | Definitions.Def_HiringLP_SimUpper_Constants
-- name    : HiringLP_SimUpper_Constants
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T10:58:07.724991+00:00
-- url     : https://prove2.me/theorems/9f6309b0-49d5-4c64-b1cc-91af9b031656
-- title:
--   Theorems 3–4, p. 30 — E[min{Pois(λ), k}] and the constants α^τ_k, β^τ_k
-- statement:
--   For $\lambda \ge 0$ and an integer $k$, let
--   $$
--   \mathbb{E}[\min\{\mathrm{Pois}(\lambda), k\}] = \sum_{j \ge 0} \min\{j, k\}\, e^{-\lambda} \frac{\lambda^j}{j!}
--   $$
--   be the expected value of a Poisson($\lambda$) variable truncated at $k$. For $\tau \in (0,1)$ and $k \ge 1$ consider the objective
--   $$
--   f_{k,\tau}(s) = s - \frac{s}{\tau} + \frac{\mathbb{E}[\min\{\mathrm{Pois}(sk), k\}]}{\tau k}.
--   $$
--   The paper's constants are
--   $$
--   \alpha^\tau_k = \sup_{0 \le s \le 1} f_{k,\tau}(s), \qquad \beta^\tau_k = \sup_{s \ge 0} f_{k,\tau}(s).
--   $$
--   $\alpha^\tau_k$ is the guarantee of the truncated-LP value-ordered policy (Theorem 3) and $\beta^\tau_k$ is the upper bound on what any value-ordered policy can guarantee (Theorem 4). They differ only in the constraint $s \le 1$.
--
--   **Formalization Note.** The Poisson expectation is written as the series with the Poisson pmf (`tsum`), which is summable since $\min\{j,k\} \le k$. The suprema are real `sSup` of images of `[0, 1]` and `[0, ∞)`; both sets are nonempty and bounded above for $\tau \in (0,1)$, $k \ge 1$ (the objective is at most $1/\tau$ and tends to $-\infty$), so `sSup` is the true supremum there. $f_{k,\tau}(0) = 0$.
-- source:
--   Epstein, Ma, Selection and Ordering Policies for Hiring Pipelines via Linear Programming, arXiv:2210.04059v3, p. 30, Theorem 3 (α^τ_k) and Theorem 4 (β^τ_k)

import Mathlib
import Definitions.Def_HiringLP_SimLower_PoissonRatio

namespace HiringLP.SimUpper

open Finset

/-- `β^τ_k = sup_{s ≥ 0} (s − s/τ + E[min{Pois(sk), k}]/(τk))` (Theorem 4, p. 30). -/
noncomputable def beta (k : ℕ) (τ : ℝ) : ℝ := sSup (HiringLP.SimLower.ratioObj k τ '' Set.Ici 0)

end HiringLP.SimUpper


