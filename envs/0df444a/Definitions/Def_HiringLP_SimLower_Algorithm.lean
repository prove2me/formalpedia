-- Prove2me | Definitions.Def_HiringLP_SimLower_Algorithm
-- name    : HiringLP_SimLower_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T09:01:45.169482+00:00
-- url     : https://prove2.me/theorems/b127eed5-7f45-4239-99c9-7d7d10823c26
-- title:
--   §6.3, pp. 28–29 — the truncation y′ and the expected reward of ALG^s_sim
-- statement:
--   The algorithm $\mathrm{ALG}^s_{\mathrm{sim}}$ takes an optimal solution $y$ of $\mathrm{LP}_{\mathrm{sim}}(I)$ and a parameter $s\in[0,1]$.
--
--   **Truncation.** Let $\kappa=s\sum_{i\in[n]}y_ip_i$ be the total mass of $y$ scaled by $s$. The truncated vector $y'$ fills mass $\kappa$ from the smallest index: with $j$ the first index such that $\sum_{i=1}^{j+1}p_i>\kappa$,
--   $$y'_i=1\ (1\le i\le j),\qquad y'_{j+1}\ \text{such that}\ \sum_{i=1}^{j+1}y'_ip_i=\kappa,\qquad y'_i=0\ (j+2\le i\le n),$$
--   and $y'=\mathbf 1$ if no such $j$ exists. Equivalently,
--   $$y'_i=\min\Big\{1,\ \max\Big\{0,\ \frac{\kappa-\sum_{l<i}p_l}{p_i}\Big\}\Big\}\qquad(p_i>0).$$
--
--   **Run.** The offer to candidate $i$ is sent independently with probability $y'_i$, so candidate $i$ is hired independently with probability $y'_ip_i$. The expected reward of the run is
--   $$R_{\mathrm{ALG}^s_{\mathrm{sim}}}(I)=R(I;y'),$$
--   the expected reward of independent offers with probabilities $y'$ defined in the model file. Because $y'$ is a filled prefix, the algorithm randomises between two value-ordered policies.
--
--   **Formalization Note** Indices are 0-based. A candidate with $p_i=0$ gets $y'_i=0$ (the page's construction may set it to 1 when it lies in the filled prefix); such a candidate never accepts, so no reward changes. The algorithm uses $y$ only through its total mass, so `algReward I y s` is defined for any vector $y$; the theorems apply it to optimal solutions.
-- source:
--   Epstein, Ma, Selection and Ordering Policies for Hiring Pipelines via Linear Programming, arXiv:2210.04059v3, pp. 28–29, §6.3

import Mathlib
import Definitions.Def_HiringLP_SimLower_Model

open Finset

namespace HiringLP.SimLower

/-- The truncation of pp. 28–29: fill mass `κ` from the smallest index, `y′ᵢ = 1` while the prefix mass
`Σ_{l ≤ i} p_l` stays at most `κ`, then one fractional entry with `Σ y′ᵢpᵢ = κ`, then `0`. Entries with
`pᵢ = 0` are set to `0`; they never accept, so this does not affect any reward. -/
noncomputable def truncate {n : ℕ} (I : SimInstance n) (κ : ℝ) (i : Fin n) : ℝ :=
  if I.p i = 0 then 0
  else min 1 (max 0 ((κ - ∑ l ∈ univ.filter (fun l => l < i), I.p l) / I.p i))

/-- Expected reward `R_{ALG^s_sim}(I)` of `ALG^s_sim` (pp. 28–29) run on the LP solution `y`:
`κ = s · Σᵢ yᵢpᵢ`, `y′ = truncate I κ`, and the offer to candidate `i` is sent independently with
probability `y′ᵢ`. -/
noncomputable def algReward {n : ℕ} (I : SimInstance n) (y : Fin n → ℝ) (s : ℝ) : ℝ :=
  rewardIndep I (truncate I (s * ∑ i, y i * I.p i))

end HiringLP.SimLower


