-- Prove2me | Definitions.Def_AutobidSPPE_IsBayesianSPPE
-- name    : AutobidSPPE_IsBayesianSPPE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T18:01:32.12164+00:00
-- url     : https://prove2.me/theorems/eba01ea4-a7a8-44d4-9689-d03e244bad99
-- title:
--   Ex-ante Bayesian second-price pacing equilibrium (Problem 1.1)
-- statement:
--   Given budgets $\rho_1,\dots,\rho_n$, a profile $\alpha\in[0,1]^n$ is an **ex-ante Bayesian SPPE** if for every bidder $i$
--   $$
--   \alpha_i \in \operatorname*{arg\,min}_{a_i\in[0,1],\ g_i(a_i,\alpha_{-i})\le 0} l_i(a_i,\alpha_{-i}),
--   \qquad g_i = s_i-\rho_i .
--   $$
--   That is, $\alpha_i$ is budget feasible, $s_i(\alpha)\le\rho_i$, and no feasible deviation $a\in[0,1]$ with $s_i(a,\alpha_{-i})\le\rho_i$ has a strictly smaller loss.
--
--   **Formalization Note** The argmin is spelled out as feasibility plus "loss at most that of every feasible deviation".
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), Problem 1.1, p.4

import Mathlib
import Definitions.Def_AutobidSPPE_loss
import Definitions.Def_AutobidSPPE_spend

namespace AutobidSPPE

/-- An ex-ante Bayesian second-price pacing equilibrium (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), Problem 1.1, p.4): a profile
`α ∈ [0,1]ⁿ` such that for every bidder `i`,
`αᵢ ∈ argmin {lᵢ(aᵢ, α₋ᵢ) : aᵢ ∈ [0,1], gᵢ(aᵢ, α₋ᵢ) ≤ 0}`, with `gᵢ = sᵢ − ρᵢ`.

**Formalization Note** "`αᵢ ∈ argmin`" is spelled out: `αᵢ` is feasible and its loss is at
most the loss of every feasible deviation `a ∈ [0,1]`. The budget constraint is `sᵢ ≤ ρᵢ`. -/
def IsBayesianSPPE {n : ℕ} (vbar ρ : Fin n → ℝ) (tie : TieRule n) (α : Fin n → ℝ) : Prop :=
  (∀ i, α i ∈ Set.Icc (0 : ℝ) 1) ∧
  ∀ i, spend vbar tie α i ≤ ρ i ∧
    ∀ a ∈ Set.Icc (0 : ℝ) 1, spend vbar tie (Function.update α i a) i ≤ ρ i →
      loss vbar tie α i ≤ loss vbar tie (Function.update α i a) i

end AutobidSPPE


