-- Prove2me | Definitions.Def_AutobidSPPE_Supplement_IsBayesianSPTE
-- name    : AutobidSPPE_Supplement_IsBayesianSPTE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:40:16.117538+00:00
-- url     : https://prove2.me/theorems/d8ca9b39-a3d2-48e0-99ed-e0e4b76021ef
-- title:
--   Bayesian second-price throttling equilibrium (SPTE)
-- statement:
--   Let values be independent with $v_i\sim\mathrm{Unif}[0,\bar v_i]$ and let $\rho_i$ be bidder $i$'s budget. A profile $\alpha\in[0,1]^n$ is an **ex-ante Bayesian SPTE** if for every bidder $i$
--   $$
--   \alpha_i\in\operatorname*{arg\,min}_{a_i\in[0,1],\ g_i(a_i,\alpha_{-i})\le 0} l_i(a_i,\alpha_{-i}),\qquad g_i=s_i-\rho_i .
--   $$
--
--   **Formalization Note** The argmin is spelled out: $\alpha_i$ is budget-feasible and its loss is at most that of every feasible deviation $a\in[0,1]$. This is the definition of Problem 1.2, not "a fixed point of the response"; that the two agree is a claim of §3.3.
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), Problem 1.2, p.4; A1, p.28

import Mathlib
import Definitions.Def_AutobidSPPE_valueLaw
import Definitions.Def_AutobidSPPE_Supplement_spendT
import Definitions.Def_AutobidSPPE_Supplement_lossT

namespace AutobidSPPE.Supplement

open AutobidSPPE

/-- An ex-ante Bayesian second-price throttling equilibrium
(Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), Problem 1.2, p.4): a profile `α ∈ [0,1]ⁿ` such that for every bidder `i`,
`αᵢ ∈ argmin {lᵢ(aᵢ, α₋ᵢ) : aᵢ ∈ [0,1], gᵢ(aᵢ, α₋ᵢ) ≤ 0}`, `gᵢ = sᵢ − ρᵢ`, under independent uniform values
`vᵢ ∼ Unif[0, v̄ᵢ]` (A1, p.28).

**Formalization Note** "`αᵢ ∈ argmin`" is spelled out: `αᵢ` is budget-feasible and its loss is at most the
loss of every feasible deviation `a ∈ [0,1]`. This is the definition of Problem 1.2, not "fixed point of the
response" (that the two agree is a claim of §3.3, p.27). -/
def IsBayesianSPTE {n : ℕ} (vbar ρ : Fin n → ℝ) (tie : TieRule n) (α : Fin n → ℝ) : Prop :=
  (∀ i, α i ∈ Set.Icc (0 : ℝ) 1) ∧
  ∀ i, spendT (valueLaw vbar) tie α i ≤ ρ i ∧
    ∀ a ∈ Set.Icc (0 : ℝ) 1, spendT (valueLaw vbar) tie (Function.update α i a) i ≤ ρ i →
      lossT (valueLaw vbar) tie α i ≤ lossT (valueLaw vbar) tie (Function.update α i a) i

end AutobidSPPE.Supplement


