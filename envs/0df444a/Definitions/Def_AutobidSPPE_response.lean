-- Prove2me | Definitions.Def_AutobidSPPE_response
-- name    : AutobidSPPE_response
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T18:01:16.326514+00:00
-- url     : https://prove2.me/theorems/8c7be2d5-dc7c-4d9f-9821-aed7b41c2208
-- title:
--   Largest budget-feasible response $r_i(\alpha_{-i})$
-- statement:
--   The **expected-budget response** of bidder $i$ to rival multipliers $\alpha_{-i}$ is the largest feasible multiplier
--   $$
--   r_i(\alpha_{-i}) = \max\{u\in[0,1] : s_i(u,\alpha_{-i})\le\rho_i\}.
--   $$
--
--   **Formalization Note** The maximum is written as the supremum of the feasible set; the set contains $u=0$ (a zero bid never pays) and is bounded by $1$, and Lemma 2.7 shows it is a closed interval, so the supremum is attained. The own coordinate is replaced by $u$, so $r_i$ depends on $\alpha_{-i}$ only.
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), (5), p.10

import Mathlib
import Definitions.Def_AutobidSPPE_spend

namespace AutobidSPPE

/-- The largest budget-feasible response `rᵢ(α₋ᵢ) = max{u ∈ [0,1] : sᵢ(u, α₋ᵢ) ≤ ρᵢ}`
(Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), (5), p.10).

**Formalization Note** The maximum is written as `sSup`. The set contains `u = 0` (a zero bid
pays nothing) and is bounded by `1`; Lemma 2.7 shows it is a closed interval, so the `sSup` is
attained. The own coordinate `αᵢ` is overwritten, so the response depends on `α₋ᵢ` only. -/
noncomputable def response {n : ℕ} (vbar ρ : Fin n → ℝ) (tie : TieRule n) (α : Fin n → ℝ)
    (i : Fin n) : ℝ :=
  sSup {u | u ∈ Set.Icc (0 : ℝ) 1 ∧ spend vbar tie (Function.update α i u) i ≤ ρ i}

end AutobidSPPE


