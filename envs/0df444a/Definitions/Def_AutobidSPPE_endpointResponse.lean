-- Prove2me | Definitions.Def_AutobidSPPE_endpointResponse
-- name    : AutobidSPPE_endpointResponse
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T18:01:33.255818+00:00
-- url     : https://prove2.me/theorems/99273e28-eef3-4f97-b76c-f43fbc45ce97
-- title:
--   Capped endpoint response $\mathsf b_i(y_{-i})$
-- statement:
--   The **capped endpoint response** of bidder $i$ is
--   $$
--   \mathsf b_i(y_{-i}) = \max\{a\in[0,\bar v_i] : \mathsf s_i(a,y_{-i})\le\rho_i\}.
--   $$
--
--   **Formalization Note** The maximum is the supremum of the feasible set; the own coordinate $y_i$ is overwritten by $a$.
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), (7), p.10

import Mathlib
import Definitions.Def_AutobidSPPE_endpointSpend

namespace AutobidSPPE

/-- The capped endpoint response `𝖻ᵢ(y₋ᵢ) = max{a ∈ [0, v̄ᵢ] : 𝗌ᵢ(a, y₋ᵢ) ≤ ρᵢ}` (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), (7),
p.10).

**Formalization Note** `max` is `sSup`; the own coordinate `yᵢ` is overwritten. -/
noncomputable def endpointResponse {n : ℕ} (vbar ρ y : Fin n → ℝ) (i : Fin n) : ℝ :=
  sSup {a | a ∈ Set.Icc (0 : ℝ) (vbar i) ∧ endpointSpend (Function.update y i a) i ≤ ρ i}

end AutobidSPPE


