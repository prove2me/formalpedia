-- Prove2me | Definitions.Def_AutobidSPPE_IsCondEq
-- name    : AutobidSPPE_IsCondEq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T18:02:32.9212+00:00
-- url     : https://prove2.me/theorems/867733c8-d19a-4429-88fe-7171ae07c259
-- title:
--   Conditional equilibrium of a prefix of bidders
-- statement:
--   Fix the bidder order and $k\in\{0,\dots,n\}$. An endpoint profile $z$ is a **conditional equilibrium of the prefix** $[k]=\{1,\dots,k\}$ if $z\in\mathcal Y$ and every bidder of the prefix plays its capped endpoint response,
--   $$
--   z_i=\mathsf b_i(z_{-i})\qquad (i\le k),
--   $$
--   while the later endpoints $z_{>k}$ are held fixed as parameters. The paper's $p^{[k]}(v)$ is the prefix part of such a $z$ whose later endpoints equal $v\in\mathcal Y_{>k}$; for $k=n$ these are the endpoint equilibria.
--
--   **Formalization Note** Bidders $1,\dots,k$ are the indices $0,\dots,k-1$ of `Fin n`; a profile carries both its prefix and its fixed suffix.
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), Lemma 2.11, p.17; §2.8, p.21

import Mathlib
import Definitions.Def_AutobidSPPE_endpointBox
import Definitions.Def_AutobidSPPE_endpointResponse

namespace AutobidSPPE

/-- A conditional equilibrium of the prefix of the first `k` bidders (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), Lemma 2.11, p.17;
§2.8, p.21): the profile `z` lies in `𝒴` and every bidder of the prefix plays its endpoint
response, `zᵢ = 𝖻ᵢ(z₋ᵢ)`; the later endpoints `z_{>k}` are the fixed parameters.

**Formalization Note** A full profile carries both parts: the paper's `p^[k](v)` is the prefix
of the `z` with `IsCondEq k z` whose suffix `{j : k ≤ j}` (0-based) equals `v`. The paper's
bidders `1, …, k` are the indices `0, …, k − 1`. `k = n` is the full endpoint equilibrium. -/
def IsCondEq {n : ℕ} (vbar ρ : Fin n → ℝ) (k : ℕ) (z : Fin n → ℝ) : Prop :=
  z ∈ endpointBox vbar ρ ∧ ∀ i : Fin n, i.val < k → z i = endpointResponse vbar ρ z i

end AutobidSPPE


