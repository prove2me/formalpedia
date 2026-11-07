-- Prove2me | Definitions.Def_AGProxGap_curve
-- name    : AGProxGap_curve
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:34:09.459902+00:00
-- url     : https://prove2.me/theorems/73a409fd-7912-46b4-9d89-29ca9bb5d0f4
-- title:
--   The polynomial curve $r(z)=\sum_{j=0}^{\ell} u_j z^j$
-- statement:
--   Let $u_0,\dots,u_\ell\in\mathbb F_q^n$. The **polynomial curve** through them is
--   $$
--   r(z)=\sum_{j=0}^{\ell} u_j z^j\in\mathbb F_q^n\qquad (z\in\mathbb F_q).
--   $$
--   For $\ell=1$ this is the affine line $u_0+zu_1$. Proximity gaps and correlated agreement are statements about how many points $r(z)$ of such a curve are close to a code.
--
--   **Formalization Note** The words are a function `u : Fin (ℓ+1) → Fin n → K`, with `u j i` the coordinate $u_{j,i}$; indices are 0-based.
-- source:
--   Li, Xing, Yuan, Zhu, On Proximity Gaps for One-Point Algebraic Geometric Codes, arXiv:2610.39256 (held version, sha256 d2017986…3b3f), §2.2, p.13

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace AGProxGap

/-- **The polynomial curve** `r(z) = Σ_{j=0}^ℓ u_j z^j ∈ F_q^n` through the words
`u_0, …, u_ℓ ∈ F_q^n` (Li, Xing, Yuan, Zhu, *On Proximity Gaps for One-Point Algebraic Geometric Codes*, arXiv:2610.39256 (held version, sha256 d2017986…), §2.2, p.13: "For u_0, . . . , u_ℓ ∈ F_q^n, write
r(Z) = Σ_{j=0}^ℓ u_j Z^j").

**Formalization Note** The `ℓ + 1` words are indexed by `Fin (ℓ + 1)`, with `u j` the word
`u_j` (0-based, as in the paper) and `u j i` its `i`-th coordinate `u_{j,i}`; coordinates are
`Fin n` (the paper's `[n] = {1, …, n}`, shifted by one). -/
def curve {K : Type*} [Field K] {n ℓ : ℕ} (u : Fin (ℓ + 1) → Fin n → K) (z : K) : Fin n → K :=
  ∑ j : Fin (ℓ + 1), z ^ (j : ℕ) • u j

end AGProxGap


