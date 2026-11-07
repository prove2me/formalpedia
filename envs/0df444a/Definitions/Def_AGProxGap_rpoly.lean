-- Prove2me | Definitions.Def_AGProxGap_rpoly
-- name    : AGProxGap_rpoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:34:29.277709+00:00
-- url     : https://prove2.me/theorems/3fd7bd35-fcc6-445e-8735-9459edf88a7f
-- title:
--   The coordinate polynomial $r_i(Z)=\sum_{j=0}^{\ell} u_{j,i}Z^j$
-- statement:
--   Let $u_0,\dots,u_\ell\in\mathbb F_q^n$ and $i\in[n]$. The **coordinate polynomial** is
--   $$
--   r_i(Z)=\sum_{j=0}^{\ell} u_{j,i}Z^j\in\mathbb F_q[Z].
--   $$
--   Its value at $z$ is the $i$-th coordinate of $r(z)$. The interpolation identities of the proof (Lemma 3.4) are identities between these polynomials and the specializations of the auxiliary polynomials $A,B$.
--
--   **Formalization Note** A Mathlib `Polynomial K`, with the same indexing as `curve`.
-- source:
--   Li, Xing, Yuan, Zhu, On Proximity Gaps for One-Point Algebraic Geometric Codes, arXiv:2610.39256 (held version, sha256 d2017986…3b3f), §2.2, p.13

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace AGProxGap

/-- **The coordinate polynomial** `r_i(Z) = Σ_{j=0}^ℓ u_{j,i} Z^j ∈ F_q[Z]` (Li, Xing, Yuan, Zhu, *On Proximity Gaps for One-Point Algebraic Geometric Codes*, arXiv:2610.39256 (held version, sha256 d2017986…), §2.2, p.13:
"r_i(Z) = Σ_{j=0}^ℓ u_{j,i} Z^j where Z is an indeterminate").

**Formalization Note** `u : Fin (ℓ + 1) → Fin n → K` as in `curve`; `r_i(z)` is the `i`-th
coordinate of `curve u z`. -/
noncomputable def rpoly {K : Type*} [Field K] {n ℓ : ℕ} (u : Fin (ℓ + 1) → Fin n → K)
    (i : Fin n) : Polynomial K :=
  ∑ j : Fin (ℓ + 1), Polynomial.C (u j i) * Polynomial.X ^ (j : ℕ)

end AGProxGap


