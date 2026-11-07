-- Prove2me | Definitions.Def_AGProxGap_Me
-- name    : AGProxGap_Me
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:35:56.533735+00:00
-- url     : https://prove2.me/theorems/20848587-f35a-46f5-ad59-f095ed2dde8a
-- title:
--   The parameters $D_Z=\lfloor \ell e/(d-2e)\rfloor+1$ and $M_e=\lfloor(\ell+1)n(D_Z-1)/(e+1)\rfloor$
-- statement:
--   For integers $\ell\ge 1$, $e\ge 0$, $n$ and $d$ with $2e<d$, equation (3) of the paper sets
--   $$
--   D_Z=\Bigl\lfloor\frac{\ell e}{d-2e}\Bigr\rfloor+1,\qquad
--   M_e=\Bigl\lfloor\frac{(\ell+1)n(D_Z-1)}{e+1}\Bigr\rfloor .
--   $$
--   $D_Z$ is the smallest admissible $Z$-degree bound of the Berlekamp–Welch interpolation in Theorem 3.1, and $M_e$ is the resulting threshold on $|S|$; both soundness bounds of the paper (Corollaries 3.9 and 3.11) are stated through $M_e$.
--
--   **Formalization Note** Natural-number division is the floor. $d$ is passed as $n-m$; it is used only with $2e<d$, where $d-2e$ is the true difference, and $D_Z-1$ is a true difference since $D_Z\ge 1$.
-- source:
--   Li, Xing, Yuan, Zhu, On Proximity Gaps for One-Point Algebraic Geometric Codes, arXiv:2610.39256 (held version, sha256 d2017986…3b3f), Corollary 3.9, eq. (3), p.22

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace AGProxGap

/-- **The interpolation degree** `D_Z := ⌊ℓe/(d − 2e)⌋ + 1` of (3) (Li, Xing, Yuan, Zhu, *On Proximity Gaps for One-Point Algebraic Geometric Codes*, arXiv:2610.39256 (held version, sha256 d2017986…), Corollary 3.9, p.22).

**Formalization Note** Natural-number division is the floor; `d = n − m`. Only used with
`2e < d`, where `d − 2e` is the true difference. -/
def DZ (ℓ e d : ℕ) : ℕ := ℓ * e / (d - 2 * e) + 1

/-- **The threshold** `M_e := ⌊(ℓ + 1)n(D_Z − 1)/(e + 1)⌋` of (3) (Li, Xing, Yuan, Zhu, *On Proximity Gaps for One-Point Algebraic Geometric Codes*, arXiv:2610.39256 (held version, sha256 d2017986…), Corollary 3.9, p.22),
with `D_Z = ⌊ℓe/(d − 2e)⌋ + 1`.

**Formalization Note** Natural-number division is the floor; `D_Z − 1 = ⌊ℓe/(d − 2e)⌋` is a
true difference since `D_Z ≥ 1`. -/
def Me (ℓ e n d : ℕ) : ℕ := (ℓ + 1) * n * (DZ ℓ e d - 1) / (e + 1)

end AGProxGap


