-- Prove2me | Definitions.Def_AGProxGap_Supplement_localCoeff
-- name    : AGProxGap_Supplement_localCoeff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:17:15.285209+00:00
-- url     : https://prove2.me/theorems/a979bec3-3ac9-4563-8cfa-51ee5a8adfd8
-- title:
--   Local expansion coefficients $[t^j]f$ at a place
-- statement:
--   Let $P$ be a rational place with local parameter $t$ (so $v_P(t)=1$) and $f\in\mathcal O_P$. Then $f$ has a unique formal expansion $f=\sum_{j\ge0}a_jt^j$ with constant coefficients, and $[t^j]f:=a_j$; in particular $[t^0]f=f(P)$. The coefficients are computed by
--   $$a_j=\mathrm{rem}_j(P),\qquad \mathrm{rem}_0=f,\qquad \mathrm{rem}_{j+1}=\frac{\mathrm{rem}_j-a_j}{t}.$$
--
--   These coefficients enter Lemma 4.2 ($h(P_i)=\sum_j\lambda_{i,j}[t^j]h$) and the Hensel lifting (7) of §4.2.
--
--   **Formalization Note** The value at $P$ is the platform's evaluation at a place. For $f\in\mathcal O_P$ every remainder stays in $\mathcal O_P$ and $f-\sum_{k\le j}a_kt^k=t^{j+1}\mathrm{rem}_{j+1}$, so these are the expansion coefficients; off $\mathcal O_P$ the value is not meaningful and is never used.
-- source:
--   Li, Xing, Yuan, Zhu, On Proximity Gaps for One-Point Algebraic Geometric Codes, arXiv:2610.39256 (held version, sha256 d2017986…3b3f), §2.3, p.15

import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

namespace AGProxGap.Supplement

/-- The remainders of the local expansion: `rem_0 = f`, `rem_{j+1} = (rem_j − rem_j(P))/t`, so
that `f = Σ_{k ≤ j} a_k t^k + t^{j+1} rem_{j+1}` with `a_k = rem_k(P)`. -/
noncomputable def expansionRem {K F : Type*} [Field K] [Field F] [Algebra K F] (P : Place K F)
    (t f : F) : ℕ → F
  | 0 => f
  | j + 1 => (expansionRem P t f j - algebraMap K F (P.evalAt (expansionRem P t f j))) / t

/-- **The local expansion coefficient** `[t^j]f` (Li, Xing, Yuan, Zhu, *On Proximity Gaps for One-Point Algebraic Geometric Codes*, arXiv:2610.39256 (held version, sha256 d2017986…), §2.3, p.15: "For a local parameter t at
P, every f ∈ O_P has a unique formal expansion f = Σ_{j≥0} a_j t^j with a_j ∈ F_q. We write
[t^j]f = a_j and in particular, [t^0]f = f(P)").

For a rational place `P`, a local parameter `t` (`ord_P t = 1`) and `f ∈ 𝒪_P`, the coefficients
are computed by `a_0 = f(P)` and `a_j = rem_j(P)` with `rem_0 = f`,
`rem_{j+1} = (rem_j − a_j)/t` (`expansionRem`).

**Formalization Note** `f(P)` is the platform's `Place.evalAt`. When `f ∈ 𝒪_P` and `t` is a local
parameter, every remainder lies in `𝒪_P` (`rem_j − a_j` vanishes at `P`, so dividing by `t` keeps
it regular), and `f − Σ_{k≤j} a_k t^k = t^{j+1} rem_{j+1}` has order at least `j + 1`: these
are exactly the unique coefficients of the formal expansion. Off `𝒪_P` the value is junk; every
statement applies it only to functions regular at `P`. -/
noncomputable def localCoeff {K F : Type*} [Field K] [Field F] [Algebra K F] (P : Place K F)
    (t f : F) (j : ℕ) : K :=
  P.evalAt (expansionRem P t f j)

end AGProxGap.Supplement


