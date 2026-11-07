-- Prove2me | Definitions.Def_AGProxGap_OnePointData
-- name    : AGProxGap_OnePointData
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:33:42.617087+00:00
-- url     : https://prove2.me/theorems/cd22b72b-7ad7-400e-9742-014763136472
-- title:
--   Pairwise distinct rational points $P_1,\dots,P_n,P_\infty$ and $0<m<n$
-- statement:
--   Let $F/\mathbb F_q$ be the function field of a curve $X$. The data $(P_1,\dots,P_n,P_\infty,m)$ of a one-point AG code satisfy:
--   1. $P_1,\dots,P_n$ are pairwise distinct;
--   2. every $P_i$ is a rational point of $X$ (residue field $\mathbb F_q$);
--   3. $P_\infty$ is a rational point;
--   4. $P_i\ne P_\infty$ for every $i$;
--   5. $m$ is a positive integer;
--   6. $m<n$.
--
--   These are the hypotheses of §2.3 ("Let $P_1,\dots,P_n,P_\infty\in X(\mathbb F_q)$ be pairwise distinct … $m<n$ is a positive integer") under which $C_L(D,mP_\infty)$ has length $n$ and designed distance $d=n-m\ge 1$.
--
--   **Formalization Note** Rational points are places with `AlgebraicCurve.Place.IsRational` (the map $\mathbb F_q\to$ residue field is onto). The genus condition $2\mathfrak g-1\le m$ of §1.1 and the assumption $l(G)=m+1-\mathfrak g$ of §3 are deliberately not included; no statement of the mission needs them.
-- source:
--   Li, Xing, Yuan, Zhu, On Proximity Gaps for One-Point Algebraic Geometric Codes, arXiv:2610.39256 (held version, sha256 d2017986…3b3f), §2.3, p.14

import Mathlib
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

namespace AGProxGap

/-- **The data of a one-point AG code** (Li, Xing, Yuan, Zhu, *On Proximity Gaps for One-Point Algebraic Geometric Codes*, arXiv:2610.39256 (held version, sha256 d2017986…), §2.3, p.14: "Let P_1, . . . , P_n, P_∞ ∈ X(F_q) be
pairwise distinct, and set D = P_1 + · · · + P_n and G = mP_∞ where m < n is a positive
integer"). The fields are:
1. `injective`: the places `P_1, …, P_n` are pairwise distinct;
2. `isRational`: every `P_i` is a rational point (residue field equal to the constant field);
3. `isRational_inf`: `P_∞` is a rational point;
4. `ne_inf`: `P_i ≠ P_∞` for every `i`;
5. `pos`: `0 < m`;
6. `lt`: `m < n`.

**Formalization Note** Points of `X(F_q)` are places of the function field `F/F_q` with residue
degree one (`AlgebraicCurve.Place.IsRational`). The genus condition `2𝔤 − 1 ≤ m` of §1.1 (p.3)
and the assumption `l(G) = m + 1 − 𝔤` of §3 (p.17) are not part of this structure. -/
structure OnePointData {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ}
    (P : Fin n → Place K F) (Pinf : Place K F) (m : ℕ) : Prop where
  injective : Function.Injective P
  isRational : ∀ i, (P i).IsRational
  isRational_inf : Pinf.IsRational
  ne_inf : ∀ i, P i ≠ Pinf
  pos : 0 < m
  lt : m < n

end AGProxGap


