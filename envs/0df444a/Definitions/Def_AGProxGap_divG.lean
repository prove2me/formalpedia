-- Prove2me | Definitions.Def_AGProxGap_divG
-- name    : AGProxGap_divG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:33:20.476866+00:00
-- url     : https://prove2.me/theorems/18e82551-57c7-40a7-80f9-3d477df778b1
-- title:
--   The one-point divisor $G=mP_\infty$
-- statement:
--   Let $F/K$ be an algebraic function field and $P_\infty$ a place of $F$. For an integer $m\ge 0$ the **one-point divisor** is
--   $$
--   G = mP_\infty ,
--   $$
--   the divisor with multiplicity $m$ at $P_\infty$ and $0$ elsewhere. With $D=P_1+\dots+P_n$ it is the pair of divisors defining the one-point algebraic geometric code $C_L(D,G)$.
--
--   **Formalization Note** A divisor is the platform's `AlgebraicCurve.Divisor K F` (finitely supported functions from places to $\mathbb Z$), and $G$ is `Finsupp.single Pinf m`. The definition is generic in the constant field, so applied to the place $P_\infty'$ of a constant field extension it gives the base-changed divisor $G$ on $X_K$.
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

/-- **The one-point divisor** `G = m P_∞` (Li, Xing, Yuan, Zhu, *On Proximity Gaps for One-Point Algebraic Geometric Codes*, arXiv:2610.39256 (held version, sha256 d2017986…), §2.3, p.14: "set D = P_1 + · · · + P_n and
G = mP_∞ where m < n is a positive integer").

**Formalization Note** A divisor is the platform's `AlgebraicCurve.Divisor K F`, a finitely
supported function from places to `ℤ`; `G` is the single place `P_∞` with multiplicity `m`. The
definition is generic in the constant field, so the same `divG` gives the base-changed divisor
`m P'_∞` on a constant field extension (§3, p.17: "We use the same notation for … the divisor G
after base change"). -/
noncomputable def divG {K F : Type*} [Field K] [Field F] [Algebra K F] (Pinf : Place K F)
    (m : ℕ) : Divisor K F :=
  Finsupp.single Pinf (m : ℤ)

end AGProxGap


