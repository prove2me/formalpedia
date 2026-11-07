-- Prove2me | Definitions.Def_AGProxGap_evalPolyAt
-- name    : AGProxGap_evalPolyAt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:37:06.95929+00:00
-- url     : https://prove2.me/theorems/f6b45b2b-f4ea-4a97-a1b6-6382c0475d76
-- title:
--   The specialization $A(P,Z)$ of a polynomial with function coefficients
-- statement:
--   Let $K(X)/K$ be a function field, $P$ a place, and $A(\cdot,Z)=\sum_j A_jZ^j$ a polynomial whose coefficients $A_j$ are functions in $K(X)$. Its **specialization at $P$** is
--   $$
--   A(P,Z)=\sum_j A_j(P)\,Z^j\in K[Z].
--   $$
--   The interpolation identities $A(P_i,Z)r_i(Z)=B(P_i,Z)$ of Lemma 3.4 and the set $T=\{i: A(P_i,Z)\equiv 0\}$ of Lemma 3.6 are written with it.
--
--   **Formalization Note** $A_j(P)$ is `AlgebraicCurve.Place.evalAt` (junk $0$ off the valuation ring of $P$). It is applied only to coefficients in $L_K(H)$ or $L_K(G+H)$ at points outside $\operatorname{supp}G\cup\operatorname{supp}H$, where they are regular.
-- source:
--   Li, Xing, Yuan, Zhu, On Proximity Gaps for One-Point Algebraic Geometric Codes, arXiv:2610.39256 (held version, sha256 d2017986…3b3f), Lemma 3.4, p.19; §3, p.20

import Mathlib
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

namespace AGProxGap

/-- **Specializing the function coefficients of a polynomial at a point**: for
`A(·, Z) = Σ_j A_j Z^j` with `A_j` in the function field, `A(P, Z) = Σ_j A_j(P) Z^j ∈ K[Z]`
(Li, Xing, Yuan, Zhu, *On Proximity Gaps for One-Point Algebraic Geometric Codes*, arXiv:2610.39256 (held version, sha256 d2017986…), Lemma 3.4, p.19: "A(P_i, Z)r_i(Z) = B(P_i, Z)"; §3, p.20: "T := {i ∈ [n] : A(P_i, Z) ≡ 0}").

**Formalization Note** `A_j(P)` is `AlgebraicCurve.Place.evalAt`, the value at `P` (junk `0` off
the valuation ring of `P`). Every statement applies it only to polynomials whose coefficients lie
in `L_K(H)` or `L_K(G + H)` with `P ∉ supp G ∪ supp H`, where all coefficients are regular at
`P`. -/
noncomputable def evalPolyAt {K F : Type*} [Field K] [Field F] [Algebra K F] (Q : Place K F)
    (A : Polynomial F) : Polynomial K :=
  A.sum (fun j a => Polynomial.monomial j (Q.evalAt a))

end AGProxGap


