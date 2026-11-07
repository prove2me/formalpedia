-- Prove2me | Definitions.Def_AGProxGap_agCode
-- name    : AGProxGap_agCode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:35:20.027181+00:00
-- url     : https://prove2.me/theorems/f8984806-ec4f-446d-ba4d-66395fda4ddf
-- title:
--   The one-point AG code $C_L(D,mP_\infty)$
-- statement:
--   Let $F/\mathbb F_q$ be the function field of a curve $X$, let $P_1,\dots,P_n,P_\infty$ be places of $F$, $D=P_1+\dots+P_n$ and $G=mP_\infty$. The **one-point algebraic geometric code** is
--   $$
--   C = C_L(D,G) = \{\, f(D) : f\in L(G)\,\}\subseteq \mathbb F_q^n,
--   $$
--   where $L(G)=\{0\}\cup\{f\in F^\ast : (f)+G\ge 0\}$ is the Riemann–Roch space of $G$ and $f(D)=(f(P_1),\dots,f(P_n))$.
--
--   This is the code whose proximity properties the mission studies. When the places are pairwise distinct and rational and $0<m<n$, it is a linear code of designed distance $d=n-m$.
--
--   **Formalization Note** The general code $C_L(D,G)$ is the published `BeatingGV42.goppaCode`: the $K$-span of the image of $L(G)$ = `AlgebraicCurve.LSpace` under the evaluation map `BeatingGV42.evalVec` ($f\mapsto(f(P_1),\dots,f(P_n))$, with $f(P_i)$ the platform's `Place.evalAt`). This definition takes $G=mP_\infty$ and views the code as a set of words `Fin n → K`. Under the hypotheses every statement carries as `OnePointData` (distinct rational places, $P_\infty\notin\operatorname{supp}D$, $0<m<n$), $L(G)$ lies in every valuation ring at $P_i$ and evaluation is $K$-linear there, so the span is exactly the set displayed above.
-- source:
--   Li, Xing, Yuan, Zhu, On Proximity Gaps for One-Point Algebraic Geometric Codes, arXiv:2610.39256 (held version, sha256 d2017986…3b3f), §2.3, p.14

import Mathlib
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AGProxGap_divG
import Definitions.Def_BeatingGV42_goppaCode

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

namespace AGProxGap

/-- **The one-point algebraic geometric code** `C = C_L(D, G) = {f(D) : f ∈ L(G)} ⊆ F_q^n`
with `D = P_1 + ⋯ + P_n` and `G = m P_∞` (Li, Xing, Yuan, Zhu, *On Proximity Gaps for One-Point Algebraic Geometric Codes*, arXiv:2610.39256 (held version, sha256 d2017986…), §2.3, p.14).

**Formalization Note** The general code `C_L(D, G)` is the published
`BeatingGV42.goppaCode P G`: the `K`-span of the image of the Riemann–Roch space
`L(G) = AlgebraicCurve.LSpace G` under the evaluation map `BeatingGV42.evalVec P`
(`f ↦ (f(P_1), …, f(P_n))`, with `f(P_i)` the platform's `Place.evalAt`). This definition takes
`G = m P_∞` and views the code as a set of words `Fin n → K`. Under the hypotheses every statement
carries as `OnePointData` (distinct rational places, `P_∞ ∉ supp D`, `0 < m < n`), `L(G)` lies in
every valuation ring `𝒪_{P_i}` and evaluation is `K`-linear there, so the span is the paper's set
`{f(D) : f ∈ L(G)}`. -/
noncomputable def agCode {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ}
    (P : Fin n → Place K F) (Pinf : Place K F) (m : ℕ) : Set (Fin n → K) :=
  (BeatingGV42.goppaCode P (divG Pinf m) : Set (Fin n → K))

end AGProxGap


