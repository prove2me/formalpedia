-- Prove2me | Definitions.Def_BeatingGV42_goppaCode
-- name    : BeatingGV42_goppaCode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:31:43.569498+00:00
-- url     : https://prove2.me/theorems/92cff4d6-ec3f-43c0-8f3b-7819f300bbf0
-- title:
--   The Goppa code $C_L(D,G)$
-- statement:
--   Let $F/\mathbb F_Q$ be a function field, $P_1,\dots,P_N$ distinct rational places of $F$, $D=P_1+\dots+P_N$, and $G$ a divisor with $\operatorname{supp}(G)\cap\operatorname{supp}(D)=\emptyset$. The **Goppa code** is
--   $$
--   C_L(D,G)=\{(f(P_1),\dots,f(P_N)) : f\in\mathcal L(G)\}\subseteq\mathbb F_Q^N,
--   $$
--   where $\mathcal L(G)=\{0\}\cup\{f\in F^\times:(f)+G\ge 0\}$ is the Riemann–Roch space and $f(P)\in\mathbb F_Q$ is the residue of $f$ at the rational place $P$.
--
--   The codes $C_\gamma=C_L(D,G_\gamma)$, one for each divisor class $\gamma$ of degree $m$, are the "mother codes" whose average weight distribution Lemma 4.3 computes.
--
--   **Formalization Note** $f(P)$ is the platform's `AlgebraicCurve.Place.evalAt` (residue class pulled back along $k\to\kappa(P)$, a bijection when $\deg P=1$; junk $0$ off the valuation ring). The code is the $k$-span of the evaluation image of $\mathcal L(G)$ = `AlgebraicCurve.LSpace G`. When $\operatorname{supp}(G)\cap\operatorname{supp}(D)=\emptyset$, $\mathcal L(G)$ lies in every valuation ring $\mathcal O_{P_i}$, evaluation is linear there, and the span is the image itself. The hypotheses (distinct rational places, disjoint supports) are carried by the statements.
-- source:
--   Cohen, Manket, Beating the Gilbert–Varshamov Bound at Alphabet Size 42, manuscript of October 24, 2026 (STOC 2027 submission; held version sha256 da05fc8e…eb595), §3, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

namespace BeatingGV42

/-- **Evaluation vector** `(f(P_1), …, f(P_N))` of `f ∈ F` at places `P_1, …, P_N`
(Cohen, Manket, *Beating the Gilbert–Varshamov Bound at Alphabet Size 42*, manuscript of October 24, 2026 (held version sha256 da05fc8e…), §3, p.11 (PDF p.13)): "If f ∈ F is regular at a rational place P, its residue f(P) is an
element of F_Q."

**Formalization Note** `f(P)` is the platform's `AlgebraicCurve.Place.evalAt`: the residue class of
`f` in `κ(P)`, pulled back to `k` along a left inverse of `k → κ(P)`. For a rational place
(`deg P = 1`) the map `k → κ(P)` is a bijection, so this is the paper's `f(P)`. Off the valuation
ring of `P` the value is the junk `0`; it never matters below, since every statement assumes
`supp(G) ∩ supp(D) = ∅`, which puts `L(G)` inside every valuation ring `𝒪_{P_i}`. -/
noncomputable def evalVec {k F : Type*} [Field k] [Field F] [Algebra k F] {N : ℕ}
    (P : Fin N → Place k F) (f : F) : Fin N → k :=
  fun i => (P i).evalAt f

/-- **The Goppa code** `C_L(D, G) = {(f(P_1), …, f(P_N)) : f ∈ L(G)} ⊆ F_Q^N`
(Cohen, Manket, *Beating the Gilbert–Varshamov Bound at Alphabet Size 42*, manuscript of October 24, 2026 (held version sha256 da05fc8e…), §3, p.11 (PDF p.13)), for distinct rational places `P_1, …, P_N`, `D = P_1 + ⋯ + P_N` and a
divisor `G` with `supp(G) ∩ supp(D) = ∅`.

**Formalization Note** Defined as the `k`-span of the evaluation image of the Riemann–Roch space
`L(G) = AlgebraicCurve.LSpace G`. When `supp(G) ∩ supp(D) = ∅` and every `P_i` is rational,
`L(G) ⊆ 𝒪_{P_i}` and evaluation at `P_i` is `k`-linear on `𝒪_{P_i}`, so the image is already a
subspace and the span equals the paper's set. Every statement using `goppaCode` carries the
hypotheses `Function.Injective P` (distinct places), `∀ i, (P i).deg = 1` (rational places) and
`∀ i, G (P i) = 0` (`supp(G) ∩ supp(D) = ∅`). -/
noncomputable def goppaCode {k F : Type*} [Field k] [Field F] [Algebra k F] {N : ℕ}
    (P : Fin N → Place k F) (G : Divisor k F) : Submodule k (Fin N → k) :=
  Submodule.span k (evalVec P '' (LSpace G : Set F))

end BeatingGV42


