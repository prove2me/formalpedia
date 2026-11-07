-- Prove2me | Definitions.Def_AGProxGap_HasVanishing
-- name    : AGProxGap_HasVanishing
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:38:55.950045+00:00
-- url     : https://prove2.me/theorems/2d0eb233-574e-49f5-aa64-d5522309ac06
-- title:
--   The vanishing property $L_K(G+H-\sum_{i\in I}P_i)=\{0\}$ for all $|I|=n-e$
-- statement:
--   Let $K(X)$ with points $P_1',\dots,P_n',P_\infty'$ be a finite constant field extension of $F=\mathbb F_q(X)$, let $H$ be a divisor on $X_K$, $G=mP_\infty'$ and $e\ge 0$. The divisor $H$ has the **vanishing property** if
--   $$
--   L_K\Bigl(G+H-\sum_{i\in I}P_i'\Bigr)=\{0\}\quad\text{for every } I\subseteq[n] \text{ with } |I|=n-e .
--   $$
--   Equivalently, a function in $L_K(G+H)$ that vanishes at $n-e$ of the evaluation points is zero. This is the property of the auxiliary divisor of Lemma 3.3, and it is what Lemmas 3.4–3.7 use.
--
--   **Formalization Note** $L_K$ is `AlgebraicCurve.LSpace` over $K$ and $\{0\}$ the zero subspace.
-- source:
--   Li, Xing, Yuan, Zhu, On Proximity Gaps for One-Point Algebraic Geometric Codes, arXiv:2610.39256 (held version, sha256 d2017986…3b3f), Lemma 3.3, p.18

import Mathlib
import Definitions.Def_AGProxGap_ConstExt
import Definitions.Def_AGProxGap_divG

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

universe u v

namespace AGProxGap

/-- **The vanishing property of the auxiliary divisor `H`** (Li, Xing, Yuan, Zhu, *On Proximity Gaps for One-Point Algebraic Geometric Codes*, arXiv:2610.39256 (held version, sha256 d2017986…), Lemma 3.3, p.18): "for every
subset I ⊆ [n] with |I| = n − e, L_K(G + H − Σ_{i∈I} P_i) = {0}."

**Formalization Note** `G = m P'_∞` and `P'_i` are the points of `X_K` given by the constant
field extension datum `E` (`E.liftInf`, `E.lift i`); `L_K` is `AlgebraicCurve.LSpace` over `K`,
and `{0}` is the zero subspace `⊥`. -/
def HasVanishing {Fq : Type u} {F : Type v} [Field Fq] [Field F] [Algebra Fq F] {n : ℕ}
    {P : Fin n → Place Fq F} {Pinf : Place Fq F} (E : ConstExt P Pinf) (m : ℕ)
    (H : Divisor E.K E.FK) (e : ℕ) : Prop :=
  ∀ I : Finset (Fin n), I.card = n - e →
    LSpace (divG E.liftInf m + H - ∑ i ∈ I, Finsupp.single (E.lift i) (1 : ℤ)) = ⊥

end AGProxGap


