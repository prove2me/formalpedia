-- Prove2me | Definitions.Def_ChowFormsCH_IsPrimitiveY1
-- name    : ChowFormsCH_IsPrimitiveY1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T22:01:42.681521+00:00
-- url     : https://prove2.me/theorems/8091e52b-b10c-4085-b05e-510fcabab0cb
-- title:
--   Projective Noether position and primitive element $y_1$ (Definition 3.2)
-- statement:
--   Let $V\subseteq K^{m+n}$, with coordinates $x=(x_1,\dots,x_m)$ and $y=(y_1,\dots,y_n)$, be an equidimensional variety of dimension $m$, and let $\pi_x$ be the projection onto the $x$-coordinates. Then $V$ is in **projective Noether position** if there is $\alpha\in K^m$ such that the fiber $\pi_x^{-1}(\alpha)\cap V$ has cardinality exactly $\deg V$; and **$y_1$ is a primitive element for $V$** if there is $\alpha$ such that this fiber has cardinality exactly $\deg V$ and all points in it have distinct $y_1$-coordinates.
--
--   These hypotheses make the general projection and the geometric resolution of $V$ well behaved (Lemmas 3.8–3.13) and are produced by random coordinates in Lemma 4.8.
--
--   **Formalization Note** "Equidimensional variety of dimension $m$" is part of both predicates, since the paper's definition applies only to such $V$. The fiber is required to be finite. $y_1$ is the coordinate `Sum.inr 0`, so $n\ge 1$.
-- source:
--   Andrews, Garg, Oliveira, Schost, Some algebraic and geometric computations in CH via Chow forms, arXiv:2611.05289 (held version, sha256 75e796c6…), Definition 3.2, p.22

import Mathlib
import Definitions.Def_ChowFormsCH_affDegree

set_option autoImplicit false

namespace ChowFormsCH

/-- The fiber `π_x^{-1}(α) ∩ V` of `V ⊆ K^{m+n}` over `α ∈ K^m`, where `π_x` is the projection onto
the coordinates `x₁, …, x_m` (Andrews–Garg–Oliveira–Schost, *Some algebraic and geometric
computations in CH via Chow forms*, arXiv:2611.05289, held version, sha256 75e796c6…, §3.2,
p.22). -/
def xFiber {m n : ℕ} {K : Type*} [Field K] (V : Set (AffSp (Fin m ⊕ Fin n) K)) (α : Fin m → K) :
    Set (AffSp (Fin m ⊕ Fin n) K) :=
  {v | v ∈ V ∧ ∀ j : Fin m, (show Fin m ⊕ Fin n → K from v) (Sum.inl j) = α j}

/-- `V ⊆ K^{m+n}` is an equidimensional variety of dimension `m` in projective Noether position
(Definition 3.2, p.22: "We say that an equidimensional variety V of dimension m is in projective
Noether position if there exists a point α ∈ K^m such that the fiber π_x^{-1}(α) ∩ V has cardinality
exactly deg V").

**Formalization Note** "equidimensional variety of dimension m" is part of the predicate (the
paper's definition applies only to such `V`); the fiber is required to be finite so that its
cardinality is a natural number. -/
def IsNoetherPosition {m n : ℕ} {K : Type*} [Field K] (V : Set (AffSp (Fin m ⊕ Fin n) K)) : Prop :=
  IsAffVariety V ∧ IsPureDim V m ∧
    ∃ α : Fin m → K, (xFiber V α).Finite ∧ (xFiber V α).ncard = affDegree V

/-- `y₁` is a primitive element for the equidimensional variety `V ⊆ K^{m+n}` of dimension `m`
(Definition 3.2, p.22: "We say that y1 is a primitive element for V if there is a point α such that
the fiber π_x^{-1}(α) ∩ V has cardinality exactly deg V, and all points in this fiber have distinct
y1 coordinates").

**Formalization Note** `y₁` is the coordinate `Sum.inr 0` (so `n ≥ 1`); as for
`IsNoetherPosition`, `V` is required to be an equidimensional variety of dimension `m`. -/
def IsPrimitiveY1 {m n : ℕ} [NeZero n] {K : Type*} [Field K] (V : Set (AffSp (Fin m ⊕ Fin n) K)) :
    Prop :=
  IsAffVariety V ∧ IsPureDim V m ∧
    ∃ α : Fin m → K, (xFiber V α).Finite ∧ (xFiber V α).ncard = affDegree V ∧
      Set.InjOn (fun v : AffSp (Fin m ⊕ Fin n) K => (show Fin m ⊕ Fin n → K from v) (Sum.inr 0))
        (xFiber V α)

end ChowFormsCH


