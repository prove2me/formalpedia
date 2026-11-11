-- Prove2me | Definitions.Def_ChowFormsCH_affTrace
-- name    : ChowFormsCH_affTrace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:58:13.907208+00:00
-- url     : https://prove2.me/theorems/fd0e6a29-cccc-4960-a12a-3720d17d8838
-- title:
--   Homogenization $(1,x,y)$, affine part of $W\subseteq\mathbb P^{m+n}$, and projective closure
-- statement:
--   The coordinates of $\mathbb P^{m+n}$ are ordered $(z,x_1,\dots,x_m,y_1,\dots,y_n)$, with homogenizing variable $z$. For $(x,y)\in K^{m+n}$ the point $(1,x,y)$ lies over it. For $W\subseteq\mathbb P^{m+n}$ its **affine part** is
--   $$
--   \{(x,y)\in K^{m+n} : [1:x:y]\in W\},
--   $$
--   the restriction to the chart of points at finite distance, and for $V\subseteq K^{m+n}$ its **projective closure** $\overline V\subseteq\mathbb P^{m+n}$ is the Zariski closure of the points $[1:x:y]$, $(x,y)\in V$.
--
--   These connect the affine geometric resolutions of Section 3.2 with the projective Chow forms (Lemmas 3.12, 3.13, 4.8).
--
--   **Formalization Note** Each point $[1:x:y]$ is represented by all of its nonzero multiples, as in `ProjSpace`; the closure is taken in the topology of `ProjSpace`. The coordinate map `zxyCoord` fixes the order used for Chow-form variables in Lemmas 3.12 and 3.13.
-- source:
--   Andrews, Garg, Oliveira, Schost, Some algebraic and geometric computations in CH via Chow forms, arXiv:2611.05289 (held version, sha256 75e796c6…), Lemma 3.12, p.27; Lemma 3.13, p.28; Lemma 4.8, p.33

import Mathlib
import Definitions.Def_ChowFormsCH_ProjSpace

set_option autoImplicit false

namespace ChowFormsCH

/-- The coordinates of `P^{m+n}` in the order `(z, x₁, …, x_m, y₁, …, yₙ)` (Andrews–Garg–Oliveira–
Schost, *Some algebraic and geometric computations in CH via Chow forms*, arXiv:2611.05289, held
version, sha256 75e796c6…, Lemma 3.12, p.27: "say we homogenize by adding a new variable z"):
coordinate `0` is `z` (`none`), coordinates `1, …, m` are `x₁, …, x_m` (`some (inl j)`), and
coordinates `m + 1, …, m + n` are `y₁, …, yₙ` (`some (inr j)`). -/
def zxyCoord {m n : ℕ} : Fin (m + n + 1) → Option (Fin m ⊕ Fin n) :=
  Fin.cases none (Fin.addCases (fun j => some (Sum.inl j)) (fun j => some (Sum.inr j)))

/-- The point `(1, x, y) ∈ K^{m+n+1}` over the affine point `(x, y) ∈ K^{m+n}` (homogenization with
`z = 1`; §3.3, p.27), in the coordinate order of `zxyCoord`. -/
def homPt {m n : ℕ} {K : Type*} [Field K] (v : AffSp (Fin m ⊕ Fin n) K) : Fin (m + n + 1) → K :=
  Fin.cons (α := fun _ => K) 1
    (Fin.append (fun j : Fin m => (show Fin m ⊕ Fin n → K from v) (Sum.inl j))
      (fun j : Fin n => (show Fin m ⊕ Fin n → K from v) (Sum.inr j)))

/-- The affine part `W ∩ {z ≠ 0}` of `W ⊆ P^{m+n}`, as a subset of `K^{m+n}`: the points
`(x, y)` with `(1, x, y) ∈ W` (Lemma 4.8, p.33: "the restriction of ϕ(W) to the affine chart of
points at finite distance"; Lemma 3.13, p.28, components of `V` "that lie in W"). -/
def affTrace {m n : ℕ} {K : Type*} [Field K] (W : Set (ProjSpace (m + n) K)) :
    Set (AffSp (Fin m ⊕ Fin n) K) :=
  {v | ∃ p ∈ W, p.1 = homPt v}

/-- The projective closure `V̄ ⊆ P^{m+n}` of `V ⊆ K^{m+n}`: the Zariski closure in `P^{m+n}` of the
points `[1 : x : y]`, `(x, y) ∈ V` (Lemma 3.12, p.27; Lemma 4.8, p.33).

**Formalization Note** Each point `[1 : x : y]` is represented by all its nonzero multiples
`c · (1, x, y)`, as in `ProjSpace`; the closure is taken in the topology of `ProjSpace`. -/
def projClosure {m n : ℕ} {K : Type*} [Field K] (V : Set (AffSp (Fin m ⊕ Fin n) K)) :
    Set (ProjSpace (m + n) K) :=
  closure {p | ∃ v ∈ V, ∃ c : K, c ≠ 0 ∧ p.1 = c • homPt v}

end ChowFormsCH


