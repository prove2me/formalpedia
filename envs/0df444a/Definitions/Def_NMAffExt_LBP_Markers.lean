-- Prove2me | Definitions.Def_NMAffExt_LBP_Markers
-- name    : NMAffExt_LBP_Markers
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T04:29:45.728662+00:00
-- url     : https://prove2.me/theorems/b72347f7-52be-42f0-b3a2-3b5cd65f6344
-- title:
--   Pure-input query rank $\rho(W)=\dim(W\cap E_X)$ and cut markers for programs on $(X,R)$ (§A.1)
-- statement:
--   For inputs $(X,R)\in\mathbb F_2^n\times\mathbb F_2^t$, let $E_X=\{(\lambda,0):\lambda\in(\mathbb F_2^n)^*\}$ be the space of linear forms that depend only on $X$. For a space $W$ of query forms on $(X,R)$, the **pure-input query rank** is
--   $$\rho(W)=\dim(W\cap E_X),$$
--   an intersection dimension (for $W=\langle x_1+r_1\rangle$, $\rho(W)=0$). $\pi_X:\mathbb F_2^{n+t}\to\mathbb F_2^n$ is the projection onto the $X$ coordinates.
--
--   A **cut marker** is a designated point on an edge, not an additional query node. Here a marker sits after the query of an internal vertex $u$: on its outgoing edge labelled $b$, or, when both outgoing edges of $u$ have the same destination, at one point covering both edges ("its answers have the same continuation and use one marker", p. 102). A computation **crosses** the marker when it reaches $u$ and leaves along a marked edge. The **prefix space** of the marker on a path to $u$ is the span of the forms queried on that path, $q_u$ included; the marker's continuation is the vertex its edge enters.
--
--   **Formalization Note.** `pureForms n t` ($E_X$: coefficient vectors on $n+t$ bits whose last $t$ coordinates vanish), `pureRank W`, `projX`, and `Marker s` with fields `src` and `label : Option (ZMod 2)` (`some b`: the edge labelled $b$; `none`: both edges, valid only when they share their destination), `Marker.Valid`, `Marker.Crosses`, `Marker.next`.
-- source:
--   Xin Li, Yan Zhong, Non-Malleable Affine Extractors with Small Error and Complexity Lower Bounds, arXiv:2610.02407 (version of 2026-11-02, sha256 e80dad4d…), p. 101 (PDF 103), §A.1; p. 101–102 (PDF 103–104), proof of Lemma A.1

import Mathlib
import Definitions.Def_NMAffExt_LBP_Program

/-!
# Pure-input query rank and cut markers for programs on (X, R)

Xin Li, Yan Zhong, *Non-Malleable Affine Extractors with Small Error and Complexity Lower Bounds*,
arXiv:2610.02407 (version of 2026-11-02, sha256 e80dad4d…), p. 101 (PDF 103), §A.1, and
p. 101–102 (PDF 103–104), proof of Lemma A.1.

"For inputs (X, R) ∈ 𝔽₂ⁿ × 𝔽₂ᵗ, let E_X = {(λ, 0) : λ ∈ (𝔽₂ⁿ)*} be the space of linear forms
depending only on X. For a linear space W of query forms on (X, R), define its pure-input query
rank by ρ(W) = dim(W ∩ E_X). … A cut marker is a designated point on an edge, not an additional
query node. Its prefix space is the span of the forms queried before that point."

Conventions.
* An input `(x, r)` is the string `Fin.append x r` on `n + t` bits; `projX` is `π_X`.
* `pureForms n t` is `E_X`: the coefficient vectors vanishing on the last `t` coordinates.
* A marker sits after the query of an internal vertex `src`: on its outgoing edge labelled `b`
  (`label = some b`), or (`label = none`) at one point after the query when both outgoing edges have
  the same destination ("its answers have the same continuation and use one marker", p. 102).
* A computation crosses a marker when it reaches `src` and leaves it along a marked edge. The
  prefix space of a marker on a path to `src` is the span of the forms queried on the path,
  `src`'s own query included (`Program.prefixSpan`). `Marker.next` is the vertex the marked edge
  enters.
-/

namespace NMAffExt.LBP

/-- `E_X`: the linear forms on `(X, R) ∈ 𝔽₂ⁿ × 𝔽₂ᵗ` that depend only on `X`, i.e. coefficient
vectors on `n + t` bits whose last `t` coordinates vanish. -/
def pureForms (n t : ℕ) : Submodule (ZMod 2) (Fin (n + t) → ZMod 2) :=
  ⨅ j : Fin t, LinearMap.ker (LinearMap.proj (R := ZMod 2) (φ := fun _ : Fin (n + t) => ZMod 2)
    (Fin.natAdd n j))

/-- The pure-input query rank `ρ(W) = dim(W ∩ E_X)`. -/
noncomputable def pureRank {n t : ℕ} (W : Submodule (ZMod 2) (Fin (n + t) → ZMod 2)) : ℕ :=
  Module.finrank (ZMod 2) ↥(W ⊓ pureForms n t)

/-- The projection `π_X : 𝔽₂ⁿ⁺ᵗ → 𝔽₂ⁿ` onto the `X` coordinates. -/
def projX {n t : ℕ} (y : Fin (n + t) → ZMod 2) : Fin n → ZMod 2 :=
  fun i => y (Fin.castAdd t i)

/-- A cut marker: a designated point on the outgoing edge labelled `b` of the vertex `src`
(`label = some b`), or one point on both outgoing edges of `src` (`label = none`). -/
structure Marker (s : ℕ) where
  src : Fin s
  label : Option (ZMod 2)
  deriving DecidableEq

namespace Marker

variable {N s : ℕ}

/-- The marker sits on an edge of `P`: `src` is internal, and a `none` marker is only placed when
both outgoing edges of `src` have the same destination. -/
def Valid (P : Program N s) (m : Marker s) : Prop :=
  ∃ (q : Fin N → ZMod 2) (v0 v1 : Fin s), P.node m.src = Node.query q v0 v1 ∧
    (m.label = none → v0 = v1)

/-- The computation on `x` crosses the marker `m`: it reaches `src` and leaves along a marked
edge. -/
def Crosses (P : Program N s) (x : Fin N → ZMod 2) (m : Marker s) : Prop :=
  P.Reaches x m.src ∧ ∃ (q : Fin N → ZMod 2) (v0 v1 : Fin s), P.node m.src = Node.query q v0 v1 ∧
    (m.label = none ∨ m.label = some (ip q x))

/-- The vertex entered by the marked edge (for a `none` marker both edges enter it). -/
def next (P : Program N s) (m : Marker s) : Fin s :=
  match P.node m.src with
  | Node.sink _ => m.src
  | Node.query _ v0 v1 => if m.label = some 1 then v1 else v0

end Marker

end NMAffExt.LBP


