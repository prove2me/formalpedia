-- Prove2me | Definitions.Def_CodeSW_IsIncidence
-- name    : CodeSW_IsIncidence
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:23:28.719576+00:00
-- url     : https://prove2.me/theorems/a77ec3b0-9068-47bd-9726-ce36be6ef8e3
-- title:
--   Edge-vertex incidence matrices; $\Delta$-graphic and $\Delta$-cographic parity check matrices via a coupling $g$
-- statement:
--   A matrix $g\in\{0,1\}^{c\times m}$ is an **edge-vertex incidence matrix** when every row has exactly two ones, in distinct columns: it describes a graph on $m$ vertices with one edge per row. Parallel edges are allowed and self-loops are not.
--
--   Let $h\in\{0,1\}^{c\times n}$ be a parity check matrix.
--
--   1. $h$ is **$\Delta$-graphic via $g$** (the primal coupling) if $g$ is an edge-vertex incidence matrix, $\ker(g^T)\supseteq\ker(h^T)$ and $\dim\ker(g^T)-\dim\ker(h^T)\le\Delta$.
--   2. $h$ is **$\Delta$-cographic via $g$** (the dual coupling) if a column-generator matrix $h^\perp$ of $\mathrm{col}(h)^\perp$ is $\Delta$-graphic via $g$; equivalently, $\ker(g^T)\supseteq\mathrm{col}(h)$ and $\dim\ker(g^T)-\dim\mathrm{col}(h)\le\Delta$.
--
--   These are the structural hypotheses of the rapid mixing theorem: up to a gap of dimension $\Delta$, the even covers of $h$, or its syndrome space, are the cycle space of a graph.
--
--   **Formalization Note** For every column generator $h^\perp$ of $\mathrm{col}(h)^\perp$ one has $\ker((h^\perp)^T)=\mathrm{col}(h)$, so the second condition does not depend on the choice of $h^\perp$ and is stated directly. Definition 10's $m\le O(n)$ is not imposed: $m$ enters every bound instead (footnote 5 of the paper: any $m=\mathrm{poly}(n)$ suffices). The dimension gap is written as $\dim\ker(g^T)\le\dim\ker(h^T)+\Delta$ to avoid natural-number subtraction.
-- source:
--   Hangleiter, Ju, Vazirani, Code Swendsen-Wang Dynamics, arXiv:2510.08446 (manuscript sha256 4e4abb5e…), Definition 10, p.18; §3.3.2, p.21

import Mathlib
open Matrix
noncomputable section

namespace CodeSW

/-- `g ∈ {0,1}^{c×m}` is an **edge-vertex incidence matrix** of a graph on `m` vertices with one
edge per row: every row has exactly two ones, in distinct columns (Hangleiter, Ju, Vazirani,
*Code Swendsen-Wang Dynamics*, arXiv:2510.08446, manuscript sha256 4e4abb5e…, Definition 10,
p.18; §3.3.2, p.21: "The auxiliary graph g has one edge for each check of h, with the same row
index").

**Formalization Note** Parallel edges (equal rows) are allowed: repeated checks force them.
Self-loops are not edges (Definition 19 indexes vertex pairs by `u < v`). -/
def IsIncidence {c m : ℕ} (g : Matrix (Fin c) (Fin m) (ZMod 2)) : Prop :=
  ∀ e : Fin c, ∃ u v : Fin m, u ≠ v ∧ g e = Pi.single u 1 + Pi.single v 1

/-- `h` is **∆-graphic via `g`** (Definition 10, first bullet): `g` is an edge-vertex incidence
matrix, `ker(gᵀ) ⊇ ker(hᵀ)` and `dim ker(gᵀ) − dim ker(hᵀ) ≤ ∆`
(arXiv:2510.08446, manuscript sha256 4e4abb5e…, Definition 10, p.18). `g` is the primal coupling.

**Formalization Note** Kernels are of `Matrix.mulVecLin` over `ZMod 2`, subspaces of `F₂^c`.
The difference of dimensions is written `dim ker gᵀ ≤ dim ker hᵀ + ∆` (natural numbers; the
inclusion makes the two forms equivalent). The page's `m ≤ O(n)` is not imposed; `m` enters
every bound instead (footnote 5: any `m = poly(n)` suffices). -/
def IsDeltaGraphicVia {c n m : ℕ} (h : Matrix (Fin c) (Fin n) (ZMod 2))
    (g : Matrix (Fin c) (Fin m) (ZMod 2)) (Δ : ℕ) : Prop :=
  IsIncidence g ∧ LinearMap.ker hᵀ.mulVecLin ≤ LinearMap.ker gᵀ.mulVecLin ∧
    Module.finrank (ZMod 2) (LinearMap.ker gᵀ.mulVecLin) ≤
      Module.finrank (ZMod 2) (LinearMap.ker hᵀ.mulVecLin) + Δ

/-- `h` is **∆-cographic via `g`** (Definition 10, second bullet): a column-generator matrix `h^⊥`
of `col(h)^⊥` is ∆-graphic via `g`, i.e. `ker(gᵀ) ⊇ col(h)` and `dim ker(gᵀ) − dim col(h) ≤ ∆`
(arXiv:2510.08446, manuscript sha256 4e4abb5e…, Definition 10, p.18; §3.3.2, p.21: "in the dual
case, col(h) ⊆ ker(gᵀ)"). `g` is the dual coupling.

**Formalization Note** For every column generator `h^⊥` of `col(h)^⊥ ⊆ F₂^c`,
`ker((h^⊥)ᵀ) = (col(h)^⊥)^⊥ = col(h)`, so "`h^⊥` is ∆-graphic via `g`" is exactly the condition
stated here with `col(h) = range h.mulVecLin`; it does not depend on the choice of `h^⊥`. -/
def IsDeltaCographicVia {c n m : ℕ} (h : Matrix (Fin c) (Fin n) (ZMod 2))
    (g : Matrix (Fin c) (Fin m) (ZMod 2)) (Δ : ℕ) : Prop :=
  IsIncidence g ∧ LinearMap.range h.mulVecLin ≤ LinearMap.ker gᵀ.mulVecLin ∧
    Module.finrank (ZMod 2) (LinearMap.ker gᵀ.mulVecLin) ≤
      Module.finrank (ZMod 2) (LinearMap.range h.mulVecLin) + Δ

end CodeSW


