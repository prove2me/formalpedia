-- Prove2me | Definitions.Def_GivenDegreeSeq_Interior_IsGraphic
-- name    : GivenDegreeSeq_Interior_IsGraphic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T04:50:55.116377+00:00
-- url     : https://prove2.me/theorems/2163c117-8878-4fc6-b49d-429a856e9769
-- title:
--   Graphic sequences — degree sequences of simple graphs on $n$ labelled vertices
-- statement:
--   Let $n\ge 0$ and let $d=(d_1,\dots,d_n)$ be nonnegative integers. The sequence $d$ is **graphic** (a *degree sequence*) if there is a simple graph $G$ — undirected, without loops and without multiple edges — on the vertex set $\{1,\dots,n\}$ such that
--   $$\deg_G(i)=d_i\qquad\text{for every } i=1,\dots,n.$$
--
--   This is the notion of "degree sequence" used throughout the paper; the Erdős–Gallai criterion characterizes it by linear inequalities, and the set $\mathcal F$ of scaling limits is built from sequences of graphic vectors.
--
--   **Formalization Note** Vertices are `Fin n` $=\{0,\dots,n-1\}$, so the paper's $d_i$ is `d ⟨i-1, _⟩`. Graphs are Mathlib's `SimpleGraph (Fin n)`; the degree is computed with classical decidability, which does not affect its value.
-- source:
--   Chatterjee, Diaconis & Sly, Random Graphs with a Given Degree Sequence, arXiv:1005.1136v5, p. 3 (§1.1, degree sequences) and p. 5, Remark 1

import Mathlib

namespace GivenDegreeSeq.Interior

/-! Chatterjee, Diaconis & Sly, *Random Graphs with a Given Degree Sequence*,
arXiv:1005.1136v5, p. 5 (Remark 1) and p. 3: a sequence of nonnegative integers is a degree
sequence ("graphic") if it is the degree sequence of a simple graph on `n` vertices.

The paper's vertices `1, …, n` are `Fin n = {0, …, n − 1}`; the paper's `d_i` is `d ⟨i − 1, _⟩`. -/

open Classical in
/-- `d : Fin n → ℕ` is **graphic**: there is a simple graph (no loops, no multiple edges) on the
vertex set `Fin n` in which vertex `i` has degree `d i`, for every `i`. -/
def IsGraphic {n : ℕ} (d : Fin n → ℕ) : Prop :=
  ∃ G : SimpleGraph (Fin n), ∀ i, G.degree i = d i

end GivenDegreeSeq.Interior


