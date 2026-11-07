-- Prove2me | Definitions.Def_SparseDisc_subdivide
-- name    : SparseDisc_subdivide
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:50:08.949578+00:00
-- url     : https://prove2.me/theorems/dfcd727c-045a-4602-9722-22c31a9ced56
-- title:
--   Subdivision $S_k(G_0)$ of a graph
-- statement:
--   The **subdivision** $S_k(G_0)$ of a simple graph $G_0$, for $k : E(G_0) \to \mathbb{N}$, is obtained by subdividing every edge $e$ by $k(e) + 1 \ge 1$ new vertices: each edge $uv$ is replaced by a path $u - x_{e,0} - x_{e,1} - \cdots - x_{e,k(e)} - v$.
--
--   **Formalization Note** The vertices are the old vertices and the new vertices $x_{e,i}$, $0 \le i \le k(e)$. Each edge is given an arbitrary orientation $(a, b)$ (`Quot.out`), which does not affect the graph up to isomorphism; $a \sim x_{e,0}$, $x_{e,i} \sim x_{e,i+1}$, $x_{e,k(e)} \sim b$, and there are no other edges. $k \equiv 0$ subdivides every edge exactly once.
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions: Acyclic, Bounded-Degree and Degenerate Sparsity Patterns, STOC 2027 submission (manuscript sha256 0f09ec60…25b81), Theorem 1.9(b), p.5

import Mathlib

namespace SparseDisc

/-- The **subdivision** `S_k(G₀)` of a simple graph `G₀` in which every edge `e = uv` is replaced by
a path `u – x_{e,0} – x_{e,1} – ⋯ – x_{e,k(e)} – v` through `k(e) + 1 ≥ 1` new vertices
(Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive Functions*, STOC 2027 submission
manuscript (sha256 0f09ec60…25b81), Theorem 1.9(b), p.5: "patterns obtained by subdividing every
edge").

**Formalization Note** Vertices are the old vertices `inl v` and the new vertices `inr ⟨e, i⟩`,
`i = 0, …, k(e)`. Each edge `e` is given the orientation `(a, b) = Quot.out e` (an arbitrary choice
of which end comes first; it does not affect the graph up to isomorphism). Then `inl a ~ inr ⟨e, 0⟩`,
`inr ⟨e, i⟩ ~ inr ⟨e, i + 1⟩`, `inr ⟨e, k(e)⟩ ~ inl b`, and there are no other edges. `k ≡ 0`
is the subdivision of every edge by exactly one vertex. -/
noncomputable def subdivide {W : Type} (G₀ : SimpleGraph W) (k : G₀.edgeSet → ℕ) :
    SimpleGraph (W ⊕ (Σ e : G₀.edgeSet, Fin (k e + 1))) :=
  SimpleGraph.fromRel (fun a b => match a, b with
    | Sum.inl v, Sum.inr ⟨e, i⟩ =>
        (v = (Quot.out (e : Sym2 W)).1 ∧ i.val = 0) ∨
          (v = (Quot.out (e : Sym2 W)).2 ∧ i.val = k e)
    | Sum.inr ⟨e, i⟩, Sum.inr ⟨e', j⟩ => e = e' ∧ i.val + 1 = j.val
    | _, _ => False)

end SparseDisc


