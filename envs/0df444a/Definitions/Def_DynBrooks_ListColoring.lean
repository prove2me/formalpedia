-- Prove2me | Definitions.Def_DynBrooks_ListColoring
-- name    : DynBrooks_ListColoring
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:08:03.518199+00:00
-- url     : https://prove2.me/theorems/92df5b66-1c6d-4d83-a425-3c8d67f6101c
-- title:
--   Lemma 3.1 setting — static list-coloring runs, input layout and halting
-- statement:
--   The input of a list-coloring instance on a graph $F$ with vertex set $\{0,\dots,N-1\}$ and lists $L(v)\subseteq[\Delta]$ is the word sequence: $N$, $\Delta$, the number of edges, the edges of $F$ in an arbitrary listing and orientation, and then, for $v=0,\dots,N-1$, the length $|L(v)|$ followed by the entries of $L(v)$ in an arbitrary order.
--
--   A list-coloring run starts with all memory zero, the coin cursor at $0$, and all these words pending. A configuration has **halted** if its program counter is at a $\mathtt{halt}$ instruction or outside the program; it never moves again.
--
--   **Formalization Note** The zero memory at the start is the "preallocated temporary color-mark array" of Lemma 3.1.
-- source:
--   Mishra, Mukherjee, Fully Dynamic Brooks Coloring (STOC 2027 submission, preprint, sha256 6542a9f18a48e0b539c2aadee984a641d38a01a551fd32d5fa4d4c5164e32d7b), Lemma 3.1, p.14 (PDF 16)

import Mathlib
import Definitions.Def_DynBrooks_Protocol

namespace DynBrooks

/-! # Static list-coloring runs (the setting of Lemma 3.1)

Mishra, Mukherjee, *Fully Dynamic Brooks Coloring* (STOC 2027 submission, sha256 6542a9f1…), §3,
p.14 (PDF 16), Lemma 3.1: "Let F be a connected graph that is not a Gallai tree, and let L(v) ⊆ [∆] be
explicit lists satisfying |L(v)| ≥ d_F(v) for every v ∈ V(F). A proper coloring from these lists can be
found in time O(|V(F)| + |E(F)| + Σ_{v∈V(F)} |L(v)|), using a preallocated temporary color-mark array."

**Formalization Note.** The graph `F` has vertex set `Fin N`. A run starts with all memory zero, which
is the preallocated (cleared) color-mark array, and all input words pending: `N`, `Δ`, the edge count,
the edges (in an arbitrary listing and orientation), then for each vertex `v = 0, …, N − 1` the length of
its list followed by its entries (in an arbitrary order). The program reports the coloring by writing
the colors of `0, …, N − 1` in this order, and then halts. -/

/-- The input words of a list-coloring instance. -/
def listWords {N : ℕ} (Δ : ℕ) (es : List (Fin N × Fin N)) (Lst : Fin N → List ℕ) : List ℕ :=
  [N, Δ, es.length] ++ es.flatMap (fun e => [e.1.val, e.2.val]) ++
    (List.finRange N).flatMap fun v => (Lst v).length :: Lst v

/-- The starting configuration of a list-coloring run: memory zero, coin cursor `0`, all input
pending. -/
def listStart (w : ℕ) {N : ℕ} (Δ : ℕ) (es : List (Fin N × Fin N)) (Lst : Fin N → List ℕ) :
    Config w :=
  ⟨0, fun _ => 0, listWords Δ es Lst, 0, [], ∅⟩

/-- The machine has halted: it is at `halt` or outside the program, so it never moves again. -/
def Halted {w : ℕ} (P : Program) (c : Config w) : Prop :=
  P[c.pc]? = some Instr.halt ∨ P[c.pc]? = none

end DynBrooks


