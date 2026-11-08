-- Prove2me | Definitions.Def_SkewMatching_DecodesFlow
-- name    : SkewMatching_DecodesFlow
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:09:31.920872+00:00
-- url     : https://prove2.me/theorems/e1e34ad2-394b-41f6-a676-89868ef3080f
-- title:
--   The input and output layouts of Lemma 11 and Theorem 2
-- statement:
--   For a skew-symmetric graph on $\{0,\dots,N-1\}$, the input memory holds $N$ in cell $0$, $s$ in cell $1$, the parameter $K$ in cell $2$ ($0$ when there is no such parameter), the number of edges in cell $3$, $\sigma(v)$ in cell $4+v$, and the tail and head of the $j$-th listed edge in cells $4+N+2j$ and $5+N+2j$; all other cells hold $0$. The list contains every edge exactly once.
--
--   The output is read from the memory of the halted machine: cell $-1$ holds $\ell$, and cells $-2-2j$ and $-3-2j$ hold the tail and head of the $j$-th edge with flow $1$, each such edge once.
--
--   **Formalization Note** The paper fixes no format. On a simple graph an edge is determined by its tail and head, so the list of pairs determines the graph and $\sigma$ on edges.
-- source:
--   Li, Li, Zhang, Maximum Cardinality Matching in n^{2+o(1)} Time, STOC 2027 submission (manuscript sha256 3fc151f5…), Lemma 11, p.5; Theorem 2, pp.1, 5

import Mathlib
import Definitions.Def_SkewMatching_Machine
import Definitions.Def_SkewMatching_SkewGraph_IsFlow

namespace SkewMatching

/-- The input memory of Lemma 11 and Theorem 2: cell `0` holds `N`, cell `1` holds `s`, cell `2` holds `K` (`0` when there is no such
parameter), cell `3` holds the number `L` of edges, cells `4 + v` (`v < N`) hold `σ v`, and cells `4 + N + 2j`, `5 + N + 2j` hold the tail
and head of the `j`-th listed edge. Every other cell holds `0`.

Li, Li, Zhang, *Maximum Cardinality Matching in n^{2+o(1)} Time*, STOC 2027 submission (manuscript sha256 3fc151f5…), Lemma 11, p.5;
Theorem 2, p.1.

**Formalization Note.** The paper names no input format. For a `Simple` graph an edge is determined by its tail and head, so `σ` on edges is
forced by `σ` on vertices and the list. -/
def flowMem {N : ℕ} {E : Type*} (G : SkewGraph (Fin N) E) (s : Fin N) (K : ℕ) (el : List E) (a : ℤ) : ℤ :=
  if a = 0 then (N : ℤ) else if a = 1 then ((s : ℕ) : ℤ) else if a = 2 then (K : ℤ)
  else if a = 3 then (el.length : ℤ)
  else if 4 ≤ a ∧ a < 4 + (N : ℤ) then
    if h : (a - 4).toNat < N then ((G.σV ⟨(a - 4).toNat, h⟩ : Fin N) : ℕ) else 0
  else Machine.pairCells (4 + (N : ℤ)) (el.map fun e => (((G.tail e : Fin N) : ℕ), ((G.head e : Fin N) : ℕ))) a

/-- `el` lists every edge of `G` exactly once. -/
def IsFullListing {E : Type*} (el : List E) : Prop := el.Nodup ∧ ∀ e, e ∈ el

/-- The output of Lemma 11 and Theorem 2, read from the memory `mem` of the halted machine: cell `−1` holds `ℓ`, and cells `−2 − 2j`,
`−3 − 2j` hold the tail and head of the `j`-th of the `ℓ` edges with flow `1`, each edge once. -/
def DecodesFlow {N : ℕ} {E : Type*} (G : SkewGraph (Fin N) E) (mem : ℤ → ℤ) (f : E → ℕ) : Prop :=
  ∃ (ℓ : ℕ) (es : Fin ℓ → E), mem (-1) = (ℓ : ℤ) ∧
    (∀ j : Fin ℓ, mem (-2 - 2 * ((j : ℕ) : ℤ)) = (((G.tail (es j) : Fin N) : ℕ) : ℤ) ∧
      mem (-3 - 2 * ((j : ℕ) : ℤ)) = (((G.head (es j) : Fin N) : ℕ) : ℤ)) ∧
    Function.Injective es ∧ ∀ e, f e = 1 ↔ e ∈ Set.range es

end SkewMatching


