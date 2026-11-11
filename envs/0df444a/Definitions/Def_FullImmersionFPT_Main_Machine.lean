-- Prove2me | Definitions.Def_FullImmersionFPT_Main_Machine
-- name    : FullImmersionFPT_Main_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T04:47:11.86228+00:00
-- url     : https://prove2.me/theorems/427d35ec-c9a4-41dd-b395-45b71429f882
-- title:
--   The word RAM reading and the codes of graphs (§5 "Algorithmic aspects", p. 15)
-- statement:
--   The paper's algorithms store graphs "as adjacency lists of half-edges, with pointers between the two half-edges of each edge", with constant-time access to per-edge variables. The machine is read as the published deterministic word RAM `TrulySubcubicAPSP` (unit cost per instruction) with words of logarithmic length, using the published conventions `FOMCMonDep.WordSizeOK` (a program comes with a factor $b$ and must be correct at every word size $W\ge b(\lfloor\log_2(N+2)\rfloor+1)$, $N$ the input length plus its largest absolute entry) and `FOMCMonDep.DecidesWithin` (halting within $t$ steps with the correct verdict). `RunsWithin P W t ws spec` says that $P$, started on the input words $ws$, halts within $t$ steps and the words in the cells after the input satisfy `spec`.
--
--   An input graph is an edge list: vertices $0,\dots,n-1$, edges $0,\dots,m-1$, edge $e$ has the two half-edges $(e,0)$ and $(e,1)$ at the vertices $\mathrm{ends}(e,0)$ and $\mathrm{ends}(e,1)$; every multigraph with loops and parallel edges is isomorphic to one of these. The half-edge $(e,i)$ is written as the word $2e+i$, a vector of $\mathbb F_2^d$ as its $d$ bits, a subset of $[q]$ as its $q$ membership bits, a trail as its length followed by its half-edges.
--
--   **Formalization Note.** `ofEnds ends` is the concrete multigraph on `Fin n` and `Fin m × Fin 2` with `mate (e, i) = (e, i.rev)`.
-- source:
--   Barabash, Geelen, McCarty, McFarland, Wollan, Finding full immersions is fixed-parameter tractable in labeled tour graphs, STOC 2027 submission (manuscript of November 2, 2026, sha256 c071967d…), p. 15 ("Algorithmic aspects"), p. 11 (footnote 8)

import Mathlib
import Definitions.Def_FOMCMonDep_DecidesWithin
import Definitions.Def_FullImmersionFPT_Main_Multigraph

set_option autoImplicit false

/-!
# The machine and the concrete graph codes (§5 "Algorithmic aspects", p. 15; footnote 8, p. 11)

Barabash, Geelen, McCarty, McFarland, Wollan, *Finding full immersions is fixed-parameter
tractable in labeled tour graphs* (STOC 2027 submission, manuscript of November 2, 2026).

The paper's algorithms store graphs "as adjacency lists of half-edges, with pointers between the
two half-edges of each edge" with constant-time access to per-edge variables (p. 15). Reading: the
machine is the published deterministic word RAM `TrulySubcubicAPSP` (unit cost per instruction)
with words of logarithmic length, as fixed by the published `FOMCMonDep.WordSizeOK` /
`FOMCMonDep.DecidesWithin` (a program comes with a factor `b` and must be correct at every word size
`W ≥ b(⌊log₂(N+2)⌋+1)`, `N` = input length plus largest absolute entry).

A graph given as input is an edge list on `Fin n`: edge `e : Fin m` has the half-edges `(e, 0)` and
`(e, 1)` at the vertices `ends e 0` and `ends e 1`; every multigraph with loops and parallel edges
is isomorphic to such a one. Half-edge `(e, i)` is written as the word `2e + i`.
-/

namespace FullImmersionFPT.Main

open Classical

noncomputable section

/-- The program `P`, started on the word list `ws` (published `loadWords`), halts within `t` steps
(any verdict) and the signed words in the cells after the input satisfy `spec`
(`out a` = the word in cell `|ws| + a`). -/
def RunsWithin (P : List TrulySubcubicAPSP.Instr) (W t : ℕ) (ws : List ℤ)
    (spec : (ℕ → ℤ) → Prop) : Prop :=
  ∃ (verdict : Bool) (mem : ℤ → BitVec W),
    TrulySubcubicAPSP.exec P t 0 (TrulySubcubicAPSP.loadWords W ws) = some (verdict, mem) ∧
      spec fun a => (mem ((ws.length + a : ℕ) : ℤ)).toInt

/-- The concrete multigraph of an edge list: vertices `Fin n`, half-edges `Fin m × Fin 2`,
`inc (e, i) = ends e i`, `mate (e, i) = (e, 1 - i)`. -/
def ofEnds {n m : ℕ} (ends : Fin m → Fin 2 → Fin n) : Multigraph (Fin n) (Fin m × Fin 2) where
  verts := Finset.univ
  halves := Finset.univ
  inc p := ends p.1 p.2
  mate p := (p.1, p.2.rev)

/-- The edge `e` of an edge list, as an unordered pair of half-edges. -/
def edgeSym {m : ℕ} (e : Fin m) : Sym2 (Fin m × Fin 2) := s((e, 0), (e, 1))

/-- The word of the half-edge `(e, i)`: `2e + i`. -/
def hword {m : ℕ} (p : Fin m × Fin 2) : ℤ := 2 * (p.1 : ℤ) + (p.2 : ℤ)

/-- A bit as a word. -/
def bitWord (b : Prop) : ℤ := if b then 1 else 0

/-- The words of a vector of `F₂^d`, coordinate by coordinate. -/
def vecWords {d : ℕ} (x : Fin d → ZMod 2) : List ℤ := (List.finRange d).map fun i => ((x i).val : ℤ)

/-- The words of a subset of `[q]`, as its `q` membership bits. -/
def setWords {q : ℕ} (s : Finset (Fin q)) : List ℤ := (List.finRange q).map fun i => bitWord (i ∈ s)

/-- The words of a trail (or any list of half-edges): its length, then its half-edges. -/
def trailWords {m : ℕ} (T : List (Fin m × Fin 2)) : List ℤ := (T.length : ℤ) :: T.map hword

end

end FullImmersionFPT.Main


