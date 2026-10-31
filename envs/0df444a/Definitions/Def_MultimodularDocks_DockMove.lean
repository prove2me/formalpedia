-- Prove2me | Definitions.Def_MultimodularDocks_DockMove
-- name    : MultimodularDocks_DockMove
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:35:41.382556+00:00
-- url     : https://prove2.me/theorems/ea7a0e94-0f07-4642-b051-a383ba3776ce
-- title:
--   Dock-moves $o_{ij}$, $e_{ij}$, $E_{ijh}$, $O_{ijh}$ and their inverses
-- statement:
--   With $e_i$ the $i$-th unit vector, a **dock-move** from station $i$ to station $j$ is one of
--
--   1. $o_{ij}(\vec d,\vec b)=(\vec d-e_i+e_j,\ \vec b)$: one empty dock from $i$ to $j$;
--   2. $e_{ij}(\vec d,\vec b)=(\vec d,\ \vec b-e_i+e_j)$: one full dock (dock and bike) from $i$ to $j$;
--   3. $E_{ijh}(\vec d,\vec b)=(\vec d-e_i+e_h,\ \vec b+e_j-e_h)$: one dock from $i$ to $j$ and one bike from $h$ to $j$;
--   4. $O_{ijh}(\vec d,\vec b)=(\vec d+e_j-e_h,\ \vec b-e_i+e_h)$: one bike from $i$ to $h$ and one dock from $i$ to $j$.
--
--   The source of the move is $i$ and its destination is $j$. The inverse moves are $o_{ji}$, $e_{ji}$, $O_{jih}$ and $E_{jih}$ respectively: applying the inverse after the move gives back the original allocation.
--
--   **Formalization Note** The four kinds are the constructors of `DockMove`; `apply` performs the move with $e_i$ written `Pi.single i 1`.
-- source:
--   Freund, Henderson, Shmoys, Minimizing Multimodular Functions and Allocating Capacity in Bike-Sharing Systems, arXiv:1611.09304v5, Definition 3, p.17; inverse moves, p.46

import Mathlib
import Definitions.Def_MultimodularDocks_Instance

namespace MultimodularDocks

/-- **Dock-moves** (Freund, Henderson, Shmoys, arXiv:1611.09304v5, Definition 3, p.17), from
station `i` to station `j`:
1. `o i j`: `(d⃗ − e_i + e_j, b⃗)`, one empty dock from `i` to `j`;
2. `e i j`: `(d⃗, b⃗ − e_i + e_j)`, one full dock from `i` to `j`;
3. `E i j h`: `(d⃗ − e_i + e_h, b⃗ + e_j − e_h)`, one dock from `i` to `j` and one bike from `h`
   to `j`;
4. `O i j h`: `(d⃗ + e_j − e_h, b⃗ − e_i + e_h)`, one bike from `i` to `h` and one dock from `i`
   to `j`. -/
inductive DockMove (S : Type*)
  | o (i j : S)
  | e (i j : S)
  | E (i j h : S)
  | O (i j h : S)

namespace DockMove

variable {S : Type*}

/-- The station a dock-move takes a dock from. -/
def src : DockMove S → S
  | o i _ => i
  | e i _ => i
  | E i _ _ => i
  | O i _ _ => i

/-- The station a dock-move brings a dock to. -/
def dst : DockMove S → S
  | o _ j => j
  | e _ j => j
  | E _ j _ => j
  | O _ j _ => j

/-- The inverse dock-move (p.46, "inverting the dock-move"): `o j i`, `e j i`, `O j i h` and
`E j i h` undo `o i j`, `e i j`, `E i j h` and `O i j h`. -/
def inv : DockMove S → DockMove S
  | o i j => o j i
  | e i j => e j i
  | E i j h => O j i h
  | O i j h => E j i h

/-- The allocation obtained by a dock-move (Definition 3, p.17), with `e_i = Pi.single i 1`. -/
def apply [DecidableEq S] : DockMove S → Alloc S → Alloc S
  | o i j, a => ⟨a.d - Pi.single i 1 + Pi.single j 1, a.b⟩
  | e i j, a => ⟨a.d, a.b - Pi.single i 1 + Pi.single j 1⟩
  | E i j h, a => ⟨a.d - Pi.single i 1 + Pi.single h 1, a.b + Pi.single j 1 - Pi.single h 1⟩
  | O i j h, a => ⟨a.d + Pi.single j 1 - Pi.single h 1, a.b - Pi.single i 1 + Pi.single h 1⟩

end DockMove

end MultimodularDocks


