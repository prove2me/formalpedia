-- Prove2me | Definitions.Def_LCPlanarSteiner_stagedArcs
-- name    : LCPlanarSteiner_stagedArcs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:04:54.542518+00:00
-- url     : https://prove2.me/theorems/99f690ee-c5f0-4f2c-8b23-c79aa54f1413
-- title:
--   The staged length-layer graph of a pair
-- statement:
--   For a root $v$ and a pair $(s_i, t_i)$, the staged graph has states $(u, j, d)$ with $u$ a vertex, $0 \le j \le Q$ and phase $d \in \{-, +\}$, plus a private sink. Its arcs are
--   1. for each original arc $u \to w$, each phase $d$ and each level $j$ with $j + q_e \le Q$, the copy $(u, j, d) \to (w, j + q_e, d)$;
--   2. for each level $j$, the switch $(v, j, -) \to (v, j, +)$;
--   3. for each level $j$, the sink arc $(t_i, j, +) \to \text{sink}$.
--
--   The source is $(s_i, 0, -)$. An endpoint equal to $v$ permits an empty arm.
--
--   **Formalization Note** "When permitted" is read as $j + q_e \le Q$. Staged arcs are indexed by (kind, arc, level), the same index set for all pairs and roots.
-- source:
--   Mahboub, Rahgoshay, Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar Graphs, STOC 2027 submission (manuscript sha256 5af18346c1fe696ca8ed57aa7736510e10e27188695bb15edcbe662315790dda), §4.4, p.14

import Mathlib
import Definitions.Def_LCPlanarSteiner_lpQ

namespace LCPlanarSteiner

/-- **The staged length-layer graph of one pair.**
Mahboub, Rahgoshay, *Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar
Graphs*, STOC 2027 submission (manuscript sha256 5af18346…), §4.4, p.14: "Each pair has states (u, j, d) for 0 ≤ j ≤ Q, d ∈ {−, +}. An original edge
u → w induces (u, j, d) → (w, j + q_e, d) when permitted. Only at v can flow switch from − to +, at
the same length level. The source is (s_i, 0, −) and a private sink accepts all (t_i, j, +). An
endpoint equal to v permits an empty arm."

A staged arc is a triple `(kind, e, j)`: kind `0`/`1` is the copy of original arc `e` at level `j` in
phase `−`/`+`, present when `j + q_e ≤ Q`; kind `2` is the switch `(v, j, −) → (v, j, +)`; kind `3` is
the sink arc `(t_i, j, +) → sink` (for kinds `2, 3` the middle entry is `0`). `stagedArcs G ε h` is
the finite set of these arcs (the same index set for every pair and root).

A state is `some (u, j, d)` (`d = false` for `−`, `true` for `+`) or `none`, the sink. `stSrc` and
`stDst` give the tail and head state of a staged arc for the root `v` and the target `t`.

**Formalization Note.** "When permitted" is read as `j + q_e ≤ Q` (the copy stays inside the levels). -/
def stagedArcs (G : Net) (ε h : ℚ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range 2 ×ˢ Finset.range G.arcs.length ×ˢ Finset.range (lpQ G ε h + 1)).filter
      fun a => a.2.2 + lpq G ε h a.2.1 ≤ lpQ G ε h) ∪
    (({2, 3} : Finset ℕ) ×ˢ ({0} : Finset ℕ) ×ˢ Finset.range (lpQ G ε h + 1))

/-- Tail state of a staged arc (root `v`, target `t`). -/
def stSrc (G : Net) (v t : ℕ) (a : ℕ × ℕ × ℕ) : Option (ℕ × ℕ × Bool) :=
  match a.1 with
  | 0 => some (G.tl a.2.1, a.2.2, false)
  | 1 => some (G.tl a.2.1, a.2.2, true)
  | 2 => some (v, a.2.2, false)
  | _ => some (t, a.2.2, true)

/-- Head state of a staged arc (root `v`); `none` is the private sink. -/
def stDst (G : Net) (ε h : ℚ) (v : ℕ) (a : ℕ × ℕ × ℕ) : Option (ℕ × ℕ × Bool) :=
  match a.1 with
  | 0 => some (G.hd a.2.1, a.2.2 + lpq G ε h a.2.1, false)
  | 1 => some (G.hd a.2.1, a.2.2 + lpq G ε h a.2.1, true)
  | 2 => some (v, a.2.2, true)
  | _ => none

end LCPlanarSteiner


