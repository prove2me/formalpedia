-- Prove2me | Definitions.Def_LCPlanarSteiner_ThreePieces
-- name    : LCPlanarSteiner_ThreePieces
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:03:35.575199+00:00
-- url     : https://prove2.me/theorems/bb2e9b85-97a9-4d48-aa06-1dcd77dffe64
-- title:
--   At most three directed pieces of length at most $h$
-- statement:
--   A list of oriented arcs (a root path) **consists of at most three directed pieces of length at most $h$** when it is the concatenation $l_1 l_2 l_3$ of three consecutive, possibly empty, pieces such that in each piece all arcs are oriented the same way (it is a directed path, forward or backward) and
--   $$
--   \ell(l_j) \le h \qquad (j = 1, 2, 3).
--   $$
--   The pendant arc has length $0$.
--
--   This is the shape of the root paths in the windows of Lemma 4.2, used by the separator recursion of Lemma 4.3.
-- source:
--   Mahboub, Rahgoshay, Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar Graphs, STOC 2027 submission (manuscript sha256 5af18346c1fe696ca8ed57aa7736510e10e27188695bb15edcbe662315790dda), Lemma 4.2 and its proof, p.12

import Mathlib
import Definitions.Def_LCPlanarSteiner_Net

namespace LCPlanarSteiner

/-- **At most three directed pieces of length at most `h`.**
Mahboub, Rahgoshay, *Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar
Graphs*, STOC 2027 submission (manuscript sha256 5af18346…), Lemma 4.2, p.12: "A spanning tree of M has at most three directed pieces of length at most h
on each root path." Proof, p.12: "A root path traverses at most one forest piece per layer, with at
most three layers and length at most h in each piece."

For a list `l` of oriented arcs (`none` = the free pendant arc, length `0`), `ThreePieces G h l`
says that `l` is the concatenation of three consecutive (possibly empty) pieces, each with all its
arcs oriented the same way (a directed path, forward or backward along `l`) and of total length at
most `h`.

**Formalization Note.** `olen G a` is the length of an oriented arc. -/
def olen (G : Net) (a : Option ℕ × Bool) : ℚ :=
  match a.1 with
  | some e => G.lng e
  | none => 0

/-- `l` splits into at most three directed pieces of length `≤ h`. -/
def ThreePieces (G : Net) (h : ℚ) (l : List (Option ℕ × Bool)) : Prop :=
  ∃ l₁ l₂ l₃ : List (Option ℕ × Bool), l = l₁ ++ l₂ ++ l₃ ∧
    ∀ piece ∈ [l₁, l₂, l₃], (∀ a ∈ piece, ∀ b ∈ piece, a.2 = b.2) ∧
      (piece.map (olen G)).sum ≤ h

end LCPlanarSteiner


