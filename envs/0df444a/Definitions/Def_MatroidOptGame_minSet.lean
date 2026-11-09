-- Prove2me | Definitions.Def_MatroidOptGame_minSet
-- name    : MatroidOptGame_minSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:49:44.714929+00:00
-- url     : https://prove2.me/theorems/8bed238f-457b-446e-86c8-03c832b37e73
-- title:
--   MIN's played set $S$ of a history
-- statement:
--   In a history $h = (h_0, h_1, \dots)$ of the matroid base minimization game, the set $S$ of elements **contracted by MIN** is $\{h_i : i \text{ odd}\}$; after $j$ rounds it is the paper's $S_j = \{s(M'_1), \dots, s(M'_j)\}$.
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2, p.3

import Mathlib

namespace MatroidOptGame

/-- The set `S` of elements played (contracted) by MIN in a history `h` (the moves at odd
positions `1, 3, 5, …`).

Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2, p.3 (`S_j = {s(M′_1), …, s(M′_j)}`). -/
def minSet {α : Type*} [DecidableEq α] (h : List α) : Finset α :=
  (Finset.univ.filter (fun i : Fin h.length => i.val % 2 = 1)).image (fun i => h[i])

end MatroidOptGame


