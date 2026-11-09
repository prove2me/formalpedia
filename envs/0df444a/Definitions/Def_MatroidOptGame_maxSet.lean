-- Prove2me | Definitions.Def_MatroidOptGame_maxSet
-- name    : MatroidOptGame_maxSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:49:46.940439+00:00
-- url     : https://prove2.me/theorems/54822b96-c942-41cb-8ab0-ebced2180cd6
-- title:
--   MAX's played set $C$ of a history
-- statement:
--   A play of the matroid base minimization game is recorded as its **history**: the list $h = (h_0, h_1, h_2, \dots)$ of the elements played so far, in order. MAX moves first, so the moves at even positions $0, 2, 4, \dots$ are MAX's and those at odd positions are MIN's.
--
--   The set $C$ of elements **deleted by MAX** in $h$ is $\{h_i : i \text{ even}\}$; after $j$ rounds it is the paper's $C_j = \{c(M_1), \dots, c(M_j)\}$.
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2, p.3

import Mathlib

namespace MatroidOptGame

/-- The set `C` of elements played by MAX in a history `h` (the moves at even positions
`0, 2, 4, …`; MAX moves first).

Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2, p.3 (`C_j = {c(M_1), …, c(M_j)}`).

**Formalization Note.** A play is recorded as its history: the list of moves made so far, in
order. Position `i` of the list is MAX's move if `i` is even and MIN's move if `i` is odd. -/
def maxSet {α : Type*} [DecidableEq α] (h : List α) : Finset α :=
  (Finset.univ.filter (fun i : Fin h.length => i.val % 2 = 0)).image (fun i => h[i])

end MatroidOptGame


