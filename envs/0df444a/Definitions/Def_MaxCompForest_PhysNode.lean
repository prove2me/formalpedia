-- Prove2me | Definitions.Def_MaxCompForest_PhysNode
-- name    : MaxCompForest_PhysNode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:45.248797+00:00
-- url     : https://prove2.me/theorems/88e200cc-fd96-482f-aa82-0d8bb1c81a01
-- title:
--   Outcome of one recursion node
-- statement:
--   The three outcomes of a node of the physical recursion: terminal with a set of complete candidates (empty for a discarded branch), an all-low stop, or branching on a set of labels to include.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), proof of Lemma E.2, pp.38–39

import Mathlib

namespace MaxCompForest

/-- **What one node of the physical recursion does**: it ends with a set of complete candidates (possibly
none, a discarded branch), stops as an all-low node, or branches on a set of labels.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), proof of Lemma E.2, pp.38–39. -/
inductive PhysNode (E : Type*) where
  /-- a terminal node with its complete candidates -/
  | terminal (cands : Finset (Finset E))
  /-- an all-low node -/
  | allLow
  /-- include and contract each of these labels -/
  | branch (labels : Finset E)

end MaxCompForest


