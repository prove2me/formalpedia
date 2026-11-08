-- Prove2me | Definitions.Def_MaxCompForest_RInst
-- name    : MaxCompForest_RInst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:30.686194+00:00
-- url     : https://prove2.me/theorems/7b6d8db2-356e-4113-9121-8945525a9fe2
-- title:
--   A rational input graph
-- statement:
--   An explicit input: numbers $n$ of vertices and $m$ of labelled edges, the two endpoints of each label, and a positive rational conductance for each label. Loops are excluded and parallel labels are allowed; the real weighted graph is obtained by casting the conductances.
--
--   **Formalization Note** The paper's "binary rational" is read as rationals written in binary, not as dyadic rationals only: Theorem 3.1 says "positive rational conductances", and the proof nowhere needs dyadic inputs.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), p.14, p.15

import Mathlib
import Definitions.Def_EffResSparsify_ResistanceSketch_Graph
open EffResSparsify.ResistanceSketch

namespace MaxCompForest

/-- **An explicit rational input**: `n` vertices, `m` labelled edges, each with its endpoints and a positive
rational conductance.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), p.14: "All algorithmic inputs are binary rational", p.15.

**Formalization Note.** Loopless and positive by construction, so inputs outside these conditions are not
inputs at all; connectivity, simplicity and the spectral promise are hypotheses of each theorem. Reading
of "binary rational": rationals written in binary, reduced (see `encRat`), not dyadic rationals only;
Theorem 3.1 says "positive rational". -/
structure RInst where
  /-- number of vertices -/
  n : ℕ
  /-- number of labelled edges -/
  m : ℕ
  /-- endpoint of each label -/
  head : Fin m → Fin n
  /-- other endpoint of each label -/
  tail : Fin m → Fin n
  /-- conductance of each label -/
  c : Fin m → ℚ
  head_ne_tail : ∀ e, head e ≠ tail e
  c_pos : ∀ e, 0 < c e

/-- The real graph of a rational input: the conductances cast to `ℝ`. -/
def RInst.graph (I : RInst) : WGraph (Fin I.n) (Fin I.m) where
  head := I.head
  tail := I.tail
  w e := (I.c e : ℝ)
  head_ne_tail := I.head_ne_tail
  w_pos e := by exact_mod_cast I.c_pos e

end MaxCompForest


