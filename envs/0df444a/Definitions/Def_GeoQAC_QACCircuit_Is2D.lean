-- Prove2me | Definitions.Def_GeoQAC_QACCircuit_Is2D
-- name    : GeoQAC_QACCircuit_Is2D
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:30:51.269425+00:00
-- url     : https://prove2.me/theorems/189e1504-d2eb-495a-bb2c-3d4890e3ce25
-- title:
--   $[w,h]$-2D-QAC circuits
-- statement:
--   A **2D-QAC circuit** is a QAC circuit whose qubits fill a rectangle $[w]\times[h]$ of $w$ rows and $h$ columns, and in which each multi-qubit gate has contiguous support in one row or column. We call $w$ its **width** and $h$ its **length**, and write $[w,h]$-2D-QAC for this layout. Width one gives the 1D-QAC model.
--
--   The one-qubit gates are unrestricted; only the supports of the generalized controlled-Z gates are constrained to be row or column intervals.
--
--   **Formalization Note** The qubits are the positions `Fin w × Fin h` (row first); every support of every multi-qubit layer is an interval support.
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), Definition 2.3, p.11

import Mathlib
import Definitions.Def_GeoQAC_IsInterval
import Definitions.Def_GeoQAC_QACCircuit

namespace GeoQAC

/-- A `[w, h]`-2D-QAC circuit (arXiv:2604.07178, version of 2026-11-03, Definition 2.3, p.11): a QAC
circuit whose qubits fill the rectangle `[w] × [h]` (`w` rows, `h` columns) and in which every
multi-qubit gate has contiguous support in one row or one column.

**Formalization Note.** The qubits are `Pos w h = Fin w × Fin h`, row first, so `w` is the width
and `h` the length; every support of every multi-qubit layer satisfies `IsInterval`. One-qubit gates
are unrestricted. -/
def QACCircuit.Is2D {w h d : ℕ} (C : QACCircuit (Pos w h) d) : Prop :=
  ∀ j, ∀ S ∈ (C.multi j).supp, IsInterval S

end GeoQAC


