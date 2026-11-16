-- Prove2me | Definitions.Def_GeoQAC_Supplement_gateCount
-- name    : GeoQAC_Supplement_gateCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:18:23.947521+00:00
-- url     : https://prove2.me/theorems/4a150e95-9f48-465a-9163-6873c8fb4cb5
-- title:
--   The gate count of a QAC circuit
-- statement:
--   The **gates** of a QAC circuit $C=L_dM_d\cdots L_1M_1L_0$ are the generalized controlled-$Z$ gates of the layers $M_j$, one per support, and the non-identity one-qubit unitaries of the layers $L_j$. The **gate count** is their number.
--
--   It expresses "$O(n^c)$ qubits and gates" and "polynomial-size" in Theorem 3.20.
--
--   **Formalization Note** Identity one-qubit slots are not counted as gates.
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), Definition 2.2, p.11; Theorem 3.20, p.27

import Mathlib
import Definitions.Def_GeoQAC_QACCircuit

namespace GeoQAC.Supplement

open GeoQAC

/-!
# The gate count of a QAC circuit

Dong, Ou, Yao, arXiv:2604.07178 (version of 2026-11-03), Definition 2.2, p.11 ("polynomially many
qubits and gates") and Theorem 3.20, p.27 ("`O(n^c)` qubits and gates", "polynomial-size").

**Formalization Note.** The gates of `C = L_d M_d ⋯ L_1 M_1 L_0` are the generalized controlled-Z
gates of the layers `M_j` (one per support) and the non-identity one-qubit unitaries of the layers
`L_j` (one per qubit slot `(j, v)` with `C.oneQ j v ≠ 1`). Identity slots are not gates.
-/

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The number of gates of `C`: multi-qubit gates `Σ_j |supp(M_j)|` plus non-identity one-qubit
gates. -/
noncomputable def gateCount {d : ℕ} (C : QACCircuit V d) : ℕ :=
  (∑ j : Fin d, (C.multi j).supp.card) +
    (Finset.univ.filter fun jv : Fin (d + 1) × V => C.oneQ jv.1 jv.2 ≠ 1).card

end GeoQAC.Supplement


