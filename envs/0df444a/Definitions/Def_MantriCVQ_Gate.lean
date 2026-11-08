-- Prove2me | Definitions.Def_MantriCVQ_Gate
-- name    : MantriCVQ_Gate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:08:18.580205+00:00
-- url     : https://prove2.me/theorems/ac9cac9d-e8b8-4191-a6a4-467e656683c1
-- title:
--   Quantum gates and their action on chosen wires
-- statement:
--   A **gate** on $k$ qubits is a complex $2^k\times 2^k$ matrix $U$ indexed by bit strings of length $k$. Applied to an ordered list $w$ of $k$ distinct wires of an $N$-qubit state $\psi$, it acts as $U$ on those wires and as the identity on the others:
--   $$(U_w\psi)(y)=\sum_{b\in\{0,1\}^k} U(y|_w,b)\,\psi(y[w\mapsto b]).$$
--   This is the elementary step of every circuit in the mission.
--
--   **Formalization Note** Unitarity is not part of a gate; it is required of a gate set by `Admissible`.
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), §3.1, p. 14 (PDF p. 16)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity

open QAlgorithms.Complexity

namespace MantriCVQ

/-- A quantum gate on `k` qubits: a `2^k × 2^k` complex matrix indexed by bit strings of length `k`
(Mantri, *Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy*,
arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), §3.1, p. 14 (PDF p. 16)).

**Formalization Note** Unitarity is not a field of the structure; it is required of a gate set by
`MantriCVQ.Admissible`. -/
structure Gate where
  /-- the number of qubits the gate acts on -/
  k : ℕ
  /-- the matrix of the gate -/
  U : Matrix (Bits k) (Bits k) ℂ

open Classical in
/-- The basis string `y` with the wires `w` overwritten by the bits `b`. -/
noncomputable def overwrite {N k : ℕ} (w : Fin k ↪ Fin N) (y : Bits N) (b : Bits k) : Bits N :=
  fun j => if h : ∃ i, w i = j then b h.choose else y j

/-- The gate `g` acting on the wires `w` of an `N`-qubit state and as the identity on the other
wires: the amplitude at `y` is `∑_b U(y|_w, b) ψ(y[w ↦ b])`. -/
noncomputable def Gate.apply {N : ℕ} (g : Gate) (w : Fin g.k ↪ Fin N) (ψ : QState N) : QState N :=
  fun y => ∑ b : Bits g.k, g.U (fun i => y (w i)) b * ψ (overwrite w y b)

end MantriCVQ


