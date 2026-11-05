-- Prove2me | Definitions.Def_HardyFLocal_Instrument
-- name    : HardyFLocal_Instrument
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:38:24.946967+00:00
-- url     : https://prove2.me/theorems/38178dbd-b948-495d-ad2e-f440094a112c
-- title:
--   The box at a vertex: a general two-qubit measurement with countably many outcomes
-- statement:
--   At each vertex of the lattice two qubits pass through a box with a knob and a display panel. A knob setting is an **instrument** on two qubits: to each outcome $y\in\mathbb N$ it assigns a completely positive superoperator $\$_y$, such that for every matrix $A$
--   $$\sum_y \operatorname{Tr}\$_y(A)=\operatorname{Tr}A,$$
--   as an unconditional sum. Every branch is then trace non-increasing.
--
--   This is the paper's "general measurement": each (outcome, choice) pair is associated with a superoperator.
--
--   **Formalization Note** The paper fixes no outcome count. Outcomes are all of $\mathbb N$ with zero branches allowed, which covers every finite instrument. The published instrument definition of the platform has finite outcomes and is not used for this reason.
-- source:
--   L. Hardy, Formalism Locality in Quantum Theory and Quantum Gravity, arXiv:0804.0054v1, §5, p.12

import Mathlib
import Definitions.Def_HardyFLocal_Superoperator

set_option autoImplicit false

namespace HardyFLocal

/-- **The box at a vertex: a general measurement on two qubits**, Hardy, arXiv:0804.0054v1, §5,
p.12 ("The box has a knob which is used to set F_uv and a display panel recording the outcome,
Y_uv"; "an (outcome, choice) pair is associated with a superoperator $"). A knob setting is an
instrument: to each outcome `y` a completely positive map `op y`, whose traces sum to the trace of
the input.

**Formalization Note** The paper fixes no outcome count. Outcomes are all of `ℕ`, with zero branches
padding a finite instrument, so every finite instrument is covered. The normalization is an
unconditional sum for every matrix `A`. Each branch is trace non-increasing as a consequence. -/
structure Instrument where
  /-- The superoperator `$_α` of the outcome `y`. -/
  op : ℕ → Op (Fin 2 × Fin 2)
  /-- Every branch is completely positive. -/
  cp : ∀ y, IsCP (op y)
  /-- The traces of the branches sum to the trace of the input. -/
  hasSum_trace : ∀ A : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ,
    HasSum (fun y => (op y A).trace) A.trace

end HardyFLocal


