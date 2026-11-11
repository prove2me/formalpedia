-- Prove2me | Definitions.Def_ArbLindbladLearn_Gate
-- name    : ArbLindbladLearn_Gate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:21:55.198046+00:00
-- url     : https://prove2.me/theorems/4727a012-4480-4737-b1c9-a6e3f7a67d1d
-- title:
--   Clifford gates $H$, $S$, CNOT and circuit unitaries
-- statement:
--   A Clifford gate is a Hadamard $H_i$ or phase gate $S_i$ on qubit $i$, or $\mathrm{CNOT}_{ij}$ with control $i$ and target $j$. `gateMatrix` gives its unitary on $n$ qubits and `circuitU` the unitary of a gate list (first gate applied first). These circuits are the state preparations and measurement bases of the learner's experiments.
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), Algorithms 1–2, pp.23, 31; Clifford group, p.27

import Mathlib
import Definitions.Def_LindbladTolerant_Testing_lindblad_model

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker
noncomputable section

namespace ArbLindbladLearn

open LindbladTolerant.Testing

/-- A Clifford gate on `n` qubits: Hadamard `H` or phase `S` on qubit `i`, or `CNOT` with control
`i` and target `j` (the circuits of the experiments of Algorithms 1–2, Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…),
pp.23, 31; Clifford circuits, p.27). -/
inductive Gate (n : ℕ) : Type
  | H (i : Fin n)
  | S (i : Fin n)
  | CNOT (i j : Fin n)

/-- The unitary matrix of a gate on `Qubits n`: `⟨x|H_i|y⟩ = 1[x_k = y_k, k ≠ i] (−1)^{x_i y_i}/√2`,
`S_i = diag(i^{x_i})`, and `CNOT_{ij}|y⟩ = |y with y_j ↦ y_j ⊕ y_i⟩`.

**Formalization Note** `CNOT i i` is not a unitary; the parser of the experiment instruction
rejects it. -/
def gateMatrix {n : ℕ} : Gate n → Op (Qubits n)
  | .H i => fun x y => if ∀ k, k ≠ i → x k = y k then
      (if x i = true ∧ y i = true then -1 else 1) / (Real.sqrt 2 : ℂ) else 0
  | .S i => fun x y => if x = y then (if x i = true then Complex.I else 1) else 0
  | .CNOT i j => fun x y => if x = Function.update y j (xor (y j) (y i)) then 1 else 0

/-- The unitary of a gate list, the first gate applied first: `U = G_L ⋯ G₁`. -/
def circuitU {n : ℕ} (gs : List (Gate n)) : Op (Qubits n) :=
  gs.foldl (fun U g => gateMatrix g * U) 1

end ArbLindbladLearn


