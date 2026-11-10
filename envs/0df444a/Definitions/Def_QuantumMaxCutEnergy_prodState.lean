-- Prove2me | Definitions.Def_QuantumMaxCutEnergy_prodState
-- name    : QuantumMaxCutEnergy_prodState
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T14:15:24.419812+00:00
-- url     : https://prove2.me/theorems/12c80286-0124-45d9-bfa8-4aed7d4b2a6c
-- title:
--   The product state of n qubits with given amplitudes
-- statement:
--   **Product states of $n$ qubits.**
--
--   Given amplitude pairs $(\alpha_i,\beta_i)\in\mathbb C^2$, one for each qubit $i\in\{1,\dots,n\}$, the associated product state assigns to each computational basis vector $x\in\{0,1\}^n$ the amplitude
--   $$\psi(x)=\prod_{i=1}^{n}\begin{cases}\beta_i & x_i=1\\ \alpha_i & x_i=0.\end{cases}$$
--
--   This is the state $\bigotimes_i(\alpha_i|0\rangle+\beta_i|1\rangle)$. It is the bridge between the classical relaxation and the quantum problem: a Bloch assignment $r_1,\dots,r_n$ with $r_i\in S^2$ arises from such a product state via the Bloch parametrisation, and — this is the content of the two-qubit correlation identity — the energy of the product state on an edge is determined by the inner product $\langle r_i,r_j\rangle$.
--
--   Hence evaluating the classical relaxation objective at the Gram matrix of the Bloch vectors computes exactly the quantum energy of the corresponding product state, which is why product states supply sound candidate values for the Quantum Max-Cut optimum.
-- source:
--   Product states of the Quantum Max Cut Hamiltonian; Anshu-Gosset-Morenz, TQC 2020, doi 10.4230/LIPIcs.TQC.2020.7.

import Mathlib
import Definitions.Def_QuantumMaxCutEnergyEstimationModel

/-!
# Product states of `n` qubits

A Bloch assignment is the same data as a product state: given amplitudes `α i` on `|0⟩` and `β i` on
`|1⟩` for each qubit, the product state is

  `prodState α β x = ∏ i, if x i then β i else α i`.

This file fixes that construction, so that the energy of the product state can be compared with the
classical relaxation objective at the Gram matrix of the Bloch vectors.
-/

open Complex
open scoped BigOperators

namespace QuantumMaxCutEnergy

/-- The product state with amplitudes `α i` on `|0⟩` and `β i` on `|1⟩`. -/
noncomputable def prodState {n : ℕ} (α β : Fin n → ℂ) : Wave n :=
  fun x => ∏ i, if x i then β i else α i

end QuantumMaxCutEnergy


