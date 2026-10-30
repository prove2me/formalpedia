-- Prove2me | Definitions.Def_MITMSynthesis_Gate
-- name    : MITMSynthesis_Gate
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:01:50.018423+00:00
-- url     : https://prove2.me/theorems/7b913f57-2477-4ec5-a0d3-8f9e7c531f7f
-- title:
--   Quantum gates and instruction sets closed under inverses
-- statement:
--   A **gate** acts on a non-empty set of $k \ge 1$ qubits by a unitary $g \in U(2^k)$, a $2^k \times 2^k$ complex matrix indexed by bit strings $\{0,1\}^k$. Its **inverse** $g^\dagger$ is the gate of the same arity with the conjugate-transpose matrix.
--
--   An **instruction set** is a set $\mathcal G$ of gates that contains the inverse of each of its gates:
--
--   $$
--   g \in \mathcal G \implies g^\dagger \in \mathcal G .
--   $$
--
--   This is the standing assumption of the paper on the gate sets over which circuits are synthesized, for example $\{H, P, P^\dagger, \mathrm{CNOT}, T, T^\dagger\}$.
--
--   **Formalization Note** The basis of $k$ qubits is `Q k = Fin k → Fin 2`, so $U(2^k)$ is `Matrix.unitaryGroup (Q k) ℂ`. A gate is a structure with its arity, the proof that the arity is positive, and its unitary. The instruction set is a `Set Gate`, with no finiteness assumption.
-- source:
--   Amy, Maslov, Mosca, Roetteler, A meet-in-the-middle algorithm for fast synthesis of depth-optimal quantum circuits, arXiv:1206.0758v3, §2, p. 4 (definition of instruction set: "require that it contains the inverse of each gate in the set"; gates applied to non-empty subsets of qubits)

import Mathlib

namespace MITMSynthesis

/-- The computational basis of `k` qubits: bit strings `Fin k → Fin 2`. Matrices indexed by
`Q k` are the `2^k × 2^k` matrices, and `Matrix.unitaryGroup (Q k) ℂ` is `U(2^k)`. -/
abbrev Q (k : ℕ) : Type := Fin k → Fin 2

/-- **A quantum gate.** Amy–Maslov–Mosca–Roetteler, arXiv:1206.0758v3, §2, p. 4: a gate acts on
a non-empty set of qubits by a unitary. A gate has an arity `k ≥ 1` and a unitary matrix in
`U(2^k)`. -/
structure Gate where
  /-- the number of qubits the gate acts on -/
  arity : ℕ
  /-- gates act on non-empty sets of qubits -/
  arity_pos : 0 < arity
  /-- the gate's unitary, a `2^arity × 2^arity` matrix -/
  mat : Matrix.unitaryGroup (Q arity) ℂ

/-- The inverse gate `g†`: same arity, conjugate-transpose matrix. -/
def Gate.inv (g : Gate) : Gate := ⟨g.arity, g.arity_pos, star g.mat⟩

/-- **Instruction set.** arXiv:1206.0758v3, §2, p. 4: "We call this fixed set an instruction set,
and require that it contains the inverse of each gate in the set." -/
def IsInstructionSet (G : Set Gate) : Prop := ∀ g ∈ G, g.inv ∈ G

end MITMSynthesis


