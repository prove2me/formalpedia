-- Prove2me | Definitions.Def_SelfCorrect3D_Memory_Op
-- name    : SelfCorrect3D_Memory_Op
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:30:42.825692+00:00
-- url     : https://prove2.me/theorems/babe5da4-8290-4c45-ac99-b9bda1d2efec
-- title:
--   Operators on $n$ qubits
-- statement:
--   The Hilbert space of $n$ qubits has the computational basis $\{|x\rangle : x\in\mathbb F_2^n\}$. An **operator on $n$ qubits** is a complex $2^n\times 2^n$ matrix whose rows and columns are indexed by bit strings $x\in\mathbb F_2^n$; $\mathrm{Op}(n)$ denotes the algebra of all of them.
--
--   This is the operator algebra $L(\mathcal H_S)$ in which the paper's Hamiltonians, Gibbs states, Lindbladians and encoded states live.
--
--   **Formalization Note** Bit strings are functions $\mathrm{Fin}\,n\to\mathbb Z/2$, and bit $0$ is the state $|0\rangle$.
-- source:
--   Balasubramanian, Davydova, Lin, A passive self-correcting quantum memory in three dimensions, arXiv:2605.10943, §2.1, p. 10 (unnumbered)

import Mathlib

namespace SelfCorrect3D.Memory

/-- **Operators on `n` qubits.** Balasubramanian, Davydova, Lin, *A passive self-correcting quantum memory in three dimensions*, arXiv:2605.10943, §2.1, p. 10 (unnumbered):
the Hilbert space of `n` qubits with computational basis `|x⟩`, `x ∈ 𝔽₂ⁿ`; `Op n` is the algebra
of all linear operators on it, written as complex matrices indexed by bit strings.

**Formalization Note.** Bit strings are `Fin n → ZMod 2`; bit `0` is `|0⟩`. Same convention as the
draft `AutoQMem.Lindblad.Op` (not imported: still a draft). -/
abbrev Op (n : ℕ) : Type := Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ

end SelfCorrect3D.Memory


