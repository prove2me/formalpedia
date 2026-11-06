-- Prove2me | Definitions.Def_AutoQMem_Lindblad_Op
-- name    : AutoQMem_Lindblad_Op
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:52:47.953846+00:00
-- url     : https://prove2.me/theorems/3d1a72ec-0ebb-405d-b8fd-30595117b52b
-- title:
--   $n$-qubit operators $\mathcal B(\mathcal H)$
-- statement:
--   The physical system consists of $n$ qubits with Hilbert space $\mathcal H=(\mathbb C^2)^{\otimes n}$ and computational basis $|x\rangle$, $x\in\mathbb F_2^n$. An operator on $\mathcal H$ is a complex $2^n\times 2^n$ matrix whose rows and columns are indexed by bit strings $x\in\mathbb F_2^n$.
--
--   This is the ambient algebra $\mathcal B(\mathcal H)$ in which stabilizers, observables, density matrices and Lindblad generators of the mission live.
--
--   **Formalization Note** Bit strings are functions $\mathrm{Fin}\,n\to\mathbb Z/2$; the same type is the sector configuration space $\Omega_X=\Omega_Z=\mathbb F_2^n$ of Definition 2.2.
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), Definition 2.1, p. 13 (PDF p. 15); Definition 2.2, p. 14

import Mathlib
open Matrix

namespace AutoQMem.Lindblad

/-- **Operators on n qubits.** Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*,
arXiv:2610.05589 (PDF of 2026-11-03), §2.1, Definition 2.1, p. 13 (PDF 15):
the physical Hilbert space of n qubits, with computational basis `|x⟩`, `x ∈ 𝔽₂ⁿ`.
`Op n` is the algebra B(H) of n-qubit operators, written as complex matrices indexed by
`Fin n → ZMod 2`.

**Formalization Note.** Bit strings `x ∈ 𝔽₂ⁿ` are `Fin n → ZMod 2` (also the sector configuration
spaces Ω_X = Ω_Z = 𝔽₂ⁿ of Definition 2.2, p. 14). -/
abbrev Op (n : ℕ) : Type := Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ

end AutoQMem.Lindblad


