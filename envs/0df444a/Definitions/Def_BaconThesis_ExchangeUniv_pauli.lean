-- Prove2me | Definitions.Def_BaconThesis_ExchangeUniv_pauli
-- name    : BaconThesis_ExchangeUniv_pauli
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:50:08.951436+00:00
-- url     : https://prove2.me/theorems/5d6e48e9-dfbb-4658-bc71-e1bc1eb96fe5
-- title:
--   The Pauli matrices $\sigma_x,\sigma_y,\sigma_z$
-- statement:
--   The **Pauli matrices** are the $2\times 2$ complex matrices
--   $$
--   \sigma_x=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad \sigma_y=\begin{pmatrix}0&-i\\ i&0\end{pmatrix},\qquad \sigma_z=\begin{pmatrix}1&0\\0&-1\end{pmatrix},
--   $$
--   written in the computational basis $|0\rangle,|1\rangle$ of a qubit.
--
--   They are the single-qubit building blocks of the collective spin operators and of the exchange interaction.
--
--   **Formalization Note** The labels $x,y,z$ are $0,1,2$. Since $\sigma_z|0\rangle=|0\rangle$, the state $|0\rangle$ is spin up ($m=+\tfrac12$ for $S_z=\sigma_z/2$).
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, eq. (8.30), p.113 (PDF p.130); used in (9.5)–(9.8), p.126 (PDF p.143)

import Mathlib

open scoped Matrix

namespace BaconThesis.ExchangeUniv

/-- **The Pauli matrices `σ_x, σ_y, σ_z`.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1, the single-qubit Pauli operators of (8.30), §8.4, p.113 (PDF p.130), used in (9.5)–(9.8),
§9.1.2, p.126 (PDF p.143), and (C.7), p.248 (PDF p.265).

`pauli 0 = σ_x = [[0,1],[1,0]]`, `pauli 1 = σ_y = [[0,-i],[i,0]]`, `pauli 2 = σ_z = [[1,0],[0,-1]]`,
in the computational basis `|0⟩, |1⟩` of a qubit.

**Formalization Note.** The labels `α ∈ {x, y, z}` are `0, 1, 2 : Fin 3`. The basis state `|0⟩` is
index `0 : Fin 2`, so `σ_z|0⟩ = |0⟩`: `|0⟩` is spin up (`m = +1/2` for `S_z = σ_z/2`). -/
def pauli : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![0, 1; 1, 0], !![0, -Complex.I; Complex.I, 0], !![1, 0; 0, -1]]

end BaconThesis.ExchangeUniv


