-- Prove2me | Definitions.Def_FowlerLSQC_Canonical_magicQ
-- name    : FowlerLSQC_Canonical_magicQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:34:48.952464+00:00
-- url     : https://prove2.me/theorems/3a9feb22-113b-4780-a1c7-527edea95370
-- title:
--   The magic-basis transformation matrix $Q$
-- statement:
--   The **magic basis** of two qubits consists of the four maximally entangled states
--   $$
--   |\Phi_1\rangle=\tfrac{1}{\sqrt2}(|00\rangle+|11\rangle),\quad
--   |\Phi_2\rangle=\tfrac{-i}{\sqrt2}(|00\rangle-|11\rangle),\quad
--   |\Phi_3\rangle=\tfrac{1}{\sqrt2}(|01\rangle-|10\rangle),\quad
--   |\Phi_4\rangle=\tfrac{-i}{\sqrt2}(|01\rangle+|10\rangle).
--   $$
--   The transformation matrix from the magic basis to the computational basis $\{|00\rangle,|01\rangle,|10\rangle,|11\rangle\}$ is the $4\times4$ matrix whose columns are $|\Phi_1\rangle,\dots,|\Phi_4\rangle$:
--   $$
--   Q=\frac{1}{\sqrt2}\begin{pmatrix}1&-i&0&0\\0&0&1&-i\\0&0&-1&-i\\1&i&0&0\end{pmatrix}.
--   $$
--   A matrix $G$ written in the magic basis is $\tilde G=Q^\dagger G Q$. In this basis the purely non-local two-qubit gates become diagonal, and the local gates $SU(2)\otimes SU(2)$ become the real rotations $SO(4)$, which is what makes the canonical decomposition computable.
--
--   **Formalization Note** Rows are indexed by the computational basis `Bool × Bool` (first component = qubit A, `false` = $|0\rangle$), so the rows $|00\rangle,|01\rangle,|10\rangle,|11\rangle$ are `(false,false)`, `(false,true)`, `(true,false)`, `(true,true)`. Columns are indexed by `Fin 4`; column $k$ is $|\Phi_{k+1}\rangle$.
-- source:
--   Fowler, Towards Large-Scale Quantum Computation, arXiv:quant-ph/0506126v1, §4.2, (4.2)–(4.3), p.48 (PDF p.66)

import Mathlib

namespace FowlerLSQC.Canonical

/-- Fowler, *Towards Large-Scale Quantum Computation*, arXiv:quant-ph/0506126v1, §4.2, (4.2)–(4.3),
p.48 (PDF p.66): the transformation matrix `Q` from the magic basis to the computational basis,
```
Q = (1/√2) [[1, -i,  0,  0],
            [0,  0,  1, -i],
            [0,  0, -1, -i],
            [1,  i,  0,  0]],
```
whose columns are the magic states `|Φ1⟩ = (|00⟩+|11⟩)/√2`, `|Φ2⟩ = -i(|00⟩-|11⟩)/√2`,
`|Φ3⟩ = (|01⟩-|10⟩)/√2`, `|Φ4⟩ = -i(|01⟩+|10⟩)/√2`.

**Formalization Note.** Rows are indexed by the computational basis `Bool × Bool` (first
component = qubit A, `false` = `|0⟩`), so the rows `|00⟩, |01⟩, |10⟩, |11⟩` of (4.3) are
`(false,false), (false,true), (true,false), (true,true)`. Columns are indexed by `Fin 4`, with
column `k` the book's `|Φ(k+1)⟩`. -/
noncomputable def magicQ : Matrix (Bool × Bool) (Fin 4) ℂ :=
  Matrix.of fun p j =>
    ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ *
      match p with
      | (false, false) => ![1, -Complex.I, 0, 0] j
      | (false, true) => ![0, 0, 1, -Complex.I] j
      | (true, false) => ![0, 0, -1, -Complex.I] j
      | (true, true) => ![1, Complex.I, 0, 0] j

end FowlerLSQC.Canonical


