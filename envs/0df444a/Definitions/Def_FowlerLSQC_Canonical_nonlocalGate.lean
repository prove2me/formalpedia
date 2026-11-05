-- Prove2me | Definitions.Def_FowlerLSQC_Canonical_nonlocalGate
-- name    : FowlerLSQC_Canonical_nonlocalGate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:35:10.422798+00:00
-- url     : https://prove2.me/theorems/f4b6f873-8410-4aa3-a912-036d36ccf153
-- title:
--   The purely non-local gate $G_{\vec\theta}=e^{i(\theta_1X\otimes X+\theta_2Y\otimes Y+\theta_3Z\otimes Z)}$
-- statement:
--   For $\vec\theta=(\theta_1,\theta_2,\theta_3)\in\mathbb R^3$ the **purely non-local gate** is the two-qubit unitary
--   $$
--   G_{\vec\theta}=e^{i(\theta_1X\otimes X+\theta_2Y\otimes Y+\theta_3Z\otimes Z)},
--   $$
--   where $X,Y,Z$ are the Pauli matrices and the exponential is the matrix exponential. The three terms commute, so $G_{\vec\theta}$ is a product of three commuting interactions. Every two-qubit gate is, up to single-qubit gates before and after and a global phase, one of these gates.
--
--   **Formalization Note** `θ 0, θ 1, θ 2` are $\theta_1,\theta_2,\theta_3$. The Pauli matrices are the published `QAlgorithms.pauliX`, `pauliY`, `pauliZ` (indexed by `Bool`, `false` = $|0\rangle$); $\otimes$ is the Kronecker product with qubit A first; the exponential is `NormedSpace.exp`.
-- source:
--   Fowler, Towards Large-Scale Quantum Computation, arXiv:quant-ph/0506126v1, §4.2, p.48 (PDF p.66)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Gates

open scoped Kronecker

namespace FowlerLSQC.Canonical

/-- Fowler, *Towards Large-Scale Quantum Computation*, arXiv:quant-ph/0506126v1, §4.2, p.48
(PDF p.66): the purely non-local gate
`G_θ = e^{i(θ1 X⊗X + θ2 Y⊗Y + θ3 Z⊗Z)}` for `θ = (θ1, θ2, θ3) ∈ ℝ³`.

**Formalization Note.** `θ 0, θ 1, θ 2` are the book's `θ1, θ2, θ3`. The exponential is the
matrix exponential `NormedSpace.exp`. `X, Y, Z` are the Pauli matrices `QAlgorithms.pauliX`,
`pauliY`, `pauliZ` (indexed by `Bool`, `false` = `|0⟩`), and `⊗` is the Kronecker product with
qubit A as the first factor. -/
noncomputable def nonlocalGate (θ : Fin 3 → ℝ) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  NormedSpace.exp (Complex.I •
    ((θ 0 : ℂ) • (QAlgorithms.pauliX ⊗ₖ QAlgorithms.pauliX) +
      (θ 1 : ℂ) • (QAlgorithms.pauliY ⊗ₖ QAlgorithms.pauliY) +
      (θ 2 : ℂ) • (QAlgorithms.pauliZ ⊗ₖ QAlgorithms.pauliZ)))

end FowlerLSQC.Canonical


