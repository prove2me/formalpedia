-- Prove2me | Definitions.Def_WildeQIT_expectedFidelity
-- name    : WildeQIT_expectedFidelity
-- status  : Definition
-- author  : @nonlocally
-- created : 2026-09-07T06:40:21.712779+00:00
-- url     : https://prove2.me/theorems/78695da3-01cf-4004-a953-77093c66ed43
-- title:
--   Expected fidelity $F(\psi,\rho) = \langle\psi|\rho|\psi\rangle$
-- statement:
--   **Definition 9.2.2 (Expected Fidelity).** The expected fidelity $F(\psi, \rho)$ between a pure state $|\psi\rangle \in \mathcal{H}$ and a mixed state $\rho \in \mathcal{D}(\mathcal{H})$ is
--
--   $$
--   F(\psi, \rho) \equiv \langle \psi | \rho | \psi \rangle .
--   $$
--
--   It is the probability that $\rho$ passes the test $\{|\psi\rangle\langle\psi|, I - |\psi\rangle\langle\psi|\}$ (Exercise 9.2.2) and the expected pure-state fidelity over any ensemble decomposition of $\rho$.
--
--   **Formalization Note.** `WildeQIT.expectedFidelity ψ ρ = (star ψ ⬝ᵥ (ρ *ᵥ ψ)).re`, the real part of $\langle\psi|\rho|\psi\rangle$ (which is real when $\rho$ is Hermitian); `ψ : n → ℂ`, `ρ : Matrix n n ℂ`.
-- source:
--   Wilde, *Quantum Information Theory*, 2nd ed. (Cambridge University Press, 2017; arXiv:1106.1445v8), §9.2.2 "Expected Fidelity", Definition 9.2.2 (Expected Fidelity).

import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Complex.Basic

/-!
Wilde, *Quantum Information Theory* (2nd ed.), §9.2.2, Definition 9.2.2 (Expected Fidelity).

The expected fidelity `F(ψ, ρ)` between a pure state `|ψ⟩ ∈ ℋ` and a mixed state `ρ ∈ 𝒟(ℋ)` is
`F(ψ, ρ) ≡ ⟨ψ|ρ|ψ⟩`.
-/

open Matrix

namespace WildeQIT

/-- **Definition 9.2.2 (Expected Fidelity).** For a vector `ψ : n → ℂ` and a matrix
`ρ : Matrix n n ℂ`, `expectedFidelity ψ ρ = ⟨ψ|ρ|ψ⟩`, recorded as the real part of the complex
number `star ψ ⬝ᵥ (ρ *ᵥ ψ)` (which is real when `ρ` is Hermitian). -/
noncomputable def expectedFidelity {n : Type} [Fintype n] (ψ : n → ℂ) (ρ : Matrix n n ℂ) : ℝ :=
  (star ψ ⬝ᵥ (ρ *ᵥ ψ)).re

end WildeQIT


