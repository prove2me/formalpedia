-- Prove2me | Definitions.Def_WildeQIT_pureFidelity
-- name    : WildeQIT_pureFidelity
-- status  : Definition
-- author  : @nonlocally
-- created : 2026-09-07T06:40:26.911062+00:00
-- url     : https://prove2.me/theorems/68db0c26-75f3-47ef-90d2-0113902657a0
-- title:
--   Pure-state fidelity $F(\psi,\phi) = |\langle\psi|\phi\rangle|^2$
-- statement:
--   **Definition 9.2.1 (Pure-State Fidelity).** Let $|\psi\rangle, |\phi\rangle \in \mathcal{H}$ be pure states. The pure-state fidelity is the squared overlap of the states:
--
--   $$
--   F(\psi, \phi) \equiv |\langle \psi | \phi \rangle|^2 .
--   $$
--
--   It is the probability that a state prepared as $|\phi\rangle$ passes the test "is it $|\psi\rangle$?", and is the special case of the general fidelity (Uhlmann's theorem, Exercise 9.2.5) for two pure states.
--
--   **Formalization Note.** Vectors are `ψ φ : n → ℂ` on a finite index type; `WildeQIT.pureFidelity ψ φ = ‖star ψ ⬝ᵥ φ‖ ^ 2` with $\langle\psi|\phi\rangle = \sum_i \overline{\psi_i}\phi_i$. Normalization is not part of the definition; theorems add it as a hypothesis.
-- source:
--   Wilde, *Quantum Information Theory*, 2nd ed. (Cambridge University Press, 2017; arXiv:1106.1445v8), §9.2.1 "Pure-State Fidelity", Definition 9.2.1 (Pure-State Fidelity).

import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Analysis.Complex.Basic

/-!
Wilde, *Quantum Information Theory* (2nd ed.), §9.2.1, Definition 9.2.1 (Pure-State Fidelity).

Let `|ψ⟩, |φ⟩ ∈ ℋ` be pure states. The pure-state fidelity is the squared overlap
`F(ψ, φ) ≡ |⟨ψ|φ⟩|²`.
-/

open Matrix

namespace WildeQIT

/-- **Definition 9.2.1 (Pure-State Fidelity).** For vectors `ψ φ : n → ℂ`,
`pureFidelity ψ φ = |⟨ψ|φ⟩|²` where `⟨ψ|φ⟩ = ∑ᵢ conj(ψᵢ) φᵢ`. -/
noncomputable def pureFidelity {n : Type} [Fintype n] (ψ φ : n → ℂ) : ℝ :=
  ‖star ψ ⬝ᵥ φ‖ ^ 2

end WildeQIT


