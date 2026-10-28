-- Prove2me | Definitions.Def_WildeQIT_IsSeparable
-- name    : WildeQIT_IsSeparable
-- status  : Definition
-- author  : @nonlocally
-- created : 2026-09-07T06:10:42.205706+00:00
-- url     : https://prove2.me/theorems/1a22549e-a9d5-4c36-b4b6-18b4cc7397ca
-- title:
--   Separable state: $\sigma_{AB} = \sum_x p_X(x)\, |\psi_x\rangle\langle\psi_x|_A \otimes |\phi_x\rangle\langle\phi_x|_B$
-- statement:
--   **Definition 4.3.2 (Separable State).** A bipartite density operator $\sigma_{AB}$ is a separable state if it can be written in the following form:
--
--   $$
--   \sigma_{AB} = \sum_x p_X(x)\, |\psi_x\rangle\langle\psi_x|_A \otimes |\phi_x\rangle\langle\phi_x|_B
--   $$
--
--   for some probability distribution $p_X(x)$ and sets $\{|\psi_x\rangle_A\}$ and $\{|\phi_x\rangle_B\}$ of pure states.
--
--   Separable states are exactly the bipartite states that can be prepared by local operations and classical communication; a bipartite state that is not separable is entangled (Definition 4.3.3). In Chapter 9 the notion is used to compare channel discrimination with and without entangled inputs (Exercise 9.1.12).
--
--   **Formalization Note.** `WildeQIT.IsSeparable σ` for `σ : Matrix (a × b) (a × b) ℂ` asserts the existence of a finite index type `ι`, a probability distribution `p : ι → ℝ` (nonnegative, summing to one), and unit vectors `ψ x : a → ℂ`, `φ x : b → ℂ` (Euclidean norm one) with `σ = ∑ x, (p x : ℂ) • (vecMulVec (ψ x) (star (ψ x)) ⊗ₖ vecMulVec (φ x) (star (φ x)))`, where `vecMulVec v (star v)` is the rank-one projector $|v\rangle\langle v|$ and `⊗ₖ` the Kronecker product. The predicate does not itself assert that `σ` is a density operator, but any matrix of this form is one.
-- source:
--   Wilde, *Quantum Information Theory*, 2nd ed. (Cambridge University Press, 2017; arXiv:1106.1445v8), §4.3.2 "Separable States", Definition 4.3.2 (Separable State).

import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.Complex.Basic

/-!
Wilde, *Quantum Information Theory* (2nd ed.), §4.3.2, Definition 4.3.2 (Separable State).

"A bipartite density operator `σ_{AB}` is a separable state if it can be written in the form
`σ_{AB} = ∑_x p_X(x) |ψ_x⟩⟨ψ_x|_A ⊗ |φ_x⟩⟨φ_x|_B` for some probability distribution `p_X(x)` and
sets `{|ψ_x⟩_A}` and `{|φ_x⟩_B}` of pure states."
-/

open Matrix
open Kronecker

namespace WildeQIT

/-- **Definition 4.3.2 (Separable State).** A matrix on the composite system `a × b` is
separable when it is a convex combination `∑ₓ pₓ |ψₓ⟩⟨ψₓ| ⊗ |φₓ⟩⟨φₓ|` of tensor products of pure
states: a finite index type, a probability distribution `p`, and unit vectors `ψ x : a → ℂ`,
`φ x : b → ℂ`, with `|ψ⟩⟨ψ| = vecMulVec ψ (star ψ)`. -/
def IsSeparable {a b : Type} [Fintype a] [Fintype b] (σ : Matrix (a × b) (a × b) ℂ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (p : ι → ℝ) (ψ : ι → a → ℂ) (φ : ι → b → ℂ),
    (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1 ∧
    (∀ x, ∑ i, ‖ψ x i‖ ^ 2 = 1) ∧ (∀ x, ∑ j, ‖φ x j‖ ^ 2 = 1) ∧
    σ = ∑ x, (p x : ℂ) • (vecMulVec (ψ x) (star (ψ x)) ⊗ₖ vecMulVec (φ x) (star (φ x)))

end WildeQIT


