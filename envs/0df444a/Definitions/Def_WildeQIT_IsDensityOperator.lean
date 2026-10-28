-- Prove2me | Definitions.Def_WildeQIT_IsDensityOperator
-- name    : WildeQIT_IsDensityOperator
-- status  : Definition
-- author  : @nonlocally
-- created : 2026-09-07T03:51:19.031957+00:00
-- url     : https://prove2.me/theorems/a150ee42-b071-4892-bea1-25bd358cde64
-- title:
--   Density operator: $\rho \ge 0$ and $\mathrm{Tr}\{\rho\} = 1$
-- statement:
--   **Definition 4.1.3 (Density Operator as the State).** The state of a quantum system is given by a density operator $\rho$, which is a positive semi-definite operator with trace equal to one:
--
--   $$
--   \rho \ge 0, \qquad \mathrm{Tr}\{\rho\} = 1 .
--   $$
--
--   $\mathcal{D}(\mathcal{H})$ denotes the set of all density operators acting on a Hilbert space $\mathcal{H}$.
--
--   This is the shared notion of quantum state for the whole Wilde formalization series: distance measures (Chapter 9), entropies (Chapters 10–11) and channel coding are all stated for $\rho \in \mathcal{D}(\mathcal{H})$.
--
--   **Formalization Note.** Operators on a finite-dimensional Hilbert space are matrices `ρ : Matrix n n ℂ` over a finite index type `n`. `WildeQIT.IsDensityOperator ρ : Prop` is the predicate `ρ.PosSemidef ∧ ρ.trace = 1`; Mathlib's `Matrix.PosSemidef` includes Hermiticity ($\rho = \rho^\dagger$) together with $x^\dagger \rho x \ge 0$ for all vectors $x$ (the complex order `open scoped ComplexOrder`). A bipartite state on $\mathcal{H}_A \otimes \mathcal{H}_B$ is a matrix indexed by the product type `a × b`.
-- source:
--   Wilde, *Quantum Information Theory*, 2nd ed. (Cambridge University Press, 2017; arXiv:1106.1445v8), §4.1.1 "The Density Operator", Definition 4.1.3 (Density Operator as the State).

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Basic

open scoped ComplexOrder

/-!
Wilde, *Quantum Information Theory* (2nd ed.), §4.1.1, Definition 4.1.3
(Density Operator as the State).

"The state of a quantum system is given by a density operator `ρ`, which is a positive
semi-definite operator with trace equal to one. Let `𝒟(ℋ)` denote the set of all density
operators acting on a Hilbert space `ℋ`."

Operators on a finite-dimensional Hilbert space are matrices over `ℂ` indexed by a finite type.
-/

namespace WildeQIT

/-- **Definition 4.1.3 (Density Operator).** A matrix `ρ : Matrix n n ℂ` is a density operator
when it is positive semidefinite and has trace equal to one. `ρ ∈ 𝒟(ℋ)` is written
`IsDensityOperator ρ`. -/
def IsDensityOperator {n : Type} [Fintype n] (ρ : Matrix n n ℂ) : Prop :=
  ρ.PosSemidef ∧ ρ.trace = 1

end WildeQIT


