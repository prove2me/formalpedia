-- Prove2me | Definitions.Def_PathRecording_Supplement_IsIrrepAlg
-- name    : PathRecording_Supplement_IsIrrepAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:31:15.545897+00:00
-- url     : https://prove2.me/theorems/7e9a0327-f463-4914-89d2-04f6f8172046
-- title:
--   Simple modules of an algebra in a basis, and their isomorphism
-- statement:
--   Let $A$ be a complex algebra. A **simple module** $V^\lambda_A$ with a basis $B(V^\lambda_A)$ is a unital algebra homomorphism $\rho_\lambda:A\to\mathbb C^{n\times n}$ that is **irreducible**: $n>0$ and the only subspaces of $\mathbb C^n$ invariant under every $\rho_\lambda(a)$ are $0$ and $\mathbb C^n$. Its matrix elements are $\langle a|\rho_\lambda(\sigma)|b\rangle$. Two representations $\rho:A\to\mathbb C^{m\times m}$ and $\rho':A\to\mathbb C^{n\times n}$ are **isomorphic** when there is an invertible matrix $X$ with
--   $$\rho(a)\,X=X\,\rho'(a)\qquad\text{for all }a\in A .$$
--
--   Distinct labels $\lambda\neq\mu$ in $\Lambda(A)$ are simple modules that are not isomorphic; these notions are used in the Schur orthogonality relations for semisimple algebras.
-- source:
--   Foxman, Lombardi, Ma, Nehoran, Wright, Quantum Lazy Sampling and Path Recording for Any Group, arXiv:2606.30281v2, Theorem 5.9, p.69

import Mathlib

set_option autoImplicit false

namespace PathRecording.Supplement

/-!
# Simple modules of an algebra, in a basis

Foxman, Lombardi, Ma, Nehoran, Wright, *Quantum Lazy Sampling and Path Recording for Any Group*,
arXiv:2606.30281v2, Theorem 5.9, p.69: "Let `λ, µ ∈ Λ(A)` be the labels of two simple modules,
`V^λ_A` and `V^µ_A`, of `A`. Let `|a⟩, |b⟩ ∈ B(V^λ_A)` …", with matrix elements `⟨a|ρ_λ(σ)|b⟩`.

**Formalization Note.**
* A simple module `V^λ_A` with a basis `B(V^λ_A)` is an algebra homomorphism
  `ρ : A →ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ` (unital) that is irreducible: `n > 0` and the only
  subspaces of `ℂⁿ` invariant under every `ρ(a)` are `0` and `ℂⁿ`. The entry `ρ(σ) a b` is
  `⟨a|ρ(σ)|b⟩`.
* Distinct labels `λ ≠ µ` of `Λ(A)` are non-isomorphic simple modules: `AlgRepEquiv` is
  isomorphism of matrix representations by an invertible intertwiner.
-/

open Matrix

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- `ρ` is an irreducible matrix representation of `A` (a simple module in a basis). -/
def IsIrrepAlg {n : ℕ} (ρ : A →ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ) : Prop :=
  0 < n ∧ ∀ W : Submodule ℂ (Fin n → ℂ), (∀ a : A, ∀ v ∈ W, ρ a *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤

/-- Two matrix representations of `A` are isomorphic: an invertible `X` with
`ρ(a) X = X ρ'(a)` for all `a`. -/
def AlgRepEquiv {m n : ℕ} (ρ : A →ₐ[ℂ] Matrix (Fin m) (Fin m) ℂ)
    (ρ' : A →ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ (X : Matrix (Fin m) (Fin n) ℂ) (Y : Matrix (Fin n) (Fin m) ℂ),
    X * Y = 1 ∧ Y * X = 1 ∧ ∀ a : A, ρ a * X = X * ρ' a

end PathRecording.Supplement


