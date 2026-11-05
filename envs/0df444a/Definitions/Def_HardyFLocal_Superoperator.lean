-- Prove2me | Definitions.Def_HardyFLocal_Superoperator
-- name    : HardyFLocal_Superoperator
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:37:54.746093+00:00
-- url     : https://prove2.me/theorems/8aff7132-2088-4767-b43d-6e320f17ab6e
-- title:
--   One-qubit and two-qubit superoperators: complete positivity, $\Phi\otimes\Psi$, Hermiticity preservation
-- statement:
--   A **superoperator** on a finite-dimensional system with index set $\iota$ is a complex-linear map on the $\iota\times\iota$ complex matrices: $\iota$ has two elements for one qubit and four for a pair of qubits. It is **completely positive** if it has a finite Kraus form
--   $$\Phi(A)=\sum_i K_i A K_i^\dagger,$$
--   and **trace non-increasing** if $\operatorname{Tr}\Phi(A)\le\operatorname{Tr}A$ for every positive semidefinite $A$.
--
--   The maps carrying Hermitian matrices to Hermitian matrices form a real vector space, the **Hermiticity-preserving maps**. The **product** $\Phi\otimes\Psi$ is the map on the product index set with
--   $$(\Phi\otimes\Psi)(A\otimes B)=\Phi(A)\otimes\Psi(B).$$
--   Finally, for a family $(B_i)$ of vectors of a real vector space and a vector $v$, the **coordinates** of $v$ are real numbers $c_i$ with $v=\sum_i c_i B_i$, or zero if no such expansion exists.
--
--   These are the objects of §5 of the paper: its boxes, its expansion (20), and the phrase "we can solve equation (20)".
--
--   **Formalization Note** The product is written through matrix units, and its property on Kronecker products is proved in the mission's verification file. Coordinates are obtained by choice; on an independent family they are unique, so nothing depends on the choice. The junk value zero is not reached on Hermiticity-preserving maps.
-- source:
--   L. Hardy, Formalism Locality in Quantum Theory and Quantum Gravity, arXiv:0804.0054v1, §5, eq. (20), pp.12–13

import Mathlib

set_option autoImplicit false

namespace HardyFLocal

open scoped Kronecker ComplexOrder

/-- **Superoperators on square matrices**, Hardy, *Formalism Locality in Quantum Theory and
Quantum Gravity*, arXiv:0804.0054v1, §5, p.12: a linear map on the `ι × ι` complex matrices. A
single qubit has `ι = Fin 2`, a pair of qubits `ι = Fin 2 × Fin 2`. -/
abbrev Op (ι : Type) : Type := Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ

/-- **Complete positivity**, arXiv:0804.0054v1, §5, p.12 ("superoperators are trace non-increasing
maps on density operators that take allowed states to allowed states"): `Φ` has a finite Kraus
form `Φ A = Σ_i K_i A K_iᴴ`.

**Formalization Note** "Allowed states" is read as complete positivity, the standard meaning;
positivity alone fails on the entangled inputs this lattice produces. In finite dimension the
Kraus form is equivalent to complete positivity. -/
def IsCP {ι : Type} [Fintype ι] (Φ : Op ι) : Prop :=
  ∃ (r : ℕ) (K : Fin r → Matrix ι ι ℂ), ∀ A, Φ A = ∑ i, K i * A * (K i).conjTranspose

/-- **Trace non-increasing**, arXiv:0804.0054v1, §5, p.12: on positive semidefinite matrices the
trace does not grow. -/
def IsTraceNonIncreasing {ι : Type} [Fintype ι] (Φ : Op ι) : Prop :=
  ∀ A : Matrix ι ι ℂ, A.PosSemidef → (Φ A).trace.re ≤ A.trace.re

/-- **The real space of Hermiticity-preserving maps**, arXiv:0804.0054v1, §5, p.13 ("the space of
superoperators acting on a single qubit") and p.9 ("a real vector space"): the maps carrying
Hermitian matrices to Hermitian matrices, as a real subspace of `Op ι`.

**Formalization Note** Coordinates with respect to a fiducial set are real only on this subspace;
every completely positive map lies in it. -/
def hpMaps (ι : Type) : Submodule ℝ (Op ι) where
  carrier := {Φ | ∀ A : Matrix ι ι ℂ, A.IsHermitian → (Φ A).IsHermitian}
  add_mem' := by
    intro Φ Ψ hΦ hΨ A hA
    simpa using (hΦ A hA).add (hΨ A hA)
  zero_mem' := by
    intro A _
    simp
  smul_mem' := by
    intro c Φ hΦ A hA
    have h := hΦ A hA
    ext i j
    have hij := congrFun (congrFun h i) j
    simp only [Matrix.conjTranspose_apply] at hij
    simp [Matrix.conjTranspose_apply, ← hij]

/-- **The product superoperator** `Φ ⊗ Ψ`, arXiv:0804.0054v1, §5, eq. (20), p.12: the map on
`ι × κ` matrices with `(Φ ⊗ Ψ)(A ⊗ₖ B) = Φ A ⊗ₖ Ψ B`, written through matrix units.

**Formalization Note** The defining property on Kronecker products is checked in the mission's
verification file. -/
noncomputable def prodOp {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (Φ : Op ι) (Ψ : Op κ) : Op (ι × κ) where
  toFun A := ∑ i, ∑ i', ∑ j, ∑ j', A (i, j) (i', j') •
    (Φ (Matrix.single i i' 1) ⊗ₖ Ψ (Matrix.single j j' 1))
  map_add' A B := by
    simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c A := by
    simp only [Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

open Classical in
/-- **Solving an expansion for its real coefficients**, arXiv:0804.0054v1, §5, p.13 ("We can solve
equation (20) to find the Λ matrix"; "We can solve this this equation for the matrix"): a choice
of real `c` with `v = Σ_i c_i B_i`, or `0` if `v` has no such expansion.

**Formalization Note** On a real-linearly independent family `B` the coefficients are unique, so
no real choice is made on the vectors where this is used; the junk value `0` is never reached on
Hermiticity-preserving maps (milestones (20) and (21)). -/
noncomputable def coordsOf {κ V : Type} [Fintype κ] [AddCommMonoid V] [Module ℝ V]
    (B : κ → V) (v : V) : κ → ℝ :=
  if h : ∃ c : κ → ℝ, v = ∑ i, c i • B i then h.choose else 0

end HardyFLocal


