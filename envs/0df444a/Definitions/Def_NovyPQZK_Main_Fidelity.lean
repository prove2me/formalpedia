-- Prove2me | Definitions.Def_NovyPQZK_Main_Fidelity
-- name    : NovyPQZK_Main_Fidelity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T05:34:25.285344+00:00
-- url     : https://prove2.me/theorems/b734c239-77fd-476c-9ea6-760a9c4df4ac
-- title:
--   Density matrices, projectors, fidelity (Definition 2) and purified distance (Definition 3)
-- statement:
--   A **register** is a finite-dimensional Hilbert space with a computational basis indexed by a finite set $\iota$; operators on it are complex $\iota\times\iota$ matrices. A **density matrix** $\rho\in D(Q)$ is positive semidefinite with $\operatorname{tr}\rho = 1$; a **projector** $P\in\operatorname{Proj}(Q)$ satisfies $P^* = P$ and $P^2 = P$.
--
--   For a Hermitian matrix $A = U\operatorname{diag}(\lambda_i)U^*$ let $\sqrt A = U\operatorname{diag}(\sqrt{\lambda_i})U^*$ (the positive semidefinite square root when $A\succeq 0$). The **fidelity** of two states is
--
--   $$F(\rho,\sigma) = \operatorname{tr}\sqrt{\sqrt\rho\,\sigma\sqrt\rho} = \|\sqrt\rho\sqrt\sigma\|_1,$$
--
--   and the **purified distance** is
--
--   $$\mathrm{PD}(\rho,\sigma) = \sqrt{1 - F^2(\rho,\sigma)}.$$
--
--   The pure state of a vector $\psi$ is $|\psi\rangle\langle\psi|$ (`pureDM`). These are the distance measures of the inverter analysis (Lemma 2, Lemma 3).
--
--   **Formalization Note** `fidelity` is the root fidelity (not its square), the real part of the trace; `psdSqrt` is `0` on a non-Hermitian matrix, which never occurs on density matrices.
-- source:
--   Dupuis, Ligez, Medhioub, Salvail, Thibodeau, Post-Quantum Perfect Zero-Knowledge Arguments for NP From Any One-Way Permutation, arXiv:2610.33185 (sha256 857d8563…3257f), §3 p. 14 (registers, D(Q), Proj(Q)) and §3.1 p. 16, Definitions 2 and 3

import Mathlib

open scoped ComplexOrder

namespace NovyPQZK.Main

/-!
Dupuis, Ligez, Medhioub, Salvail, Thibodeau, *Post-Quantum Perfect Zero-Knowledge Arguments for NP
From Any One-Way Permutation*, arXiv:2610.33185 (sha256 857d8563…3257f), §3 and §3.1, pp. 14, 16:
density matrices, projectors, the fidelity (Definition 2) and the purified distance
(Definition 3) on a finite-dimensional register.

A register is any finite type `ι` of computational-basis labels; operators on it are complex
`ι × ι` matrices.
-/

/-- `D(Q)` (p. 14): `ρ` is a density matrix, i.e. positive semidefinite with trace `1`. -/
def IsDensity {ι : Type*} [Fintype ι] (ρ : Matrix ι ι ℂ) : Prop :=
  ρ.PosSemidef ∧ ρ.trace = 1

/-- `Proj(Q)` (p. 14): `P` is an orthogonal projector, `P* = P` and `P² = P`. -/
def IsProjector {ι : Type*} [Fintype ι] (P : Matrix ι ι ℂ) : Prop :=
  P.IsHermitian ∧ P * P = P

/-- The spectral square root `U diag(√λᵢ) U*` of a Hermitian matrix `A = U diag(λᵢ) U*` (`0` if
`A` is not Hermitian). On a positive semidefinite matrix it is the positive semidefinite square
root, which is the only case used below. -/
noncomputable def psdSqrt {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) :
    Matrix ι ι ℂ :=
  if h : A.IsHermitian then
    (h.eigenvectorUnitary : Matrix ι ι ℂ) *
      Matrix.diagonal (fun i => ((Real.sqrt (h.eigenvalues i) : ℝ) : ℂ)) *
      star (h.eigenvectorUnitary : Matrix ι ι ℂ)
  else 0

/-- Definition 2 (p. 16), the (root) fidelity `F(ρ, σ) = tr √(√ρ σ √ρ)`. For density matrices
the trace is a nonnegative real number; the real part is taken. -/
noncomputable def fidelity {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ σ : Matrix ι ι ℂ) : ℝ :=
  (psdSqrt (psdSqrt ρ * σ * psdSqrt ρ)).trace.re

/-- Definition 3 (p. 16), the purified distance `PD(ρ, σ) := √(1 − F²(ρ, σ))`. -/
noncomputable def purifiedDist {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ σ : Matrix ι ι ℂ) : ℝ :=
  Real.sqrt (1 - fidelity ρ σ ^ 2)

/-- The pure state `|ψ⟩⟨ψ|` of a vector `ψ`. -/
def pureDM {ι : Type*} (ψ : ι → ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun i j => ψ i * star (ψ j)

end NovyPQZK.Main


