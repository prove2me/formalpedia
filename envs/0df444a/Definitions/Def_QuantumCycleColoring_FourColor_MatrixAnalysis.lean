-- Prove2me | Definitions.Def_QuantumCycleColoring_FourColor_MatrixAnalysis
-- name    : QuantumCycleColoring_FourColor_MatrixAnalysis
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T17:59:16.576201+00:00
-- url     : https://prove2.me/theorems/21b22030-60bd-49c1-80dd-561eac9b45f6
-- title:
--   Vectorization, partial traces, trace and $\Lambda$-norms, $\Lambda$-mass and $\Lambda$-energy
-- statement:
--   Fix a finite index set $d$ and write $\mathbb C^N$ for $\mathbb C^d$, $N=|d|$. Operators on $\mathbb C^N\otimes\mathbb C^N$ are matrices indexed by pairs $(i,j)$; the first tensor factor is $\mathcal A$, the second $\mathcal B$, and $X\otimes Y$ is the Kronecker product, $(X\otimes Y)_{(i,j),(i',j')}=X_{ii'}Y_{jj'}$. For a matrix $X$, $\bar X$ is its entrywise complex conjugate and $X^\top$ its transpose.
--
--   1. **Vectorization** sends $X\in\mathbb C^{M\times N}$ to $\mathrm{vec}(X)\in\mathbb C^M\otimes\mathbb C^N$ with $\mathrm{vec}(E_{i,j})=e_i\otimes e_j$, i.e. $\mathrm{vec}(X)_{(i,j)}=X_{ij}$. For a vector $v$, $|v\rangle\langle v|=vv^\dagger$.
--   2. **Partial traces**: $(\mathrm{Tr}_{\mathcal A}X)_{jj'}=\sum_i X_{(i,j),(i,j')}$ and $(\mathrm{Tr}_{\mathcal B}X)_{ii'}=\sum_j X_{(i,j),(i',j)}$.
--   3. **Norms**: the Frobenius norm $\|X\|_F=(\sum_{i,j}|X_{ij}|^2)^{1/2}$; the trace norm $\|X\|_1=\mathrm{Tr}\sqrt{X^\dagger X}$, the sum of the singular values of $X$; and, for PSD $\Lambda$, the **$\Lambda$-norm** $\|X\|_\Lambda=\|(\Lambda\otimes\bar\Lambda)X(\Lambda\otimes\bar\Lambda)\|_1$.
--   4. For PSD $P$ on $\mathbb C^N\otimes\mathbb C^N$ and PSD $\Lambda$, the **$\Lambda$-mass** and **$\Lambda$-energy** are
--   $$m_\Lambda(P)=\mathrm{Tr}\big(P(\Lambda^2\otimes\bar\Lambda^2)\big),\qquad \mathcal E_\Lambda(P)=\mathrm{Tr}(\Lambda A\Lambda B),$$
--   with $A=\mathrm{Tr}_{\mathcal A}\big((\Lambda^2\otimes I)P\big)^\top$ and $B=\mathrm{Tr}_{\mathcal B}\big((I\otimes\bar\Lambda^2)P\big)$.
--   5. For a subspace $U\subseteq\mathbb C^N$, $\Pi_U$ is the orthogonal projector onto $U$ (as a matrix), and the **cut space** $L(U^\perp,U)=\mathrm{span}\{xy^\dagger:x\in U,\ y\in U^\perp\}$ is viewed through vectorization as the subspace $\mathrm{span}\{\mathrm{vec}(xy^\dagger)\}$ of $\mathbb C^N\otimes\mathbb C^N$; its projector is $\Pi_{L(U^\perp,U)}$.
--   6. For a matrix $B$ and a threshold $t$, the **spectral subspace** $\mathrm{span}\{v_i:\rho_i\ge t\}$ is the sum of the eigenspaces of $B$ for real eigenvalues $\rho\ge t$; for Hermitian $B=\sum_i\rho_iv_iv_i^\dagger$ it is the span of the eigenvectors with $\rho_i\ge t$, and it is $\{0\}$ if there are none.
--   7. The register regrouping $((a,(b,c)),d)\mapsto((a,b),(c,d))$ identifies the space of $\rho\otimes|\Psi\rangle\langle\Psi|\otimes\bar\rho$ with that of $P\otimes P$ (Lemma 4.7).
--
--   These objects carry the whole energy formulation: the mass and energy of a POVM element are the probabilities of one and of two adjacent equal outputs on a cycle, and the norms measure how far operators and weights move in the stability theorem.
--
--   **Formalization Note** Mass and energy are the real parts of the two traces, which are real for PSD $P$ and $\Lambda$. Definition 4.1 also writes $m_\Lambda(P)=\|P\|_\Lambda$; the trace form is used, which agrees with it for PSD $P$. Vectorization is row-index first, unlike Mathlib's column-stacking `Matrix.vec`. The trace norm is defined for every square matrix through the eigenvalues of $X^\dagger X$.
-- source:
--   Tom Gur, Longcheng Li, STOC 2027 submission #515 (October 2026), §3.1 Definitions 3.1, 3.2, 3.4 and the vectorization paragraph (pp.17–18); Definition 4.1 (p.20); Theorem 5.1 (P1) (p.25); §5.2.1 (p.29); Lemma 4.7 (p.23)

import Mathlib

open scoped Kronecker ComplexOrder

/-!
# Matrix analysis for the Λ-energy of bipartite operators

Tom Gur, Longcheng Li, *Impossibility of One-Way One-Round Quantum 4-Coloring via Matrix-Space
Stability*, STOC 2027 submission #515 (October 2026), §3.1 (pp.17–18) and §4 (p.20), with the
cut space of Theorem 5.1 (p.25) and the spectral subspace of §5.2.1 (p.29).

A local dimension is a finite index type `d` (the paper's `ℂ^N` has standard basis indexed by
`d`, `N = Fintype.card d`). A bipartite operator on `ℂ^N ⊗ ℂ^N` is a matrix indexed by `d × d`,
the first factor being `𝒜` and the second `ℬ`. The tensor product `X ⊗ Y` is Mathlib's Kronecker
product `X ⊗ₖ Y`, whose entry at `((i,j),(i',j'))` is `X i i' * Y j j'`.
-/

namespace QuantumCycleColoring.FourColor

open Matrix

variable {m k d : Type} [Fintype m] [Fintype k] [Fintype d] [DecidableEq d]

/-- p.17: the entrywise complex conjugate `X̄` of a matrix. -/
def conjM {m k : Type} (X : Matrix m k ℂ) : Matrix m k ℂ := X.map star

/-- p.18: vectorization `vec : ℂ^{M×N} → 𝒜 ⊗ ℬ`, `vec(E_{i,j}) = e_i ⊗ e_j`, i.e.
`vec X (i, j) = X i j` (row index first). This is *not* Mathlib's `Matrix.vec`, which stacks
columns. -/
def vecM {m k : Type} (X : Matrix m k ℂ) : m × k → ℂ := fun p => X p.1 p.2

/-- The rank-one operator `|v⟩⟨v| = v v†`. -/
def ketBra {m : Type} (v : m → ℂ) : Matrix m m ℂ := Matrix.vecMulVec v (star v)

/-- §3.1: the partial trace over the first factor `𝒜`,
`Tr_𝒜 X (j, j') = ∑_i X (i,j) (i,j')`. -/
def ptraceA (X : Matrix (m × k) (m × k) ℂ) : Matrix k k ℂ :=
  fun j j' => ∑ i, X (i, j) (i, j')

/-- §3.1: the partial trace over the second factor `ℬ`,
`Tr_ℬ X (i, i') = ∑_j X (i,j) (i',j)`. -/
def ptraceB (X : Matrix (m × k) (m × k) ℂ) : Matrix m m ℂ :=
  fun i i' => ∑ j, X (i, j) (i', j)

/-- Definition 3.1, p.17: the Frobenius norm `‖X‖_F = (∑_{i,j} |X_{i,j}|²)^{1/2}`. -/
noncomputable def frobNorm {m k : Type} [Fintype m] [Fintype k] (X : Matrix m k ℂ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, ‖X i j‖ ^ 2)

/-- Definition 3.2, p.17, `p = 1`: the trace norm `‖X‖_1 = Tr √(X†X)`, the sum of the square
roots of the eigenvalues of the positive semidefinite matrix `X†X` (the singular values of `X`).
Defined for every square matrix, Hermitian or not. -/
noncomputable def traceNorm {m : Type} [Fintype m] [DecidableEq m] (X : Matrix m m ℂ) : ℝ :=
  ∑ i, Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self X).eigenvalues i)

/-- Definition 3.4, p.18: the Λ-norm `‖X‖_Λ = ‖(Λ ⊗ Λ̄) X (Λ ⊗ Λ̄)‖_1`. -/
noncomputable def lamNorm (Λ : Matrix d d ℂ) (X : Matrix (d × d) (d × d) ℂ) : ℝ :=
  traceNorm ((Λ ⊗ₖ conjM Λ) * X * (Λ ⊗ₖ conjM Λ))

/-- Definition 4.1, p.20: the Λ-mass `m_Λ(P) = Tr(P (Λ² ⊗ Λ̄²))`. The trace is real for PSD `P`
and `Λ`; the real part is taken. -/
noncomputable def mass (Λ : Matrix d d ℂ) (P : Matrix (d × d) (d × d) ℂ) : ℝ :=
  (Matrix.trace (P * ((Λ * Λ) ⊗ₖ (conjM Λ * conjM Λ)))).re

/-- Definition 4.1, p.20: the matrix `A = Tr_𝒜((Λ² ⊗ I) P)^⊤`. -/
def energyA (Λ : Matrix d d ℂ) (P : Matrix (d × d) (d × d) ℂ) : Matrix d d ℂ :=
  (ptraceA (((Λ * Λ) ⊗ₖ (1 : Matrix d d ℂ)) * P))ᵀ

/-- Definition 4.1, p.20: the matrix `B = Tr_ℬ((I ⊗ Λ̄²) P)`. -/
def energyB (Λ : Matrix d d ℂ) (P : Matrix (d × d) (d × d) ℂ) : Matrix d d ℂ :=
  ptraceB (((1 : Matrix d d ℂ) ⊗ₖ (conjM Λ * conjM Λ)) * P)

/-- Definition 4.1, p.20: the Λ-energy `E_Λ(P) = Tr(Λ A Λ B)`. The trace is real for PSD `P`
and `Λ`; the real part is taken. -/
noncomputable def energy (Λ : Matrix d d ℂ) (P : Matrix (d × d) (d × d) ℂ) : ℝ :=
  (Matrix.trace (Λ * energyA Λ P * Λ * energyB Λ P)).re

/-- The reassociation of four registers used in Lemma 4.7 (p.23) and §6.1 (p.41): the state
`ρ ⊗ |Ψ⟩⟨Ψ| ⊗ ρ̄` lives on `(d × (d × d)) × d` (registers `B_{ℓ-1}`, `(A_ℓ, B_ℓ)`, `A_{ℓ+1}`),
the operator `P ⊗ P` on `(d × d) × (d × d)` (registers `(B_{ℓ-1}, A_ℓ)`, `(B_ℓ, A_{ℓ+1})`). -/
def regAssoc (d : Type) : ((d × (d × d)) × d) ≃ ((d × d) × (d × d)) where
  toFun x := ((x.1.1, x.1.2.1), (x.1.2.2, x.2))
  invFun y := ((y.1.1, (y.1.2, y.2.1)), y.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- §3.1, p.17: the orthogonal projector `Π_U` onto a subspace `U ⊆ ℂ^d`, as a matrix:
its `j`-th column is the orthogonal projection of the standard basis vector `e_j` onto `U`. -/
noncomputable def projMat {m : Type} [Fintype m] [DecidableEq m]
    (U : Submodule ℂ (EuclideanSpace ℂ m)) : Matrix m m ℂ :=
  fun i j => (U.starProjection (EuclideanSpace.single j 1)) i

/-- Theorem 5.1 (P1), p.25: the cut space `L(U^⊥, U) = span{x y† : x ∈ U, y ∈ U^⊥}`, viewed through
vectorization as a subspace of `ℂ^d ⊗ ℂ^d`, i.e. `span{vec(x y†)}` with
`vec(x y†) (i, j) = x i · conj (y j)`. -/
noncomputable def cutSpace (U : Submodule ℂ (EuclideanSpace ℂ d)) :
    Submodule ℂ (EuclideanSpace ℂ (d × d)) :=
  Submodule.span ℂ
    {w | ∃ x ∈ U, ∃ y ∈ Uᗮ, w = WithLp.toLp 2 (fun p : d × d => x p.1 * star (y p.2))}

/-- §5.2.1, p.29: the span of the eigenvectors of a matrix `B` whose eigenvalues are real and at
least `t`, i.e. the sum of the eigenspaces of `B` for real eigenvalues `μ ≥ t`. For a Hermitian `B`
with spectral decomposition `B = ∑_i ρ_i v_i v_i†` this is `span{v_i : ρ_i ≥ t}`, independent of
the chosen eigenbasis; it is `{0}` when no eigenvalue is `≥ t`. -/
noncomputable def specSubspaceGe (B : Matrix d d ℂ) (t : ℝ) : Submodule ℂ (EuclideanSpace ℂ d) :=
  ⨆ (μ : ℝ) (_ : t ≤ μ), Module.End.eigenspace (Matrix.toEuclideanLin B) (μ : ℂ)

end QuantumCycleColoring.FourColor


