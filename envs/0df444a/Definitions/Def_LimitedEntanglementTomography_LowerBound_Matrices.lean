-- Prove2me | Definitions.Def_LimitedEntanglementTomography_LowerBound_Matrices
-- name    : LimitedEntanglementTomography_LowerBound_Matrices
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:09:54.442611+00:00
-- url     : https://prove2.me/theorems/69d126b3-811e-4aba-88e4-037feb88f048
-- title:
--   Matrix norms, trace distance, spectral functions, $\mathrm{Herm}_0(\mathbb C^d)$ coordinates and the unfolded matrix $G_1(u)$
-- statement:
--   Operators on $\mathbb C^d$ are complex $d\times d$ matrices, with the Borel $\sigma$-algebra of their finite-dimensional topology. For a square matrix $A$ with singular values $\sigma_i(A)$ (square roots of the eigenvalues of $A^\dagger A$):
--
--   1. the trace norm is $\|A\|_1=\sum_i\sigma_i(A)$;
--   2. the Frobenius norm is $\|A\|_F=\big(\sum_{i,j}|A_{ij}|^2\big)^{1/2}$;
--   3. the operator norm is $\|A\|_{\mathrm{op}}=\max_i\sigma_i(A)$;
--   4. the trace distance between two matrices is $D_{\mathrm{tr}}(\rho,\sigma)=\tfrac12\|\rho-\sigma\|_1$.
--
--   For a Hermitian matrix with eigen-decomposition $A=U\,\mathrm{diag}(\lambda)\,U^\dagger$ and $f:\mathbb R\to\mathbb R$, $f(A)=U\,\mathrm{diag}(f(\lambda_i))\,U^\dagger$; this gives $A^{1/2}$ and $A^{-1/2}$, and $\lambda_{\min}(A)$ is the smallest eigenvalue. $A\succeq c\,I_d$ means that $A-cI_d$ is positive semidefinite.
--
--   $\mathrm{Herm}_0(\mathbb C^d)=\{H:H=H^\dagger,\ \operatorname{tr}H=0\}$ is a real Hilbert space of dimension $d^2-1$ for $\langle H,G\rangle=\operatorname{tr}(HG)$. A family $F_1,\dots,F_{d^2-1}$ of traceless Hermitian matrices with $\operatorname{tr}(F_bF_c)=\delta_{bc}$ is an orthonormal basis, and $\theta\in\mathbb R^{d^2-1}$ is identified with $\sum_b\theta_bF_b$.
--
--   For $u\in(\mathbb C^d)^{\otimes t}$ (indexed by $x\in[d]^t$), the unfolded matrix is the sum of its one-copy reduced matrices,
--   $$G_1(u)=\sum_{\ell=1}^{t}\operatorname{tr}_{[t]\setminus\{\ell\}}\big(|u\rangle\langle u|\big),\qquad \big(\operatorname{tr}_{[t]\setminus\{\ell\}}|u\rangle\langle u|\big)_{ab}=\sum_{x:\,x_\ell=a}u_x\,\overline{u_{x[\ell\mapsto b]}} .$$
--
--   These objects state every result of the mission: trace distance is the accuracy of tomography, the three norms control the Gaussian prior, and $G_1$ carries the score of a block measurement.
--
--   **Formalization Note** States are the published `WildeQIT.IsDensityOperator` and $t$ copies the published `tensorPow`, indexed by `Fin t → Fin d`. The operator norm is a real supremum over the finite index set (value $0$ only for $d=0$). Spectral functions return $0$ on non-Hermitian input, which never occurs below. $G_1$ is the sum, not the average.
-- source:
--   Ufuk Keskin, Jason Luo, Mahbod Majid, Matthew Radzihovsky, Tight Lower Bounds for State Tomography with Limited Entanglement, STOC 2027 submission #1625 (October 2026), source.pdf SHA-256 bdd8884c95899a0c563507d1c005e0dee86e418d52478a2e9e6682bb1f9d29c3, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1625.pdf, printed p.1 / PDF p.3 (trace distance); §4.1, printed pp.8–9 / PDF pp.10–11 (norms, Herm₀, orthonormal basis); §4.3, printed p.14 / PDF p.16, eq. (22) (unfolded matrix)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_ShadowTomography_ClassicalLB_tensorPow

open scoped ComplexOrder
noncomputable section

/-!
# Matrix geometry for state tomography with limited entanglement

Ufuk Keskin, Jason Luo, Mahbod Majid, Matthew Radzihovsky, *Tight Lower Bounds for State
Tomography with Limited Entanglement*, STOC 2027 submission #1625 (October 2026):
§1 (printed p.1 / PDF p.3), §4.1 (printed pp.8–9 / PDF pp.10–11), §4.3 (printed pp.13–15 /
PDF pp.15–17).

States are the published `WildeQIT.IsDensityOperator` (PSD, trace one, singular states
included); `t` independent copies are the published `ShadowTomography.ClassicalLB.tensorPow`,
indexed by `Fin t → Fin d`.
-/

namespace LimitedEntanglementTomography.LowerBound

open Matrix

/-- Complex `d × d` matrices, operators on `ℂ^d`. -/
abbrev Op (d : ℕ) := Matrix (Fin d) (Fin d) ℂ

/-- Complex square matrices over a finite index type carry the Borel σ-algebra of their
(finite-dimensional) topology. -/
instance instMeasurableSpaceMatrix {n : Type} [Fintype n] : MeasurableSpace (Matrix n n ℂ) :=
  borel _

instance instBorelSpaceMatrix {n : Type} [Fintype n] : BorelSpace (Matrix n n ℂ) := ⟨rfl⟩

/-- The singular values of a square matrix: square roots of the eigenvalues of `A† A`. -/
def singularValues {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) : n → ℝ :=
  fun i => Real.sqrt ((isHermitian_conjTranspose_mul_self A).eigenvalues i)

/-- §4.1: the trace norm `‖A‖₁`, the sum of the singular values. -/
def traceNorm {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) : ℝ :=
  ∑ i, singularValues A i

/-- §4.1: the Frobenius norm `‖A‖_F`, the Euclidean norm of the singular values, equivalently
`(∑ᵢⱼ |Aᵢⱼ|²)^{1/2}`. -/
def frobNorm {n : Type} [Fintype n] (A : Matrix n n ℂ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2)

/-- §4.1: the operator norm `‖A‖_op`, the largest singular value (`0` on the empty index type). -/
def opNorm {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) : ℝ :=
  ⨆ i, singularValues A i

/-- §1, p.1: the trace distance `D_tr(ρ, σ) = ‖ρ − σ‖₁ / 2`. -/
def traceDist {d : ℕ} (ρ σ : Op d) : ℝ :=
  traceNorm (ρ - σ) / 2

/-- Spectral calculus on Hermitian matrices: `f(A) = U diag(f(λᵢ)) U†` for an eigen-decomposition
`A = U diag(λ) U†`; the value `0` is used for a non-Hermitian argument (never used below). -/
def hermFun {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (f : ℝ → ℝ) :
    Matrix n n ℂ :=
  if h : A.IsHermitian then
    (h.eigenvectorUnitary : Matrix n n ℂ) * diagonal (fun i => ((f (h.eigenvalues i) : ℝ) : ℂ)) *
      star (h.eigenvectorUnitary : Matrix n n ℂ)
  else 0

/-- The positive square root `A^{1/2}` of a positive semidefinite matrix. -/
def psdSqrt {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) : Matrix n n ℂ :=
  hermFun A Real.sqrt

/-- The inverse square root `A^{-1/2}` of a positive definite matrix. -/
def invSqrt {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) : Matrix n n ℂ :=
  hermFun A (fun x => (Real.sqrt x)⁻¹)

/-- `λ_min(A)`, the smallest eigenvalue of a Hermitian matrix (`0` if `A` is not Hermitian). -/
def lambdaMin {d : ℕ} (A : Op d) : ℝ :=
  if h : A.IsHermitian then ⨅ i, h.eigenvalues i else 0

/-- The Loewner order `A ⪰ c · I_d` for a real number `c`. -/
def LoewnerGE {d : ℕ} (A : Op d) (c : ℝ) : Prop :=
  (A - (c : ℂ) • (1 : Op d)).PosSemidef

/-- §4.1, p.9: a basis `F₁, …, F_{d²−1}` of `Herm₀(ℂ^d) = {H : H = H†, tr H = 0}` that is
orthonormal for the Frobenius inner product `⟨H, G⟩ = tr(HG)`. -/
def IsHerm0ONB {d : ℕ} (F : Fin (d ^ 2 - 1) → Op d) : Prop :=
  (∀ b, (F b).IsHermitian ∧ (F b).trace = 0) ∧
    ∀ b c, ((F b) * (F c)).trace = if b = c then 1 else 0

/-- §4.1, p.9: the identification of `θ ∈ ℝ^{d²−1}` with `∑_b θ_b F_b ∈ Herm₀(ℂ^d)`. -/
def herm0Coord {d : ℕ} (F : Fin (d ^ 2 - 1) → Op d) (θ : EuclideanSpace ℝ (Fin (d ^ 2 - 1))) :
    Op d :=
  ∑ b, ((θ b : ℝ) : ℂ) • F b

/-- §4.3, eq. (22): the unfolded matrix `G₁(u) = ∑_{ℓ=1}^t tr_{[t]∖{ℓ}}(|u⟩⟨u|)` of a vector
`u ∈ (ℂ^d)^{⊗t}`, the **sum** (not the average) of its one-copy reduced matrices. Entry `(a, b)`
of the `ℓ`-th reduced matrix is `∑_{x : x_ℓ = a} u_x · conj(u_{x[ℓ ↦ b]})`. -/
def unfolded {d t : ℕ} (u : (Fin t → Fin d) → ℂ) : Op d :=
  fun a b => ∑ ℓ : Fin t, ∑ x : Fin t → Fin d,
    if x ℓ = a then u x * star (u (Function.update x ℓ b)) else 0

end LimitedEntanglementTomography.LowerBound


