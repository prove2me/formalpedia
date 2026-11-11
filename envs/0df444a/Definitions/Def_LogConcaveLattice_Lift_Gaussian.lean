-- Prove2me | Definitions.Def_LogConcaveLattice_Lift_Gaussian
-- name    : LogConcaveLattice_Lift_Gaussian
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:59:57.018507+00:00
-- url     : https://prove2.me/theorems/367513cb-cd7e-4224-a70a-f7d0099fa566
-- title:
--   §§2.1, 3 — Loewner order, pseudoinverse, Gaussian weights $\rho_A$, discrete Gaussian covariance, the density $f$, the potential $\Phi_\Lambda$
-- statement:
--   Matrices $A\in\mathbb R^{n\times n}$ act on $\mathbb R^n$; $\operatorname{im}(A)$ is the image.
--
--   1. **Loewner order.** For operators $S,T$ on $\mathbb R^n$, $S\preccurlyeq T$ iff $\langle v,Sv\rangle\le\langle v,Tv\rangle$ for every $v$. An operator on a subspace $E$ is extended by zero on $E^\perp$; in particular $\mathrm{Id}_E$ becomes the orthogonal projection $\Pi_E$.
--   2. **Pseudoinverse.** For $A\succcurlyeq0$, $A^+$ is the symmetric matrix with $\operatorname{im}(A^+)=\operatorname{im}(A)$ and $AA^+=A^+A=\Pi_{\operatorname{im}(A)}$; for $A\succ0$, $A^+=A^{-1}$.
--   3. **Gaussian weight.** For $A\succcurlyeq0$,
--   $$\rho_A(x)=\begin{cases}e^{-\pi\langle x,A^+x\rangle}&x\in\operatorname{im}(A),\\0&x\notin\operatorname{im}(A),\end{cases}$$
--   which is $e^{-\pi\langle x,A^{-1}x\rangle}$ when $A\succ0$. For a discrete subgroup $L$ and $x\in\mathbb R^n$, $\rho_A(x+L)=\sum_{y\in L}\rho_A(x+y)$, and $\rho_A(L)=\rho_A(0+L)$. The scalar width is $\rho_s(x)=e^{-\pi\|x\|^2/s^2}$ ($=\rho_{s^2\mathrm{Id}}$), $\rho=\rho_1$, and $\rho_s(L)=\sum_{y\in L}\rho_s(y)$.
--   4. **Discrete Gaussian.** $D_{x+L,A}$ is the law on the coset $x+L$ with $\mathbb P(Y=y)=\rho_A(y)/\rho_A(x+L)$, and
--   $$\operatorname{Cov}(D_{x+L,A})=\mathbb E[YY^{\mathsf T}]-\mathbb E[Y]\,\mathbb E[Y]^{\mathsf T}.$$
--   5. **Candidate density.** For a full-rank lattice $\Lambda$ and $A\succ0$, $f(x)=\dfrac1{\det\Lambda}\cdot\dfrac{\rho_A(x)}{\rho_A(x+\Lambda)}$.
--   6. **Potential.** $\Phi_\Lambda(A)=\dfrac{\log\rho_A(\Lambda)}{\operatorname{tr}(A)}$ for $A\succcurlyeq0$, $A\ne0$.
--
--   These objects carry the analytic half of the proof of Theorem 1.1: the Hessian of $-\log f$ is a multiple of a discrete Gaussian covariance, and the optimal matrix for $\Phi_\Lambda$ makes that covariance large.
--
--   **Formalization Note** The pseudoinverse is defined by choice from the characterization above (it exists and is unique for every symmetric matrix; the fallback $0$ is never reached for $A\succcurlyeq0$). Lattice sums are `tsum`s over the subgroup; for a discrete subgroup and $A\succcurlyeq0$ all the families involved are summable. The covariance is the matrix of the second central moments with these sums, and $\det\Lambda$ in $f$ is Mathlib's `ZLattice.covolume`.
-- source:
--   Letwin, Reis, Rothvoss, Strongly Log-Concave Measures and Lattices, STOC 2027 submission #401 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/401.pdf, §2.1 pp. 5–6 (Id_E extension, Loewner order, Moore–Penrose pseudoinverse, ρ_A, ρ_s, ρ_A(S)), §1.1 p. 3 (ρ_s(S)), §3.1 p. 9 (f, D_{x+Λ,A}), p. 11 (f), §3.2 p. 12 (singular ρ_A, Φ_Λ, (3.7))

import Mathlib
import Definitions.Def_LogConcaveLattice_Lift_Lattice

open scoped RealInnerProductSpace

namespace LogConcaveLattice.Lift

variable {n : ℕ}

/-- A real `n × n` matrix acting on `ℝⁿ`. -/
noncomputable abbrev mat (A : Matrix (Fin n) (Fin n) ℝ) : V n →ₗ[ℝ] V n :=
  Matrix.toEuclideanLin A

/-- The image `im(A)` of a matrix, a linear subspace of `ℝⁿ`. -/
noncomputable abbrev matIm (A : Matrix (Fin n) (Fin n) ℝ) : Submodule ℝ (V n) :=
  LinearMap.range (mat A)

/-- **Loewner order** (p. 6), for operators on `ℝⁿ`: `S ≼ T ⇔ ⟨v, S v⟩ ≤ ⟨v, T v⟩` for every
`v ∈ ℝⁿ`. Matrices enter through `mat`, the identity on a subspace `E` through its extension by
zero on `E⊥`, the orthogonal projection `Π_E` (p. 6). -/
def LoewnerLE (S T : V n →ₗ[ℝ] V n) : Prop :=
  ∀ v : V n, ⟪v, S v⟫ ≤ ⟪v, T v⟫

/-- The **Moore–Penrose pseudoinverse** characterization of p. 6, for `A ≽ 0`: `B` is symmetric,
`im(B) = im(A)` and `A B = B A = Π_{im(A)}`. -/
def IsPseudoinverse (A B : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  B.IsHermitian ∧ matIm B = matIm A ∧
    (∀ x : V n, mat (A * B) x = (matIm A).starProjection x) ∧
    (∀ x : V n, mat (B * A) x = (matIm A).starProjection x)

open Classical in
/-- The pseudoinverse `A⁺` (p. 6): the matrix with the property `IsPseudoinverse A`, which
exists and is unique for every symmetric `A`. (The fallback `0` is never reached for `A ≽ 0`.)
For `A ≻ 0` it is `A⁻¹`. -/
noncomputable def pinv (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  if h : ∃ B, IsPseudoinverse A B then h.choose else 0

open Classical in
/-- **Gaussian weight with matrix parameter** (p. 6; extended to singular `A ≽ 0` on p. 12):
`ρ_A(x) = exp(-π ⟨x, A⁺ x⟩)` if `x ∈ im(A)`, and `0` otherwise. For `A ≻ 0` this is
`exp(-π ⟨x, A⁻¹ x⟩)`. -/
noncomputable def rho (A : Matrix (Fin n) (Fin n) ℝ) (x : V n) : ℝ :=
  if x ∈ matIm A then Real.exp (-Real.pi * ⟪x, mat (pinv A) x⟫) else 0

/-- Gaussian mass of a coset `x + L` of a discrete subgroup `L` (p. 3, p. 6):
`ρ_A(x + L) = ∑_{y ∈ L} ρ_A(x + y)`. With `x = 0` this is `ρ_A(L)`. -/
noncomputable def rhoCoset (A : Matrix (Fin n) (Fin n) ℝ) (L : Submodule ℤ (V n)) (x : V n) : ℝ :=
  ∑' y : L, rho A (x + y)

/-- Scalar-width Gaussian `ρ_s(x) = exp(-π ‖x‖² / s²)` (p. 2, p. 6; `ρ_s = ρ_{s² Id}`). -/
noncomputable def rhoScalar (s : ℝ) (x : V n) : ℝ :=
  Real.exp (-Real.pi * ‖x‖ ^ 2 / s ^ 2)

/-- Gaussian mass `ρ_s(L) = ∑_{y ∈ L} ρ_s(y)` of a discrete set (p. 3); `ρ(L) = ρ_1(L)`. -/
noncomputable def rhoScalarMass (s : ℝ) (L : Submodule ℤ (V n)) : ℝ :=
  ∑' y : L, rhoScalar s (y : V n)

/-- **Covariance of the discrete Gaussian** `D_{x+L,A}` (p. 9): the law on the coset `x + L`
with `P(Y = y) = ρ_A(y) / ρ_A(x + L)`, and `Cov = E[Y Yᵀ] − E[Y] E[Y]ᵀ`, as a matrix. -/
noncomputable def dgCov (A : Matrix (Fin n) (Fin n) ℝ) (L : Submodule ℤ (V n)) (x : V n) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j =>
    (∑' y : L, rho A (x + y) / rhoCoset A L x * ((x + y : V n) i * (x + y : V n) j)) -
      (∑' y : L, rho A (x + y) / rhoCoset A L x * (x + y : V n) i) *
      (∑' y : L, rho A (x + y) / rhoCoset A L x * (x + y : V n) j)

/-- The candidate density of p. 9 / p. 11: `f(x) = (1 / det Λ) · ρ_A(x) / ρ_A(x + Λ)` for a
full-rank lattice `Λ` (`det Λ` is its covolume) and `A ≻ 0`. -/
noncomputable def liftDensity (A : Matrix (Fin n) (Fin n) ℝ) (Λ : Submodule ℤ (V n)) (x : V n) :
    ℝ :=
  1 / ZLattice.covolume Λ * (rho A x / rhoCoset A Λ x)

/-- The **potential** of p. 12: `Φ_Λ(A) = log ρ_A(Λ) / tr(A)`, for `A ≽ 0`, `A ≠ 0`
(then `ρ_A(Λ) ≥ ρ_A(0) = 1`). -/
noncomputable def potential (Λ : Submodule ℤ (V n)) (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Real.log (rhoCoset A Λ 0) / Matrix.trace A

end LogConcaveLattice.Lift


