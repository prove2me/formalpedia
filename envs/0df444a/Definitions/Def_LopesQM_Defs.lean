-- Prove2me | Definitions.Def_LopesQM_Defs
-- name    : LopesQM_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-26T02:39:20.228799+00:00
-- url     : https://prove2.me/theorems/b66ba78f-d500-4433-b44a-65d80f1d315b
-- title:
--   Position/momentum operators, commutator, expected value, dispersion and the Gaussian packet on $L^2(\mathbb R^n)$
-- statement:
--   Basic objects of the operator formalism on $\mathbb R^n$ used throughout the book. Wave functions are maps $\psi:\mathbb R^n\to\mathbb C$; operators are maps sending wave functions to wave functions. Fix $\hbar\in\mathbb R$ (Planck's constant) and $j\in\{1,\dots,n\}$.
--
--   1. **Position operator** (p. 22–23): $(X_j\psi)(x)=x_j\,\psi(x)$.
--   2. **Momentum operator** (Definição 1.20): $(P_j\psi)(x)=-i\hbar\,\dfrac{\partial\psi}{\partial x_j}(x)$.
--   3. **Commutator** (Definição 3.1): $[A,B]\psi=A(B\psi)-B(A\psi)$.
--   4. **Inner product and norm** (Chapter 1): $\langle\varphi,\psi\rangle=\int_{\mathbb R^n}\varphi(x)\overline{\psi(x)}\,dx$, $\;|\psi|=\big(\int_{\mathbb R^n}|\psi(x)|^2dx\big)^{1/2}$.
--   5. **Expected value** (Definição 8.1): $E_\psi(A)=\langle A\psi,\psi\rangle/\langle\psi,\psi\rangle$.
--   6. **Dispersion** (Definição 8.2): $\Delta_\psi(A)=|(A-E_\psi(A)I)\psi|$.
--   7. **Domains**: $D(X_j)=\{\psi\in L^2: x_j\psi\in L^2\}$; $D(P_j)=\{\psi\in C^1 \text{ with compact support}\}$.
--   8. **Gaussian wave packet** (Definição 8.3): for $a>0$, $x_0,p_0\in\mathbb R^n$,
--   $$\psi(x)=\frac{1}{(2\pi a^2)^{n/4}}\;e^{-\frac{|x-x_0|^2}{4a^2}}\;e^{\frac{i}{\hbar}\langle p_0,x\rangle}.$$
--
--   These definitions are shared by every statement of the series drawn from this book.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)` with Lebesgue measure, and $\partial/\partial x_j$ is the Fréchet derivative evaluated on the $j$-th standard basis vector. Integrals are Bochner integrals (value $0$ on non-integrable integrands); domains are separate predicates that theorems assume. The book writes $E_\psi(A)=\langle\psi,A\psi\rangle/|\psi|^2$ in Definição 8.1 and $\langle A\psi,\psi\rangle$ on p. 128; the two agree for the self-adjoint observables the book considers, and the second form is used here.
-- source:
--   A. O. Lopes, "Uma Breve Introdução à Matemática da Mecânica Quântica", 31º Colóquio Brasileiro de Matemática, IMPA, 2017 (http://mat.ufrgs.br/~alopes/hom/livroquantum.pdf is the extended version); Definição 1.20 (p. 24), Definição 3.1 (p. 64), Definição 8.1 (p. 125, and p. 128), Definição 8.2 (p. 128), Definição 8.3 (p. 133), domains D(X_j) p. 23 and D(P_j) p. 25.

import Mathlib

open MeasureTheory

namespace LopesQM

/-- Euclidean space `ℝⁿ`, carrying Lebesgue measure `volume`. -/
abbrev Rn (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Complex-valued wave functions `ψ : ℝⁿ → ℂ`. -/
abbrev WaveFn (n : ℕ) := Rn n → ℂ

/-- (Possibly unbounded) operators, acting on all functions `ℝⁿ → ℂ`;
domains are imposed separately as hypotheses. -/
abbrev Op (n : ℕ) := WaveFn n → WaveFn n

/-- Position operator `Xⱼ` (multiplication by the coordinate `xⱼ`). -/
def positionOp {n : ℕ} (j : Fin n) : Op n :=
  fun ψ x => ((x j : ℝ) : ℂ) * ψ x

/-- Momentum operator `Pⱼ = -iħ ∂/∂xⱼ` (Definição 1.20). -/
noncomputable def momentumOp {n : ℕ} (hbar : ℝ) (j : Fin n) : Op n :=
  fun ψ x => -(Complex.I * (hbar : ℂ)) * fderiv ℝ ψ x (EuclideanSpace.single j (1 : ℝ))

/-- Commutator `[A, B] = AB - BA` (Definição 3.1). -/
def commutator {n : ℕ} (A B : Op n) : Op n :=
  fun ψ => A (B ψ) - B (A ψ)

/-- The book's `L²` inner product `⟨φ, ψ⟩ = ∫ φ(x) conj(ψ(x)) dx`
(linear in the first argument, as in Chapter 1). -/
noncomputable def l2Inner {n : ℕ} (φ ψ : WaveFn n) : ℂ :=
  ∫ x, φ x * (starRingEnd ℂ) (ψ x)

/-- The `L²` norm `|ψ| = (∫ |ψ(x)|² dx)^{1/2}`. -/
noncomputable def l2Norm {n : ℕ} (ψ : WaveFn n) : ℝ :=
  Real.sqrt (∫ x, ‖ψ x‖ ^ 2)

/-- Expected value `E_ψ(A) = ⟨Aψ, ψ⟩ / ⟨ψ, ψ⟩` (Definição 8.1, p. 128). -/
noncomputable def expectation {n : ℕ} (A : Op n) (ψ : WaveFn n) : ℂ :=
  l2Inner (A ψ) ψ / l2Inner ψ ψ

/-- Dispersion `Δ_ψ(A) = |(A - E_ψ(A) I) ψ|` (Definição 8.2). -/
noncomputable def dispersion {n : ℕ} (A : Op n) (ψ : WaveFn n) : ℝ :=
  l2Norm (fun x => A ψ x - expectation A ψ * ψ x)

/-- Domain `D(Xⱼ)`: `ψ ∈ L²(ℝⁿ)` and `xⱼ ψ ∈ L²(ℝⁿ)`. -/
def InPositionDomain {n : ℕ} (j : Fin n) (ψ : WaveFn n) : Prop :=
  MemLp ψ 2 ∧ MemLp (positionOp j ψ) 2

/-- Domain `D(Pⱼ)`: `ψ` of class `C¹` with compact support (Definição 1.20). -/
def InMomentumDomain {n : ℕ} (ψ : WaveFn n) : Prop :=
  ContDiff ℝ 1 ψ ∧ HasCompactSupport ψ

/-- Gaussian wave packet (Definição 8.3):
`ψ(x) = (2πa²)^{-n/4} exp(-|x - x₀|²/(4a²)) exp(i⟨p₀, x⟩/ħ)`. -/
noncomputable def gaussianPacket {n : ℕ} (hbar a : ℝ) (x0 p0 : Rn n) : WaveFn n :=
  fun x => (((2 * Real.pi * a ^ 2) ^ ((n : ℝ) / 4))⁻¹ : ℝ) *
    Complex.exp (((-(‖x - x0‖ ^ 2) / (4 * a ^ 2) : ℝ) : ℂ)) *
    Complex.exp (Complex.I * (((inner ℝ p0 x) / hbar : ℝ) : ℂ))

end LopesQM


