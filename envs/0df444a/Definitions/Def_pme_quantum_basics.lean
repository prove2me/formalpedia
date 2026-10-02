-- Prove2me | Definitions.Def_pme_quantum_basics
-- name    : pme_quantum_basics
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-02T09:03:33.173114+00:00
-- url     : https://prove2.me/theorems/c18a2c3b-46e3-4d6d-bcab-5d18e1b85120
-- title:
--   Density matrices, spectral projections, pinching, Lindbladian, HS distance, relative entropy
-- statement:
--   Finite-dimensional quantum objects used throughout the mission. Let $n$ be a finite index set, so the Hilbert space is $\mathbb C^n$ and operators are $n\times n$ complex matrices.
--
--   - **Density matrix**: $\rho\succeq 0$ with $\operatorname{tr}\rho=1$.
--   - **Eigenvalue set and spectral projections** of a Hermitian $X=U\,\mathrm{diag}(\lambda_1,\dots,\lambda_n)\,U^*$: the finite set $\{\lambda_i\}$ of distinct eigenvalues, and for every real $x$ the projection $P_x=U\,\mathrm{diag}(\mathbf 1[\lambda_i=x])\,U^*$ onto the $x$-eigenspace ($P_x=0$ if $x$ is not an eigenvalue).
--   - **Pinching** (nonselective projective measurement): $\mathcal P_X(\rho)=\sum_{x}P_x\rho P_x$, summed over the distinct eigenvalues.
--   - **Dephasing Lindbladian** with zero Hamiltonian and jump operator $X$: $\mathcal L_X(\rho)=X\rho X-\tfrac12\{X^2,\rho\}=X\rho X-\tfrac12(X^2\rho+\rho X^2)$.
--   - **Lindblad solution** from $\rho_0$: a curve $t\mapsto\rho(t)$ with $\rho(0)=\rho_0$ and $\frac{d\rho}{dt}=\mathcal L_X(\rho(t))$ for all $t\ge 0$ (one-sided derivative at $t=0$).
--   - **Squared Hilbert–Schmidt distance**: $\|\rho-\sigma\|_{HS}^2=\operatorname{tr}\big((\rho-\sigma)^*(\rho-\sigma)\big)$.
--   - **Matrix logarithm** by functional calculus with the convention $\log 0=0$ (the logarithm on the support).
--   - **Support inclusion** $\operatorname{supp}\rho\subseteq\operatorname{supp}\sigma$, encoded as $\ker\sigma\subseteq\ker\rho$.
--   - **Relative entropy** $D(\rho\|\sigma)=\operatorname{tr}(\rho\log\rho)-\operatorname{tr}(\rho\log\sigma)\in\mathbb R$ if $\operatorname{supp}\rho\subseteq\operatorname{supp}\sigma$, and $+\infty$ otherwise (valued in the extended reals).
--   - **Von Neumann entropy** $S(\rho)=-\operatorname{tr}(\rho\log\rho)$.
--
--   These encode Condition QSTO:H of the source in the finite-dimensional case (in finite dimension every density matrix has finite entropy, so Condition [B]FINENT holds automatically).
-- source:
--   G. Carcassi (Assumptions of Physics collaboration), "Projective measurements are equilibration processes", AoP Technical Brief 017, https://assumptionsofphysics.org/resources/briefs, Section 2 (Condition QSTO:H, [B]FINENT) and proof of Theorem 1 (pinching map P_X, Lindblad equation, HS distance, relative entropy), pp. 1–4

import Mathlib

/-!
Finite-dimensional quantum basics for the mission
"Projective measurements are equilibration processes" (Carcassi, AoP brief 017).
The Hilbert space is `n → ℂ` for a finite type `n`; operators are `Matrix n n ℂ`.
-/

namespace ProjectiveMeasurementEquilibration

open Matrix
open scoped ComplexOrder

variable {n : Type} [Fintype n] [DecidableEq n]

/-- A density matrix: positive semidefinite with unit trace. -/
def IsDensityMatrix (ρ : Matrix n n ℂ) : Prop :=
  ρ.PosSemidef ∧ ρ.trace = 1

/-- The (finite) set of distinct eigenvalues of a Hermitian matrix. -/
noncomputable def eigenvalueSet {X : Matrix n n ℂ} (hX : X.IsHermitian) : Finset ℝ :=
  Finset.univ.image hX.eigenvalues

/-- The orthogonal projection `P_x` onto the eigenspace of `X` for the real number `x`
(the zero matrix when `x` is not an eigenvalue): `U · diag(1[λᵢ = x]) · U*`, where
`X = U · diag(λ) · U*` is the spectral decomposition. -/
noncomputable def eigenproj {X : Matrix n n ℂ} (hX : X.IsHermitian) (x : ℝ) : Matrix n n ℂ :=
  (hX.eigenvectorUnitary : Matrix n n ℂ) *
    diagonal (fun i => if hX.eigenvalues i = x then (1 : ℂ) else 0) *
    star (hX.eigenvectorUnitary : Matrix n n ℂ)

/-- The pinching map `P_X(ρ) = ∑ₓ Pₓ ρ Pₓ`, the sum running over the distinct eigenvalues. -/
noncomputable def pinching {X : Matrix n n ℂ} (hX : X.IsHermitian) (ρ : Matrix n n ℂ) :
    Matrix n n ℂ :=
  ∑ x ∈ eigenvalueSet hX, eigenproj hX x * ρ * eigenproj hX x

/-- The dephasing Lindbladian with vanishing Hamiltonian and jump operator `X`:
`L_X(ρ) = X ρ X − ½ (X² ρ + ρ X²)`. -/
noncomputable def lindbladian (X ρ : Matrix n n ℂ) : Matrix n n ℂ :=
  X * ρ * X - (1 / 2 : ℂ) • (X * X * ρ + ρ * (X * X))

/-- `ρt` solves `dρ/dt = L_X(ρ)` on `t ≥ 0` (one-sided derivative at `t = 0`) with
`ρt 0 = ρ₀`. -/
def IsLindbladSolution (X ρ₀ : Matrix n n ℂ) (ρt : ℝ → Matrix n n ℂ) : Prop :=
  ρt 0 = ρ₀ ∧ ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt ρt (lindbladian X (ρt t)) (Set.Ici 0) t

/-- Squared Hilbert–Schmidt distance `‖ρ − σ‖²_HS = tr((ρ − σ)* (ρ − σ))`. -/
noncomputable def hsDistSq (ρ σ : Matrix n n ℂ) : ℝ :=
  ((ρ - σ)ᴴ * (ρ - σ)).trace.re

/-- Matrix logarithm by the continuous functional calculus, with `Real.log 0 = 0`; for a
positive semidefinite matrix this is the logarithm on its support and `0` on its kernel. -/
noncomputable def matrixLog (A : Matrix n n ℂ) : Matrix n n ℂ :=
  cfc Real.log A

/-- `supp ρ ⊆ supp σ`, expressed as `ker σ ⊆ ker ρ`. -/
def SupportLE (ρ σ : Matrix n n ℂ) : Prop :=
  ∀ v : n → ℂ, σ *ᵥ v = 0 → ρ *ᵥ v = 0

open Classical in
/-- Umegaki relative entropy `D(ρ‖σ) = tr(ρ log ρ) − tr(ρ log σ)` (real part), valued in
`EReal`, and equal to `+∞` unless `supp ρ ⊆ supp σ`. -/
noncomputable def relEntropy (ρ σ : Matrix n n ℂ) : EReal :=
  if SupportLE ρ σ then ((ρ * (matrixLog ρ - matrixLog σ)).trace.re : EReal) else ⊤

/-- Von Neumann entropy `S(ρ) = − tr(ρ log ρ)` (real part). -/
noncomputable def vonNeumannEntropy (ρ : Matrix n n ℂ) : ℝ :=
  -(ρ * matrixLog ρ).trace.re

end ProjectiveMeasurementEquilibration


