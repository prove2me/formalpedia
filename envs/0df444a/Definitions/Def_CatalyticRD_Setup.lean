-- Prove2me | Definitions.Def_CatalyticRD_Setup
-- name    : CatalyticRD_Setup
-- status  : Definition
-- author  : @shivm
-- created : 2026-10-04T14:11:50.748089+00:00
-- url     : https://prove2.me/theorems/da9716ad-1a2d-4128-8041-6c23cd1b1058
-- title:
--   Catalytic reaction–diffusion system (1.1): domain, data and classical solutions
-- statement:
--   Setup for the catalytic system of Nguyen–Tang, eq. (1.1).
--
--   - `IsSmoothBoundedDomain Ω φ`: $\Omega$ open, bounded, connected, $\Omega=\{\varphi<0\}$ with $\varphi$ $C^\infty$ and $\nabla\varphi\ne0$ on $\{\varphi=0\}$ (so $\nabla\varphi$ is an outward normal on $\partial\Omega$).
--   - `NeumannBC Ω φ u`: on $\partial\Omega$, the derivative of $u$ within $\overline\Omega$ in direction $\nabla\varphi$ is $0$.
--   - `IsAdmissibleDatum`: $C^2$ on $\overline\Omega$, strictly positive there, and Neumann.
--   - `IsC12 Ω u`: continuous on $[0,\infty)\times\overline\Omega$; for $t>0$, $C^2$ in $x$ up to the boundary and differentiable in $t$, with $\partial_tu$, $\nabla_xu$, $D^2_xu$ jointly continuous.
--   - `IsClassicalSolution`: $(a,b,c)$ are `IsC12`, satisfy $a_t-d_1\Delta a=b(c-a)$, $b_t-d_2\Delta b=b(c-a)$, $c_t-d_3\Delta c=-b(c-a)$ in $\Omega$ for $t>0$, are Neumann for $t>0$, and equal the data at $t=0$.
--
--   Solutions are functions of $(t,x)\in\mathbb R\times\mathbb R^n$; only values on $[0,\infty)\times\overline\Omega$ matter.
-- source:
--   T. L. Nguyen and B. Q. Tang, Stability analysis of irreversible chemical reaction-diffusion systems with boundary equilibria, Z. Angew. Math. Phys. 77 (2026), 199, https://doi.org/10.1007/s00033-026-02847-0, Section 1, equation (1.1), assumption (A1), Theorem 2.1 (solution class); AIM open problem 416 (github.com/MColbrook/AIM, problems/416-catalytic-reaction-diffusion-positive-attractor.md)

import Mathlib

open MeasureTheory Set Filter Topology Laplacian
open scoped ContDiff

namespace CatalyticRD

/-- A bounded connected domain `Ω ⊆ ℝⁿ` with `C^∞` boundary, presented by a global
`C^∞` defining function `φ`: `Ω = {φ < 0}` and `∇φ ≠ 0` on `{φ = 0}`. Then
`∂Ω = {φ = 0}` and `∇φ(x)` points along the outward normal at each boundary point. -/
structure IsSmoothBoundedDomain {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) : Prop where
  isOpen : IsOpen Ω
  isBounded : Bornology.IsBounded Ω
  isConnected : IsConnected Ω
  smooth : ContDiff ℝ ∞ φ
  eq_sublevel : Ω = {x | φ x < 0}
  gradient_ne_zero : ∀ x, φ x = 0 → gradient φ x ≠ 0

/-- Homogeneous Neumann condition `∇u · ν = 0` on `∂Ω` for a function `u` on `Ω̄`, where the
normal direction at `x ∈ ∂Ω` is `∇φ(x)` and the spatial derivative is taken within `Ω̄`. -/
def NeumannBC {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) (u : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ∀ x ∈ frontier Ω, fderivWithin ℝ u (closure Ω) x (gradient φ x) = 0

/-- Admissible initial datum: `u₀ ∈ C²(Ω̄)`, strictly positive on `Ω̄`, and satisfying the
Neumann compatibility condition `∇u₀ · ν = 0` on `∂Ω`. -/
structure IsAdmissibleDatum {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) (u₀ : EuclideanSpace ℝ (Fin n) → ℝ) : Prop where
  contDiffOn : ContDiffOn ℝ 2 u₀ (closure Ω)
  pos : ∀ x ∈ closure Ω, 0 < u₀ x
  neumann : NeumannBC Ω φ u₀

/-- `u : [0,∞) × Ω̄ → ℝ` (written `u t x`) lies in `C([0,∞) × Ω̄) ∩ C^{1,2}((0,∞) × Ω̄)`:
continuous up to `t = 0`; for `t > 0` it is `C²` in `x` up to the boundary and `C¹` in `t`, with
`∂ₜu`, `∇ₓu` and `D²ₓu` jointly continuous on `(0,∞) × Ω̄`. -/
structure IsC12 {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (u : ℝ → EuclideanSpace ℝ (Fin n) → ℝ) : Prop where
  continuousOn : ContinuousOn (fun p : ℝ × EuclideanSpace ℝ (Fin n) => u p.1 p.2)
    (Ici 0 ×ˢ closure Ω)
  contDiffOn_space : ∀ t > 0, ContDiffOn ℝ 2 (u t) (closure Ω)
  continuousOn_fderiv : ContinuousOn
    (fun p : ℝ × EuclideanSpace ℝ (Fin n) => fderivWithin ℝ (u p.1) (closure Ω) p.2)
    (Ioi 0 ×ˢ closure Ω)
  continuousOn_hessian : ContinuousOn
    (fun p : ℝ × EuclideanSpace ℝ (Fin n) => iteratedFDerivWithin ℝ 2 (u p.1) (closure Ω) p.2)
    (Ioi 0 ×ˢ closure Ω)
  differentiableAt_time : ∀ x ∈ closure Ω, ∀ t > 0, DifferentiableAt ℝ (fun s => u s x) t
  continuousOn_time_deriv : ContinuousOn
    (fun p : ℝ × EuclideanSpace ℝ (Fin n) => deriv (fun s => u s p.2) p.1)
    (Ioi 0 ×ˢ closure Ω)

/-- `(a, b, c)` is a global classical solution of the irreversible catalytic
reaction–diffusion system (Nguyen–Tang, eq. (1.1)) with homogeneous Neumann boundary conditions:
```
a_t - d₁ Δa =  b (c - a),
b_t - d₂ Δb =  b (c - a),
c_t - d₃ Δc = -b (c - a)      in Ω × (0,∞),
∇a·ν = ∇b·ν = ∇c·ν = 0         on ∂Ω × (0,∞),
(a, b, c)(0) = (a₀, b₀, c₀)    on Ω̄.
``` -/
structure IsClassicalSolution {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) (d₁ d₂ d₃ : ℝ)
    (a₀ b₀ c₀ : EuclideanSpace ℝ (Fin n) → ℝ)
    (a b c : ℝ → EuclideanSpace ℝ (Fin n) → ℝ) : Prop where
  reg_a : IsC12 Ω a
  reg_b : IsC12 Ω b
  reg_c : IsC12 Ω c
  eq_a : ∀ t > 0, ∀ x ∈ Ω,
    deriv (fun s => a s x) t - d₁ * Δ (a t) x = b t x * (c t x - a t x)
  eq_b : ∀ t > 0, ∀ x ∈ Ω,
    deriv (fun s => b s x) t - d₂ * Δ (b t) x = b t x * (c t x - a t x)
  eq_c : ∀ t > 0, ∀ x ∈ Ω,
    deriv (fun s => c s x) t - d₃ * Δ (c t) x = -(b t x * (c t x - a t x))
  bc_a : ∀ t > 0, NeumannBC Ω φ (a t)
  bc_b : ∀ t > 0, NeumannBC Ω φ (b t)
  bc_c : ∀ t > 0, NeumannBC Ω φ (c t)
  init_a : ∀ x ∈ closure Ω, a 0 x = a₀ x
  init_b : ∀ x ∈ closure Ω, b 0 x = b₀ x
  init_c : ∀ x ∈ closure Ω, c 0 x = c₀ x

end CatalyticRD


