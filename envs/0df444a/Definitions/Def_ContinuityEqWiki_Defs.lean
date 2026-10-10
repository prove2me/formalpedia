-- Prove2me | Definitions.Def_ContinuityEqWiki_Defs
-- name    : ContinuityEqWiki_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-09T21:26:26.972983+00:00
-- url     : https://prove2.me/theorems/70ccadde-7bf9-4704-8866-d35edfc510ad
-- title:
--   Continuity equation: vector calculus on $\mathbb R^3$, box fluxes, and physical fields
-- statement:
--   This definition file fixes the vocabulary shared by every statement of the mission. Points of space are $x=(x_0,x_1,x_2)\in\mathbb R^3$ and points of spacetime are $X=(x^0,x^1,x^2,x^3)\in\mathbb R^4$.
--
--   1. **Partial derivative.** For $f:\mathbb R^n\to E$ (with $E=\mathbb R$ or $\mathbb C$), $\partial_i f(x)$ is the Fréchet derivative of $f$ at $x$ applied to the $i$-th standard basis vector $e_i$.
--   2. **Gradient, divergence, Laplacian, curl.** $\nabla f=(\partial_0 f,\dots,\partial_{n-1}f)$, $\nabla\cdot F=\sum_i \partial_i F_i$, $\nabla^2 f=\sum_i\partial_i\partial_i f$, and for $F:\mathbb R^3\to\mathbb R^3$
--   $$\nabla\times F=(\partial_1F_2-\partial_2F_1,\ \partial_2F_0-\partial_0F_2,\ \partial_0F_1-\partial_1F_0).$$
--   3. **Time derivative.** For a time-dependent field $f(t,x)$, $\partial_t f(t,x)$ is the derivative of $s\mapsto f(s,x)$ at $t$.
--   4. **Amount, generation and flux on a box.** For a box $V=[a,b]=\prod_i[a_i,b_i]$: $q(t)=\int_V\rho(t,x)\,dx$, $\Sigma(t)=\int_V\sigma(t,x)\,dx$, and the outward flux of $F$ through $\partial V$ is
--   $$\oint_{\partial V}F\cdot d\mathbf S=\sum_{i=0}^{2}\Big(\int_{\text{face }x_i=b_i}F_i-\int_{\text{face }x_i=a_i}F_i\Big),$$
--   each face integral being taken over the two remaining coordinates.
--   5. **Integral form** (on boxes): for every box with $a_i<b_i$ and every $t$, $\dfrac{dq}{dt}+\oint_{\partial V}\mathbf j\cdot d\mathbf S=\Sigma$. **Differential form:** $\partial_t\rho+\nabla\cdot\mathbf j=\sigma$ everywhere.
--   6. **Quantum mechanics.** $\rho=|\Psi|^2$; $\mathbf j=\frac{\hbar}{2mi}\big[\Psi^*\nabla\Psi-\Psi\nabla\Psi^*\big]$; the Schrödinger equation $-\frac{\hbar^2}{2m}\nabla^2\Psi+U\Psi=i\hbar\,\partial_t\Psi$ with real potential $U(t,x)$.
--   7. **Special relativity.** The four-current $J=(c\rho,j_x,j_y,j_z)$ viewed as a field of $X=(x^0,x)$ with $t=x^0/c$, and the four-divergence $\partial_\mu J^\mu=\sum_{\mu=0}^3\partial J^\mu/\partial x^\mu$.
--
--   These are the objects of the sections *General equation*, *Electromagnetism*, *Fluid dynamics*, *Computer vision*, *Quantum mechanics*, *Semiconductor* and *Relativistic version* of the source.
--
--   **Formalization Note** The flux integral over a general closed surface is replaced by the flux through the boundary of an axis-parallel box, the setting of Mathlib's divergence theorem. The probability current is stored as the real part of the complex expression $\frac{\hbar}{2mi}[\dots]$, which is real.
-- source:
--   Wikipedia, "Continuity equation", revision oldid=1378634825, https://en.wikipedia.org/w/index.php?title=Continuity_equation&oldid=1378634825

import Mathlib

namespace ContinuityEqWiki

open MeasureTheory

/-- Physical space `ℝ³`, with points written in Cartesian coordinates `x = (x₀, x₁, x₂)`. -/
abbrev Space := Fin 3 → ℝ

/-- Spacetime `ℝ⁴`, with coordinates `X = (x⁰, x¹, x², x³)`, where `x⁰ = c t`. -/
abbrev Spacetime := Fin 4 → ℝ

/-- The partial derivative `∂f/∂xᵢ (x)` of a function `f : ℝⁿ → E` in the `i`-th coordinate
direction, i.e. the Fréchet derivative of `f` at `x` applied to the `i`-th standard basis vector. -/
noncomputable def partialDeriv {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Fin n) (f : (Fin n → ℝ) → E) (x : Fin n → ℝ) : E :=
  fderiv ℝ f x (Pi.single i 1)

/-- The gradient `∇f (x) = (∂f/∂x₀, …, ∂f/∂xₙ₋₁)` of a scalar function `f : ℝⁿ → ℝ`. -/
noncomputable def grad {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => partialDeriv i f x

/-- The divergence `∇ · F (x) = ∑ᵢ ∂Fᵢ/∂xᵢ (x)` of a vector field `F : ℝⁿ → ℝⁿ`. -/
noncomputable def div {n : ℕ} (F : (Fin n → ℝ) → Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, partialDeriv i (fun y => F y i) x

/-- The Laplacian `∇²f (x) = ∑ᵢ ∂²f/∂xᵢ² (x)` of a function `f : ℝⁿ → E`
(used with `E = ℝ` or `E = ℂ`). -/
noncomputable def laplacian {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (Fin n → ℝ) → E) (x : Fin n → ℝ) : E :=
  ∑ i, partialDeriv i (fun y => partialDeriv i f y) x

/-- The curl `∇ × F` of a vector field `F : ℝ³ → ℝ³`:
`(∂₁F₂ - ∂₂F₁, ∂₂F₀ - ∂₀F₂, ∂₀F₁ - ∂₁F₀)`. -/
noncomputable def curl (F : Space → Space) (x : Space) : Space :=
  ![partialDeriv 1 (fun y => F y 2) x - partialDeriv 2 (fun y => F y 1) x,
    partialDeriv 2 (fun y => F y 0) x - partialDeriv 0 (fun y => F y 2) x,
    partialDeriv 0 (fun y => F y 1) x - partialDeriv 1 (fun y => F y 0) x]

/-- The partial time derivative `∂f/∂t (t, x)` of a time-dependent field `f : ℝ × X → E`
(written in curried form `f t x`). -/
noncomputable def timeDeriv {X E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → X → E) (t : ℝ) (x : X) : E :=
  deriv (fun s => f s x) t

/-- The total amount `q(t) = ∫_V ρ(t, x) dx` of a quantity with volume density `ρ` inside the
closed box `V = [a, b] = [a₀, b₀] × [a₁, b₁] × [a₂, b₂]`. -/
noncomputable def amountInBox (ρ : ℝ → Space → ℝ) (a b : Space) (t : ℝ) : ℝ :=
  ∫ x in Set.Icc a b, ρ t x

/-- The total net generation rate `Σ(t) = ∫_V σ(t, x) dx` inside the box `V = [a, b]`. -/
noncomputable def generationInBox (σ : ℝ → Space → ℝ) (a b : Space) (t : ℝ) : ℝ :=
  ∫ x in Set.Icc a b, σ t x

/-- The outward flux `∮_S F · dS` of a vector field `F : ℝ³ → ℝ³` through the boundary `S` of
the box `[a, b]`: for each coordinate `i`, the integral of `Fᵢ` over the face `xᵢ = bᵢ` minus the
integral of `Fᵢ` over the face `xᵢ = aᵢ`, each face being parametrised by the two remaining
coordinates (inserted around the fixed `i`-th coordinate). -/
noncomputable def boxFlux (F : Space → Space) (a b : Space) : ℝ :=
  ∑ i : Fin 3,
    ((∫ y in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove), F (i.insertNth (b i) y) i) -
      ∫ y in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove), F (i.insertNth (a i) y) i)

/-- **Integral form of the continuity equation** (on boxes): for every non-degenerate closed box
`V = [a, b]` (with `aᵢ < bᵢ` for all `i`) and every time `t`,
`dq/dt + ∮_{∂V} j · dS = Σ`, where `q(t) = ∫_V ρ(t, ·)` and `Σ(t) = ∫_V σ(t, ·)`. -/
def IntegralForm (ρ : ℝ → Space → ℝ) (j : ℝ → Space → Space) (σ : ℝ → Space → ℝ) : Prop :=
  ∀ a b : Space, (∀ i, a i < b i) → ∀ t : ℝ,
    deriv (amountInBox ρ a b) t + boxFlux (j t) a b = generationInBox σ a b t

/-- **Differential form of the continuity equation**: `∂ρ/∂t + ∇ · j = σ` at every time `t`
and every point `x`. -/
def DifferentialForm (ρ : ℝ → Space → ℝ) (j : ℝ → Space → Space) (σ : ℝ → Space → ℝ) : Prop :=
  ∀ (t : ℝ) (x : Space), timeDeriv ρ t x + div (j t) x = σ t x

/-- The **probability density** `ρ(r, t) = Ψ*(r, t) Ψ(r, t) = |Ψ(r, t)|²` of a wavefunction. -/
noncomputable def probDensity (Ψ : ℝ → Space → ℂ) (t : ℝ) (x : Space) : ℝ :=
  Complex.normSq (Ψ t x)

/-- The **probability current** `j(r, t) = (ħ / (2 m i)) [Ψ* (∇Ψ) - Ψ (∇Ψ*)]`.  The bracketed
complex expression is purely imaginary times `2i`, so the right-hand side is real; we record it
as the real part of the complex expression, component by component. -/
noncomputable def probCurrent (hbar m : ℝ) (Ψ : ℝ → Space → ℂ) (t : ℝ) (x : Space) : Space :=
  fun k => ((hbar : ℂ) / (2 * (m : ℂ) * Complex.I) *
    ((starRingEnd ℂ) (Ψ t x) * partialDeriv k (Ψ t) x -
      Ψ t x * partialDeriv k (fun y => (starRingEnd ℂ) (Ψ t y)) x)).re

/-- The **time-dependent Schrödinger equation** for a single particle of mass `m` in a real
potential `U`: `-(ħ²/2m) ∇²Ψ + U Ψ = i ħ ∂Ψ/∂t` at every time and point. -/
def SchrodingerEq (hbar m : ℝ) (U : ℝ → Space → ℝ) (Ψ : ℝ → Space → ℂ) : Prop :=
  ∀ (t : ℝ) (x : Space),
    -((hbar : ℂ) ^ 2 / (2 * (m : ℂ))) * laplacian (Ψ t) x + (U t x : ℂ) * Ψ t x =
      Complex.I * (hbar : ℂ) * timeDeriv Ψ t x

/-- The spacetime point `(c t, x)` with time coordinate `x⁰ = c t` and spatial part `x`. -/
def spacetimePoint (c t : ℝ) (x : Space) : Spacetime :=
  Fin.cons (c * t) x

/-- The **four-current** `J = (c ρ, j_x, j_y, j_z)` as a field on spacetime: at the spacetime
point `X = (x⁰, x)` it is evaluated at time `t = x⁰ / c` and spatial position `x`. -/
noncomputable def fourCurrent (c : ℝ) (ρ : ℝ → Space → ℝ) (j : ℝ → Space → Space)
    (X : Spacetime) : Fin 4 → ℝ :=
  Fin.cons (c * ρ (X 0 / c) (Fin.tail X)) (j (X 0 / c) (Fin.tail X))

/-- The **four-divergence** `∂_μ J^μ = ∑_{μ=0}^{3} ∂J^μ/∂x^μ` of a field `J : ℝ⁴ → ℝ⁴`. -/
noncomputable def fourDiv (J : Spacetime → Fin 4 → ℝ) (X : Spacetime) : ℝ :=
  ∑ μ : Fin 4, partialDeriv μ (fun Y => J Y μ) X

end ContinuityEqWiki


