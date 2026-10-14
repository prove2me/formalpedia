-- Prove2me | Definitions.Def_RelPartMech_coordinates
-- name    : RelPartMech_coordinates
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-12T23:05:08.79498+00:00
-- url     : https://prove2.me/theorems/ac02b0ba-84c5-4cee-8a28-b56362443b03
-- title:
--   Relativity and particle mechanics: coordinates, metric, Christoffel symbols, Poisson bracket
-- statement:
--   Shared setting for the note *Relativity and Particle Mechanics*. Space-time is one coordinate chart $\mathbb R^n$ with points $x=(x^\alpha)$, and phase space is $\mathbb R^n\times\mathbb R^n$ with points $(x,p)$. The file defines:
--
--   1. the partial derivative $\partial_\alpha f$ of a scalar field and its raised form $\partial^\alpha f = g^{\alpha\beta}\partial_\beta f$;
--   2. metric fields $g_{\alpha\beta}(x)$, the predicate that $g$ is smooth, symmetric and nondegenerate at every point (any signature), and the inverse metric $g^{\alpha\beta}$;
--   3. the Christoffel symbols $\Gamma_{\alpha\beta\gamma}=\tfrac12(\partial_\gamma g_{\alpha\beta}+\partial_\beta g_{\alpha\gamma}-\partial_\alpha g_{\beta\gamma})$ and $\Gamma^\alpha_{\beta\gamma}=g^{\alpha\delta}\Gamma_{\delta\beta\gamma}$;
--   4. the symbol $G_{\alpha\beta\gamma}=\partial_\alpha g_{\beta\gamma}-\partial_\beta g_{\alpha\gamma}$ and $G^{\alpha\beta\gamma}=g^{\alpha\delta}g^{\beta\epsilon}g^{\gamma\zeta}G_{\delta\epsilon\zeta}$;
--   5. covector fields $A_\alpha$, raising $A^\alpha=g^{\alpha\beta}A_\beta$, the force tensor $F_{\alpha\beta}=\partial_\alpha A_\beta-\partial_\beta A_\alpha$ and $F^{\alpha\beta}=g^{\alpha\gamma}g^{\beta\delta}F_{\gamma\delta}$;
--   6. the Levi-Civita covariant derivatives $\nabla_\alpha A_\beta=\partial_\alpha A_\beta-\Gamma^\gamma_{\beta\alpha}A_\gamma$ and $\nabla_\alpha V^\beta=\partial_\alpha V^\beta+\Gamma^\beta_{\gamma\alpha}V^\gamma$;
--   7. on phase space: the canonical Poisson bracket
--   $$\{f,h\}=\frac{\partial f}{\partial q^\mu}\frac{\partial h}{\partial p_\mu}-\frac{\partial f}{\partial p_\mu}\frac{\partial h}{\partial q^\mu},$$
--   the position functions $x^\alpha$, the kinetic momentum $\Pi_\alpha=p_\alpha-eA_\alpha(x)$ for charge $e$, the Hamiltonian $H=\frac1{2m}\Pi_\alpha g^{\alpha\beta}\Pi_\beta$, and the velocity $u^\alpha=\frac1m g^{\alpha\beta}\Pi_\beta$.
--
--   These are the objects of eqs. (2)–(16) of the note; every theorem of the mission is stated in terms of them.
--
--   **Formalization Note** Coordinates are `Fin n → ℝ`; partial derivatives are Fréchet derivatives applied to the coordinate basis vectors; all index sums are written explicitly. The charge, written $q$ in the note, is called $e$.
-- source:
--   G. Carcassi, C. A. Aidala, "Relativity and Particle Mechanics" (note, uploaded PDF), Sections 1–5 (eqs. (2), (4), (8), (10), (11), (15))

import Mathlib

/-!
# Relativity and particle mechanics — coordinate definitions

Shared definitions for the mission formalizing the note
*Relativity and Particle Mechanics* (G. Carcassi, C. A. Aidala).

Everything is written in a single global chart: space-time (configuration space)
is `ℝⁿ`, modelled as `Fin n → ℝ`, and phase space is `ℝⁿ × ℝⁿ` with points
`(x, p)`, written in curried form. Indices `α β γ … : Fin n` are space-time indices,
and all sums over repeated indices are written explicitly.
-/

open scoped ContDiff

namespace RelPartMech

/-- Coordinates `x = (x^α)` on space-time, a point of `ℝⁿ`. -/
abbrev Coord (n : ℕ) := Fin n → ℝ

/-- The partial derivative `∂_α f (x) = ∂f/∂x^α (x)` of a scalar field. -/
noncomputable def pd {n : ℕ} (α : Fin n) (f : Coord n → ℝ) (x : Coord n) : ℝ :=
  fderiv ℝ f x (Pi.single α 1)

/-- A field of matrices `x ↦ g_{αβ}(x)` (candidate metric tensor in coordinates). -/
abbrev MetricField (n : ℕ) := Coord n → Matrix (Fin n) (Fin n) ℝ

/-- A covector field `x ↦ A_α(x)` (e.g. the vector potential). -/
abbrev CovectorField (n : ℕ) := Fin n → Coord n → ℝ

/-- `g` is a (pseudo-Riemannian) metric in coordinates: each component `g_{αβ}` is
smooth, `g_{αβ} = g_{βα}`, and `g(x)` is nondegenerate at every point. No signature
is imposed. -/
def IsSmoothMetric {n : ℕ} (g : MetricField n) : Prop :=
  (∀ α β : Fin n, ContDiff ℝ ∞ (fun x => g x α β)) ∧
  (∀ x α β, g x α β = g x β α) ∧
  (∀ x, IsUnit (g x).det)

/-- The inverse metric `g^{αβ}(x)`, the matrix inverse of `g_{αβ}(x)`. -/
noncomputable def ginv {n : ℕ} (g : MetricField n) (x : Coord n) :
    Matrix (Fin n) (Fin n) ℝ :=
  (g x)⁻¹

/-- Christoffel symbols of the first kind (eq. (2)):
`Γ_{αβγ} = ½ (∂_γ g_{αβ} + ∂_β g_{αγ} − ∂_α g_{βγ})`. -/
noncomputable def christoffelFirst {n : ℕ} (g : MetricField n) (α β γ : Fin n)
    (x : Coord n) : ℝ :=
  (1 / 2) * (pd γ (fun y => g y α β) x + pd β (fun y => g y α γ) x
    - pd α (fun y => g y β γ) x)

/-- Christoffel symbols of the second kind (eq. (2)): `Γ^α_{βγ} = g^{αδ} Γ_{δβγ}`. -/
noncomputable def christoffel {n : ℕ} (g : MetricField n) (α β γ : Fin n)
    (x : Coord n) : ℝ :=
  ∑ δ, ginv g x α δ * christoffelFirst g δ β γ x

/-- The symbol `G_{αβγ} = ∂_α g_{βγ} − ∂_β g_{αγ}` (eq. (10)). -/
noncomputable def gSymbol {n : ℕ} (g : MetricField n) (α β γ : Fin n) (x : Coord n) : ℝ :=
  pd α (fun y => g y β γ) x - pd β (fun y => g y α γ) x

/-- All indices raised: `G^{αβγ} = g^{αδ} g^{βε} g^{γζ} G_{δεζ}` (eq. (11)). -/
noncomputable def gSymbolUp {n : ℕ} (g : MetricField n) (α β γ : Fin n)
    (x : Coord n) : ℝ :=
  ∑ δ, ∑ ε, ∑ ζ, ginv g x α δ * ginv g x β ε * ginv g x γ ζ * gSymbol g δ ε ζ x

/-- The raised partial derivative `∂^α f = g^{αβ} ∂_β f`. -/
noncomputable def pdUp {n : ℕ} (g : MetricField n) (α : Fin n) (f : Coord n → ℝ)
    (x : Coord n) : ℝ :=
  ∑ β, ginv g x α β * pd β f x

/-- Raising the index of a covector field: `A^α = g^{αβ} A_β`. -/
noncomputable def raise {n : ℕ} (g : MetricField n) (A : CovectorField n) :
    CovectorField n :=
  fun α x => ∑ β, ginv g x α β * A β x

/-- The force (field-strength) tensor `F_{αβ} = ∂_α A_β − ∂_β A_α` (eqs. (6), (10)). -/
noncomputable def forceTensor {n : ℕ} (A : CovectorField n) (α β : Fin n)
    (x : Coord n) : ℝ :=
  pd α (A β) x - pd β (A α) x

/-- The force tensor with both indices raised: `F^{αβ} = g^{αγ} g^{βδ} F_{γδ}` (eq. (11)). -/
noncomputable def forceTensorUp {n : ℕ} (g : MetricField n) (A : CovectorField n)
    (α β : Fin n) (x : Coord n) : ℝ :=
  ∑ γ, ∑ δ, ginv g x α γ * ginv g x β δ * forceTensor A γ δ x

/-- Levi-Civita covariant derivative of a covector field (eq. (15)):
`∇_α A_β = ∂_α A_β − Γ^γ_{βα} A_γ`. -/
noncomputable def covDerivCov {n : ℕ} (g : MetricField n) (A : CovectorField n)
    (α β : Fin n) (x : Coord n) : ℝ :=
  pd α (A β) x - ∑ γ, christoffel g γ β α x * A γ x

/-- Levi-Civita covariant derivative of a vector field `V^β` (eq. (15)):
`∇_α V^β = ∂_α V^β + Γ^β_{γα} V^γ`. -/
noncomputable def covDerivContra {n : ℕ} (g : MetricField n) (V : CovectorField n)
    (α β : Fin n) (x : Coord n) : ℝ :=
  pd α (V β) x + ∑ γ, christoffel g β γ α x * V γ x

/-! ### Phase space -/

/-- A function `f(x, p)` on phase space `ℝⁿ × ℝⁿ` (position `x^α`, conjugate momentum
`p_α`). -/
abbrev PhaseFn (n : ℕ) := Coord n → Coord n → ℝ

/-- `∂f/∂q^α` on phase space. -/
noncomputable def pdq {n : ℕ} (α : Fin n) (f : PhaseFn n) (x p : Coord n) : ℝ :=
  fderiv ℝ (fun y => f y p) x (Pi.single α 1)

/-- `∂f/∂p_α` on phase space. -/
noncomputable def pdp {n : ℕ} (α : Fin n) (f : PhaseFn n) (x p : Coord n) : ℝ :=
  fderiv ℝ (fun r => f x r) p (Pi.single α 1)

/-- The canonical Poisson bracket `{f, h} = ∂f/∂q^μ ∂h/∂p_μ − ∂f/∂p_μ ∂h/∂q^μ`,
i.e. the one of the symplectic form `ω = dq^α ∧ dp_α` (eq. (3)), so `{q^α, p_β} = δ^α_β`. -/
noncomputable def poisson {n : ℕ} (f h : PhaseFn n) : PhaseFn n :=
  fun x p => ∑ μ, (pdq μ f x p * pdp μ h x p - pdp μ f x p * pdq μ h x p)

/-- The position coordinate `x^α = q^α` as a function on phase space. -/
def posFn {n : ℕ} (α : Fin n) : PhaseFn n :=
  fun x _ => x α

/-- Kinetic momentum `Π_α = p_α − e A_α(x)` (eq. (4)), for a particle of charge `e`
in the vector potential `A`. -/
def kineticMomentum {n : ℕ} (A : CovectorField n) (e : ℝ) (α : Fin n) : PhaseFn n :=
  fun x p => p α - e * A α x

/-- The Hamiltonian `H = (1/2m) Π_α g^{αβ} Π_β` (eq. (4)). -/
noncomputable def hamiltonian {n : ℕ} (g : MetricField n) (A : CovectorField n)
    (e m : ℝ) : PhaseFn n :=
  fun x p => (1 / (2 * m)) * ∑ β, ∑ γ,
    kineticMomentum A e β x p * ginv g x β γ * kineticMomentum A e γ x p

/-- The velocity `u^α = (1/m) g^{αβ} Π_β`, i.e. the solution of `Π_α = m g_{αβ} u^β`
(eqs. (4), (10)), as a function on phase space. -/
noncomputable def velocity {n : ℕ} (g : MetricField n) (A : CovectorField n)
    (e m : ℝ) (α : Fin n) : PhaseFn n :=
  fun x p => (1 / m) * ∑ β, ginv g x α β * kineticMomentum A e β x p

end RelPartMech


