-- Prove2me | Definitions.Def_FlatlyFoliatedRelativity_basic
-- name    : FlatlyFoliatedRelativity_basic
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-12T20:39:10.600486+00:00
-- url     : https://prove2.me/theorems/57122ba7-2093-4e8b-9298-347ee013fd6c
-- title:
--   Flatly Foliated Relativity: FFR equations, elliptic form, spherical symmetry
-- statement:
--   Basic objects of Flatly Foliated Relativity on a flat slice $\mathbb R^3$ (all fields are functions of $x\in\mathbb R^3$; one-forms are identified with vector fields via the flat metric; the paper's $\omega$ is written `w`).
--
--   1. Coordinate derivatives $\partial_i u$, the Laplacian $\Delta u=\sum_i u_{ii}$, the divergence $\nabla\cdot\omega=\sum_i\omega_{i,i}$ (with $\omega_{i,j}=\partial_j\omega_i$), the gradient $df$, and $\|f_{ij}\|^2=\sum_{i,j}f_{ij}^2$.
--   2. **The FFR equations** (34)–(35) for $(\omega,\eta)$ with data $(\Lambda,\mu,J)$, required at every point:
--   $$2\Lambda+16\pi\mu=\frac1{\eta^2}\Big[(\nabla\cdot\omega)^2-\tfrac14\textstyle\sum_{i,j}(\omega_{i,j}+\omega_{j,i})^2\Big],$$
--   $$16\pi J_i=\frac1\eta\big(\Delta\omega_i-\partial_i(\nabla\cdot\omega)\big)+\frac2{\eta^2}(\nabla\cdot\omega)\eta_i-\frac1{\eta^2}\textstyle\sum_j(\omega_{i,j}+\omega_{j,i})\eta_j.$$
--   3. **The elliptic form** (39)–(41) for $(f,\zeta,\eta)$, with $Q_{ij}=f_{ij}+\tfrac12(\zeta_{i,j}+\zeta_{j,i})$:
--   $$(\Delta f)^2-\|Q\|^2=(16\pi\mu+2\Lambda)\eta^2,\quad \Delta\zeta_i=16\pi J_i\eta-\tfrac2\eta\textstyle\sum_j(\Delta f\,\delta_{ij}-Q_{ij})\eta_j,\quad \sum_{i,j}(\Delta f\,\delta_{ij}-Q_{ij})\eta_{ij}=8\pi\nabla\cdot(J\eta^2),$$
--   together with $\lim_{|x|\to\infty}\nabla\cdot\zeta=0$.
--   4. **Spherical symmetry**: a scalar $u$ is spherically symmetric if $u(Rx)=u(x)$ for every linear isometry $R$ of $\mathbb R^3$; $(\omega,\eta)$ is **spherically symmetric at infinity** if for some $r_0>0$, $\eta(Rx)=\eta(x)$ and $\omega(Rx)=R\,\omega(x)$ for all such $R$ and all $|x|\ge r_0$.
--   5. **Spherical symmetrization** (75): $\bar\psi(x)=\frac1{|S^2|}\int_{S^2}\psi(|x|u)\,d\sigma(u)$.
--   6. **Approximate spherical symmetry at $\infty$** (Theorem 5): with $g=f-\bar f$, $g$ is bounded and for every $\varepsilon>0$ there is $R$ with $|x|^2\,\|\nabla^2 g(x)\|\,\|\nabla g(x)\|\le\varepsilon$ whenever $|x|\ge R$.
--
--   These definitions are shared by every statement of the mission.
--
--   **Formalization Note** Space is `EuclideanSpace ℝ (Fin 3)`; partial derivatives are `fderiv` evaluated on standard basis vectors, so all theorems assume smoothness. Isometry invariance is equivalent to rotation invariance because $SO(3)$ is transitive on spheres. Norms of $\nabla g$ and $\nabla^2 g$ are operator norms (any choice of norm gives the same condition since the limit is $0$).
-- source:
--   Bray, Hamm, Hirsch, Wheeler, Zhang, Flatly Foliated Relativity, arXiv:1911.00967v2, https://arxiv.org/abs/1911.00967, pp. 6–9 (eqs. (1), (34), (35), (39)–(41)), p. 15 (spherical symmetry at infinity), pp. 16–17 (Theorem 5 hypothesis, eq. (75))

import Mathlib

/-!
# Flatly Foliated Relativity — basic definitions

Bray, Hamm, Hirsch, Wheeler, Zhang, *Flatly Foliated Relativity*, arXiv:1911.00967v2.

Everything here lives on a single flat slice `ℝ³_t` of the foliation (the FFR equations
contain no time derivatives), modelled as `EuclideanSpace ℝ (Fin 3)`.  One-forms such as
`ω`, `ζ`, `J` are identified with vector fields via the flat metric `δ_{ℝ³}`.
The paper's `ω` is written `w` in Lean (the glyph `ω` is reserved notation in Mathlib).
-/

open scoped ContDiff

namespace FlatlyFoliated

/-- Euclidean space `ℝ³`, the flat slice `ℝ³_t`. -/
abbrev R3 : Type := EuclideanSpace ℝ (Fin 3)

/-- Coordinate partial derivative `∂ᵢ u` of a real function on `ℝ³`. -/
noncomputable def pd (i : Fin 3) (u : R3 → ℝ) : R3 → ℝ :=
  fun x => fderiv ℝ u x (EuclideanSpace.single i 1)

/-- The `i`-th component `wᵢ` of a vector field (one-form) on `ℝ³`. -/
def comp (w : R3 → R3) (i : Fin 3) : R3 → ℝ := fun x => w x i

/-- Flat Laplacian `Δu = Σᵢ uᵢᵢ`. -/
noncomputable def lap (u : R3 → ℝ) : R3 → ℝ :=
  fun x => ∑ i, pd i (pd i u) x

/-- Divergence `∇ · w = Σᵢ wᵢ,ᵢ`. -/
noncomputable def divg (w : R3 → R3) : R3 → ℝ :=
  fun x => ∑ i, pd i (comp w i) x

/-- Gradient `df` (as a vector field), with components `fᵢ`. -/
noncomputable def grad (u : R3 → ℝ) : R3 → R3 :=
  fun x => ∑ i, pd i u x • EuclideanSpace.single i (1 : ℝ)

/-- Squared Frobenius norm of the Hessian, `‖fᵢⱼ‖² = Σᵢⱼ fᵢⱼ²`. -/
noncomputable def hessNormSq (u : R3 → ℝ) : R3 → ℝ :=
  fun x => ∑ i, ∑ j, (pd j (pd i u) x) ^ 2

/-- Paper eq. (34) at a point `x`:
`2Λ + 16πμ = η⁻² [ (∇·w)² − ¼ ‖wᵢ,ⱼ + wⱼ,ᵢ‖² ]`. -/
def Eq34 (Λ : ℝ) (μ : R3 → ℝ) (w : R3 → R3) (η : R3 → ℝ) (x : R3) : Prop :=
  2 * Λ + 16 * Real.pi * μ x =
    (1 / η x ^ 2) * (divg w x ^ 2 -
      (1 / 4) * ∑ i, ∑ j, (pd j (comp w i) x + pd i (comp w j) x) ^ 2)

/-- Paper eq. (35) at a point `x`, for the index `i`:
`16πJᵢ = η⁻¹(Δwᵢ − d(∇·w)ᵢ) + 2η⁻²(∇·w)ηᵢ − η⁻² Σⱼ (wᵢ,ⱼ + wⱼ,ᵢ) ηⱼ`. -/
def Eq35 (J : R3 → R3) (w : R3 → R3) (η : R3 → ℝ) (x : R3) (i : Fin 3) : Prop :=
  16 * Real.pi * J x i =
    (1 / η x) * (lap (comp w i) x - pd i (divg w) x)
      + (2 / η x ^ 2) * divg w x * pd i η x
      - (1 / η x ^ 2) * ∑ j, (pd j (comp w i) x + pd i (comp w j) x) * pd j η x

/-- **The Flatly Foliated Relativity equations** (34)–(35) on `ℝ³`, with cosmological
constant `Λ`, energy density `μ` and momentum density `J`, for the unknowns `(w, η)`. -/
def FFREquations (Λ : ℝ) (μ : R3 → ℝ) (J : R3 → R3) (w : R3 → R3) (η : R3 → ℝ) : Prop :=
  ∀ x, Eq34 Λ μ w η x ∧ ∀ i, Eq35 J w η x i

/-- `Qᵢⱼ = fᵢⱼ + ½(ζᵢ,ⱼ + ζⱼ,ᵢ)`. -/
noncomputable def Qmat (f : R3 → ℝ) (ζ : R3 → R3) (i j : Fin 3) : R3 → ℝ :=
  fun x => pd j (pd i f) x + (1 / 2) * (pd j (comp ζ i) x + pd i (comp ζ j) x)

/-- The coefficient matrix `Δf · δᵢⱼ − Qᵢⱼ` appearing in (40), (41). -/
noncomputable def ellCoeff (f : R3 → ℝ) (ζ : R3 → R3) (i j : Fin 3) : R3 → ℝ :=
  fun x => (if i = j then lap f x else 0) - Qmat f ζ i j x

/-- **The FFR equations in elliptic form** (39)–(41) on `ℝ³` for the unknowns
`(f, ζ, η)`, together with the requirement `lim_{x→∞} ∇·ζ = 0`:

* (39) `(Δf)² − ‖Qᵢⱼ‖² = (16πμ + 2Λ) η²`,
* (40) `Δζᵢ = 16π Jᵢ η − (2/η) Σⱼ (Δf δᵢⱼ − Qᵢⱼ) ηⱼ`,
* (41) `Σᵢⱼ (Δf δᵢⱼ − Qᵢⱼ) ηᵢⱼ = 8π ∇·(J η²)`. -/
def EllipticSystem (Λ : ℝ) (μ : R3 → ℝ) (J : R3 → R3) (f : R3 → ℝ) (ζ : R3 → R3)
    (η : R3 → ℝ) : Prop :=
  (∀ x, lap f x ^ 2 - ∑ i, ∑ j, Qmat f ζ i j x ^ 2 = (16 * Real.pi * μ x + 2 * Λ) * η x ^ 2) ∧
  (∀ x i, lap (comp ζ i) x =
      16 * Real.pi * J x i * η x - (2 / η x) * ∑ j, ellCoeff f ζ i j x * pd j η x) ∧
  (∀ x, ∑ i, ∑ j, ellCoeff f ζ i j x * pd j (pd i η) x =
      8 * Real.pi * divg (fun y => η y ^ 2 • J y) x) ∧
  Filter.Tendsto (divg ζ) (Bornology.cobounded R3) (nhds 0)

/-- A scalar function on `ℝ³` is spherically symmetric: invariant under every linear
isometry of `ℝ³` (equivalently, under every rotation, since `SO(3)` acts transitively on
spheres). -/
def IsSphSymm (u : R3 → ℝ) : Prop :=
  ∀ (R : R3 ≃ₗᵢ[ℝ] R3) (x : R3), u (R x) = u x

/-- The pair `(w, η)` is *spherically symmetric at infinity* (paper §5): there is
`r₀ > 0` such that `(w, η)` is spherically symmetric on `{r ≥ r₀}`, i.e. `η` is invariant and
the one-form `w` is equivariant under every linear isometry `R` of `ℝ³` at points with
`‖x‖ ≥ r₀`. -/
def SphSymmAtInfty (w : R3 → R3) (η : R3 → ℝ) : Prop :=
  ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ (R : R3 ≃ₗᵢ[ℝ] R3) (x : R3), r₀ ≤ ‖x‖ →
    η (R x) = η x ∧ w (R x) = R (w x)

/-- Spherical symmetrization (paper eq. (75)):
`ψ̄(x) = (1/|S²|) ∫_{S²} ψ(|x| u) dσ(u)`, the average of `ψ` over the sphere of radius `|x|`. -/
noncomputable def sphSymmetrization (ψ : R3 → ℝ) : R3 → ℝ :=
  fun x => ⨍ u, ψ (‖x‖ • u.1) ∂((MeasureTheory.volume : MeasureTheory.Measure R3).toSphere)

/-- `f` is *approximately spherically symmetric at ∞* (paper, Theorem 5): with
`g = f − f̄`, `g` is bounded and `limsup_{r→∞} sup_{x ∈ S_r} r² ‖∇²g(x)‖ ‖∇g(x)‖ = 0`. -/
def ApproxSphSymmAtInfty (f : R3 → ℝ) : Prop :=
  (∃ C : ℝ, ∀ x, |f x - sphSymmetrization f x| ≤ C) ∧
  ∀ ε > 0, ∃ R : ℝ, ∀ x : R3, R ≤ ‖x‖ →
    ‖x‖ ^ 2 * (‖fderiv ℝ (fderiv ℝ (fun y => f y - sphSymmetrization f y)) x‖ *
      ‖fderiv ℝ (fun y => f y - sphSymmetrization f y) x‖) ≤ ε

end FlatlyFoliated


