-- Prove2me | Definitions.Def_GaussMixHH_GridFit
-- name    : GaussMixHH_GridFit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:33:25.538334+00:00
-- url     : https://prove2.me/theorems/b18b4cb6-9f7c-4140-8e39-87914659b8dd
-- title:
--   The kernel $K_u$, grid distributions, $Q_{uv}$, $\hat Q_{uv}$ and the fitting objective $f$
-- statement:
--   For a squared radius $u\ge0$, $K_u(\theta)=(1-2i\theta)^{-n/2}\exp\big(\tfrac{i\theta u}{1-2i\theta}\big)$. A **grid** $U$ is a finite set of squared radii; a **grid distribution** is a probability vector $x=(x_u)_{u\in U}$, with
--
--   $$\Phi_x(\theta)=\sum_{u\in U}x_uK_u(\theta),\qquad \operatorname{near-mass}_R(x)=\sum_{u\le R^2/4}x_u .$$
--
--   For an interval $I=[\theta_0,q]$, $\mathbb E_{\theta\sim\mathrm{Unif}(I)}F=(q-\theta_0)^{-1}\int_{\theta_0}^{q}F$, and
--
--   $$Q_{uv}=\mathbb E_{\theta\sim\mathrm{Unif}(I)}\big[\operatorname{Re}(K_u(\theta)\overline{K_v(\theta)})\big],\qquad \hat Q_{uv}=\frac1H\sum_{t=1}^{H}\operatorname{Re}(K_u(\theta_t)\overline{K_v(\theta_t)})$$
--
--   for frequencies $\theta_1,\dots,\theta_H$. The fitting objective is $f(x)=\frac1H\sum_t|\Phi_x(\theta_t)-\hat\Phi_t|^2$ for observed values $\hat\Phi_t$.
--
--   A grid has **mesh at most $s$ on $[a,b]$, endpoints included,** if $a,b\in U$ and every point of $[a,b]$ lies between two grid points of $[a,b]$ at most $s$ apart. The **rounding map** $P$ sends each squared radius of $[0,R^2/4]$ or $[R^2,U]$ to a grid point of the same interval within $s$ and every $u>U$ to $U$; a radial law $\rho$ becomes the grid vector $x_u=\rho\{r: P(r^2)=u\}$.
--
--   These are the ingredients of the convex program by which Theorem 20 estimates the near mass.
--
--   **Formalization Note** A probability vector on a `Finset` grid is a function $\mathbb R\to\mathbb R$, nonnegative on the grid and summing to $1$ over it; values off the grid play no role. The rounding map is required to be measurable. `unifI θ₀ q` is Lebesgue measure conditioned on $[\theta_0,q]$.
-- source:
--   De, Huang, Nadimpalli, Servedio, Optimally learning mixtures of arbitrarily many Gaussians, STOC 2027 submission (manuscript sha256 4f36a53e…), proof of Theorem 20, pp.26–28 (PDF pp.28–30)

import Mathlib
import Definitions.Def_GaussMixHH_RadialTransform

open MeasureTheory ProbabilityTheory Complex

namespace GaussMixHH

/-!
# The kernel `K_u`, grid distributions and the fitted convex program (proof of Theorem 20)

A. De, Y. Huang, S. Nadimpalli, R. A. Servedio, *Optimally learning mixtures of arbitrarily many
Gaussians*, STOC 2027 submission (manuscript sha256 4f36a53e…), proof of Theorem 20, pp.26–28
(PDF pp.28–30).

* `K_u(θ) = (1 − 2iθ)^{−n/2} exp(iθu/(1 − 2iθ))` for a squared radius `u = r²`.
* A grid `U` is a finite set of squared radii and a grid distribution is a probability vector
  `x = (x_u)_{u ∈ U}`, with `Φ_x(θ) = Σ_u x_u K_u(θ)` and `near-mass_R(x) = Σ_{u ≤ R²/4} x_u`.
* `E_{θ∼Unif(I)}` for `I = [θ₀, q]` is `(q − θ₀)⁻¹ ∫_{θ₀}^{q}`.
* `Q_uv = E_{θ∼Unif(I)}[Re(K_u(θ) conj K_v(θ))]` and
  `Q̂_uv = (1/H) Σ_t Re(K_u(θ_t) conj K_v(θ_t))`.
* `f(x) = (1/H) Σ_t |Φ_x(θ_t) − Φ̂_z(θ_t)|²`, the objective of the convex program.
* "Grids of mesh at most `s` on `[0, R²/4]` and `[R², U]`, including all endpoints", and the
  rounding-and-truncation map `P` (pp.26–27).

**Formalization Note.**
* A probability vector on a `Finset` grid `G` is a function `x : ℝ → ℝ` that is nonnegative on
  `G` and sums to `1` over `G`; its values off `G` play no role.
* "Mesh at most `s` on `[a, b]`, including the endpoints" is: `a, b ∈ G`, and every `u ∈ [a, b]`
  lies between two points of `G ∩ [a, b]` at most `s` apart. This is equivalent to all gaps
  between consecutive grid points of `[a, b]` being at most `s`.
* The rounding `P` is any measurable map `round` on squared radii sending each `u` of a piece to a
  grid point of the same piece within `s`, and every `u > U` to `U`. The paper's rounding is
  such a map. A radial law `ρ` (of radii `r`) is sent to the grid vector
  `x_u = ρ{r : round(r²) = u}`.
* `unifI θ₀ q` is the uniform law on `[θ₀, q]` (Lebesgue measure conditioned on the interval).
-/

/-- `K_u(θ) = (1 − 2iθ)^{−n/2} exp(iθu/(1 − 2iθ))`. -/
noncomputable def kernelK (n : ℕ) (u θ : ℝ) : ℂ := gaussFactor n θ * cexp (wfun θ * u)

/-- `x` is a probability vector on the grid `G`. -/
def IsProbVec (G : Finset ℝ) (x : ℝ → ℝ) : Prop :=
  (∀ u ∈ G, 0 ≤ x u) ∧ ∑ u ∈ G, x u = 1

/-- `Φ_x(θ) = Σ_{u ∈ U} x_u K_u(θ)`. -/
noncomputable def PhiVec (n : ℕ) (G : Finset ℝ) (x : ℝ → ℝ) (θ : ℝ) : ℂ :=
  ∑ u ∈ G, (x u : ℂ) * kernelK n u θ

/-- `near-mass_R(x) = Σ_{u ≤ R²/4} x_u`. -/
noncomputable def nearMassVec (R : ℝ) (G : Finset ℝ) (x : ℝ → ℝ) : ℝ :=
  ∑ u ∈ G.filter (fun u => u ≤ R ^ 2 / 4), x u

/-- The uniform average `E_{θ∼Unif([θ₀, q])} F(θ) = (q − θ₀)⁻¹ ∫_{θ₀}^{q} F`. -/
noncomputable def avgI (θ₀ q : ℝ) (F : ℝ → ℝ) : ℝ := (q - θ₀)⁻¹ * ∫ θ in θ₀..q, F θ

/-- `Q_uv = E_{θ∼Unif(I)}[Re(K_u(θ) conj K_v(θ))]`. -/
noncomputable def Qmat (n : ℕ) (θ₀ q u v : ℝ) : ℝ :=
  avgI θ₀ q (fun θ => (kernelK n u θ * (starRingEnd ℂ) (kernelK n v θ)).re)

/-- `Q̂_uv = (1/H) Σ_t Re(K_u(θ_t) conj K_v(θ_t))`. -/
noncomputable def Qhat (n : ℕ) {H : ℕ} (θs : Fin H → ℝ) (u v : ℝ) : ℝ :=
  (H : ℝ)⁻¹ * ∑ t, (kernelK n u (θs t) * (starRingEnd ℂ) (kernelK n v (θs t))).re

/-- The empirical average `(1/H) Σ_t |Φ_x(θ_t) − Φ_y(θ_t)|²`. -/
noncomputable def empSqDiff (n : ℕ) (G : Finset ℝ) {H : ℕ} (θs : Fin H → ℝ) (x y : ℝ → ℝ) : ℝ :=
  (H : ℝ)⁻¹ * ∑ t, ‖PhiVec n G x (θs t) - PhiVec n G y (θs t)‖ ^ 2

/-- The uniform average `E_{θ∼Unif(I)} |Φ_x(θ) − Φ_y(θ)|²`. -/
noncomputable def avgSqDiff (n : ℕ) (G : Finset ℝ) (θ₀ q : ℝ) (x y : ℝ → ℝ) : ℝ :=
  avgI θ₀ q (fun θ => ‖PhiVec n G x θ - PhiVec n G y θ‖ ^ 2)

/-- The objective `f(x) = (1/H) Σ_t |Φ_x(θ_t) − Φ̂_t|²` of the convex program. -/
noncomputable def fitObjective (n : ℕ) (G : Finset ℝ) {H : ℕ} (θs : Fin H → ℝ)
    (Φhat : Fin H → ℂ) (x : ℝ → ℝ) : ℝ :=
  (H : ℝ)⁻¹ * ∑ t, ‖PhiVec n G x (θs t) - Φhat t‖ ^ 2

/-- The uniform probability law on `[θ₀, q]`. -/
noncomputable def unifI (θ₀ q : ℝ) : Measure ℝ := ProbabilityTheory.cond volume (Set.Icc θ₀ q)

/-- `G` has mesh at most `s` on `[a, b]`, endpoints included. -/
def HasMeshOn (G : Finset ℝ) (a b s : ℝ) : Prop :=
  a ∈ G ∧ b ∈ G ∧ ∀ u ∈ Set.Icc a b, ∃ g₁ ∈ G, ∃ g₂ ∈ G,
    g₁ ∈ Set.Icc a b ∧ g₂ ∈ Set.Icc a b ∧ g₁ ≤ u ∧ u ≤ g₂ ∧ g₂ - g₁ ≤ s

/-- The grid of the proof of Theorem 20: contained in `[0, R²/4] ∪ [R², U]`, with mesh at most `s`
on each of the two intervals, all endpoints included. -/
def IsGrid (R U s : ℝ) (G : Finset ℝ) : Prop :=
  (↑G : Set ℝ) ⊆ Set.Icc 0 (R ^ 2 / 4) ∪ Set.Icc (R ^ 2) U ∧
    HasMeshOn G 0 (R ^ 2 / 4) s ∧ HasMeshOn G (R ^ 2) U s

/-- The rounding and truncation map `P` on squared radii: a measurable map sending each squared
radius `u ≤ U` of `[0, R²/4]` or `[R², U]` to a grid point of the same interval within `s`, and
every `u > U` to `U`. -/
def IsRounding (R U s : ℝ) (G : Finset ℝ) (round : ℝ → ℝ) : Prop :=
  Measurable round ∧
    (∀ u ∈ Set.Icc 0 (R ^ 2 / 4), round u ∈ G ∧ round u ∈ Set.Icc 0 (R ^ 2 / 4) ∧
      |round u - u| ≤ s) ∧
    (∀ u ∈ Set.Icc (R ^ 2) U, round u ∈ G ∧ round u ∈ Set.Icc (R ^ 2) U ∧ |round u - u| ≤ s) ∧
    (∀ u, U < u → round u = U)

/-- The grid vector `Pρ`: `x_u = ρ{r : round(r²) = u}`. -/
noncomputable def roundedVec (ρ : Measure ℝ) (round : ℝ → ℝ) : ℝ → ℝ :=
  fun u => (ρ {r | round (r ^ 2) = u}).toReal

end GaussMixHH


