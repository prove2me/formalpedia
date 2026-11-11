-- Prove2me | Definitions.Def_MixedVolFPRAS_Main_Metropolis
-- name    : MixedVolFPRAS_Main_Metropolis
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:30:43.107288+00:00
-- url     : https://prove2.me/theorems/e2a089ef-5625-41e8-92a6-467e4a70f081
-- title:
--   Lazy Metropolis chain on the sphere (Definition B.1), its Dirichlet form, chain laws and total variation distance
-- statement:
--   Let $\psi$ be a positive density on $S^{n-1}$ and $\zeta>0$; set $\alpha=1/(n+\zeta)$. The proposal density with respect to $\omega$ is
--
--   $$q_\alpha(x,y)=\frac{1}{Z_\alpha}\max\Big\{0,1-\frac{d(x,y)^2}{\alpha^2}\Big\}^2,\qquad Z_\alpha=\int_{S^{n-1}}\max\Big\{0,1-\frac{d(x,z)^2}{\alpha^2}\Big\}^2d\omega(z),$$
--
--   $d$ the geodesic distance. The **lazy Metropolis chain** $P$ (Definition B.1): from $x$ it stays at $x$ with probability $1/2$; otherwise it proposes $y\sim q_\alpha(x,\cdot)\,d\omega$ and moves to $y$ with probability $\min\{1,\psi(y)/\psi(x)\}$, staying at $x$ otherwise. So
--
--   $$P(x,\cdot)=\Big(\tfrac12+\tfrac12\Big(1-\!\int q_\alpha(x,y)\min\{1,\tfrac{\psi(y)}{\psi(x)}\}d\omega(y)\Big)\Big)\delta_x+\tfrac12\,q_\alpha(x,y)\min\{1,\tfrac{\psi(y)}{\psi(x)}\}\,d\omega(y).$$
--
--   Further: $\mu=\psi\,\omega$; the **Dirichlet form** $\mathcal{E}_P(f,f)=\frac12\iint(f(y)-f(x))^2P(x,dy)\,d\mu(x)$; $\sigma=\omega/\omega(S^{n-1})$ the uniform distribution; the law of $X_T$ for $X_0\sim\nu$ moved by $P$; and $\|\nu-\mu\|_{TV}=\sup_A|\nu(A)-\mu(A)|$ over measurable $A$.
--
--   **Formalization Note.** Measures live on `Sph n`. `lazyMetropolis ψ ζ x` is the displayed measure (`α = 1/(n + ζ)` inside); `densityMeasure ψ`, `uniformSphere n`, `dirichletForm P μ f`, `chainLaw P ν T` (`T`-fold `Measure.bind P`) and `tvDist` are the objects above. `Measure.bind` uses the honest pushforward because $x\mapsto P(x,\cdot)$ is measurable for continuous $\psi$; nothing in an item assumes this measurability.
-- source:
--   Chen, Liu, An FPRAS for Mixed Volumes, STOC 2027 submission (manuscript sha256 0acf8d97…), p. 34, Definition B.1 and Lemma B.2

import Mathlib
import Definitions.Def_MixedVolFPRAS_Main_Sphere

noncomputable section

namespace MixedVolFPRAS.Main

open MeasureTheory

/-!
# The lazy Metropolis chain on the sphere (Definition B.1), its Dirichlet form, TV distance

Chen, Liu, *An FPRAS for Mixed Volumes*, p. 34, Definition B.1 and Lemma B.2.

Fix a density `ψ` (a function on `ℝⁿ`, used on `Sⁿ⁻¹`) and `ζ > 0`; the proposal radius is
`α = 1/(n + ζ)`.

* `proposalWeight α x y = max{0, 1 − d(x, y)²/α²}²`, `proposalNormalizer α x = Z_α = ∫ proposalWeight α x z dω(z)`,
  `q_α(x, y) = proposalWeight α x y / Z_α`.
* From `x`, the chain stays at `x` with probability `1/2`; otherwise it proposes `y ∼ q_α(x, ·) dω`
  and accepts with probability `min{1, ψ(y)/ψ(x)}`, staying at `x` on rejection. So
  `P(x, ·) = (1/2 + (1/2)(1 − ∫ q_α(x, y) min{1, ψ(y)/ψ(x)} dω(y))) δ_x
            + (1/2) q_α(x, y) min{1, ψ(y)/ψ(x)} dω(y)`.
* `densityMeasure ψ = ψ ω` (the measure `µ` of Appendix B, `dµ = ψ dω`).
* `dirichletForm P µ f = (1/2) ∬ (f(y) − f(x))² P(x, dy) dµ(x)`.
* `chainLaw P ν T` is the law of `X_T` when `X₀ ∼ ν` and the chain moves by `P`.
* `uniformSphere n = σ = ω / ω(Sⁿ⁻¹)`.
* `tvDist ν µ = sup_A |ν(A) − µ(A)|` over measurable `A`.
-/

/-- `max{0, 1 − d(x, y)²/α²}²`. -/
def proposalWeight {n : ℕ} (α : ℝ) (x y : E n) : ℝ :=
  (max 0 (1 - geodesicDist x y ^ 2 / α ^ 2)) ^ 2

/-- `Z_α = ∫ max{0, 1 − d(x, z)²/α²}² dω(z)`. -/
def proposalNormalizer {n : ℕ} (α : ℝ) (x : E n) : ℝ :=
  ∫ z : Sph n, proposalWeight α x (z : E n) ∂(surfaceMeasure n)

/-- The proposal density `q_α(x, y)` with respect to `ω`. -/
def proposalDensity {n : ℕ} (α : ℝ) (x y : E n) : ℝ :=
  proposalWeight α x y / proposalNormalizer α x

/-- Density (w.r.t. `ω`) of a proposed and accepted move from `x` to `y`. -/
def moveDensity {n : ℕ} (ψ : E n → ℝ) (α : ℝ) (x y : E n) : ℝ :=
  proposalDensity α x y * min 1 (ψ y / ψ x)

/-- The lazy Metropolis kernel `P` of Definition B.1, with `α = 1/(n + ζ)`. -/
def lazyMetropolis {n : ℕ} (ψ : E n → ℝ) (ζ : ℝ) (x : Sph n) : Measure (Sph n) :=
  ENNReal.ofReal (1 / 2 + 1 / 2 *
      (1 - ∫ y : Sph n, moveDensity ψ (1 / ((n : ℝ) + ζ)) (x : E n) (y : E n) ∂(surfaceMeasure n)))
      • Measure.dirac x +
    ENNReal.ofReal (1 / 2) • (surfaceMeasure n).withDensity
      (fun y => ENNReal.ofReal (moveDensity ψ (1 / ((n : ℝ) + ζ)) (x : E n) (y : E n)))

/-- The measure `ψ ω` on the sphere. -/
def densityMeasure {n : ℕ} (ψ : E n → ℝ) : Measure (Sph n) :=
  (surfaceMeasure n).withDensity (fun θ => ENNReal.ofReal (ψ (θ : E n)))

/-- The uniform probability measure `σ = ω / ω(Sⁿ⁻¹)`. -/
def uniformSphere (n : ℕ) : Measure (Sph n) :=
  (surfaceMeasure n Set.univ)⁻¹ • surfaceMeasure n

/-- `E_P(f, f) = (1/2) ∬ (f(y) − f(x))² P(x, dy) dµ(x)`. -/
def dirichletForm {n : ℕ} (P : Sph n → Measure (Sph n)) (μ : Measure (Sph n))
    (f : Sph n → ℝ) : ℝ :=
  (1 / 2) * ∫ x, ∫ y, (f y - f x) ^ 2 ∂(P x) ∂μ

/-- The law of `X_T` for the chain `P` started from `X₀ ∼ ν`. -/
def chainLaw {n : ℕ} (P : Sph n → Measure (Sph n)) (ν : Measure (Sph n)) (T : ℕ) :
    Measure (Sph n) :=
  (fun ρ : Measure (Sph n) => ρ.bind P)^[T] ν

/-- Total variation distance `sup_A |ν(A) − µ(A)|` over measurable sets. -/
def tvDist {α : Type} [MeasurableSpace α] (ν μ : Measure α) : ℝ :=
  ⨆ A : {A : Set α // MeasurableSet A}, |(ν A.1).toReal - (μ A.1).toReal|

end MixedVolFPRAS.Main


