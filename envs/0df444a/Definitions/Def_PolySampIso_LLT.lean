-- Prove2me | Definitions.Def_PolySampIso_LLT
-- name    : PolySampIso_LLT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:27:06.362135+00:00
-- url     : https://prove2.me/theorems/0d54486f-0445-4b15-957c-3f662acb97c7
-- title:
--   Definition 1 and Algorithm 1: log-Laplace transforms, tilts, convolution powers and the LLT proximal sampler
-- statement:
--   For a potential $\varphi$ on $\mathbb R^d$ (possibly finite only on a subspace, where $e^{-\varphi}$ is a density with respect to Lebesgue measure on that subspace), the **log-Laplace transform** is $\varphi^\sharp(x)=\log\int e^{\langle x,y\rangle-\varphi(y)}\,dy$. Writing $\rho$ for the measure of $e^{-\varphi}$, $\psi=\varphi^\sharp$ on $X$ means $\int e^{\langle x,y\rangle}\rho(dy)=e^{\psi(x)}$ for $x\in X$.
--
--   The **tilt** of a measure $\nu$ by $y$ is $T_y\nu\propto e^{\langle y,\cdot\rangle}\nu$, and $\varphi^{*\tau}$ is the potential of the $\tau$-fold convolution $\rho^{*\tau}$.
--
--   **Algorithm 1** (LLTProx) with step size $\tau\in\mathbb N$ alternates a forwards step $y_k\sim T_{x_k}e^{-\varphi^{*\tau}}$ and a backwards step $x_{k+1}\sim T_{y_k}\big(e^{-\tau\psi}\pi\big)$; these are the two conditionals of the joint density $\tilde\pi_\tau(x,y)=e^{\langle x,y\rangle-\varphi^{*\tau}(y)-\tau\psi(x)}\pi(x)$, whose $x$-marginal is $\pi$.
--
--   **Formalization Note** `lltProxLaw` is the law of $x_k$ from $x_0\sim\mu_0$, obtained by binding the forwards and backwards laws; a tilt with infinite normalizer is the zero measure (a null set of $y$).
-- source:
--   Gu, Shi, Tian, Yang, Polytope Sampling at the Speed of Isoperimetry, arXiv:2610.23775 (preprint, sha256 b6a79179…), Definition 1, (3)–(5) and Algorithm 1, pp.8–9 (PDF pp.10–11)

import Mathlib
import Definitions.Def_PolySampIso_Divergences

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PolySampIso

/-!
# Log-Laplace transforms, tilts, convolution powers and the LLT proximal sampler (Algorithm 1)

A. Gu, B. Shi, K. Tian, H. Yang, *Polytope Sampling at the Speed of Isoperimetry*,
arXiv:2610.23775 (preprint, sha256 b6a79179…), §2.1–2.2, pp.8–9 (PDF pp.10–11).
Definition 1: "The log-Laplace transform (LLT) of φ : Rd → R ∪ {∞} is defined as φ♯(x) :=
log(∫ exp (⟨x, y⟩ − φ(y)) dy). When φ is finite only on a lower-dimensional linear subspace L ⊆ Rd,
we interpret exp(−φ) as a density with respect to Lebesgue measure on L". Tilts: "Tyν(x) :=
exp(⟨y, x⟩)ν(x) / ∫ exp(⟨y, z⟩)ν(z) dz, whenever the denominator is finite." "φ∗τ refer[s] to the
potential (negative log-density) of the τ-fold convolution of the density exp(−φ)."
Algorithm 1 (LLTProx(x0, τ, K)), p.9: "yk ∼ πY|X=xk = Txk exp(−φ∗τ) ▷ Forwards step;
xk+1 ∼ πX|Y=yk = Tyk exp(−τψ)π ▷ Backwards step".

**Formalization Note.**
* The density `exp(−φ)` (on `ℝᵈ` or on a subspace `L`) is the measure `ρ` it defines on `ℝᵈ`, so
  `φ♯(x) = log ∫ e^{⟨x,y⟩} ρ(dy)`; `IsLLTOn ρ ψ X` says `ψ = φ♯` on `X`, i.e.
  `∫ e^{⟨x,y⟩} ρ(dy) = e^{ψ(x)}` (finite) for `x ∈ X`.
* `convPow ρ τ = ρ ∗ ⋯ ∗ ρ` (`τ` factors; `convPow ρ 0 = δ₀`) is the measure of `exp(−φ∗τ)`.
* `tilt y ν = T_y ν = normalize(e^{⟨y,·⟩} ν)`; when the normalizer is infinite it is the zero
  measure, which happens only on a null set of `y` in Algorithm 1.
* `lltProxLaw ρ π ψ τ μ₀ k` is `Law(x_k)` for Algorithm 1 started at `x₀ ∼ μ₀`: each iteration
  binds the forwards law `T_x(ρ^{∗τ})` and then the backwards law `T_y(e^{−τψ}π)`.
-/

/-- `∫ e^{⟨x,y⟩} ρ(dy)`, the Laplace transform of the measure `ρ` (so `φ♯ = log` of it). -/
noncomputable def laplace {d : ℕ} (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (x : EuclideanSpace ℝ (Fin d)) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (Real.exp (inner ℝ x y)) ∂ρ

/-- `ψ = φ♯` on `X`, where `exp(−φ)` is the measure `ρ` (Definition 1). -/
def IsLLTOn {d : ℕ} (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (X : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ x ∈ X, laplace ρ x = ENNReal.ofReal (Real.exp (ψ x))

/-- The tilt `T_y ν ∝ exp(⟨y, ·⟩) ν`. -/
noncomputable def tilt {d : ℕ} (y : EuclideanSpace ℝ (Fin d))
    (ν : Measure (EuclideanSpace ℝ (Fin d))) : Measure (EuclideanSpace ℝ (Fin d)) :=
  normalize (ν.withDensity fun z => ENNReal.ofReal (Real.exp (inner ℝ y z)))

/-- The `τ`-fold convolution `ρ^{∗τ}` (the measure of `exp(−φ∗τ)`). -/
noncomputable def convPow {d : ℕ} (ρ : Measure (EuclideanSpace ℝ (Fin d))) :
    ℕ → Measure (EuclideanSpace ℝ (Fin d))
  | 0 => Measure.dirac 0
  | k + 1 => ρ ∗ convPow ρ k

/-- The forwards step of Algorithm 1: `π^{Y|X=x} = T_x exp(−φ∗τ)`. -/
noncomputable def lltForward {d : ℕ} (ρ : Measure (EuclideanSpace ℝ (Fin d))) (τ : ℕ)
    (x : EuclideanSpace ℝ (Fin d)) : Measure (EuclideanSpace ℝ (Fin d)) :=
  tilt x (convPow ρ τ)

/-- The backwards step of Algorithm 1: `π^{X|Y=y} = T_y exp(−τψ)π`. -/
noncomputable def lltBackward {d : ℕ} (π : Measure (EuclideanSpace ℝ (Fin d)))
    (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (τ : ℕ) (y : EuclideanSpace ℝ (Fin d)) :
    Measure (EuclideanSpace ℝ (Fin d)) :=
  tilt y (π.withDensity fun x => ENNReal.ofReal (Real.exp (-(τ : ℝ) * ψ x)))

/-- `Law(x_k)` in Algorithm 1 (LLTProx) started from `x₀ ∼ μ₀`. -/
noncomputable def lltProxLaw {d : ℕ} (ρ π : Measure (EuclideanSpace ℝ (Fin d)))
    (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (τ : ℕ) (μ₀ : Measure (EuclideanSpace ℝ (Fin d))) :
    ℕ → Measure (EuclideanSpace ℝ (Fin d))
  | 0 => μ₀
  | k + 1 => ((lltProxLaw ρ π ψ τ μ₀ k).bind (lltForward ρ τ)).bind (lltBackward π ψ τ)

end PolySampIso


