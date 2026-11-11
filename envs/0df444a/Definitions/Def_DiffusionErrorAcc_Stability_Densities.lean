-- Prove2me | Definitions.Def_DiffusionErrorAcc_Stability_Densities
-- name    : DiffusionErrorAcc_Stability_Densities
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T14:57:42.220376+00:00
-- url     : https://prove2.me/theorems/ee2a378a-102f-43f1-a6b1-b84bffa15773
-- title:
--   Laws on ℝ^d with positive C¹ densities, total variation distance, the classical divergence and the weighted Sobolev space H¹(µ)
-- statement:
--   Throughout, $\mathbb R^d$ is `Rd d = EuclideanSpace ℝ (Fin d)` with the Euclidean norm $\|\cdot\|$. Following the paper's standing convention (§2.3) every distribution on $\mathbb R^d$ has a positive, continuously differentiable density; such a law is represented by its density $\rho$ with respect to Lebesgue measure. `IsRegDensity ρ` says $\rho(x)>0$ for all $x$, $\rho\in C^1$, $\rho$ is integrable and $\int\rho\,dx=1$; `densMeasure ρ` is the law $\mu(dx)=\rho(x)\,dx$.
--
--   The **total variation distance** of two probability measures is
--   $$\mathrm{TV}(\mu,\nu)=\sup_{A\ \text{measurable}}|\mu(A)-\nu(A)|$$
--   (`tvDist`); the supremum ranges over a nonempty family of numbers in $[0,1]$.
--
--   The **divergence** of a vector field $F:\mathbb R^d\to\mathbb R^d$ is the classical $\nabla\cdot F(x)=\sum_{i=1}^d\partial_iF_i(x)$ (`divergence`), computed from the Fréchet derivative.
--
--   The **weighted Sobolev space** of §2 is $H^1(\mu)=\{h\in L^2(\mu):\nabla h \text{ exists and lies in } L^2(\mu;\mathbb R^d)\}$; `InH1 ρ h` reads "$\nabla h$ exists" as: $h$ is differentiable on all of $\mathbb R^d$, and asks $h\in L^2(\mu)$ and its gradient $\nabla h\in L^2(\mu;\mathbb R^d)$ for $\mu=\rho\,dx$.
--
--   **Formalization Note.** `μ.real A` is the real value of $\mu(A)$; the classical gradient is Mathlib's `gradient`.
-- source:
--   Giapitzakis, Moitra, Risteski, Rohatgi, Error accumulation in reverse diffusion with an imperfect score: beyond path-space analyses, STOC 2027 submission (manuscript sha256 c0118fd2…), p. 8, §2 (L², H¹(µ), E_µ, Var_µ, Euclidean norm); p. 10, §2.3 (positive C¹ densities); p. 9 and p. 23 (η_T = TV)

import Mathlib

open MeasureTheory
open scoped ENNReal NNReal

namespace DiffusionErrorAcc.Stability

/-! # Laws with positive C¹ densities on ℝ^d, total variation, the classical divergence and H¹(µ)
(Giapitzakis–Moitra–Risteski–Rohatgi, §2 p. 8 and §2.3 p. 10)

The paper's §2.3 makes every distribution on `ℝ^d` have a positive, continuously differentiable
density. Such a law is represented by its density `ρ` with respect to Lebesgue measure on
`ℝ^d = EuclideanSpace ℝ (Fin d)`; `densMeasure ρ` is the law itself. -/

/-- The Euclidean space `ℝ^d` with the Euclidean norm and inner product. -/
abbrev Rd (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- `ρ` is a probability density on `ℝ^d` (with respect to Lebesgue measure) that is everywhere
positive and continuously differentiable (§2.3): `ρ > 0`, `ρ ∈ C¹`, `ρ` integrable, `∫ ρ = 1`. -/
def IsRegDensity {d : ℕ} (ρ : Rd d → ℝ) : Prop :=
  (∀ x, 0 < ρ x) ∧ ContDiff ℝ 1 ρ ∧ Integrable ρ ∧ ∫ x, ρ x = 1

/-- The law `µ(dx) = ρ(x) dx` with density `ρ` with respect to Lebesgue measure. -/
noncomputable def densMeasure {d : ℕ} (ρ : Rd d → ℝ) : Measure (Rd d) :=
  volume.withDensity (fun x => ENNReal.ofReal (ρ x))

/-- Total variation distance of two probability measures,
`TV(µ, ν) = sup_{A measurable} |µ(A) − ν(A)|`. The supremum is over a nonempty family (`A = ∅`)
of numbers in `[0, 1]`, so it is a genuine real supremum. -/
noncomputable def tvDist {X : Type*} [MeasurableSpace X] (μ ν : Measure X) : ℝ :=
  ⨆ A : {A : Set X // MeasurableSet A}, |μ.real A.1 - ν.real A.1|

/-- The classical divergence `∇ · F (x) = Σ_i ∂_i F_i (x)` of a vector field `F : ℝ^d → ℝ^d`
(meaningful for differentiable `F`; every vector field of the paper is `C¹`, §2.3). -/
noncomputable def divergence {d : ℕ} (F : Rd d → Rd d) (x : Rd d) : ℝ :=
  ∑ i : Fin d, (fderiv ℝ F x (EuclideanSpace.single i (1 : ℝ))) i

/-- The weighted Sobolev space `H¹(µ) = {h ∈ L²(µ) : ∇h exists, and lies in L²(µ; ℝ^d)}` (§2,
p. 8) for `µ = densMeasure ρ`, with `∇h` read as the classical gradient: `h` is differentiable
on all of `ℝ^d`. -/
def InH1 {d : ℕ} (ρ : Rd d → ℝ) (h : Rd d → ℝ) : Prop :=
  MemLp h 2 (densMeasure ρ) ∧ Differentiable ℝ h ∧ MemLp (gradient h) 2 (densMeasure ρ)

end DiffusionErrorAcc.Stability


