-- Prove2me | Definitions.Def_HuImkellerMuller_Power_BSDE
-- name    : HuImkellerMuller_Power_BSDE
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T08:43:40.239127+00:00
-- url     : https://prove2.me/theorems/912906d3-cfe4-424f-abe4-e3283ba7bffb
-- title:
--   ℋ^∞, ℋ², BMO (2), the driver f of (15) and the solution class of the BSDE (15), pp. 3–4 and 17
-- statement:
--   This file fixes the backward stochastic differential equation of Theorem 14 of Hu, Imkeller and Müller (2005) and the classes in which it is solved.
--
--   1. $\mathcal H^\infty(\mathbb R)$: predictable real processes that are $\lambda\otimes P$-a.e. bounded on $[0,T]\times\Omega$. $\mathcal H^2(\mathbb R^m)$: predictable $\mathbb R^m$-valued processes $Z$ with $E\int_0^T|Z_t|^2\,dt<\infty$.
--   2. **BMO** (2). The local martingale $\int_0^\cdot\xi_s\,dW_s$ is a BMO martingale on $[0,T]$ when $\sup_\tau \big\|E[\int_\tau^T|\xi_s|^2\,ds\mid\mathcal F_\tau]\big\|_\infty<\infty$, the supremum over stopping times $\tau\le T$. Equivalently, there is $c$ with $E[\mathbf 1_A\int_\tau^T|\xi_s|^2\,ds]\le c\,P(A)$ for every stopping time $\tau$ with values in $[0,T]$ and every $A\in\mathcal F_\tau$.
--   3. **Driver.** For $\gamma\in(0,1)$, a set $C\subseteq\mathbb R^m$ and $\theta,z\in\mathbb R^m$,
--   $$
--   f(z)=\frac{\gamma(1-\gamma)}{2}\operatorname{dist}^2\Big(\frac1{1-\gamma}(z+\theta),C\Big)-\frac{\gamma|z+\theta|^2}{2(1-\gamma)}-\frac12|z|^2,
--   $$
--   and the driver of (15) is $f(t,z)$, this expression at $\theta=\theta_t(\omega)$ and $C=C_t(\omega)$.
--   4. **Solution of (15).** $(Y,Z)\in\mathcal H^\infty(\mathbb R)\times\mathcal H^2(\mathbb R^m)$ solves
--   $$
--   Y_t=0-\int_t^T Z_s\,dW_s-\int_t^T f(s,Z_s)\,ds,\qquad t\in[0,T],
--   $$
--   when for every $t\in[0,T]$, almost surely, $s\mapsto f(s,Z_s)$ is integrable on $[t,T]$ and the identity holds.
--
--   Theorem 14 expresses the value of the power-utility problem through $Y_0$.
--
--   **Formalization Note** $\int_t^T Z\,dW$ is `I Z T − I Z t` for the Itô-integral operator `I`. The BMO condition is stated with lower integrals over events of $\mathcal F_\tau$ instead of conditional expectations; stopping times are $\mathbb R_{\ge0}$-valued, bounded by $T$. Integrability of the driver along $Z$ is part of the solution predicate, so the Bochner integral is never a junk value.
-- source:
--   Hu, Imkeller, Müller (2005), arXiv:math/0508448v1, ℋ^k and ℋ^∞, p. 3; (2), p. 4; f and (15), p. 17

import Mathlib
import Definitions.Def_HuImkellerMuller_Power_Market
import Definitions.Def_HuImkellerMuller_Exponential_BSDE

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace HuImkellerMuller.Power

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- (2), p. 4: `∫₀^· ξ_s dW_s` is a BMO martingale on `[0, T]`, i.e.
`sup_τ ‖E[∫_τ^T |ξ_s|² ds | 𝓕_τ]‖_∞ < ∞` over stopping times `τ ≤ T`. Stated without
conditional expectations: there is `c` with `E[1_A ∫_τ^T |ξ_s|² ds] ≤ c P(A)` for every stopping
time `τ` with values in `[0, T]` and every `A ∈ 𝓕_τ`. -/
def IsBMO {m : ℕ} (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (ξ : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin m)) : Prop :=
  ∃ c : ℝ, ∀ τ : Ω → ℝ≥0, ∀ hτ : IsStoppingTime 𝓕 (fun ω => ((τ ω : ℝ≥0) : WithTop ℝ≥0)),
    (∀ ω, τ ω ≤ T) → ∀ A : Set Ω, MeasurableSet[hτ.measurableSpace] A →
      ∫⁻ ω in A, (∫⁻ s in Set.Icc ((τ ω : ℝ)) T, ‖ξ s.toNNReal ω‖ₑ ^ 2) ∂P
        ≤ ENNReal.ofReal c * P A

/-- The power-utility driver at fixed data (p. 17): for `θ, z ∈ ℝᵐ`, a set `C ⊆ ℝᵐ` and
`γ ∈ (0, 1)`,
`f(z) = γ(1−γ)/2 · dist²((z + θ)/(1−γ), C) − γ|z + θ|² / (2(1−γ)) − ½|z|²`. -/
noncomputable def powerDriver {m : ℕ} (θ : EuclideanSpace ℝ (Fin m))
    (C : Set (EuclideanSpace ℝ (Fin m))) (γ : ℝ) (z : EuclideanSpace ℝ (Fin m)) : ℝ :=
  γ * (1 - γ) / 2 * Metric.infDist ((1 / (1 - γ)) • (z + θ)) C ^ 2
    - γ * ‖z + θ‖ ^ 2 / (2 * (1 - γ)) - (1 / 2) * ‖z‖ ^ 2

/-- The driver `f(t, z)` of the BSDE (15), p. 17: `powerDriver` at `θ_t(ω)` and `C_t(ω)`. -/
noncomputable def driver {d m : ℕ} (b : ℝ≥0 → Ω → (Fin d → ℝ))
    (σ : ℝ≥0 → Ω → Matrix (Fin d) (Fin m) ℝ) (Ct : Set (Fin d → ℝ)) (γ : ℝ)
    (t : ℝ≥0) (ω : Ω) (z : EuclideanSpace ℝ (Fin m)) : ℝ :=
  powerDriver (HuImkellerMuller.Exponential.theta b σ t ω) (HuImkellerMuller.Exponential.Cset Ct σ t ω) γ z

/-- `(Y, Z) ∈ ℋ^∞(ℝ) × ℋ²(ℝᵐ)` solves the BSDE (15), p. 17:
`Y_t = 0 − ∫_t^T Z_s dW_s − ∫_t^T f(s, Z_s) ds` for every `t ∈ [0, T]`, `P`-a.s., where
`∫_t^T Z dW = I Z T − I Z t` and `s ↦ f(s, Z_s)` is integrable on `[t, T]`. -/
def IsSolution15 {d m : ℕ} (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (I : (ℝ≥0 → Ω → EuclideanSpace ℝ (Fin m)) → ℝ≥0 → Ω → ℝ)
    (b : ℝ≥0 → Ω → (Fin d → ℝ)) (σ : ℝ≥0 → Ω → Matrix (Fin d) (Fin m) ℝ)
    (Ct : Set (Fin d → ℝ)) (γ : ℝ)
    (Y : ℝ≥0 → Ω → ℝ) (Z : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin m)) : Prop :=
  HuImkellerMuller.Exponential.IsHinfty P 𝓕 T Y ∧ HuImkellerMuller.Exponential.IsH2 P 𝓕 T Z ∧
  ∀ t ≤ T, ∀ᵐ ω ∂P,
    IntegrableOn (fun s : ℝ => driver b σ Ct γ s.toNNReal ω (Z s.toNNReal ω))
      (Set.Icc (t : ℝ) T) ∧
    Y t ω = 0 - (I Z T ω - I Z t ω)
      - ∫ s in Set.Icc (t : ℝ) T, driver b σ Ct γ s.toNNReal ω (Z s.toNNReal ω)

end HuImkellerMuller.Power


