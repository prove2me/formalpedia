-- Prove2me | Definitions.Def_HuImkellerMuller_Exponential_BSDE
-- name    : HuImkellerMuller_Exponential_BSDE
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T07:52:02.927837+00:00
-- url     : https://prove2.me/theorems/f670d831-bb08-4c90-9396-fb42992a1692
-- title:
--   §1 p. 3, (2) p. 4, pp. 8–9 — ℋ^∞, ℋ², BMO, the driver f of (7), v, and solutions of the BSDE (7)
-- statement:
--   This module defines the quadratic BSDE (7) of Hu, Imkeller and Müller (2005) and the function spaces it lives in.
--
--   $\mathcal H^\infty(\mathbb R)$ is the set of predictable real processes that are $\lambda\otimes P$-a.e. bounded on $[0,T]\times\Omega$; $\mathcal H^2(\mathbb R^m)$ is the set of predictable $\mathbb R^m$-valued processes $Z$ with $E\big[\int_0^T|Z_t|^2\,dt\big]<\infty$.
--
--   For a set $C\subseteq\mathbb R^m$, a vector $\theta\in\mathbb R^m$ and $\alpha>0$, put
--   $$f(z)=-\frac{\alpha}{2}\operatorname{dist}^2\Big(z+\frac1\alpha\theta,\,C\Big)+z\theta+\frac{1}{2\alpha}|\theta|^2,\qquad v(p,z)=-\alpha p\theta+\alpha f(z)+\tfrac12\alpha^2|p-z|^2 .$$
--   The **driver** of (7) is $f(t,z)$, this expression with $C=C_t(\omega)$ and $\theta=\theta_t(\omega)$.
--
--   A pair $(Y,Z)\in\mathcal H^\infty(\mathbb R)\times\mathcal H^2(\mathbb R^m)$ **solves the BSDE (7)** with terminal value $F$ when, for every $t\in[0,T]$, almost surely, $s\mapsto f(s,Z_s)$ is integrable on $[t,T]$ and
--   $$Y_t=F-\int_t^T Z_s\,dW_s-\int_t^T f(s,Z_s)\,ds .$$
--
--   Finally, $\int_0^\cdot\xi_s\,dW_s$ is a **$P$-BMO martingale** when $\xi$ is locally square integrable and there is a constant $c$ with
--   $$E\Big[\int_\tau^T|\xi_s|^2\,ds\,\Big|\,\mathcal F_\tau\Big]\le c\quad\text{for every stopping time }\tau\le T,$$
--   which is condition (2) of the paper.
--
--   **Formalization Note** The conditional expectation in (2) is written in integrated form: $E\big[\mathbf 1_A\int_\tau^T|\xi_s|^2ds\big]\le c\,P(A)$ for every $A\in\mathcal F_\tau$, with lower integrals, which is equivalent and avoids junk values. The stochastic integral $\int_t^T Z\,dW$ is $I(Z)_T-I(Z)_t$ for the Itô-integral operator $I$; the time integral is a Bochner integral whose integrability is part of the definition. $f$ and $v$ are also given in deterministic form (a fixed set $C$ and vector $\theta$), which is how the identity on p. 8 is stated.
-- source:
--   Hu, Imkeller, Müller (2005), arXiv:math/0508448v1, ℋ^k, ℋ^∞ p. 3; BMO (2), p. 4; v and f, p. 8; BSDE (7), Theorem 7, p. 9

import Mathlib
import Definitions.Def_HuImkellerMuller_Exponential_Strategy

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace HuImkellerMuller.Exponential

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d m : ℕ}

/-- `ℋ^∞(ℝ)` (p. 3): `Y` is predictable and `λ ⊗ P`-a.e. bounded on `[0, T] × Ω`. -/
def IsHinfty (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (Y : ℝ≥0 → Ω → ℝ) : Prop :=
  IsPredictable 𝓕 Y ∧
    ∃ c : ℝ, ∀ᵐ q ∂(CvitanicKaratzas92.Optimality.lebP P T), |Y q.1.toNNReal q.2| ≤ c

/-- `ℋ²(ℝ^m)` (p. 3): `Z` is predictable and `E[∫₀ᵀ |Z_t|² dt] < ∞`. -/
def IsH2 (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (Z : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin m)) : Prop :=
  IsPredictable 𝓕 Z ∧ (∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) T, ‖Z s.toNNReal ω‖ₑ ^ 2) ∂P) < ⊤

/-- The deterministic form of the driver of (7):
`f(z) = −(α/2) dist²(z + θ/α, C) + zθ + |θ|²/(2α)` for a set `C ⊆ ℝ^m` and a vector `θ ∈ ℝ^m`. -/
noncomputable def drv (C : Set (EuclideanSpace ℝ (Fin m))) (θ : EuclideanSpace ℝ (Fin m)) (α : ℝ)
    (z : EuclideanSpace ℝ (Fin m)) : ℝ :=
  -(α / 2) * Metric.infDist (z + (1 / α) • θ) C ^ 2 + inner ℝ z θ + 1 / (2 * α) * ‖θ‖ ^ 2

/-- The driver of the BSDE (7), p. 8–9:
`f(t, z) = −(α/2) dist²(z + θ_t/α, C_t(ω)) + zθ_t + |θ_t|²/(2α)`. -/
noncomputable def driver (b : ℝ≥0 → Ω → (Fin d → ℝ)) (σ : ℝ≥0 → Ω → Matrix (Fin d) (Fin m) ℝ)
    (Ct : Set (Fin d → ℝ)) (α : ℝ) (t : ℝ≥0) (ω : Ω) (z : EuclideanSpace ℝ (Fin m)) : ℝ :=
  drv (Cset Ct σ t ω) (theta b σ t ω) α z

/-- The function `v(p, z) = −α pθ + α f(z) + ½ α² |p − z|²` of p. 8, in deterministic form. -/
noncomputable def vfun (C : Set (EuclideanSpace ℝ (Fin m))) (θ : EuclideanSpace ℝ (Fin m))
    (α : ℝ) (p z : EuclideanSpace ℝ (Fin m)) : ℝ :=
  -α * inner ℝ p θ + α * drv C θ α z + 1 / 2 * α ^ 2 * ‖p - z‖ ^ 2

/-- `(Y, Z) ∈ ℋ^∞(ℝ) × ℋ²(ℝ^m)` solves the BSDE (7):
`Y_t = F − ∫ₜᵀ Z_s dW_s − ∫ₜᵀ f(s, Z_s) ds` for every `t ∈ [0, T]`, almost surely, with the
time integral existing. -/
def IsSolution7 (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (I : (ℝ≥0 → Ω → EuclideanSpace ℝ (Fin m)) → ℝ≥0 → Ω → ℝ)
    (b : ℝ≥0 → Ω → (Fin d → ℝ)) (σ : ℝ≥0 → Ω → Matrix (Fin d) (Fin m) ℝ)
    (Ct : Set (Fin d → ℝ)) (α : ℝ) (F : Ω → ℝ)
    (Y : ℝ≥0 → Ω → ℝ) (Z : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin m)) : Prop :=
  IsHinfty P 𝓕 T Y ∧ IsH2 P 𝓕 T Z ∧
  ∀ t ≤ T, ∀ᵐ ω ∂P,
    IntegrableOn (fun s : ℝ => driver b σ Ct α s.toNNReal ω (Z s.toNNReal ω))
      (Set.Icc (t : ℝ) T) ∧
    Y t ω = F ω - (I Z T ω - I Z t ω) -
      ∫ s in Set.Icc (t : ℝ) T, driver b σ Ct α s.toNNReal ω (Z s.toNNReal ω)

/-- (2), p. 4: `∫₀^· ξ_s dW_s` is a `P`-BMO martingale on `[0, T]`. The integrand `ξ` is locally
square integrable (so the stochastic integral exists), and there is a constant `c` with
`E[∫_τ^T |ξ_s|² ds | 𝓕_τ] ≤ c` for every stopping time `τ ≤ T`, written in integrated form:
`E[1_A ∫_τ^T |ξ_s|² ds] ≤ c · P(A)` for every `A ∈ 𝓕_τ`. -/
def IsBMO (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (ξ : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin m)) : Prop :=
  CvitanicKaratzas92.Optimality.IsLocallySquareIntegrable 𝓕 P T ξ ∧
  ∃ c : ℝ, ∀ (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime 𝓕 τ),
    (∀ ω, τ ω ≤ (T : WithTop ℝ≥0)) → ∀ A : Set Ω, MeasurableSet[hτ.measurableSpace] A →
      ∫⁻ ω in A, (∫⁻ s in Set.Icc (((τ ω).untopD T : ℝ≥0) : ℝ) T, ‖ξ s.toNNReal ω‖ₑ ^ 2) ∂P ≤
        ENNReal.ofReal c * P A

end HuImkellerMuller.Exponential


