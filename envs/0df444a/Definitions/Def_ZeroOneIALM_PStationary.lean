-- Prove2me | Definitions.Def_ZeroOneIALM_PStationary
-- name    : ZeroOneIALM_PStationary
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:29:50.082068+00:00
-- url     : https://prove2.me/theorems/58730df8-5f83-4650-9702-6c056fbef53c
-- title:
--   P-stationary points and triplets of problem (2)
-- statement:
--   Let $f$ be differentiable. A vector $(w^*;u^*)\in\mathbb R^p\times\mathbb R^n$ is a **P-stationary point** of problem (2) if there exist $z^*\in\mathbb R^n$ and a constant $\alpha>0$ with
--   $$
--   \nabla f(w^*)+A^\top z^*=0,\qquad u^*\in\mathrm{Prox}_{\alpha\lambda\|(\cdot)_+\|_0}(u^*+\alpha z^*),\qquad Aw^*+b-u^*=0. \tag{27}
--   $$
--   Then $z^*$ is a **P-stationary multiplier** and $(w^*;u^*;z^*)$ is a **P-stationary triplet**.
--
--   This is the first-order optimality condition for (2), and the limit of the algorithm is such a triplet.
--
--   **Formalization Note** `IsPStationaryWith` is system (27) for a given $\alpha$; `IsPStationaryTriplet` and `IsPStationaryPoint` quantify over $\alpha>0$ and over the multiplier as in Definition 2. $\nabla f$ is Mathlib's `gradient`.
-- source:
--   Zhang & Xiu, Global Convergence of Inexact Augmented Lagrangian Method for Zero-One Composite Optimization, arXiv:2112.00440v1, Definition 2, display (27), p.11

import Mathlib
import Definitions.Def_ZeroOneIALM_Prox

namespace ZeroOneIALM

variable {p n : ℕ}

/-- The system (27) of Definition 2, Zhang & Xiu, arXiv:2112.00440v1, p.11, for a given constant
`α`: `∇f(w) + Aᵀz = 0`, `u ∈ Prox_{αλ‖(·)₊‖₀}(u + αz)` and `Aw + b - u = 0`.

**Formalization Note.** `∇f` is Mathlib's `gradient`, and `Aᵀ` is the adjoint of the continuous
linear map `A`. -/
def IsPStationaryWith (f : EuclideanSpace ℝ (Fin p) → ℝ)
    (A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) (lam α : ℝ)
    (w : EuclideanSpace ℝ (Fin p)) (u z : EuclideanSpace ℝ (Fin n)) : Prop :=
  gradient f w + ContinuousLinearMap.adjoint A z = 0 ∧
    u ∈ proxVec lam α (u + α • z) ∧
    A w + b - u = 0

/-- `(w; u; z)` is a P-stationary triplet of problem (2), Definition 2, arXiv:2112.00440v1, p.11:
the system (27) holds for some constant `α > 0`. -/
def IsPStationaryTriplet (f : EuclideanSpace ℝ (Fin p) → ℝ)
    (A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) (lam : ℝ)
    (w : EuclideanSpace ℝ (Fin p)) (u z : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ α : ℝ, 0 < α ∧ IsPStationaryWith f A b lam α w u z

/-- `(w; u)` is a P-stationary point of problem (2), Definition 2, arXiv:2112.00440v1, p.11: there
is a multiplier `z` such that `(w; u; z)` is a P-stationary triplet. -/
def IsPStationaryPoint (f : EuclideanSpace ℝ (Fin p) → ℝ)
    (A : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) (lam : ℝ)
    (w : EuclideanSpace ℝ (Fin p)) (u : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ z, IsPStationaryTriplet f A b lam w u z

end ZeroOneIALM


