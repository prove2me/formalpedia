-- Prove2me | Definitions.Def_TeschlODE_PeriodicOrbits_IsHyperbolicPeriodicPoint
-- name    : TeschlODE_PeriodicOrbits_IsHyperbolicPeriodicPoint
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T04:16:47.426585+00:00
-- url     : https://prove2.me/theorems/c67b9235-92af-42ea-9eb6-e499349346c8
-- title:
--   Hyperbolic periodic orbit: no eigenvalue of $dP_\Sigma(x_0)$ on the unit circle
-- statement:
--   Let $f \in C^k(M, \mathbb{R}^n)$ have flow $\Phi$. A point $x_0$ lies on a **hyperbolic periodic orbit** $\gamma(x_0)$ of period $T$ if $x_0$ is a periodic point with period $T > 0$ and, for some codimension-one submanifold $\Sigma = \{x \in U \mid S(x) = 0\}$ through $x_0$ transversal to $f$, with Poincaré map $P_\Sigma(y) = \Phi(\tau(y), y)$ ($\tau$ a $C^k$ return time, $\tau(x_0) = T$), no eigenvalue of $dP_\Sigma(x_0)$ lies on the unit circle:
--   $$\sigma\big(dP_\Sigma(x_0)\big) \cap \{z \in \mathbb{C} : |z| = 1\} = \emptyset .$$
--
--   The notion is used from Lemma 12.7 on (Lemma 12.7, Theorems 12.8–12.10).
--
--   **Formalization Note.** The author's preliminary version never defines a hyperbolic periodic orbit (p. 319 invites the reader to compare "this definition" with the one for fixed points, but no definition precedes it). The proof of Lemma 12.7 uses exactly "no eigenvalue of $dP_\Sigma(x_0)$ lies on the unit circle", which is taken here. Eigenvalues are the complex roots of the characteristic polynomial of $dP_\Sigma(x_0)$. By Theorem 12.4 the condition does not depend on the choice of $\Sigma$, so "for some $\Sigma$" and "for every $\Sigma$" agree.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 319, Lemma 12.7 and its proof (the term is not defined in the preliminary version)

import Mathlib
import Definitions.Def_TeschlODE_PeriodicOrbits_IsRegularPeriodicPoint
import Definitions.Def_TeschlODE_PeriodicOrbits_IsTransversalSection
import Definitions.Def_TeschlODE_PeriodicOrbits_IsReturnTime
import Definitions.Def_TeschlODE_PeriodicOrbits_IsPoincareDerivative

namespace TeschlODE.PeriodicOrbits

/-- Teschl, §12.2–12.3, pp. 319–321: `x₀` lies on a **hyperbolic periodic orbit** `γ(x₀)` of
`ẋ = f(x)` (flow `Φ`, maximal time intervals `I`, `f ∈ Cᵏ(M)`). The preliminary version uses
this notion from Lemma 12.7 on without defining it; the proof of Lemma 12.7 uses exactly "no
eigenvalue of `dP_Σ(x₀)` lies on the unit circle", which is taken as the definition: `x₀` is a
regular periodic point of period `T`, and for some codimension-one submanifold
`Σ = {x ∈ U | S(x) = 0}` through `x₀` transversal to `f`, with Poincaré map
`P_Σ(y) = Φ(τ(y), y)` (`τ` a `Cᵏ` return time with `τ(x₀) = T`), the derivative
`dP_Σ(x₀)` (an endomorphism of `ker (∂S/∂x)(x₀)`) has no complex eigenvalue of modulus one
(eigenvalues = complex roots of its characteristic polynomial). By Theorem 12.4 this does not
depend on the choice of `Σ`. -/
def IsHyperbolicPeriodicPoint {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ)) (M : Set (Fin n → ℝ))
    (k : ℕ) (I : (Fin n → ℝ) → Set ℝ) (Φ : ℝ → (Fin n → ℝ) → (Fin n → ℝ))
    (x₀ : Fin n → ℝ) (T : ℝ) : Prop :=
  IsRegularPeriodicPoint I Φ x₀ T ∧
    ∃ (U : Set (Fin n → ℝ)) (S : (Fin n → ℝ) → ℝ) (τ : (Fin n → ℝ) → ℝ)
      (L : Module.End ℝ (LinearMap.ker (fderiv ℝ S x₀ : (Fin n → ℝ) →ₗ[ℝ] ℝ))),
      IsTransversalSection f M k U S ∧ x₀ ∈ U ∧ S x₀ = 0 ∧ IsReturnTime I Φ k U S x₀ T τ ∧
        IsPoincareDerivative Φ τ S x₀ L ∧
        ∀ z : ℂ, (L.charpoly.map (algebraMap ℝ ℂ)).IsRoot z → ‖z‖ ≠ 1

end TeschlODE.PeriodicOrbits


