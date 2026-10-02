-- Prove2me | Definitions.Def_HunterPDE_Friedrichs_Mollifier
-- name    : HunterPDE_Friedrichs_Mollifier
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T00:54:42.877085+00:00
-- url     : https://prove2.me/theorems/6b44a8e6-4598-4f5e-80f6-9481f25f77ed
-- title:
--   Mollifier profile, rescaled mollifier η_ε, smoothing operator J_ε (8.13) and the commutator [J_ε, L]
-- statement:
--   A **mollifier profile** is a function $\eta : \mathbb{R}^n \to \mathbb{R}$ that is $C^\infty$, compactly supported, non-negative, radially symmetric ($\eta(x) = \eta(y)$ whenever $|x| = |y|$), with $\int_{\mathbb{R}^n} \eta\,dx = 1$; the bump (1.5) of the notes is an example. For $\varepsilon > 0$ its rescaling is $\eta_\varepsilon(x) = \varepsilon^{-n}\eta(x/\varepsilon)$, and the associated **smoothing operator** (8.13) acts on $u : \mathbb{R}^n \to \mathbb{R}^m$ by convolution,
--   $$J_\varepsilon u(x) = (\eta_\varepsilon * u)(x) = \int_{\mathbb{R}^n} \eta_\varepsilon(x-y)\, u(y)\,dy .$$
--   For the operator $L = A^i\partial_i + C$ of (8.3), the **commutator** is $[J_\varepsilon, L]u = J_\varepsilon(Lu) - L(J_\varepsilon u)$. Friedrichs' lemma (Lemma 8.11) says this commutator is bounded on $L^2$ uniformly in $\varepsilon$ and tends to zero strongly.
--
--   **Formalization Note.** `IsMollifierProfile η` bundles the five properties ($C^\infty$ is `ContDiff ℝ ∞`, smoothness, not analyticity). `mollifierScaled η ε x` is $\eta_\varepsilon(x)$, `Jeps η ε u x` is the Bochner integral $\int \eta_\varepsilon(x-y)u(y)\,dy$, and `commutator η ε A C u x` is $([J_\varepsilon,L]u)(x)$, evaluated pointwise on functions; it is used only on $u \in C^1_c$, where every integral involved converges.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), pp. 227–228, Eq. (1.6), Eq. (8.13) and Lemma 8.11

import Mathlib
import Definitions.Def_HunterPDE_Friedrichs_SymmetricOperator

open MeasureTheory
open scoped ContDiff

namespace HunterPDE.Friedrichs

/-- `η : ℝⁿ → ℝ` is a mollifier profile in the sense of Hunter, p. 228: a compactly supported,
non-negative, radially symmetric `C^∞` function (`ContDiff ℝ ∞`, smooth — not the analytic `ω`)
with unit integral. The standard bump (1.5) is one such function. -/
def IsMollifierProfile {n : ℕ} (η : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧ (∀ x, 0 ≤ η x) ∧
    (∀ x y, ‖x‖ = ‖y‖ → η x = η y) ∧ ∫ x, η x = 1

/-- The rescaled mollifier `η_ε(x) = ε^{-n} η(x/ε)` (Hunter (1.6), p. 227). -/
noncomputable def mollifierScaled {n : ℕ} (η : EuclideanSpace ℝ (Fin n) → ℝ) (ε : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (ε ^ n)⁻¹ * η (ε⁻¹ • x)

/-- The smoothing operator of Hunter (8.13), `J_ε u = η_ε ∗ u`:
`(J_ε u)(x) = ∫_{ℝⁿ} η_ε(x − y) u(y) dy` for `u : ℝⁿ → ℝᵐ`. -/
noncomputable def Jeps {n m : ℕ} (η : EuclideanSpace ℝ (Fin n) → ℝ) (ε : ℝ)
    (u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin m) :=
  ∫ y, mollifierScaled η ε (x - y) • u y

/-- The commutator `[J_ε, L] u = J_ε(Lu) − L(J_ε u)` of the smoothing operator (8.13) with the
operator `L = Aⁱ∂ᵢ + C` of (8.3), evaluated on a function `u : ℝⁿ → ℝᵐ` (Hunter, Lemma 8.11). -/
noncomputable def commutator {n m : ℕ} (η : EuclideanSpace ℝ (Fin n) → ℝ) (ε : ℝ)
    (A : Fin n → EuclideanSpace ℝ (Fin n) → Matrix (Fin m) (Fin m) ℝ)
    (C : EuclideanSpace ℝ (Fin n) → Matrix (Fin m) (Fin m) ℝ)
    (u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin m) :=
  Jeps η ε (Lop A C u) x - Lop A C (Jeps η ε u) x

end HunterPDE.Friedrichs


