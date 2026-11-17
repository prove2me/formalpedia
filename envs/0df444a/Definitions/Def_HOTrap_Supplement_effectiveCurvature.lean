-- Prove2me | Definitions.Def_HOTrap_Supplement_effectiveCurvature
-- name    : HOTrap_Supplement_effectiveCurvature
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T04:29:07.675535+00:00
-- url     : https://prove2.me/theorems/5cd1543e-0c28-4056-9016-b261191be67a
-- title:
--   Effective curvature and the hard function classes of Section 6
-- statement:
--   For $p\ge2$, define the **effective curvature**
--   $$
--   \gamma_p(\varepsilon)=\min\left\{L_1,\left(L_p\varepsilon^{p-1}\right)^{1/p}\right\}.
--   $$
--   The class $\mathcal F^{(d)}_{1,p}(\Delta,L_1,L_p)$ consists of nonnegative functions $f:\mathbb R^d\to\mathbb R$ in $C^{1,1}(L_1)\cap C^{p,1}(L_p)$ satisfying $f(0)-\inf f\le\Delta$. The class $\mathcal F^{(d)}_p(\Delta,L_p)$ imposes the same nonnegativity, higher-order smoothness, and initial-gap condition without the $C^{1,1}(L_1)$ constraint.
--
--   The bundle also defines the smooth coercive part of either class: functions that are $C^\infty$ and tend to $+\infty$ as $\lVert x\rVert\to\infty$. These are the hard instances permitted by Theorem 6.5.
--
--   **Formalization Note** The initial-gap condition is written as $f(0)-f(y)\le\Delta$ for every $y$, avoiding a default-valued real infimum. Coercivity is the equivalent bounded-sublevel condition.
-- source:
--   Zhou–Sugiyama–Suzuki, Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds, arXiv:2610.02791, Eq. (27), p.36; Theorem 6.5, p.38

import Mathlib
import Definitions.Def_HOTrap_HolderClass

namespace HOTrap.Supplement

/-- The effective curvature scale
`γ_p(ε) = min {L₁, (L_p ε^(p-1))^(1/p)}` of Eq. (27).
Zhou--Sugiyama--Suzuki, *Finding Stationary Points under Higher-Order Smoothness: Trapping
Algorithms and First-Order Lower Bounds*, arXiv:2610.02791, p.36. -/
noncomputable def effectiveCurvature (p : ℕ) (L₁ Lp ε : ℝ) : ℝ :=
  min L₁ (Real.rpow (Lp * ε ^ (p - 1)) (1 / (p : ℝ)))

/-- The class `F^(d)_{1,p}(Δ,L₁,L_p)` from Section 6, p.36: nonnegative globally
`C^{1,1}(L₁) ∩ C^{p,1}(L_p)` functions whose initial gap at the origin is at most `Δ`. -/
def HardClass1p (d p : ℕ) (Δ L₁ Lp : ℝ) :
    Set (EuclideanSpace ℝ (Fin d) → ℝ) :=
  {f | HOTrap.HolderClass 1 1 L₁ f ∧ HOTrap.HolderClass p 1 Lp f ∧
    (∀ x, 0 ≤ f x) ∧ (∀ y, f 0 - f y ≤ Δ)}

/-- The class `F^(d)_p(Δ,L_p)` from Section 6, p.36, without a gradient-Lipschitz budget. -/
def HardClassP (d p : ℕ) (Δ Lp : ℝ) : Set (EuclideanSpace ℝ (Fin d) → ℝ) :=
  {f | HOTrap.HolderClass p 1 Lp f ∧ (∀ x, 0 ≤ f x) ∧ (∀ y, f 0 - f y ≤ Δ)}

/-- A real function on Euclidean space is coercive when every real sublevel is contained in some
closed ball.  This is the `f(x) → +∞` as `‖x‖ → ∞` convention used after Theorem 6.5. -/
def IsCoercive {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ∀ B : ℝ, ∃ R : ℝ, 0 ≤ R ∧ ∀ x, R ≤ ‖x‖ → B ≤ f x

/-- The smooth coercive members of a function class.  Theorem 6.5 says its hard instances may be
chosen in this subclass. -/
def SmoothCoercivePart {d : ℕ} (F : Set (EuclideanSpace ℝ (Fin d) → ℝ)) :
    Set (EuclideanSpace ℝ (Fin d) → ℝ) :=
  {f | f ∈ F ∧ ContDiff ℝ ⊤ f ∧ IsCoercive f}

end HOTrap.Supplement


