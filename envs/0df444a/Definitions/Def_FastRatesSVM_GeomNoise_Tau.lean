-- Prove2me | Definitions.Def_FastRatesSVM_GeomNoise_Tau
-- name    : FastRatesSVM_GeomNoise_Tau
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:51:20.307456+00:00
-- url     : https://prove2.me/theorems/ed4a9802-78fe-4016-b091-1387012366b8
-- title:
--   Equation (7) — the classes $X_{-1}, X_0, X_1$ and the distance $\tau_x$ to the decision boundary
-- statement:
--   Let $X \subset \mathbb R^d$ and let $P$ be a distribution on $X \times \{-1, 1\}$ with marginal $P_X$ and regression function $\eta(x) = P(y = 1 \mid x)$, for some fixed choice of the version $\eta$. The **classes** of $P$ are
--
--   $$X_{-1} := \{x \in X : \eta(x) < \tfrac12\}, \qquad X_1 := \{x \in X : \eta(x) > \tfrac12\}, \qquad X_0 := \{x \in X : \eta(x) = \tfrac12\}.$$
--
--   The **distance to the decision boundary** is the function $x \mapsto \tau_x$ defined by
--
--   $$\tau_x := \begin{cases} d(x, X_0 \cup X_1), & x \in X_{-1},\\ d(x, X_0 \cup X_{-1}), & x \in X_1,\\ 0, & \text{otherwise},\end{cases}$$
--
--   where $d(x, A) = \inf_{a \in A} \|x - a\|$ is the Euclidean distance of $x$ to the set $A$. Roughly, $\tau_x$ is the distance from $x$ to the region where the other label is at least as likely. It is the geometric quantity in which the geometric noise exponent and the envelope condition are stated.
--
--   **Formalization Note** The point $x$ ranges over `EuclideanSpace ℝ (Fin d)`, $X$ is a set in it, and $\eta$ is any real function on it; only its values on $X$ enter. The paper does not say what $d(x, \emptyset)$ is. Lean's `Metric.infDist x ∅ = 0` pins the convention $d(x, \emptyset) := 0$, so a version of $\eta$ with one class empty and $X_0 = \emptyset$ gets $\tau_x = 0$, not $\infty$. Under $d(x,\emptyset)=\infty$ the companion statements of the paper (Theorem 2.7, Lemma 4.1) are false for such a version (take $\eta \equiv 0.9$); Theorem 2.6 holds under both readings.
-- source:
--   Steinwart, Scovel, Fast Rates for Support Vector Machines Using Gaussian Kernels, arXiv:0708.1838v1, p. 7, definition of X_{-1}, X_1, X_0 and equation (7)

import Mathlib

open MeasureTheory

namespace FastRatesSVM.GeomNoise

/-- The class `X₋₁ := {x ∈ X : η(x) < 1/2}` of a distribution with regression function `η`
(Steinwart–Scovel, arXiv:0708.1838v1, p. 7). -/
def negClass {d : ℕ} (X : Set (EuclideanSpace ℝ (Fin d))) (η : EuclideanSpace ℝ (Fin d) → ℝ) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {x | x ∈ X ∧ η x < 1 / 2}

/-- The class `X₁ := {x ∈ X : η(x) > 1/2}` (p. 7). -/
def posClass {d : ℕ} (X : Set (EuclideanSpace ℝ (Fin d))) (η : EuclideanSpace ℝ (Fin d) → ℝ) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {x | x ∈ X ∧ 1 / 2 < η x}

/-- The set `X₀ := {x ∈ X : η(x) = 1/2}` (p. 7). -/
def zeroClass {d : ℕ} (X : Set (EuclideanSpace ℝ (Fin d))) (η : EuclideanSpace ℝ (Fin d) → ℝ) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {x | x ∈ X ∧ η x = 1 / 2}

/-- The distance to the decision boundary, equation (7), p. 7:
`τ_x = d(x, X₀ ∪ X₁)` on `X₋₁`, `τ_x = d(x, X₀ ∪ X₋₁)` on `X₁`, and `0` otherwise, with the
Euclidean distance `d(x, A) = Metric.infDist x A`. The paper leaves `d(x, ∅)` unspecified;
`Metric.infDist x ∅ = 0` pins the convention `d(x, ∅) := 0`. -/
noncomputable def tau {d : ℕ} (X : Set (EuclideanSpace ℝ (Fin d)))
    (η : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ := by
  classical
  exact if x ∈ negClass X η then Metric.infDist x (zeroClass X η ∪ posClass X η)
    else if x ∈ posClass X η then Metric.infDist x (zeroClass X η ∪ negClass X η)
    else 0

end FastRatesSVM.GeomNoise


