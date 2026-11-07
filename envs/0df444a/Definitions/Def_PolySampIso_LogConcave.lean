-- Prove2me | Definitions.Def_PolySampIso_LogConcave
-- name    : PolySampIso_LogConcave
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:26:26.785576+00:00
-- url     : https://prove2.me/theorems/7c9d0c13-85b7-418a-b652-444d7aabcd49
-- title:
--   Log-concave densities on X and strongly log-concave measures
-- statement:
--   A function $g\ge0$ vanishing off a convex set $X$ is a **log-concave density on $X$** if
--
--   $$g(\lambda x+(1-\lambda)y)\ge g(x)^\lambda g(y)^{1-\lambda}\qquad(x,y\in X,\ \lambda\in[0,1]);$$
--
--   the measure $g\,dx$ is then a log-concave measure supported on $X$. A measure $\nu$ is **$\alpha$-strongly log-concave on a convex set $K$** if $\nu$ has Lebesgue density $e^{-U}$ on $K$ (and none off $K$) with $U-\frac\alpha2\|\cdot\|^2$ convex on $K$.
--
--   The first notion is the class to which Remark 2 extends Lemma 3 (it contains every cooled measure $\pi_t$); the second is the hypothesis of the conductance bound of Proposition 7.
-- source:
--   Gu, Shi, Tian, Yang, Polytope Sampling at the Speed of Isoperimetry, arXiv:2610.23775 (preprint, sha256 b6a79179…), Remark 2, p.13 (PDF p.15); Proposition 7, p.44 (PDF p.46)

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace PolySampIso

/-!
# Log-concave densities and strong log-concavity

A. Gu, B. Shi, K. Tian, H. Yang, *Polytope Sampling at the Speed of Isoperimetry*,
arXiv:2610.23775 (preprint, sha256 b6a79179…). Remark 2, p.13 (PDF p.15): "any log-concave measure
π supported on X"; Proposition 7, p.44 (PDF p.46): "µ(· | K) is α-strongly log-concave".

**Formalization Note.**
* `IsLogConcaveDensityOn X g`: `g ≥ 0`, `g = 0` off `X`, and
  `g(λx + (1 − λ)y) ≥ g(x)^λ g(y)^{1−λ}` for `x, y ∈ X`, `λ ∈ [0, 1]` (so `g` may vanish on part of
  `X`). A log-concave measure supported on `X` is `volume.withDensity g` for such `g` (the reading
  of Remark 2: its cited input, [LV07] Theorem 2.5, is about log-concave densities).
* `IsStronglyLogConcaveOn ν K α`: `ν` has Lebesgue density `e^{−U}` on `K` and none off `K`, with
  `U − (α/2)‖·‖²` convex on `K`.
-/

/-- `g` is a log-concave density supported on `X`. -/
def IsLogConcaveDensityOn {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (g : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  (∀ x, 0 ≤ g x) ∧ (∀ x, x ∉ X → g x = 0) ∧
    ∀ x ∈ X, ∀ y ∈ X, ∀ l : ℝ, 0 ≤ l → l ≤ 1 →
      g x ^ l * g y ^ (1 - l) ≤ g (l • x + (1 - l) • y)

/-- `ν` is `α`-strongly log-concave on `K`: `ν = e^{−U}·Leb|_K` with `U − (α/2)‖·‖²` convex on
`K`. -/
def IsStronglyLogConcaveOn {n : ℕ} (ν : Measure (EuclideanSpace ℝ (Fin n)))
    (K : Set (EuclideanSpace ℝ (Fin n))) (α : ℝ) : Prop :=
  ∃ U : EuclideanSpace ℝ (Fin n) → ℝ, ConvexOn ℝ K (fun x => U x - α / 2 * ‖x‖ ^ 2) ∧
    ν = (volume.restrict K).withDensity fun x => ENNReal.ofReal (Real.exp (-U x))

end PolySampIso


