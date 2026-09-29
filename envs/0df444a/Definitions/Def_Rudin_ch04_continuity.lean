-- Prove2me | Definitions.Def_Rudin_ch04_continuity
-- name    : Rudin_ch04_continuity
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-12T19:47:02.579347+00:00
-- url     : https://prove2.me/theorems/51f35a42-8ce2-4fc6-a2f4-75fadb2c6735
-- title:
--   Uniform continuity in the $\varepsilon$–$\delta$ form
-- statement:
--   Rudin's Definition 4.18: $f$ is **uniformly continuous** on a metric space $X$ if for every $\varepsilon > 0$ there is a single $\delta > 0$ such that $d(f(p), f(q)) < \varepsilon$ for all $p, q \in X$ with $d(p,q) < \delta$ — the $\delta$ depends on $\varepsilon$ only, not on the point. A relativized version, with $p$ and $q$ restricted to a subset $E$ of the domain, is included for use in later chapters. Continuity itself, and Rudin's punctured limit $\lim_{x \to p} f(x)$, are taken from Mathlib.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 4, p. 90, Definition 4.18

import Mathlib

/-!
# Rudin, Chapter 4 — uniform continuity

Definition transcribed from Walter Rudin, *Principles of Mathematical Analysis*, 3rd edition,
Chapter 4 (Definition 4.18).

Continuity itself is Mathlib's `Continuous` / `ContinuousAt` / `ContinuousWithinAt`, and Rudin's
limit $\lim_{x \to p} f(x) = q$ along a set $E$ is `Filter.Tendsto f (𝓝[E \ {p}] p) (𝓝 q)`;
both are reused.  Uniform continuity in Mathlib is phrased through the uniformity filter, so the
$\varepsilon$–$\delta$ form Rudin uses — one $\delta$ serving all pairs of points — is stated
here directly.
-/

namespace Rudin

/-- Rudin, Definition 4.18: `f` is **uniformly continuous** on the metric space `X` if for every
`ε > 0` there is a `δ > 0` such that `dist (f p) (f q) < ε` for all points `p, q` with
`dist p q < δ`. -/
def UniformlyContinuous {X Y : Type*} [MetricSpace X] [MetricSpace Y] (f : X → Y) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ p q : X, dist p q < δ → dist (f p) (f q) < ε

/-- The version of `Rudin.UniformlyContinuous` relative to a subset `E` of the domain: the
points `p, q` are restricted to `E`. -/
def UniformlyContinuousOn {X Y : Type*} [MetricSpace X] [MetricSpace Y] (f : X → Y) (E : Set X) :
    Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ E, ∀ q ∈ E, dist p q < δ → dist (f p) (f q) < ε

end Rudin


