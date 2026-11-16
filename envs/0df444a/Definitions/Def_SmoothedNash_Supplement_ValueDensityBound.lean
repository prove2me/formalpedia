-- Prove2me | Definitions.Def_SmoothedNash_Supplement_ValueDensityBound
-- name    : SmoothedNash_Supplement_ValueDensityBound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:58:44.839017+00:00
-- url     : https://prove2.me/theorems/8f448ed7-8e8f-4159-adb3-ff9ff5be410b
-- title:
--   Assumption 1.6: the value $F(x)$ has density at most $P_v$
-- statement:
--   Let $F$ be a random map $\mathbb R^n \to \mathbb R^n$ on a probability space $(\Omega, \mathbb P)$. It satisfies **Assumption 1.6 (bounded density)** with constant $P_v > 0$ if, for every $x \in B(0,1)$, the law of $F(x)$ has a probability density bounded by $P_v$. Equivalently, for every Borel set $S \subseteq \mathbb R^n$,
--   $$
--   \mathbb P[F(x) \in S] \le P_v \cdot \lambda_n(S),
--   $$
--   where $\lambda_n$ is Lebesgue measure.
--
--   **Formalization Note** The density bound is stated as this measure inequality; $P_v > 0$ is part of the predicate, as printed.
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), Assumption 1.6, p.4, and Assumption 3.2, p.21

import Mathlib
open MeasureTheory

namespace SmoothedNash.Supplement

/-- **Assumption 1.6 (Bounded Density)** (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), p.4; Assumption 3.2, p.21), for a
random map `F : Ω → (ℝ^n → ℝ^n)` on a probability space `(Ω, P)`: `Pv > 0`, and for every
`x ∈ B_n(0,1)` the law of `F(x)` has a probability density bounded by `Pv`.

**Formalization Note** The density bound is stated as the equivalent measure inequality
`P[F(x) ∈ S] ≤ Pv · λ_n(S)` for every Borel `S ⊆ ℝ^n`, with `λ_n` Lebesgue measure (`volume`) on
`EuclideanSpace ℝ (Fin n)`. The inequality makes the law absolutely continuous with Radon–Nikodym
derivative at most `Pv` almost everywhere, and conversely. The bound `Pv > 0` is bundled as printed
("There exists some `Pv > 0`"). -/
def ValueDensityBound {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Ω → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (Pv : ℝ) : Prop :=
  0 < Pv ∧ ∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1,
    ∀ S : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet S →
      P {ω | F ω x ∈ S} ≤ ENNReal.ofReal Pv * volume S

end SmoothedNash.Supplement


