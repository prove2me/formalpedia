-- Prove2me | Definitions.Def_SmoothedNash_Supplement_JointDensityBound
-- name    : SmoothedNash_Supplement_JointDensityBound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:59:03.303859+00:00
-- url     : https://prove2.me/theorems/a9da86b4-255f-4d6d-ace2-4f75f41ad14c
-- title:
--   Assumption 1.7: $(F(x), v^\top J_F(x))$ and $(F(x), J_F(x)v)$ have density at most $P_d$
-- statement:
--   A random map $F$ on $(\Omega, \mathbb P)$ satisfies **Assumption 1.7 (bounded joint density for the derivative)** with constant $P_d > 0$ if, for every $x \in B(0,1)$ and every unit vector $v \in S^{n-1}$, the joint laws of
--   $$
--   \bigl(F(x),\, v^\top J_F(x)\bigr) \qquad\text{and}\qquad \bigl(F(x),\, J_F(x) v\bigr)
--   $$
--   in $\mathbb R^{2n}$ both have probability densities bounded by $P_d$; that is, $\mathbb P[(\cdot) \in S] \le P_d\, \lambda_{2n}(S)$ for every Borel $S \subseteq \mathbb R^n \times \mathbb R^n$.
--
--   **Formalization Note** The row vector $v^\top J_F(x)$ is represented by the column vector $J_F(x)^\top v$ (the adjoint applied to $v$); $J_F$ is the derivative within the ball, as in Assumption 1.10.
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), Assumption 1.7, p.5

import Mathlib
open MeasureTheory

namespace SmoothedNash.Supplement

/-- **Assumption 1.7 (Bounded Joint Density for Derivative)** (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), p.5), for a
random map `F : Ω → (ℝ^n → ℝ^n)` on `(Ω, P)`: `Pd > 0`, and for every `x ∈ B_n(0,1)` and every
unit vector `v ∈ S^{n−1}`, the joint laws of `(F(x), v^⊤ J_F(x))` and `(F(x), J_F(x) v)` in
`ℝ^{2n}` both have probability densities bounded by `Pd`.

**Formalization Note** The row vector `v^⊤ J_F(x)` is the column vector `J_F(x)^⊤ v`, i.e. the adjoint
of `J_F(x)` applied to `v`. `J_F(x)` is `fderivWithin ℝ (F ω) (closedBall 0 1) x` (see
`JacobianLipschitz`). `ℝ^{2n}` is `EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)` with the
product Lebesgue measure `volume`, and each density bound is the measure inequality
`P[(…) ∈ S] ≤ Pd · λ_{2n}(S)` for every Borel `S`. `Pd > 0` is bundled as printed. -/
def JointDensityBound {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Ω → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (Pd : ℝ) : Prop :=
  0 < Pd ∧ ∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1,
    ∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ = 1 →
      ∀ S : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)), MeasurableSet S →
        P {ω | (F ω x, ContinuousLinearMap.adjoint
            (fderivWithin ℝ (F ω) (Metric.closedBall 0 1) x) v) ∈ S}
            ≤ ENNReal.ofReal Pd * volume S ∧
        P {ω | (F ω x, fderivWithin ℝ (F ω) (Metric.closedBall 0 1) x v) ∈ S}
            ≤ ENNReal.ofReal Pd * volume S

end SmoothedNash.Supplement


