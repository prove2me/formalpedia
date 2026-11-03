-- Prove2me | Definitions.Def_RiskAverseConsistency_IsRFunction
-- name    : RiskAverseConsistency_IsRFunction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:21:40.508808+00:00
-- url     : https://prove2.me/theorems/16e4abd5-201e-4725-9bcd-19de2e864831
-- title:
--   R-function
-- statement:
--   A function $\phi:V\to[0,\infty)$ on a normed space is an **R-function** if it is convex and continuous, and $v_k\to v$ in norm whenever $v_k\rightharpoonup v$ weakly and $\phi(v_k)\to\phi(v)$.
--
--   The squared norm of a Hilbert space is an R-function (Radon–Riesz property). When the regularizer $\wp$ of (8) is an R-function, weak limits of approximate minimizers are strong limits, which upgrades value consistency to consistency of solution sets.
-- source:
--   Milz, Surowiec, Asymptotic consistency for nonconvex risk-averse stochastic optimization with infinite dimensional decision spaces, arXiv:2207.14756v2, p.4

import Mathlib
import Definitions.Def_QuasiHemiVI_Existence_WeakConv

open Filter Topology QuasiHemiVI.Existence

namespace RiskAverseConsistency

/-- `φ : V → [0, ∞)` is an **R-function**: it is convex and continuous, and `vₖ → v` (in norm)
whenever `vₖ ⇀ v` (weakly) and `φ(vₖ) → φ(v)`.

Milz, Surowiec, arXiv:2207.14756v2, §2.2, p.4 (generalizing the Radon–Riesz / Kadec–Klee
property).

Formalization Note: the codomain `[0, ∞)` is `ℝ` with the conjunct `0 ≤ φ v`. -/
def IsRFunction {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (φ : V → ℝ) : Prop :=
  (∀ v, 0 ≤ φ v) ∧ ConvexOn ℝ Set.univ φ ∧ Continuous φ ∧
    ∀ (u : ℕ → V) (v : V), WeakConv u v → Tendsto (fun k => φ (u k)) atTop (𝓝 (φ v)) →
      Tendsto u atTop (𝓝 v)

end RiskAverseConsistency


