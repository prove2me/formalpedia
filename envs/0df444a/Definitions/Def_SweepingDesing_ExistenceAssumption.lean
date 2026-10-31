-- Prove2me | Definitions.Def_SweepingDesing_ExistenceAssumption
-- name    : SweepingDesing_ExistenceAssumption
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:17:00.229543+00:00
-- url     : https://prove2.me/theorems/7eea2ff8-5701-45f2-9a10-18848d42f0bd
-- title:
--   Assumption (A1) — existence of orbits from non-critical points
-- statement:
--   A set-valued map $S:\mathbb R\rightrightarrows\mathbb R^n$ with graph $\mathcal S$ satisfies the **existence assumption (A1)** if for every $(t,x)\in\mathcal S$ with $\|D^*S(t,x)|^+<+\infty$ there exist $\delta_x>0$ and at least one orbit $\gamma_x\in\mathcal{AC}(S;[t,t+\delta_x))$ with $\gamma_x(t)=x$.
--
--   It guarantees that an orbit can be started from every point where the oriented modulus is finite.
--
--   **Formalization Note** Absolute continuity on $[t,t+\delta_x)$ is read on compact subintervals.
-- source:
--   Daniilidis, Tapia-García, Desingularization of the Sweeping Process Mapping, arXiv:2110.08686v1, Assumption (A1), p.8

import Mathlib
import Definitions.Def_SweepingDesing_orientedModulus
import Definitions.Def_SweepingDesing_IsACOrbit
open Filter Topology MeasureTheory Set
open scoped ENNReal

namespace SweepingDesing

/-- Daniilidis, Tapia-García, Desingularization of the Sweeping Process Mapping, arXiv:2110.08686v1, §3.1, Assumption (A1), p.8: `S` satisfies the *existence assumption* if for every
`(t, x) ∈ 𝒮` with `‖D*S(t, x)|⁺ < +∞` there exist `δ_x > 0` and at least one orbit
`γ_x ∈ 𝒜𝒞(S; [t, t + δ_x))` with `γ_x(t) = x`.

**Formalization Note** Absolute continuity on `[t, t + δ_x)` is read as on its compact
subintervals (`IsACOrbit`). -/
def ExistenceAssumption {n : ℕ} (S : ℝ → Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ t : ℝ, ∀ x ∈ S t, orientedModulus S t x < ⊤ →
    ∃ δ > (0 : ℝ), ∃ γ : ℝ → EuclideanSpace ℝ (Fin n), IsACOrbit S γ (Ico t (t + δ)) ∧ γ t = x

end SweepingDesing


