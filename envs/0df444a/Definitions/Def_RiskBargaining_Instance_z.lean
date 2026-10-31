-- Prove2me | Definitions.Def_RiskBargaining_Instance_z
-- name    : RiskBargaining_Instance_z
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:28:02.919997+00:00
-- url     : https://prove2.me/theorems/0cdbc0c0-1da2-4b28-8e11-650b05b14f7a
-- title:
--   The value $z(R,M,\mathcal A)$ of problem (8)
-- statement:
--   The value of the instance is
--   $$
--   z(R,M,\mathcal A)=\max_{u,L,x}\Big\{\sum_{i=1}^n u_i \;\Big|\; \sum_{i=1}^n L_i=M_x,\ \mathcal A_i(R_i)\le u_i\le\mathcal A_i(L_i)\ \forall i\in N,\ x\in\mathcal X\Big\}.
--   $$
--
--   **Formalization Note** $z$ is the real supremum of the value set. It is the printed $\max$ exactly on attained instances, and a junk value elsewhere (for example $0$ if the set is unbounded above). Every statement that mentions $z$ assumes attainment.
-- source:
--   Gutjahr, Kovacevic, Wozabal, Risk-Averse Bargaining in a Stochastic Optimization Context, manuscript, equation (8), p.9

import Mathlib
import Definitions.Def_RiskBargaining_Instance_totals

open MeasureTheory
open scoped ENNReal

namespace RiskBargaining

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {X : Type*} [TopologicalSpace X] [CompactSpace X] {ι : Type*}

/-- **The value** `z(R, M, 𝒜)` of problem (8).
Gutjahr, Kovacevic, Wozabal, *Risk-Averse Bargaining in a Stochastic Optimization Context*, manuscript, equation (8), p.9.

**Formalization Note.** `z` is the real `sSup` of `Instance.totals`. It equals the printed `max` exactly
when `Instance.Attained` holds; on other instances it is a junk value (`0` when the set is unbounded
above or empty), so every statement that mentions `z` assumes `Attained`. -/
noncomputable def Instance.z [Fintype ι] (I : Instance μ p X ι) : ℝ :=
  sSup I.totals

end RiskBargaining


