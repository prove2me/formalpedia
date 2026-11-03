-- Prove2me | Definitions.Def_RiskAverseConsistency_IsCaratheodoryOn
-- name    : RiskAverseConsistency_IsCaratheodoryOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:21:24.218669+00:00
-- url     : https://prove2.me/theorems/59441bf6-af37-40f0-b881-36b226bcfa74
-- title:
--   Carathéodory mapping
-- statement:
--   Let $S$ be a subset of a topological space and $(\Xi,\mathcal A)$ a measurable space. A map $g:S\times\Xi\to\beta$ is a **Carathéodory mapping** if $g(\upsilon,\cdot)$ is measurable for every $\upsilon\in S$ and $g(\cdot,\xi)$ is continuous on $S$ for every $\xi\in\Xi$.
--
--   **Formalization Note** $g$ is given on the ambient space; only its values on $S$ matter, and continuity is that of the restriction to $S$.
-- source:
--   Milz, Surowiec, Asymptotic consistency for nonconvex risk-averse stochastic optimization with infinite dimensional decision spaces, arXiv:2207.14756v2, p.4

import Mathlib

namespace RiskAverseConsistency

/-- `g : S × Ξ → β` is a **Carathéodory mapping**: `g(υ, ·)` is measurable for every `υ ∈ S` and
`g(·, ξ)` is continuous on `S` for every `ξ ∈ Ξ`.

Milz, Surowiec, arXiv:2207.14756v2, §2.2, p.4.

Formalization Note: `g` is a curried function on the ambient space `Y`; only its values on `S`
matter, and continuity is continuity of the restriction to `S` (`ContinuousOn`), i.e. continuity on
the metric space `S`. -/
def IsCaratheodoryOn {Y Ξ β : Type*} [TopologicalSpace Y] [MeasurableSpace Ξ] [TopologicalSpace β]
    [MeasurableSpace β] (S : Set Y) (g : Y → Ξ → β) : Prop :=
  (∀ y ∈ S, Measurable (g y)) ∧ ∀ x : Ξ, ContinuousOn (fun y => g y x) S

end RiskAverseConsistency


