-- Prove2me | Definitions.Def_DigitalPrivacy_DataStrategy_IsBusinessOptimal
-- name    : DigitalPrivacy_DataStrategy_IsBusinessOptimal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:04:40.326028+00:00
-- url     : https://prove2.me/theorems/61ac954b-d72c-4117-8317-f5bf4d46e300
-- title:
--   Optimal data strategy of the business
-- statement:
--   A data strategy $(\xi,C)$ is **optimal for the business** if $\xi\in[0,1]$, $C\ge0$, and
--
--   $$\Pi(\xi,C)\ge\Pi(\xi',C')\qquad\text{for all }\xi'\in[0,1],\ C'\ge 0 .$$
--
--   **Formalization Note** A predicate, so statements about it describe the whole set of maximizers. The feasible set contains the boundary $C=0$.
-- source:
--   Fainmesser, Galeotti, Momot, Digital Privacy, author manuscript (April 2022 draft; SSRN 3459274), §2.3–2.4, pp. 8–9 (PDF 9–10)

import Mathlib
import Definitions.Def_DigitalPrivacy_DataStrategy_profit

namespace DigitalPrivacy.DataStrategy

/-- **Optimal data strategy of the business.**
Fainmesser, Galeotti, Momot, *Digital Privacy*, author manuscript (April 2022 draft; SSRN 3459274), §2.3–2.4, pp. 8–9 (PDF 9–10): the business chooses `ξ ∈ [0, 1]` and `C ∈ ℝ₊` and
"maximizes its profit given (a*, v*)".

`IsBusinessOptimal β ρ P ψ ξ C` holds iff `ξ ∈ [0, 1]`, `C ≥ 0` and `Π(ξ, C) ≥ Π(ξ', C')` for every
`ξ' ∈ [0, 1]`, `C' ≥ 0`, with `Π` the profit (2) at the subgame outcome (3).

**Formalization Note.** This is a predicate (the set of maximizers), not a selected value, so
statements about it range over every maximizer. The feasible set includes the boundary `C = 0`. -/
def IsBusinessOptimal (β ρ P ψ ξ C : ℝ) : Prop :=
  ξ ∈ Set.Icc (0 : ℝ) 1 ∧ 0 ≤ C ∧
    ∀ ξ' C' : ℝ, ξ' ∈ Set.Icc (0 : ℝ) 1 → 0 ≤ C' → profit β ρ P ψ ξ' C' ≤ profit β ρ P ψ ξ C

end DigitalPrivacy.DataStrategy


