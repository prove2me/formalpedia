-- Prove2me | Definitions.Def_DworczakDACC_potential
-- name    : DworczakDACC_potential
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:51:43.456263+00:00
-- url     : https://prove2.me/theorems/6c630ecc-7de0-4733-b824-1a3c886ff632
-- title:
--   Distance to stability $d(\mathcal B,\mu)=\sum_i d_i(\mathcal B,\mu)$
-- statement:
--   The **distance to stability** of a state is
--
--   $$d(\mathcal B,\mu)=\sum_{i\in N} d_i(\mathcal B,\mu),$$
--
--   the sum of the individual distances over all men and women. This is equation (3.2); the paper uses it as the potential function in the termination proof.
-- source:
--   Dworczak, Deferred Acceptance with Compensation Chains (working paper, Nov 9, 2017), eq. (3.2), p. 10

import Mathlib
import Definitions.Def_RuralHospitals_Market
import Definitions.Def_DworczakDACC_State
import Definitions.Def_DworczakDACC_agentPotential

namespace DworczakDACC

open RuralHospitals

variable {D H : Type*} [Fintype D] [Fintype H] [DecidableEq D] [DecidableEq H]

/-- **The distance to stability `d(B, µ) = Σ_{i ∈ N} dᵢ(B, µ)`.**
Dworczak, *Deferred Acceptance with Compensation Chains* (working paper, Nov 9, 2017),
eq. (3.2), p. 10.

`potential Mk s` is the sum of `agentPotential Mk s i` over all agents `i ∈ N = D ⊕ H`. -/
def potential (Mk : Market D H) (s : State D H) : ℕ :=
  ∑ i : D ⊕ H, agentPotential Mk s i

end DworczakDACC


