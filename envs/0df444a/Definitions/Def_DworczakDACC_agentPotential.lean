-- Prove2me | Definitions.Def_DworczakDACC_agentPotential
-- name    : DworczakDACC_agentPotential
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:50:55.866864+00:00
-- url     : https://prove2.me/theorems/0088d3d8-ebc6-4c29-ab40-6b3292427952
-- title:
--   Individual distance to stability $d_i(\mathcal B,\mu)$
-- statement:
--   For an agent $i$ in a state with budget sets $\mathcal B=(B_j)_{j\in N}$ and matching $\mu$,
--
--   $$d_i(\mathcal B,\mu)=\bigl|\{j\in B_i:\ j\succ^i\mu(i)\}\bigr| ,$$
--
--   the number of members of $i$'s budget set that $i$ strictly prefers to its current partner (to $\emptyset$ if $i$ is unmatched). This is equation (3.1).
--
--   **Formalization Note** The paper evaluates $d_i$ at the end of rounds; here it is defined on every state.
-- source:
--   Dworczak, Deferred Acceptance with Compensation Chains (working paper, Nov 9, 2017), eq. (3.1), p. 9

import Mathlib
import Definitions.Def_RuralHospitals_Market
import Definitions.Def_DworczakDACC_State

namespace DworczakDACC

open RuralHospitals

variable {D H : Type*} [Fintype D] [Fintype H] [DecidableEq D] [DecidableEq H]

/-- **The individual distance to stability `dᵢ(B, µ) = |{j ∈ Bᵢ : j ≻ⁱ µ(i)}|`.**
Dworczak, *Deferred Acceptance with Compensation Chains* (working paper, Nov 9, 2017),
eq. (3.1), p. 9: "The function dᵢ counts the agents in i's budget set that i prefers to his or her
current match" (p. 10).

`agentPotential Mk s i` is the number of members `j` of `i`'s budget set in state `s` that `i`
strictly prefers to its current partner `µ(i)` (to `∅` if `i` is unmatched).

**Formalization Note.** The paper evaluates `dᵢ` at end-of-round budget systems `(Bᵏ, µᵏ)`; here
it is defined on any state, and `roundState` supplies the end-of-round states. -/
def agentPotential (Mk : Market D H) (s : State D H) : D ⊕ H → ℕ
  | Sum.inl d =>
    ((s.budM d).filter (fun h => Mk.docRank d (some h) < Mk.docRank d (s.mateM d))).card
  | Sum.inr h =>
    ((s.budW h).filter (fun d => Mk.hospRank h (some d) < Mk.hospRank h (s.mateW h))).card

end DworczakDACC


