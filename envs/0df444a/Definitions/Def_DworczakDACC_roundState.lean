-- Prove2me | Definitions.Def_DworczakDACC_roundState
-- name    : DworczakDACC_roundState
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:55:46.723906+00:00
-- url     : https://prove2.me/theorems/e35f4fe3-543a-4efb-b07a-09e8811b82c1
-- title:
--   State at the end of round $k$: $(\mathcal B^k,\mu^k)$ and $A^k$
-- statement:
--   The state of the run at the end of round $k$. Its budget sets and matching are the paper's $(\mathcal B^k,\mu^k)$, "the budget system and matching at the end of round $k$", and its applicant sets are $A^k_i$, "the set of agents that applied to agent $i$ up to and including round $k$". Round $0$ is the initial state.
-- source:
--   Dworczak, Deferred Acceptance with Compensation Chains (working paper, Nov 9, 2017), proof of Claim 3, p. 9; Appendix A, p. 23

import Mathlib
import Definitions.Def_RuralHospitals_Market
import Definitions.Def_DworczakDACC_State
import Definitions.Def_DworczakDACC_run
import Definitions.Def_DworczakDACC_roundEnd

namespace DworczakDACC

open RuralHospitals

variable {D H : Type*} [Fintype D] [Fintype H] [DecidableEq D] [DecidableEq H]

/-- **The state at the end of round `k`: the paper's `(Bᵏ, µᵏ)` together with `Aᵏ`.**
Dworczak, *Deferred Acceptance with Compensation Chains* (working paper, Nov 9, 2017), proof of
Claim 3, p. 9 ("the budget system and matching at the end of round k") and Appendix A, p. 23
(`Aᵏᵢ` "is the set of agents that applied to agent i up to and including round k").

`roundState Mk Φ ord k = run Mk Φ ord (roundEnd Mk Φ ord k)`; `roundState … 0` is the initial
state. -/
noncomputable def roundState (Mk : Market D H) (Φ : ℕ → D ⊕ H) (ord : ℕ → Bool) (k : ℕ) :
    State D H :=
  run Mk Φ ord (roundEnd Mk Φ ord k)

end DworczakDACC


