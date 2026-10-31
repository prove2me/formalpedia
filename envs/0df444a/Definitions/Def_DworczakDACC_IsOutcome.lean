-- Prove2me | Definitions.Def_DworczakDACC_IsOutcome
-- name    : DworczakDACC_IsOutcome
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:54:59.393639+00:00
-- url     : https://prove2.me/theorems/78f9e353-b441-4857-a8db-99062ba33d5b
-- title:
--   $\mu$ is the outcome of DACC($\Phi$)
-- statement:
--   A matching $\mu$ is the **outcome** of DACC($\Phi$) (with (a)/(b) order $\operatorname{ord}$) when the run stops in finite time with matching $\mu$: there is a time $t$ at which the run satisfies the stopping criterion and its matching is $\mu$.
--
--   Because the run is frozen once it stops, the outcome does not depend on which stopped time is chosen.
--
--   **Formalization Note** A matching is a function from men to $\text{Option}$ women (`RuralHospitals.Assignment`), read off the men's side of the state.
-- source:
--   Dworczak, Deferred Acceptance with Compensation Chains (working paper, Nov 9, 2017), Theorem 1, p. 7

import Mathlib
import Definitions.Def_RuralHospitals_Market
import Definitions.Def_DworczakDACC_Stopped
import Definitions.Def_DworczakDACC_run

namespace DworczakDACC

open RuralHospitals

variable {D H : Type*} [Fintype D] [Fintype H] [DecidableEq D] [DecidableEq H]

/-- **`µ` is the outcome of DACC(Φ): the run stops in finite time with matching `µ`.**
Dworczak, *Deferred Acceptance with Compensation Chains* (working paper, Nov 9, 2017),
Theorem 1, p. 7 ("DACC(Φ) stops in finite time and its outcome µ").

`IsOutcome Mk Φ ord μ` holds when at some time `t` the run `run Mk Φ ord` satisfies the stopping
criterion and its matching (seen from the men's side) is `μ`.

**Formalization Note.** A matching is `RuralHospitals.Assignment D H = D → Option H` (man ↦ his
partner or `∅`). The run is frozen once it stops, so the outcome does not depend on the stopped
time chosen. `ord` resolves footnote a's (a)/(b) order per time step. -/
def IsOutcome (Mk : Market D H) (Φ : ℕ → D ⊕ H) (ord : ℕ → Bool) (μ : Assignment D H) : Prop :=
  ∃ t, Stopped Mk (run Mk Φ ord t) ∧ (run Mk Φ ord t).mateM = μ

end DworczakDACC


