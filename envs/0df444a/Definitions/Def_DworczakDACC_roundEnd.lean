-- Prove2me | Definitions.Def_DworczakDACC_roundEnd
-- name    : DworczakDACC_roundEnd
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:54:50.795797+00:00
-- url     : https://prove2.me/theorems/c379f670-03b2-4e04-a92d-a942238f68e8
-- title:
--   End time of round $k$ of DACC($\Phi$)
-- statement:
--   Round $k\ge1$ of DACC($\Phi$) consists of the application of $\Phi(k)$ (paper numbering) together with the compensation chains it triggers. The round **ends** at the first time at which at least $k$ order-proposals have been made and the stack $CC$ is empty, or at the first stopped time if the algorithm stops earlier. Round $0$ ends at time $0$.
--
--   **Formalization Note** Defined as an infimum over $\mathbb N$. The set is nonempty because every compensation chain stops (Claim 2), so the convention $\inf\emptyset=0$ is never used. If the algorithm stops inside a round, every later round ends at the first stopped time.
-- source:
--   Dworczak, Deferred Acceptance with Compensation Chains (working paper, Nov 9, 2017), proof of Claim 3, p. 9; Appendix A, p. 23

import Mathlib
import Definitions.Def_RuralHospitals_Market
import Definitions.Def_DworczakDACC_Stopped
import Definitions.Def_DworczakDACC_run

namespace DworczakDACC

open RuralHospitals

variable {D H : Type*} [Fintype D] [Fintype H] [DecidableEq D] [DecidableEq H]

/-- **The time at which round `k` of DACC(Φ) ends.**
Dworczak, *Deferred Acceptance with Compensation Chains* (working paper, Nov 9, 2017), proof of
Claim 3, p. 9: "let (Bᵏ, µᵏ) be the budget system and matching at the end of round k"; Appendix A,
p. 23: "I use the superscript k to denote sets at the end of round k".

`roundEnd Mk Φ ord k` is the first time `t` at which either the run has stopped, or at least `k`
order-proposals have been made and the stack `CC` is empty (all compensation chains of round `k`
are over). Round `k ≥ 1` of the paper is the application of `Φ (k - 1)` (0-based `Φ`) together
with the compensation chains it causes; `roundEnd … 0 = 0` is the initial state.

**Formalization Note.** `sInf ∅ = 0` in `ℕ`; the set is nonempty because every compensation chain
ends (Claim 2, milestone `claim_2`), so this junk value is never the one used. If the run stops
inside a round, every later `roundEnd` is the first stopped time, and the end-of-round state is the
final state. -/
noncomputable def roundEnd (Mk : Market D H) (Φ : ℕ → D ⊕ H) (ord : ℕ → Bool) (k : ℕ) : ℕ :=
  sInf {t | Stopped Mk (run Mk Φ ord t) ∨
    (k ≤ (run Mk Φ ord t).round ∧ (run Mk Φ ord t).stack = [])}

end DworczakDACC


