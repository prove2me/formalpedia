-- Prove2me | Definitions.Def_DworczakDACC_Interacts
-- name    : DworczakDACC_Interacts
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:54:59.039517+00:00
-- url     : https://prove2.me/theorems/90b8f5fb-2ecd-4728-8de5-17bedfbde8c9
-- title:
--   Man $d$ and woman $h$ interact at time $t$
-- statement:
--   Man $d$ and woman $h$ **interact** at time $t$ of the run when, in the pass from $t$ to $t+1$,
--
--   1. the main loop runs and the applying agent (the order's proposer if $CC$ is empty, the top of $CC$ otherwise) is $d$ applying to $h$ or $h$ applying to $d$ (an actual application, not a skip); or
--   2. $d$ and $h$ are matched at time $t$ and not at time $t+1$ (a divorce).
--
--   The paper uses this notion in the proofs of Claim 1 ("$i$ applied to $j$ and was rejected, or $i$ and $j$ were matched and $j$ divorced $i$") and Claim 5, and in the definition of $X^k$.
--
--   **Formalization Note** A man–woman pair is an element of $D\times H$ (the paper's unordered pair $\{i,j\}$ with $j\in N_i$). An application to one's current partner or to $\emptyset$ ends at step 2 of "$i$ applies" and is not an interaction.
-- source:
--   Dworczak, Deferred Acceptance with Compensation Chains (working paper, Nov 9, 2017), Appendix A, p. 23; proofs of Claim 1 (pp. 7–9) and Claim 5 (p. 24)

import Mathlib
import Definitions.Def_RuralHospitals_Market
import Definitions.Def_DworczakDACC_State
import Definitions.Def_DworczakDACC_bestM
import Definitions.Def_DworczakDACC_bestW
import Definitions.Def_DworczakDACC_Stopped
import Definitions.Def_DworczakDACC_run

namespace DworczakDACC

open RuralHospitals

variable {D H : Type*} [Fintype D] [Fintype H] [DecidableEq D] [DecidableEq H]

/-- **Man `d` and woman `h` interact at time `t`.**
Dworczak, *Deferred Acceptance with Compensation Chains* (working paper, Nov 9, 2017), Appendix A,
p. 23 ("i and j never interact after round k"), with the interactions of the proof of Claim 1,
pp. 7–9 ("either (i) i applied to j and was rejected, or (ii) i and j were matched and j divorced
i") and of the proof of Claim 5, p. 24 ("l can never apply to l′ … l′ never applies to l").

`Interacts Mk Φ ord t d h` holds when, in the pass from time `t` to `t + 1`,
* the loop runs (the stopping criterion fails at `t`) and the applying agent (`Φ round` if `CC` is
  empty, the top of `CC` otherwise) is `d` applying to `h`, or `h` applying to `d` (an actual
  application: the target is the best option of the budget set and not the current partner); or
* `d` and `h` are matched at time `t` and not at time `t + 1` (a divorce).

**Formalization Note.** A man–woman pair is an element of `D × H` (the paper's unordered pair
`{i, j}` with `j ∈ Nᵢ`). An application to the current partner or to `∅` returns at step 2 of
"i applies" and is not an interaction. -/
def Interacts (Mk : Market D H) (Φ : ℕ → D ⊕ H) (ord : ℕ → Bool) (t : ℕ) (d : D) (h : H) :
    Prop :=
  let s := run Mk Φ ord t
  let a : D ⊕ H :=
    match s.stack with
    | [] => Φ s.round
    | i :: _ => i
  (¬ Stopped Mk s ∧
      ((a = Sum.inl d ∧ bestM Mk d (s.budM d) = some h ∧ s.mateM d ≠ some h) ∨
        (a = Sum.inr h ∧ bestW Mk h (s.budW h) = some d ∧ s.mateW h ≠ some d))) ∨
    (s.mateM d = some h ∧ (run Mk Φ ord (t + 1)).mateM d ≠ some h)

end DworczakDACC


