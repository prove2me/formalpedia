-- Prove2me | solution 2 for A166944Research.a166944_record_is_greater_twin_prime
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tara_sooo
-- created : 2026-11-15T06:32:23.510203+00:00
-- url     : https://prove2.me/submissions/3db922d4-94f6-4084-a5b9-dd6d258677b8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_a166944_moving_horizon
import Theorems.Thm_A166944Research_a166944_horizon_cap_from_45895573
import Theorems.Thm_A166944Research_a166944_relaxed_index_cap
import Theorems.Thm_A166944Research_a166944_target_of_two_caps

/-!
Reduction of `a166944_record_is_greater_twin_prime` to the two relaxed caps.

The parent is the A166944 record/twin-prime statement, with no arguments. Three
children compose to give it:

  * `a166944_horizon_cap_from_45895573`  -- the horizon cap `Cf <= 3*M + 4`;
  * `a166944_relaxed_index_cap`          -- the index cap `4*sf <= 7*M - 1`;
  * `a166944_target_of_two_caps`         -- those two caps imply the parent.

The composition is direct because the children are stated at the threshold the
parent needs: no argument has to be threaded.

## What this changes for the frontier

Before this reduction the route's frontier was the single stronger inequality
`2 * (sf - (M + 2)) <= M`, the travel bound. After it the frontier is the pair of
caps, and each can be attacked on its own.

The second cap is strictly weaker than the travel bound: travel gives
`4*sf <= 6*M + 8`, so the relaxation is `M/4`, about 11.5 million at the threshold
45895573. The pair does not imply the travel bound -- at `M = 45895573` the pair
`(sf, Cf) = (80317252, 137686723)` satisfies both caps and violates travel -- so
this is a genuine weakening rather than a restatement, and a proof of either cap is
not a proof of the old target in disguise.

One structural gain comes with the split: the case analysis inside the argument has
a branch where the replay crosses the record, and that branch is discharged by an
existing theorem about horizon growth using only the first cap. Only the quiet
branch consumes the second.

Note the direction: this file does not assume the conjecture. It shows that the
parent follows from children that are themselves Open.
-/

open A166944Research

theorem solution :
    ∀ R : Nat, 5 < R → IsDifferenceRecord R → IsGreaterTwinPrime R :=
  a166944_target_of_two_caps
    a166944_horizon_cap_from_45895573
    a166944_relaxed_index_cap
