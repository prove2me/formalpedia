-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_JointEvents
-- name    : Sensitivity214439_Phase0_Solutions_JointEvents
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T18:12:00.888595+00:00
-- url     : https://prove2.me/theorems/bfe63bc9-77a0-4a0b-8c2e-b310ffb45f51
-- title:
--   Promotion and joint-event auxiliary profiles
-- statement:
--   For one color $c$, weak rank $w$, and strong rank $n$, the joint event set is
--   $$
--   J_c(w,n,x)
--   =\operatorname{rowLoss}_c(w,x)\cup\operatorname{rowGain}_c(n,x).
--   $$
--   An auxiliary profile above core $k$ consists of promotion bounds $P(a,n)$ and joint bounds $J(w,a,n)$. At an input of exact global rank $a$, with color $c$ accepted at $a$, it bounds promotions to $n>a$ and the preceding union whenever $k\le w\le a<n$.
--
--   The next-below rank is $a+1$ as a valid finite rank whenever $a<n$; it is automatically at most $n$.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/JointEvents.lean lines 22–96; SHA256 77adfc64e67c1c82af4d6b11d914caa1f4f1ed27550479945276c31cf69b064b; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_Profile456
import Definitions.Def_Sensitivity214439_Phase0_Solutions_RankedBooleanConstruction
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SensitivityJointEvents
end SensitivityJointEvents
namespace SensitivityProfile456
end SensitivityProfile456
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction



/-!
Actual event-set lemmas for the promotion, joint-loss and marked-socket
refinements. These lemmas prove semantic inclusions, rather than replacing
the construction by an assumed numerical recurrence.
-/

namespace SensitivityJointEvents

noncomputable section
open scoped Classical
open SensitivityRankedConstruction SensitivityProfile456

set_option autoImplicit false

variable {I Color : Type} {L : ℕ} [Fintype I]

def jointEvents (row : RowFamily I Color L) (c : Color) (weak strong : Fin L)
    (x : I → Bool) : Finset I :=
  rowLossEvents row c weak x ∪ rowGainEvents row c strong x







def nextBelow (a n : Fin L) (han : a < n) : Fin L :=
  ⟨a.val + 1, (Nat.succ_le_of_lt han).trans_lt n.isLt⟩



theorem nextBelow_le (a n : Fin L) (han : a < n) : nextBelow a n han ≤ n :=
  Nat.succ_le_of_lt han









structure AuxiliaryBounds (row : RowFamily I Color L) (core : ℕ)
    (promotion : Fin L → Fin L → ℝ) (joint : Fin L → Fin L → Fin L → ℝ) : Prop where
  promotion : ∀ c x a n, core ≤ a.val → a < n → ExactGlobalRank row a x → row c a x →
    ((rowGainEvents row c n x).card : ℝ) ≤ promotion a n
  joint : ∀ c x weak a n, core ≤ weak.val → weak ≤ a → a < n →
    ExactGlobalRank row a x → row c a x →
    ((jointEvents row c weak n x).card : ℝ) ≤ joint weak a n

































end
end SensitivityJointEvents


