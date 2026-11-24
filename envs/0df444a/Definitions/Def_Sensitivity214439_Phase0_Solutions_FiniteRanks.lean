-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_FiniteRanks
-- name    : Sensitivity214439_Phase0_Solutions_FiniteRanks
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T13:06:28.323466+00:00
-- url     : https://prove2.me/theorems/11cf061f-7b06-4242-a385-723fd35798aa
-- title:
--   Maximum accepted heights of children and OR guards
-- statement:
--   For a colored family with ranks $0,\ldots,L-1$, define
--   $$
--   h_F(x)=\max\bigl(\{r+1:F\text{ accepts }r\text{ at }x\}\cup\{0\}\bigr).
--   $$
--   The height of a finite OR guard is the maximum of its child socket heights, with zero for an empty guard. Both heights are at most $L$. At a chosen cutoff $j$, the occupied-height list records one height for each active guard check; repeated heights remain repeated entries because distinct checks are counted separately.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/FiniteRanks.lean lines 18–165; SHA256 5b8683b5ea607ba70428c9c2d448954bbb81198e4f3a3b0466ad29e78fcecf41; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_RankedBooleanConstruction
import Definitions.Def_Sensitivity214439_Phase0_Solutions_SocketGateConstruction
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
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

namespace SensitivityFiniteRanks
end SensitivityFiniteRanks
namespace SensitivityGuardEvents
end SensitivityGuardEvents
namespace SensitivityProfile456
end SensitivityProfile456
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction



/-!
Finite rank states for actual nested Boolean families. Height zero is the
all-false state; height r+1 is exact rank r. This makes every enumerated state
finite without encoding the all-false case by truncated natural subtraction.
-/
namespace SensitivityFiniteRanks

noncomputable section
open scoped Classical
open SensitivityRankedConstruction SensitivityProfile456 SensitivityGuardEvents
set_option autoImplicit false

variable {I Color V S : Type} {L : ℕ}

def rankHeight (row : RowFamily I Color L) (x : I → Bool) : ℕ :=
  Finset.univ.sup fun r : Fin L => if accepts row r x then r.val + 1 else 0

theorem rankHeight_le (row : RowFamily I Color L) (x : I → Bool) :
    rankHeight row x ≤ L := by
  apply Finset.sup_le
  intro r _
  split
  · exact Nat.succ_le_of_lt r.isLt
  · exact Nat.zero_le _













def guardHeight (row : RowFamily I Color L)
    (x : ((V × S) × I) → Bool) (check : Finset (V × S)) : ℕ :=
  check.sup fun socket => rankHeight row (socketInput x socket)

theorem guardHeight_le (row : RowFamily I Color L)
    (x : ((V × S) × I) → Bool) (check : Finset (V × S)) : guardHeight row x check ≤ L := by
  exact Finset.sup_le fun socket _ => rankHeight_le row (socketInput x socket)







def occupiedGuardHeights (row : RowFamily I Color L) (guards : GuardFamily V S)
    (v : V) (j : Fin L) (x : ((V × S) × I) → Bool) : List ℕ :=
  (((guards v).filter (guardActive row j.val x)).toList).map (guardHeight row x)











end
end SensitivityFiniteRanks


