-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_OwnNaturalFees
-- name    : Sensitivity214439_Phase0_Solutions_OwnNaturalFees
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T18:12:09.380823+00:00
-- url     : https://prove2.me/theorems/185175f0-69e7-48de-9291-caf01932e55c
-- title:
--   Own promotion slices and natural-rank gains
-- statement:
--   The own promotion set for side $s$ of row $v$ consists of child coordinates whose lifted flip lies in the parent row's destination gain set. Natural-rank acceptance at $n$ means that there exists a finite rank equal to $n$ which the child accepts:
--   $$
--   \operatorname{acceptsAtNat}(n,x)
--   \iff\exists j<L,\ j=n\land F\text{ accepts }j\text{ at }x.
--   $$
--   Consequently it is false for $n\ge L$. Natural-rank gain events are the bit coordinates whose flip satisfies this predicate. The natural formulation allows unattainable sentinel ranks to be used directly in numerical fees.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/OwnNaturalFees.lean lines 33–144; SHA256 ea38e6fbd12841f52cbd4c715f78ba374be357fa9491b280e606f68d9d0c610a; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_Profile456
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

namespace SensitivityJointEvents
end SensitivityJointEvents
namespace SensitivityNaturalTargetNeeds
end SensitivityNaturalTargetNeeds
namespace SensitivityOwnNaturalFees
end SensitivityOwnNaturalFees
namespace SensitivityOwnTargetBounds
end SensitivityOwnTargetBounds
namespace SensitivityProfile456
end SensitivityProfile456
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction
namespace SensitivityStrictGateStates
end SensitivityStrictGateStates



/-! Exact own-child P/J fees, with the disabled natural target sentinel. -/
namespace SensitivityOwnNaturalFees

noncomputable section
open scoped Classical
open SensitivityRankedConstruction SensitivityProfile456 SensitivityJointEvents
open SensitivityNaturalTargetNeeds
open SensitivityStrictGateStates SensitivityOwnTargetBounds
set_option autoImplicit false

variable {I Color V S : Type} {L core : ℕ}







def ownPromotionEvents [Fintype V] [Fintype S] [Fintype I]
    (row : RowFamily I Color L) (guards : GuardFamily V S) (recipe : GateRecipe S L)
    (v : V) (n : Fin L) (x : ((V × S) × I) → Bool) (s : S) : Finset I :=
  Finset.univ.filter fun i => ((v,s),i) ∈ rowGainEvents (gateRow row guards recipe) v n x









def acceptsAtNat (row : RowFamily I Color L) (needed : ℕ) (x : I → Bool) : Prop :=
  ∃ j : Fin L, j.val = needed ∧ accepts row j x

def natGainEvents [Fintype I] (row : RowFamily I Color L)
    (needed : ℕ) (x : I → Bool) : Finset I :=
  Finset.univ.filter fun i => acceptsAtNat row needed (bitFlip x i)













end
end SensitivityOwnNaturalFees


