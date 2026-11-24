-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_GuardIntervalCertificates
-- name    : Sensitivity214439_Phase0_Solutions_GuardIntervalCertificates
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T18:10:53.115698+00:00
-- url     : https://prove2.me/theorems/f4f7d4c5-28f1-4393-8cee-68e9e974fb8a
-- title:
--   Two-tail height certificates for guard events
-- statement:
--   For a family with $L$ ranks, a new guard height $h$ hits the interval certificate with endpoints $u,d$ when
--   $$
--   (u<L\land u<h)\ \lor\ (d<L\land h\le d).
--   $$
--   An endpoint at least $L$ disables its corresponding tail. A guard-interval cover requires every bad replacement height in $\{0,\ldots,L\}$ to satisfy this condition. The associated coordinate set is the union of guard rises above $u$ and guard drops to at most $d$, with disabled terms omitted.
--
--   For paired and unary strict states, the bad-replacement predicates mean that substituting the fresh guard weight either destroys weak acceptance or creates strong acceptance. The definitions hold the other guard weights and target heights fixed, and all finite predicates have decidable instances.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/GuardIntervalCertificates.lean lines 20–156; SHA256 2e6fe22248547f3c8d9dfaa98eede2866ab475a66e6d0d58326609e8a134e3e2; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_GuardEvents
import Definitions.Def_Sensitivity214439_Phase0_Solutions_LocalConfigurationCoverage
import Definitions.Def_Sensitivity214439_Phase0_Solutions_RankedBooleanConstruction
import Definitions.Def_Sensitivity214439_Phase0_Solutions_SocketGateConstruction
import Definitions.Def_Sensitivity214439_Phase0_Solutions_StrictGateStates
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
namespace SensitivityGuardIntervalCertificates
end SensitivityGuardIntervalCertificates
namespace SensitivityJointEvents
end SensitivityJointEvents
namespace SensitivityLocalConfigurationCoverage
end SensitivityLocalConfigurationCoverage
namespace SensitivityProfile456
end SensitivityProfile456
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction
namespace SensitivitySocketEventSupport
end SensitivitySocketEventSupport
namespace SensitivityStrictGateStates
end SensitivityStrictGateStates



/-!
Sound finite certificates for the rise/bot thresholds in the local recurrence.
The sentinel L disables a direction. Every possible fresh guard height is
checked, so correctness does not rely on trusting the Python `next` search.
-/
namespace SensitivityGuardIntervalCertificates

noncomputable section
open scoped Classical
open SensitivityRankedConstruction SensitivityProfile456 SensitivityJointEvents
open SensitivityGuardEvents SensitivityFiniteRanks SensitivityStrictGateStates
open SensitivitySocketEventSupport SensitivityLocalConfigurationCoverage
set_option autoImplicit false

variable {V S I Color : Type} {L core : ℕ}

def intervalHit (L top bot height : ℕ) : Prop :=
  (top < L ∧ top < height) ∨ (bot < L ∧ height ≤ bot)

instance (L top bot height : ℕ) : Decidable (intervalHit L top bot height) := by
  unfold intervalHit
  infer_instance

def GuardIntervalCover (L : ℕ) (bad : Fin (L+1) → Prop) (top bot : ℕ) : Prop :=
  ∀ fresh, bad fresh → intervalHit L top bot fresh.val

instance (L : ℕ) (bad : Fin (L+1) → Prop) [DecidablePred bad] (top bot : ℕ) :
    Decidable (GuardIntervalCover L bad top bot) := by
  unfold GuardIntervalCover
  infer_instance

def intervalCoordinates [Fintype V] [Fintype S] [Fintype I]
    (row : RowFamily I Color L) (top bot : ℕ)
    (x : ((V × S) × I) → Bool) (check : Finset (V × S)) : Finset ((V × S) × I) :=
  (if top < L then risingCoordinates row top x check else ∅) ∪
    (if bot < L then droppingCoordinates row bot x check else ∅)



def pairedGuardBad (recipe : GateRecipe Bool L) (lo hi : Fin L → ℕ → Fin L)
    (weak strong : Fin L) (weakRest strongRest leftHeight rightHeight : ℕ)
    (fresh : Fin (L+1)) : Prop :=
  ¬ pairedStateAccepts lo hi weak (weakRest + guardWeight recipe weak fresh.val) leftHeight rightHeight ∨
    pairedStateAccepts lo hi strong (strongRest + guardWeight recipe strong fresh.val) leftHeight rightHeight

instance (recipe : GateRecipe Bool L) (lo hi : Fin L → ℕ → Fin L)
    (weak strong : Fin L) (weakRest strongRest leftHeight rightHeight : ℕ)
    (fresh : Fin (L+1)) :
    Decidable (pairedGuardBad recipe lo hi weak strong weakRest strongRest leftHeight rightHeight fresh) := by
  unfold pairedGuardBad
  infer_instance





def unaryGuardBad (recipe : GateRecipe Unit L) (target : Fin L → ℕ → Fin L)
    (weak strong : Fin L) (weakRest strongRest targetHeight : ℕ)
    (fresh : Fin (L+1)) : Prop :=
  ¬ unaryStateAccepts target weak (weakRest + guardWeight recipe weak fresh.val) targetHeight ∨
    unaryStateAccepts target strong (strongRest + guardWeight recipe strong fresh.val) targetHeight

instance (recipe : GateRecipe Unit L) (target : Fin L → ℕ → Fin L)
    (weak strong : Fin L) (weakRest strongRest targetHeight : ℕ)
    (fresh : Fin (L+1)) :
    Decidable (unaryGuardBad recipe target weak strong weakRest strongRest targetHeight fresh) := by
  unfold unaryGuardBad
  infer_instance










end
end SensitivityGuardIntervalCertificates


