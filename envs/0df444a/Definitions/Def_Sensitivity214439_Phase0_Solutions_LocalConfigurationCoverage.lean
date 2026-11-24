-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_LocalConfigurationCoverage
-- name    : Sensitivity214439_Phase0_Solutions_LocalConfigurationCoverage
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T13:33:04.628002+00:00
-- url     : https://prove2.me/theorems/48d067ed-cf3f-4c19-8fbe-c63931569f00
-- title:
--   Weighted strict failures and unary scalar acceptance
-- statement:
--   The failure count of a finite guard-height configuration is the sum of its strict guard weights:
--   $$
--   F_j(h_1,\ldots,h_m)=\sum_{r=1}^{m}\operatorname{guardWeight}_j(h_r).
--   $$
--   A unary scalar state with own height $h$ accepts rank $j$ when its weighted count is at most one and exceeds the corresponding target in height:
--   $$
--   F_j\le1\quad\land\quad \operatorname{target}_j(F_j)<h.
--   $$
--   The acceptance predicate is decidable.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/LocalConfigurationCoverage.lean lines 19–152; SHA256 993f80c61cb2b22cf0a441a8ed63a07cc9086adbdef1e57e5ad3ea034893f832; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

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
namespace SensitivityJointEvents
end SensitivityJointEvents
namespace SensitivityLocalConfigurationCoverage
end SensitivityLocalConfigurationCoverage
namespace SensitivityProfile456
end SensitivityProfile456
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction
namespace SensitivityStrictGateStates
end SensitivityStrictGateStates



/-!
Completeness of the finite source configurations used for the local promotion
and joint bounds. These theorems start from actual Boolean inputs and an actual
one-bit promotion. They recover the bounded list of occupied guard ranks and
the exact acceptance/rejection tests used by the source enumerator.
-/
namespace SensitivityLocalConfigurationCoverage

noncomputable section
open scoped Classical
open SensitivityRankedConstruction SensitivityProfile456 SensitivityJointEvents
open SensitivityGuardEvents SensitivityFiniteRanks SensitivityStrictGateStates
set_option autoImplicit false

variable {I Color V : Type} {L core : ℕ}

def configurationFailures {S : Type} (recipe : GateRecipe S L) (j : Fin L) (heights : List ℕ) : ℕ :=
  (heights.map (guardWeight recipe j)).sum













def unaryStateAccepts (target : Fin L → ℕ → Fin L) (j : Fin L)
    (failures height : ℕ) : Prop := failures ≤ 1 ∧ (target j failures).val < height

instance (target : Fin L → ℕ → Fin L) (j : Fin L) (failures height : ℕ) :
    Decidable (unaryStateAccepts target j failures height) := by
  unfold unaryStateAccepts
  infer_instance











end
end SensitivityLocalConfigurationCoverage


