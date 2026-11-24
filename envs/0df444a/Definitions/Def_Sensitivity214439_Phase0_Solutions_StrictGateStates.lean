-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_StrictGateStates
-- name    : Sensitivity214439_Phase0_Solutions_StrictGateStates
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T13:19:42.2693+00:00
-- url     : https://prove2.me/theorems/48a69ca9-8f8c-4d02-aece-51fe48a0dd0a
-- title:
--   Weighted representation of strict gate failures
-- statement:
--   A strict guard shape is either a disabled hard cutoff $L$ with soft allowance zero, or a hard cutoff below $L$ with allowance one and soft cutoff no larger than the hard cutoff. The effective hard cutoff equals the hard cutoff when enabled and the soft cutoff otherwise.
--
--   A guard of height $h$ receives weight
--   $$
--   \mathbf1_{s_j<h}+\mathbf1_{h_j^{\rm eff}<h},
--   $$
--   and a row's weighted failure count is the sum over its checks. Paired scalar acceptance at weight $f$ means
--   $$
--   f\le1,\qquad
--   \ell_j(f)<\min(h_0,h_1),\qquad
--   u_j(f)<\max(h_0,h_1).
--   $$
--   This finite predicate records the strict guard conditions together with the matching target requirements.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/StrictGateStates.lean lines 21–191; SHA256 8a707cceb665a7f88c56310be7495b8933682225933379f4c87f2becce290cbf; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_FiniteRanks
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
namespace SensitivityStrictGateStates
end SensitivityStrictGateStates
namespace SensitivityTargetEvents
end SensitivityTargetEvents



/-!
Exact finite-state semantics for the strict rows in the P/J recurrences.
Ordinary strict rows have zero tolerance and a disabled hard cutoff; warm
strict rows have allowance one and a finite hard cutoff. Both are represented
by the source's sum of two indicator weights, with legal total at most one.
-/
namespace SensitivityStrictGateStates

noncomputable section
open scoped Classical BigOperators
open SensitivityRankedConstruction SensitivityProfile456 SensitivityGuardEvents
open SensitivityFiniteRanks SensitivityTargetEvents
set_option autoImplicit false

variable {I Color V S : Type} {L : ℕ}

def StrictGuardShape (recipe : GateRecipe S L) (j : Fin L) : Prop :=
  (recipe.hard j = L ∧ recipe.allowance j = 0) ∨
    (recipe.hard j < L ∧ recipe.allowance j = 1 ∧ recipe.soft j ≤ recipe.hard j)

def effectiveHard (recipe : GateRecipe S L) (j : Fin L) : ℕ :=
  if recipe.hard j < L then recipe.hard j else recipe.soft j

def guardWeight (recipe : GateRecipe S L) (j : Fin L) (height : ℕ) : ℕ :=
  (if recipe.soft j < height then 1 else 0) +
    (if effectiveHard recipe j < height then 1 else 0)

def weightCount (row : RowFamily I Color L) (guards : GuardFamily V S)
    (recipe : GateRecipe S L) (v : V) (j : Fin L) (x : ((V × S) × I) → Bool) : ℕ :=
  ∑ check ∈ guards v, guardWeight recipe j (guardHeight row x check)

























def pairedStateAccepts (lo hi : Fin L → ℕ → Fin L) (j : Fin L)
    (failures leftHeight rightHeight : ℕ) : Prop :=
  failures ≤ 1 ∧
  (lo j failures).val < min leftHeight rightHeight ∧
  (hi j failures).val < max leftHeight rightHeight

instance (lo hi : Fin L → ℕ → Fin L) (j : Fin L)
    (failures leftHeight rightHeight : ℕ) :
    Decidable (pairedStateAccepts lo hi j failures leftHeight rightHeight) := by
  unfold pairedStateAccepts
  infer_instance

















end
end SensitivityStrictGateStates


