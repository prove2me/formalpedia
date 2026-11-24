-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_GateSwitchBounds
-- name    : Sensitivity214439_Phase0_Solutions_GateSwitchBounds
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T13:06:31.074845+00:00
-- url     : https://prove2.me/theorems/f8ff1851-81fa-4d2b-a4a6-81acd0dd0a45
-- title:
--   Forbidden cutoffs and uniform target floors for switching
-- statement:
--   A recipe at rank $j$ forbids a cutoff $g$ when either its soft allowance is zero and its soft cutoff is at most $g$, or its hard cutoff is at most $g$:
--   $$
--   \operatorname{ForbidsAt}(j,g)
--   \iff(q_j=0\land s_j\le g)\ \lor\ h_j\le g.
--   $$
--   It has target floor $t$ at $j$ when every assignment permitted by any legal failure count requires every side to reach at least $t$. These two predicates express the quiet-guard and positive-target facts needed in a color-switch argument.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/GateSwitchBounds.lean lines 19–24; SHA256 804ec6f1d7d467e7f7109cc54706c22f4f6569ca97a4a12a476dda1116971747; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

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

namespace SensitivityGateSwitchBounds
end SensitivityGateSwitchBounds
namespace SensitivityGuardEvents
end SensitivityGuardEvents
namespace SensitivityProfile456
end SensitivityProfile456
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction
namespace SensitivitySocketEventSupport
end SensitivitySocketEventSupport
namespace SensitivityStrictGateStates
end SensitivityStrictGateStates



/-!
Strict identity switches between different parent rows are supported on one
child socket selected by a separating guard. In the lowering orientation the
child B profile pays for the event. In the raising orientation the unary A
profile suffices, while an unchanged paired mate fixes the child color and
permits the sharper C profile.
-/
namespace SensitivityGateSwitchBounds

noncomputable section
open scoped Classical
open SensitivityRankedConstruction SensitivityProfile456 SensitivityGuardEvents
open SensitivityStrictGateStates SensitivitySocketEventSupport

variable {V S I Color : Type} {L core : ℕ}

def ForbidsAt (recipe : GateRecipe S L) (j cutoff : Fin L) : Prop :=
  (recipe.allowance j = 0 ∧ recipe.soft j ≤ cutoff.val) ∨ recipe.hard j ≤ cutoff.val

def TargetsAt (recipe : GateRecipe S L) (j target : Fin L) : Prop :=
  ∀ f, f ≤ recipe.allowance j →
    ∀ assignment ∈ recipe.targets j f, ∀ s, target ≤ assignment s






















end
end SensitivityGateSwitchBounds


