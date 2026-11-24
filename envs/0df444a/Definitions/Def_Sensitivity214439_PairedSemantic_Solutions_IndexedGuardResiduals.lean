-- Prove2me | Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_IndexedGuardResiduals
-- name    : Sensitivity214439_PairedSemantic_Solutions_IndexedGuardResiduals
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T19:45:50.50582+00:00
-- url     : https://prove2.me/theorems/b3ea6fa7-d375-4ac0-aadf-a9c11805632b
-- title:
--   Active destinations and destinations outside the high set
-- statement:
--   Defines positiveDestinations as the outgoing arc destinations whose indexed check is active at the cutoff. outsideDestinations removes the selected high set from those destinations. These sets give actual finite versions of the residual guard budgets.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/IndexedGuardResiduals.lean lines 16–25; SHA256 a4046b847e979818a00c6068b7044053500d72171b28fe88aa4867023fb587e5; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_HighHeadGuardBridge
import Definitions.Def_Sensitivity214439_Phase0_Solutions_RankedBooleanConstruction
import Definitions.Def_Sensitivity214439_Phase0_Solutions_SocketGateConstruction
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SensitivityGlobalGainAccounting
end SensitivityGlobalGainAccounting
namespace SensitivityGuardEvents
end SensitivityGuardEvents
namespace SensitivityHighHeadGuardBridge
end SensitivityHighHeadGuardBridge
namespace SensitivityIndexedGuardResiduals
end SensitivityIndexedGuardResiduals
namespace SensitivityOperativeHeads
end SensitivityOperativeHeads
namespace SensitivityOrdinarySingleGain
end SensitivityOrdinarySingleGain
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction



/-! The residual record field counts the positive guards whose destinations
are outside the high-head set. Each destination corresponds to one check. -/
namespace SensitivityIndexedGuardResiduals

noncomputable section
open scoped Classical BigOperators
open SensitivityRankedConstruction SensitivityGuardEvents SensitivityHighHeadGuardBridge
open SensitivityGlobalGainAccounting SensitivityOrdinarySingleGain SensitivityOperativeHeads
set_option autoImplicit false

variable {V S I Color : Type} {L : ℕ}

def positiveDestinations [Fintype V]
    (row : RowFamily I Color L) {guards : GuardFamily V S} {arc : V → V → Prop}
    (idx : GuardIndexing guards arc) (v : V) (cutoff : ℕ) (x : ((V × S) × I) → Bool) : Finset V :=
  Finset.univ.filter fun w => arc v w ∧ guardActive row cutoff x (idx.check v w)

def outsideDestinations [Fintype V]
    (row : RowFamily I Color L) {guards : GuardFamily V S} {arc : V → V → Prop}
    (idx : GuardIndexing guards arc) (H : Finset V) (v : V) (cutoff : ℕ)
    (x : ((V × S) × I) → Bool) : Finset V :=
  (positiveDestinations row idx v cutoff x).filter fun w => w ∉ H


















end
end SensitivityIndexedGuardResiduals


