-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_GateEventAggregation
-- name    : Sensitivity214439_Phase0_Solutions_GateEventAggregation
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T13:06:26.534801+00:00
-- url     : https://prove2.me/theorems/5023b063-10f3-404a-8f08-7123c9097990
-- title:
--   Occupied guard checks at a given cutoff
-- statement:
--   For a row $v$ and input $x$, the occupied-check set at cutoff $j$ is
--   $$
--   \operatorname{occupiedChecks}(v,j,x)
--   =\{Q\in\mathcal G_v:\operatorname{guardActive}(j,x,Q)\}.
--   $$
--   A check is retained when at least one of its child sockets passes the cutoff. This finite set is used to partition guard contributions into occupied and cold terms.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/GateEventAggregation.lean lines 49–52; SHA256 2b789d437d944ed0a543c0e39154df06370145557fe83be53a19f8a9caa974e9; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_RankedBooleanConstruction
import Definitions.Def_Sensitivity214439_Phase0_Solutions_SocketGateConstruction
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Range
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SensitivityFiniteRanks
end SensitivityFiniteRanks
namespace SensitivityGateEventAggregation
end SensitivityGateEventAggregation
namespace SensitivityGuardEvents
end SensitivityGuardEvents
namespace SensitivityGuardFeeAggregation
end SensitivityGuardFeeAggregation
namespace SensitivityJointEvents
end SensitivityJointEvents
namespace SensitivityLocalNumericSemantics
end SensitivityLocalNumericSemantics
namespace SensitivityPairedGuardNumericSlices
end SensitivityPairedGuardNumericSlices
namespace SensitivityProfile456
end SensitivityProfile456
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction
namespace SensitivitySocketEventSupport
end SensitivitySocketEventSupport



/-! Summing exact own-socket and guard slices, with physical guard slots. -/
namespace SensitivityGateEventAggregation

noncomputable section
open scoped Classical BigOperators
open SensitivityRankedConstruction SensitivityProfile456 SensitivityJointEvents
open SensitivityFiniteRanks SensitivityGuardEvents SensitivitySocketEventSupport
open SensitivityLocalNumericSemantics SensitivityPairedGuardNumericSlices
open SensitivityGuardFeeAggregation
set_option autoImplicit false







def occupiedChecks {I Color V S : Type} {L : ℕ}
    (row : RowFamily I Color L) (guards : GuardFamily V S) (v : V)
    (cutoff : Fin L) (x : ((V × S) × I) → Bool) : Finset (Finset (V × S)) :=
  (guards v).filter (guardActive row cutoff.val x)





















end
end SensitivityGateEventAggregation


