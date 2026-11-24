-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_GuardEvents
-- name    : Sensitivity214439_Phase0_Solutions_GuardEvents
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T17:59:22.271301+00:00
-- url     : https://prove2.me/theorems/d5b79cd9-af4e-48c6-ac65-3d8e00f0f5d9
-- title:
--   OR-guard rise and drop coordinates with disjoint checks
-- statement:
--   For an OR guard $Q$, input $x$, and natural cutoff $a$, define its rising coordinates to be all parent bit coordinates whose flip makes $Q$ active, and its dropping coordinates to be all coordinates whose flip makes $Q$ inactive:
--   $$
--   R_a(Q,x)=\{b:\operatorname{active}_a(Q,\operatorname{flip}_b x)\},
--   \qquad
--   D_a(Q,x)=\{b:\neg\operatorname{active}_a(Q,\operatorname{flip}_b x)\}.
--   $$
--   The definitions specify the resulting state; the corresponding event bounds supply the old quietness or activity hypothesis. A guard family has disjoint checks when distinct checks of each one row inspect disjoint socket sets.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/GuardEvents.lean lines 69–181; SHA256 1b56a6abbd5030bdbdb802bf315aabc9ab7788e424e99c93e27a407937d81993; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_RankedBooleanConstruction
import Definitions.Def_Sensitivity214439_Phase0_Solutions_SocketGateConstruction
import Definitions.Def_SensitivitySeparation
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

namespace SensitivityGuardEvents
end SensitivityGuardEvents
namespace SensitivityJointEvents
end SensitivityJointEvents
namespace SensitivityProfile456
end SensitivityProfile456
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction



/-! One-bit guard events on actual independent Boolean sockets. -/
namespace SensitivityGuardEvents

noncomputable section
open scoped Classical BigOperators
open SensitivityRankedConstruction SensitivityProfile456 SensitivityJointEvents
set_option autoImplicit false

variable {V S I Color : Type} {L : ℕ}









def droppingCoordinates [Fintype V] [Fintype S] [Fintype I]
    (row : RowFamily I Color L) (cutoff : ℕ)
    (x : ((V × S) × I) → Bool) (check : Finset (V × S)) : Finset ((V × S) × I) :=
  Finset.univ.filter fun bit => ¬ guardActive row cutoff (OAI.Paper320.flip x {bit}) check





def risingCoordinates [Fintype V] [Fintype S] [Fintype I]
    (row : RowFamily I Color L) (cutoff : ℕ)
    (x : ((V × S) × I) → Bool) (check : Finset (V × S)) : Finset ((V × S) × I) :=
  Finset.univ.filter fun bit => guardActive row cutoff (OAI.Paper320.flip x {bit}) check





/-- Distinct checks of one row inspect disjoint child sockets. This is the
precise support condition needed for a single-bit change to affect one check. -/
def DisjointChecks (guards : GuardFamily V S) : Prop :=
  ∀ v a, a ∈ guards v → ∀ b, b ∈ guards v → a ≠ b → Disjoint a b


















end
end SensitivityGuardEvents


