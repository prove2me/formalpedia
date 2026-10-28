-- Prove2me | Definitions.Def_Sensitivity213981Formal_ActualCapPrefix
-- name    : Sensitivity213981Formal_ActualCapPrefix
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T19:58:27.025762+00:00
-- url     : https://prove2.me/theorems/3a771636-3fc3-4697-a36e-6fe523660fdc
-- title:
--   Actual Cap Prefix — sensitivity certificate definitions
-- statement:
--   The definitions for Actual Cap Prefix in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundActualCaps.CapsSound`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; ActualCapPrefix.lean, lines 1–118.

import Definitions.Def_Sensitivity213981Formal_ActualPrefixCaps
import Definitions.Def_Sensitivity213981Formal_GlobalAccounting
import Definitions.Def_Sensitivity213981Formal_GradedCandidates
import Definitions.Def_Sensitivity213981Formal_HeadCostExpressions
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Q2EnumerationBridge
import Definitions.Def_Sensitivity213981Formal_Q2RawExpressions
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Sensitivity213981Formal
section
/- All numerical prefix constraints hold for the actual candidate record. -/


set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 10000

namespace ThreeBoundActualCaps
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundGradedCandidates
open ThreeBoundGradedCover ThreeBoundActualHeadCosts ThreeBoundActualEnumeration
open ThreeBoundActualTargets ThreeBoundActualResidualCaps ThreeBoundTagPrefixes
open ThreeBoundNumeric ThreeBoundCapAlgorithm ThreeBoundRecordCaps ThreeBoundAccounting
open scoped Classical BigOperators
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]

/-- The combinatorial exclusions used by the numerical q2 prefix routine. -/
structure CapsSound (R : V → V → Prop) (ell : V → V → Bool) (caps : Caps) : Prop where
  ordinary : ∀ q, q ≤  2 → CandidateCoherence.NoOrdinary R ell q (Caps.at caps.ordinary q)
  source : ResidualCaps.DominatorCardBound R ell 1 (caps.pcross+1)
  double : ResidualCaps.DominatorCardBound R ell 2 (Caps.at caps.zero 2+1)
  markedOne : ∀ q, 1 ≤  q → q ≤  2 →
    ResidualCaps.MarkedCardBound R ell q 1 (q+1) (Caps.at caps.marked (q-1))
  markedTwo : ∀ q, 1 ≤  q → q ≤  2 →
    ResidualCaps.MarkedCardBound R ell q 2 (2*(q+1))
      (Caps.at caps.marked (if q=1 then 4 else 5))
  zeroThree : ResidualCaps.MarkedCardBound R ell 1 3 0 (Caps.at caps.marked 6)
  zeroFour : ResidualCaps.MarkedCardBound R ell 2 4 0 (Caps.at caps.marked 7)
  zeroThree_pos : 1 ≤  Caps.at caps.marked 6
  zeroFour_pos : 1 ≤  Caps.at caps.marked 7



end
end ThreeBoundActualCaps



end
end Sensitivity213981Formal


