-- Prove2me | Definitions.Def_Sensitivity213303_Q2RecordFields
-- name    : Sensitivity213303_Q2RecordFields
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-25T22:21:25.848903+00:00
-- url     : https://prove2.me/theorems/ef493a4d-b9d1-4451-94d7-878a604f8f91
-- title:
--   The exact 29 scalar statistics of a typed tournament record
-- statement:
--   For a kind list and orientation bits, residual(v) is its kind budget minus outdegree, and incoming(v) counts guard-kind sources directed into v. typeCount and histogram count kinds and their one-hit or at-least-two-hit classes. external sums residuals over guard kinds. sortedResiduals orders all vertex residuals, and residualPrefix sums the smallest requested number, using the sentinel 1000000 when too few vertices exist. These statistics specify every field of the finite q≤2 record.
-- source:
--   Original Lean formalization for the Prove2Me block-sensitivity-versus-sensitivity campaign, module Q2RecordFields; source SHA256 00882f676a90870216de7259384922917139ae5d9fd115cc2c73bcce1d414a2e.

/- Exact meanings of the 29 fields of the executable q2 record. -/
import Definitions.Def_Sensitivity213303_CandidateCoherence
import Definitions.Def_Sensitivity213303_FullProfileClosure
import Definitions.Def_Sensitivity213303_GuardAugmentation
import Definitions.Def_Sensitivity213303_NumericExpressions
import Definitions.Def_Sensitivity213303_ProfileClosures
import Definitions.Def_Sensitivity213303_Q2CandidateTypes
import Definitions.Def_Sensitivity213303_Q2Enumeration
import Definitions.Def_Sensitivity213303_Q2EnumerationBridge
import Definitions.Def_Sensitivity213303_Q2RawExpressions
import Definitions.Def_Sensitivity213303_TournamentHighRows
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
namespace ThreeBoundNumeric
end ThreeBoundNumeric
namespace ThreeBoundQ2
end ThreeBoundQ2


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

namespace ThreeBoundRecordFields
open ThreeBoundQ2 ThreeBoundNumeric
open scoped Classical BigOperators
noncomputable section

def residual (ts : List Kind) (ds : List Bool) (v : Fin ts.length) : ℕ :=
  budget (ts.get v) - outCount (edges ts.length) ds v

def incoming (ts : List Kind) (ds : List Bool) (v : Fin ts.length) : ℕ :=
  ((directedEdges (edges ts.length) ds).filter
    fun e => isGuard (ts.get e.1) && decide (e.2 = v)).length

def typeCount (ts : List Kind) (k : Kind) : ℕ := (ts.filter fun u => u = k).length

def histogram (ts : List Kind) (ds : List Bool) (k : Kind) (hits : ℕ) : ℕ :=
  ((List.finRange ts.length).filter fun v => ts.get v = k ∧ min 2 (incoming ts ds v) = hits).length

def external (ts : List Kind) (ds : List Bool) : ℕ :=
  (((List.finRange ts.length).filter fun v => isGuard (ts.get v)).map (residual ts ds)).sum

def sortedResiduals (ts : List Kind) (ds : List Bool) : List ℕ :=
  ((List.finRange ts.length).map (residual ts ds)).mergeSort (· ≤ ·)

def residualPrefix (ts : List Kind) (ds : List Bool) (k : ℕ) : ℕ :=
  if k ≤ ts.length then ((sortedResiduals ts ds).take k).sum else 1000000























end
end ThreeBoundRecordFields


