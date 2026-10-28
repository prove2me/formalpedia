-- Prove2me | Definitions.Def_Sensitivity213981Formal_Q3RecordFields
-- name    : Sensitivity213981Formal_Q3RecordFields
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T21:06:30.240402+00:00
-- url     : https://prove2.me/theorems/dee71621-286d-4985-8e98-8fd7d5d4fd62
-- title:
--   Q3 Record Fields — sensitivity certificate definitions
-- statement:
--   The definitions for Q3 Record Fields in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundQ3RecordFields.sortedResiduals`, `ThreeBoundQ3RecordFields.residualPrefix`, `ThreeBoundQ3RecordFields.residual`, `ThreeBoundQ3RecordFields.incoming`, `ThreeBoundQ3RecordFields.typeCount`, `ThreeBoundQ3RecordFields.histogram`, `ThreeBoundQ3RecordFields.external`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Q3RecordFields.lean, lines 1–139.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Q2RawExpressions
import Definitions.Def_Sensitivity213981Formal_Q3Enumeration
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
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Sensitivity213981Formal
section
/- Exact meanings of the 41 fields of the executable q3 record. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

namespace ThreeBoundQ3RecordFields
open ThreeBoundQ3 ThreeBoundNumeric

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
  ((List.finRange ts.length).map (residual ts ds)).mergeSort (· ≤  ·)

def residualPrefix (ts : List Kind) (ds : List Bool) (k : ℕ) : ℕ :=
  if k ≤  ts.length then ((sortedResiduals ts ds).take k).sum else 1000000























end
end ThreeBoundQ3RecordFields





end
end Sensitivity213981Formal


