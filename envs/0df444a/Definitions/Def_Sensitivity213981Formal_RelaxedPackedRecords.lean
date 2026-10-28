-- Prove2me | Definitions.Def_Sensitivity213981Formal_RelaxedPackedRecords
-- name    : Sensitivity213981Formal_RelaxedPackedRecords
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T21:10:13.329781+00:00
-- url     : https://prove2.me/theorems/a6114eb7-d7a9-4e09-b8a1-bea3fb733524
-- title:
--   Relaxed Packed Records — sensitivity certificate definitions
-- statement:
--   The definitions for Relaxed Packed Records in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundRelaxedPacked.core`, `ThreeBoundRelaxedPacked.coreCode`, `ThreeBoundRelaxedPacked.singleCode`, `ThreeBoundRelaxedPacked.radix`, `ThreeBoundRelaxedPacked.typeFields`, `ThreeBoundRelaxedPacked.fastSingle`, `ThreeBoundRelaxedPacked.digits`, `ThreeBoundRelaxedPacked.fastKey`, `ThreeBoundRelaxedPacked.validSingle`, `ThreeBoundRelaxedPacked.histIndices`, `ThreeBoundRelaxedPacked.histFields`, `ThreeBoundRelaxedPacked.external`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; RelaxedPackedRecords.lean, lines 1–117.

import Definitions.Def_Sensitivity213981Formal_Endpoint22RecordDecode
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RelaxedCompiledSearch
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

namespace Sensitivity213981Formal
section
/- Linear packed keys for the exact forty-one-field degree record. -/


set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

namespace ThreeBoundRelaxedPacked
open ThreeBoundQ3 ThreeBoundRelaxed

def radix : ℕ := 1048576

def typeFields (ss : List State) : List ℕ :=
  (List.finRange 11).map fun t => (ss.filter fun s => s.kind=t).length

def histIndices : List (Kind × ℕ) :=
  (List.finRange 11).flatMap fun t => [(t,1),(t,2)]

def histFields (ss : List State) : List ℕ :=
  histIndices.map fun p => (ss.filter fun s => s.kind=p.1 ∧ min 2 s.incoming=p.2).length

def external (ss : List State) : ℕ :=
  ((ss.filter fun s => isGuard s.kind).map fun s => budget s.kind-s.out).sum

def prefixes (ss : List State) : List ℕ :=
  let rs := (ss.map fun s => budget s.kind-s.out).insertionSort (·≤ ·)
  [1,2,3,4,5,6,7].map fun k => if k≤ ss.length then (rs.take k).sum else 1000000

def core (ss : List State) : List ℕ := typeFields ss++[external ss]++histFields ss















def coreCode (ss : List State) : ℕ := Nat.ofDigits radix (core ss).reverse
def singleCode (s : State) : ℕ := coreCode [s]







def fastSingle (s : State) : ℕ :=
  radix^(33-s.kind.val) + (if isGuard s.kind then budget s.kind-s.out else 0)*radix^22 +
  (if min 2 s.incoming=0 then 0 else radix^(21-2*s.kind.val-(min 2 s.incoming-1)))

def digits : List ℕ → ℕ
  | [] => 0
  | a::as => a+radix*digits as



def fastKey (ss : List State) : ℕ :=
  radix^7 * (ss.map fastSingle).sum + digits (prefixes ss).reverse

def validSingle (t : Kind) : Bool := (List.range 5).all fun d=>
  (List.range 9).all fun h => decide (singleCode ⟨t,d,h⟩=fastSingle ⟨t,d,h⟩)

end ThreeBoundRelaxedPacked

end
end Sensitivity213981Formal


