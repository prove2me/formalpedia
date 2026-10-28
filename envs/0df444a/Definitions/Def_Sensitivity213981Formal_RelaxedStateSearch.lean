-- Prove2me | Definitions.Def_Sensitivity213981Formal_RelaxedStateSearch
-- name    : Sensitivity213981Formal_RelaxedStateSearch
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T21:07:06.85491+00:00
-- url     : https://prove2.me/theorems/176c6c6b-545b-40e5-bed3-31e683545218
-- title:
--   Relaxed State Search — sensitivity certificate definitions
-- statement:
--   The definitions for Relaxed State Search in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundRelaxed.previousLE`, `ThreeBoundRelaxed.instDecidablePreviousLE`, `ThreeBoundRelaxed.Canonical`, `ThreeBoundRelaxed.weight`, `ThreeBoundRelaxed.weightSum`, `ThreeBoundRelaxed.lower`, `ThreeBoundRelaxed.upper`, `ThreeBoundRelaxed.State`, `ThreeBoundRelaxed.Possible`, `ThreeBoundRelaxed.instDecidablePossible`, `ThreeBoundRelaxed.indicator`, `ThreeBoundRelaxed.record`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; RelaxedStateSearch.lean, lines 1–195.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Q3Enumeration
import Definitions.Def_Sensitivity213981Formal_Supplement_RecordSetLookup
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
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

namespace Sensitivity213981Formal
section
/- Complete degree/incoming search for the relaxed q3 record table. -/


set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000

namespace ThreeBoundRelaxed
open ThreeBoundQ3

structure State where
  kind : Kind
  out : ℕ
  incoming : ℕ
  deriving DecidableEq, Repr

def indicator (t : Kind) : ℕ := if isGuard t then 1 else 0

def Local (n ng : ℕ) (s : State) : Prop :=
  s.out ≤  min (n-1) (budget s.kind) ∧
  ng-indicator s.kind-s.out ≤  s.incoming ∧
  s.incoming ≤  min (ng-indicator s.kind) (n-1-s.out)

instance _root_.Sensitivity213981Formal.ThreeBoundRelaxed.instDecidableLocal (n ng : ℕ) (s : State) : Decidable (Local n ng s) := by
  unfold Local
  infer_instance

def options (n ng : ℕ) (t : Kind) : List State :=
  (List.range (min (n-1) (budget t)+1)).flatMap fun d =>
    let lo := ng-indicator t-d
    let hi := min (ng-indicator t) (n-1-d)
    if lo≤ hi then ((List.range (hi-lo+1)).map fun k => ⟨t,d,lo+k⟩) else []



def previousLE (p : Option State) (s : State) : Prop :=
  match p with
  | none => True
  | some r => r.kind=s.kind → r.out< s.out ∨ (r.out=s.out ∧ r.incoming≤ s.incoming)

instance _root_.Sensitivity213981Formal.ThreeBoundRelaxed.instDecidablePreviousLE (p : Option State) (s : State) : Decidable (previousLE p s) := by
  unfold previousLE
  split <;> infer_instance

def Canonical : Option State → List State → Prop
  | _, [] => True
  | p, s::ss => previousLE p s ∧ Canonical (some s) ss

/-- Integer coordinates make the guard-incidence conservation law additive. -/
def weight (s : State) (k : Fin 3) : ℤ :=
  if k.val=0 then s.out else if k.val=1 then
    (if isGuard s.kind then s.incoming else 0) else
    (s.incoming : ℤ)-(if isGuard s.kind then s.out else 0)

def weightSum (ss : List State) (k : Fin 3) : ℤ := (ss.map fun s => weight s k).sum

def lower (n ng : ℕ) (ts : List Kind) (k : Fin 3) : ℤ :=
  (ts.map fun t => ((options n ng t).map fun s => weight s k).foldr min 100).sum

def upper (n ng : ℕ) (ts : List Kind) (k : Fin 3) : ℤ :=
  (ts.map fun t => ((options n ng t).map fun s => weight s k).foldr max (-100)).sum

def Possible (n ng : ℕ) (ts : List Kind) (target : Fin 3 → ℤ) : Prop :=
  ∀ k, lower n ng ts k≤ target k ∧ target k≤ upper n ng ts k

instance _root_.Sensitivity213981Formal.ThreeBoundRelaxed.instDecidablePossible (n ng : ℕ) (ts : List Kind) (target : Fin 3 → ℤ) :
    Decidable (Possible n ng ts target) := by
  unfold Possible
  infer_instance







def record (ss : List State) : List ℕ := Id.run do
  let typeCounts := (List.finRange 11).map fun t => (ss.filter fun s => s.kind=t).length
  let external := ((ss.filter fun s => isGuard s.kind).map fun s => budget s.kind-s.out).sum
  let hist := (List.finRange 11).flatMap fun t => [1,2].map fun h =>
    (ss.filter fun s => s.kind=t ∧ min 2 s.incoming=h).length
  let residuals := (ss.map fun s => budget s.kind-s.out).insertionSort (·≤ ·)
  let prees := [1,2,3,4,5,6,7].map fun k =>
    if k≤ ss.length then (residuals.take k).sum else 1000000
  return typeCounts++[external]++hist++prees





def guardCount (ts : List Kind) : ℕ := (ts.filter isGuard).length

def target (ts : List Kind) (k : Fin 3) : ℤ :=
  if k.val=0 then ts.length*(ts.length-1)/2 else if k.val=1 then
    guardCount ts*(guardCount ts-1)/2 else 0





end ThreeBoundRelaxed



end
end Sensitivity213981Formal


