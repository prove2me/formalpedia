-- Prove2me | Definitions.Def_Sensitivity213981Formal_RelaxedReachableSearch
-- name    : Sensitivity213981Formal_RelaxedReachableSearch
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:27:41.94998+00:00
-- url     : https://prove2.me/theorems/657366e9-66a4-4249-b252-05d348d82b91
-- title:
--   Relaxed Reachable Search — sensitivity certificate definitions
-- statement:
--   The definitions for Relaxed Reachable Search in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundRelaxedReachable.Plan.Valid`, `ThreeBoundRelaxedReachable.localCheck`, `ThreeBoundRelaxedReachable.linear`, `ThreeBoundRelaxedReachable.targetCode`, `ThreeBoundRelaxedReachable.point`, `ThreeBoundRelaxedReachable.Plan.run`, `ThreeBoundRelaxedReachable.reached`, `ThreeBoundRelaxedReachable.Plan`, `ThreeBoundRelaxedReachable.Plan.bits`, `ThreeBoundRelaxedReachable.Job`, `ThreeBoundRelaxedReachable.Job.check`, `ThreeBoundRelaxedReachable.Job.frontier`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; RelaxedReachableSearch.lean, lines 1–270.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RelaxedPackedRecords
import Definitions.Def_Sensitivity213981Formal_RelaxedPackedTreeData
import Definitions.Def_Sensitivity213981Formal_RelaxedRecordCoverage
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
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Sensitivity213981Formal
section
/- Shared suffix bitsets retain every degree completion. -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 200000
namespace ThreeBoundRelaxedReachable
open ThreeBoundQ3 ThreeBoundRelaxed ThreeBoundRelaxedCompiled
open ThreeBoundRelaxedPacked (Tree fastKey)

def linear (x : Int3) : ℤ := x.a+16*x.b+256*x.c
def targetCode (x : Int3) (n : ℕ) : ℤ := linear x+1024*n
def point (s : State) : ℤ := linear (weight3 s)+1024

def reached (bits : ℕ) (x : ℤ) : Bool := decide (0≤ x) && bits.testBit x.toNat

inductive Plan where
  | done : Plan
  | step (choices : List State) (bits : ℕ) (tail : Plan) : Plan

def Plan.bits : Plan → ℕ
  | .done => 1
  | .step _ b _ => b

def Plan.length : Plan → ℕ
  | .done => 0
  | .step _ _ t => t.length+1

def Plan.choices : Plan → List (List State)
  | .done => []
  | .step c _ t => c::t.choices

def Plan.Follows : Plan → List State → Prop
  | .done,[] => True
  | .step cs _ p,s::ss => s∈cs ∧ p.Follows ss
  | _,_ => False

def Plan.Valid : Plan → Prop
  | .done => True
  | .step cs bits tail => tail.Valid ∧ ∀s∈cs,0≤ point s ∧
      ((tail.bits <<< (point s).toNat) &&& bits)=tail.bits <<< (point s).toNat

def localCheck (cs : List State) (bits tailBits : ℕ) : Bool :=
  cs.all fun s=>decide (0≤ point s) &&
    decide (((tailBits <<< (point s).toNat) &&& bits)=tailBits <<< (point s).toNat)















def Plan.run (tree : Tree) (p : Plan) (pre : List State) (previous : Option State) (remaining : Int3) : Bool :=
  if reached p.bits (targetCode remaining p.length) then
    match p with
    | .done => if remaining=zero then tree.contains (fastKey pre) else true
    | .step cs _ tail => cs.all fun s=>if previousLE previous s then
        tail.run tree (pre++[s]) (some s) (remaining.sub (weight3 s)) else true
  else true



structure Job where
  plan : Plan
  pre : List State
  previous : Option State
  remaining : Int3

def Job.check (tree : Tree) (j : Job) : Bool := j.plan.run tree j.pre j.previous j.remaining

def Job.frontier : ℕ → Job → List Job
  | 0,j => [j]
  | d+1,j =>
      match j.plan with
      | .done => [j]
      | .step cs _ tail =>
          if reached j.plan.bits (targetCode j.remaining j.plan.length) then
            cs.flatMap fun s=>if previousLE j.previous s then
              Job.frontier d ⟨tail,j.pre++[s],some s,j.remaining.sub (weight3 s)⟩ else []
          else []





def Checked (tree : Tree) (ts : List Kind) : Prop :=
  ∃ p : Plan,p.Valid ∧ p.choices=ts.map (options ts.length (guardCount ts)) ∧
    p.run tree [] none (Int3.ofFn (target ts))=true



def Covers (tree : Tree) (xs : List (List Kind)) : Prop := ∀ts∈xs,Checked tree ts









end ThreeBoundRelaxedReachable


end
end Sensitivity213981Formal


