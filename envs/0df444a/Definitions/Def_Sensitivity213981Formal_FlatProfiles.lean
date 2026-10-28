-- Prove2me | Definitions.Def_Sensitivity213981Formal_FlatProfiles
-- name    : Sensitivity213981Formal_FlatProfiles
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T20:16:49.651369+00:00
-- url     : https://prove2.me/theorems/1cd69b3f-2104-4903-985b-8c24477263ec
-- title:
--   Flat Profiles — sensitivity certificate definitions
-- statement:
--   The definitions for Flat Profiles in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundNumeric.validCoords`, `ThreeBoundNumeric.aIndex`, `ThreeBoundNumeric.bIndex`, `ThreeBoundNumeric.mIndex`, `ThreeBoundNumeric.pIndex`, `ThreeBoundNumeric.dIndex`, `ThreeBoundNumeric.flatIndex`, `ThreeBoundNumeric.NatTable`, `ThreeBoundNumeric.NatTable.get`, `ThreeBoundNumeric.profileOfTable`, `ThreeBoundNumeric.valid`, `ThreeBoundNumeric.instDecidableValid`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; FlatProfiles.lean, lines 1–117.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Supplement_NumericExpressions
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Ring

namespace Sensitivity213981Formal
section
/- Compressed numerical profile layout and a complete coordinate checker.
The interpretation is always the named semantic A/B/M/P/D coordinate. -/


set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace ThreeBoundNumeric
open ThreeBoundProfiles ThreeBoundFullProfile

def valid {n : ℕ} : Coord n → Prop
  | .a i j | .b i j => i ≤  j
  | .m i j => i ≤  j ∧ j.val+1< n
  | .p j l => j< l
  | .d i j l => i≤ j ∧ j< l

instance _root_.Sensitivity213981Formal.ThreeBoundNumeric.instDecidableValid {n : ℕ} (c : Coord n) : Decidable (valid c) := by cases c <;> unfold valid <;> infer_instance

def coords (n : ℕ) : List (Coord n) :=
  ((List.finRange n).flatMap fun i => (List.finRange n).flatMap fun j =>
    [.a i j,.b i j,.m i j,.p i j]) ++
  ((List.finRange n).flatMap fun i => (List.finRange n).flatMap fun j =>
    (List.finRange n).map fun l => .d i j l)



def validCoords (n : ℕ) : List (Coord n) := (coords n).filter fun c => decide (valid c)



def aIndex (n i j : ℕ) : ℕ := i*(2*n+1-i)/2+(j-i)
def bIndex (n i j : ℕ) : ℕ := n*(n+1)/2+aIndex n i j
def mIndex (n i j : ℕ) : ℕ := n*(n+1)+j*(j+1)/2+i
def pIndex (n j l : ℕ) : ℕ := n*(n+1)+n*(n-1)/2+j*(2*n-1-j)/2+(l-j-1)
def dIndex (n i j l : ℕ) : ℕ :=
  2*n*n+((List.range j).map fun k=>(k+1)*(n-k-1)).sum+i*(n-j-1)+(l-j-1)

def flatIndex {n : ℕ} : Coord n → ℕ
  | .a i j => aIndex n i.val j.val
  | .b i j => bIndex n i.val j.val
  | .m i j => mIndex n i.val j.val
  | .p j l => pIndex n j.val l.val
  | .d i j l => dIndex n i.val j.val l.val



/-- A balanced lookup tree gives logarithmic kernel reduction for certificates. -/
inductive NatTable where
  | leaf : ℕ → NatTable
  | branch : ℕ → NatTable → NatTable → NatTable

def NatTable.get : NatTable → ℕ → ℕ
  | .leaf v, _ => v
  | .branch cut left right, i => if i <  cut then left.get i else right.get i

def profileOfTable (n : ℕ) (v : NatTable) : Profile n := fun c=>v.get (flatIndex c)











end ThreeBoundNumeric



end
end Sensitivity213981Formal


