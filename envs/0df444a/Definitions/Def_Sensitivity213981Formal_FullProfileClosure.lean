-- Prove2me | Definitions.Def_Sensitivity213981Formal_FullProfileClosure
-- name    : Sensitivity213981Formal_FullProfileClosure
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T17:10:09.067702+00:00
-- url     : https://prove2.me/theorems/731053ed-a53c-4827-8185-f6bdb16090e3
-- title:
--   Full Profile Closure — sensitivity certificate definitions
-- statement:
--   The definitions for Full Profile Closure in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundFullProfile.Sem`, `ThreeBoundFullProfile.Upper`, `ThreeBoundFullProfile.Rule`, `ThreeBoundFullProfile.Rule.target`, `ThreeBoundFullProfile.Coord`, `ThreeBoundFullProfile.Profile`, `ThreeBoundFullProfile.next`, `ThreeBoundFullProfile.prev`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; FullProfileClosure.lean, lines 1–303.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_ProfileClosures
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange

namespace Sensitivity213981Formal
section
/- Soundness of the complete finite five-profile closure procedure.
The update schedule is the one in graded2_union_recurrence.IntegerModel.close.
It does not establish the raw sensitivity transfer preceding that procedure. -/


set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

namespace ThreeBoundFullProfile
open ThreeBoundProfiles
open scoped Classical
noncomputable section

variable {n : ℕ} {I : Type} [Fintype I]

inductive Coord (n : ℕ) where
  | a : Fin n → Fin n → Coord n
  | b : Fin n → Fin n → Coord n
  | m : Fin n → Fin n → Coord n
  | p : Fin n → Fin n → Coord n
  | d : Fin n → Fin n → Fin n → Coord n
  deriving DecidableEq

abbrev Profile (n : ℕ) := Coord n → ℕ

def next (j : Fin n) : Fin n :=
  if h : j.val+1 < n then ⟨j.val+1,h⟩ else j

def prev (j : Fin n) : Fin n := ⟨j.val-1,(Nat.sub_le _ _).trans_lt j.isLt⟩













/-- Only the triangular and adjacent-gap coordinates carry an obligation.
The unused coordinates make in-place updates uncomplicated and harmless. -/
def Sem (F : Fin n → (I → Bool) → Bool) : Coord n → ℕ → Prop
  | .a i j, v => i ≤ j → ABound F i j v
  | .b i j, v => i ≤ j → BBound F i j v
  | .m i j, v => i ≤ j → j.val+1 < n → MBound F i j (next j) v
  | .p j l, v => j < l → PBound F j (next j) l v
  | .d i j l, v => i ≤ j → j < l → DBound F i j (next j) l v

def Upper (F : Fin n → (I → Bool) → Bool) (v : Profile n) : Prop :=
  ∀ c, Sem F c (v c)











/-- Each constructor is exactly one of the semantic closure rules. The index
conditions are part of the command, not assumed by the execution theorem. -/
inductive Rule (n : ℕ) where
  | aCond (i j : Fin n) (h : i < j)
  | aTarget (i j : Fin n) (h : i < j)
  | bTarget (i j : Fin n) (h : i < j)
  | bCond (i j : Fin n) (h : i < j)
  | mFromB (i j : Fin n) (h : i ≤ j) (hn : j.val+1 < n)
  | mTarget (i j : Fin n) (h : i < j) (hn : j.val+1 < n)
  | pFromA (j l : Fin n) (h : j < l)
  | pTarget (j l : Fin n) (h : j.val+1 < l.val)
  | dFromMP (i j l : Fin n) (h : i ≤ j) (hl : j < l)
  | dDown (i j l : Fin n) (h : i < j) (hl : j < l)
  | dUp (i j l : Fin n) (h : i ≤ j) (hl : j.val+1 < l.val)
  | bPartition (i j : Fin n) (h : i ≤ j) (hn : j.val+1 < n)
  | aPartition (j l : Fin n) (h : j < l)

def Rule.target : Rule n → Coord n
  | .aCond i j _ | .aTarget i j _ => .a i j
  | .bTarget i j _ | .bCond i j _ => .b i j
  | .mFromB i j _ _ | .mTarget i j _ _ => .m i j
  | .pFromA j l _ | .pTarget j l _ => .p j l
  | .dFromMP i j l _ _ | .dDown i j l _ _ | .dUp i j l _ _ => .d i j l
  | .bPartition i j _ _ => .b i j
  | .aPartition j l _ => .a (next j) l

































end
end ThreeBoundFullProfile




end
end Sensitivity213981Formal


