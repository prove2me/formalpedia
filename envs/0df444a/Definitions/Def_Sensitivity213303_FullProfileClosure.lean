-- Prove2me | Definitions.Def_Sensitivity213303_FullProfileClosure
-- name    : Sensitivity213303_FullProfileClosure
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-25T21:54:54.109473+00:00
-- url     : https://prove2.me/theorems/b04f17f9-7fd1-4968-9c6f-7f3d7eb6030c
-- title:
--   Finite A/B/M/P/D coordinates and semantic closure instructions
-- statement:
--   A profile assigns a natural-number bound to each of five coordinate types on Fin n. A and B coordinates use i≤j; M uses the adjacent gap j,j+1; P and D also use an adjacent conditional gap and an upper level l>j. Upper(F,v) means every valid coordinate satisfies its corresponding semantic sensitivity bound. The Rule datatype records the permitted monotonicity, conditional, partition and union updates, including their index-order requirements and the coordinate they improve. It is the typed instruction language for the finite closure certificates.
-- source:
--   Original Lean formalization for the Prove2Me block-sensitivity-versus-sensitivity campaign, module FullProfileClosure; source SHA256 5a60de39b5ad6accffb5dbd5d6529c02c34ba478739e73e4c3db3c10e08132be.

/- Soundness of the complete finite five-profile closure procedure.
The update schedule is the one in graded2_union_recurrence.IntegerModel.close.
It does not establish the raw sensitivity transfer preceding that procedure. -/
import Definitions.Def_Sensitivity213303_ProfileClosures
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Union
import Mathlib.Data.List.FinRange
namespace ThreeBoundProfiles
end ThreeBoundProfiles


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


