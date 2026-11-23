-- Prove2me | Definitions.Def_GrothendieckLB_Supplement_cqInitialHermite251
-- name    : GrothendieckLB_Supplement_cqInitialHermite251
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-23T20:54:24.899429+00:00
-- url     : https://prove2.me/theorems/a1fa2f2a-9c3a-4aaf-a0f0-12b45fb5b173
-- title:
--   Integer polynomial certificate for the initial Hermite transform
-- statement:
--   The first Hermite moment row is the even probabilists’ Hermite transform of three interval-valued sequences. For each sequence, the sum of the two endpoints and their difference give signed and unsigned transforms. Clearing the factorial denominators turns each transform into one integer polynomial convolution. The coefficient vectors, factorial scales and base $2^{16000}$ are specified here so the six convolution identities can be checked independently.
-- source:
--   Degree-251 fixed-point Hermite certificate for the cubic–quintic scheme of Saha et al., arXiv:2608.11158v2, and Prove2Me fc28e7f8-2588-498a-8ea6-e8d0e220ae2b.

import Definitions.Def_GrothendieckLB_Supplement_cqHermite251Checkpoints

open GrothendieckLB.Supplement.CQHeadArithmetic GrothendieckLB.Supplement.CQHermite251

/-! Integer data and polynomial evaluations for the initial Hermite transform at cutoff 251. -/
namespace CQInitial251
set_option maxRecDepth 100000
set_option exponentiation.threshold 50000

def den (d : ℕ) := 2^d*d.factorial
def fac (i : ℕ) := (2*i).factorial
def Q := fac 376
def T := den 376
def scaleF (i : ℕ) := Q / fac i
def scaleD (d : ℕ) := T / den d

inductive Axis where | e0 | e2 | e4 deriving DecidableEq,Inhabited

def component (a : Axis) (x : MomentCombination) : Interval := match a with
  | .e0 => x.e0
  | .e2 => x.e2
  | .e4 => x.e4

def projection (a : Axis) (width : Bool) (x : MomentCombination) : ℤ :=
  let v := component a x
  if width then v.hi-v.lo else v.lo+v.hi

def multiplier (width : Bool) (k : ℤ) := if width then |k| else k

def sign (w : Bool) (d : ℕ) : ℤ := if w then 1 else (-1)^d

noncomputable def rawValues : List MomentCombination := eval% ((momentRows 748).toList)
noncomputable def rawAt (i : ℕ) : MomentCombination := rawValues[i]?.getD zeroCombination

noncomputable def cacheF : Array ℕ := eval% (tab 377 scaleF)
noncomputable def cacheD : Array ℕ := eval% (tab 377 scaleD)
noncomputable def sf (i : ℕ) := entry 0 cacheF i
noncomputable def sd (i : ℕ) := entry 0 cacheD i

noncomputable def initialAt (i : ℕ) := (pair 0).2[i]?.getD zeroCombination
noncomputable def A (a : Axis) (w : Bool) (j : ℕ) : ℤ :=
  (sf j:ℤ)*projection a w (rawAt (2*j))
noncomputable def K (w : Bool) (d : ℕ) : ℤ := sign w d * sd d
noncomputable def Z (a : Axis) (w : Bool) (i : ℕ) : ℤ :=
  (sf i:ℤ)*T*projection a w (initialAt (2*i))
def sample (f : ℕ → ℤ) := (List.range 377).map f
def shiftHorner : List ℤ → ℤ
  | [] => 0
  | x::xs => x + ((shiftHorner xs) <<< (16000:ℕ))
def B : ℤ := 2^16000

noncomputable def correctProduct (a : Axis) (w : Bool) : Prop :=
  (shiftHorner (sample (A a w))*shiftHorner (sample (K w)) - shiftHorner (sample (Z a w))) % B^377 = 0
noncomputable instance (a : Axis) (w : Bool) : Decidable (correctProduct a w) :=
  inferInstanceAs (Decidable (_ = _))

end CQInitial251


