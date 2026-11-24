-- Prove2me | Definitions.Def_ValiantBorder_approxAccelerator
-- name    : ValiantBorder_approxAccelerator
-- status  : Definition
-- author  : @Abhishek Anand
-- created : 2026-11-24T00:31:57.672868+00:00
-- url     : https://prove2.me/theorems/d9099264-2570-41c1-afc8-3f5760d48a45
-- title:
--   Approximate accelerators for weighted sum programs
-- statement:
--   A weighted program on a binary tree defines a sum over accepting runs. An approximate accelerator returns that sum as the constant term of a Laurent polynomial, with every negative coefficient zero. The definition specifies which programs and inputs it must handle and charges for execution time, program length, and access to its constants.
--
--   See [Claude (Anthropic), *VP ≠ VNP over every field*](https://hexagonmath.org/2611.00954v1) and the [corresponding Lean source](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/NS1/ApproxRound.lean).
-- source:
--   Claude (Anthropic), VP ≠ VNP over every field, https://hexagonmath.org/2611.00954v1. Lean source: https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/NS1/ApproxRound.lean.

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib
/-! Source: Claude (Anthropic), *VP ≠ VNP over every field* (2026),
`anthropics/formal-math` commit 11b6c7e3c927df2658f513b6b68ea7f8929c62c5.
Adapted with attribution under the Apache-2.0 license. -/
namespace NS1

/-- Binary trees. -/
inductive Tree where
  /-- the empty tree -/
  | nil
  /-- a tree with two subtrees -/
  | cons (a b : Tree)
  deriving DecidableEq

namespace Tree

/-- First subtree. -/
def hd : Tree → Tree
  | nil => nil
  | cons a _ => a

/-- Second subtree. -/
def tl : Tree → Tree
  | nil => nil
  | cons _ b => b

/-- The number of nodes. -/
def size : Tree → ℕ
  | nil => 1
  | cons a b => a.size + b.size + 1

/-- The length of a tree as a list. -/
def len : Tree → ℕ
  | nil => 0
  | cons _ b => b.len + 1

/-- A tree as a list of bits. -/
def path : Tree → List Bool
  | nil => []
  | cons a b => decide (a ≠ nil) :: b.path

/-- A tree as a list of trees. -/
def toList : Tree → List Tree
  | nil => []
  | cons a b => a :: b.toList

/-- The number `k` as a tree. -/
def num : ℕ → Tree
  | 0 => nil
  | k + 1 => cons nil (num k)

/-- The bit 1. -/
def one : Tree := cons nil nil

/-- A bit. -/
def bit (b : Bool) : Tree := if b then one else nil

/-- A list of bits as a tree. -/
def ofBits : List Bool → Tree
  | [] => nil
  | b :: w => cons (bit b) (ofBits w)

theorem size_hd_le (x : Tree) : x.hd.size ≤ x.size := by
  cases x with
  | nil => exact le_rfl
  | cons a b => simp only [hd, size]; omega

theorem size_tl_le (x : Tree) : x.tl.size ≤ x.size := by
  cases x with
  | nil => exact le_rfl
  | cons a b => simp only [tl, size]; omega

end Tree
open _root_.NS1.Tree
/-- Formulas. -/
inductive Fm where
  /-- a fixed tree -/
  | quote (c : Tree)
  /-- the argument -/
  | id
  /-- first subtree -/
  | hd (a : Fm)
  /-- second subtree -/
  | tl (a : Fm)
  /-- a tree with two given subtrees -/
  | cons (a b : Fm)
  /-- if the value of `a` is not empty then `b` else `c` -/
  | ite (a b c : Fm)
  /-- apply the program that is the value of `a` to the value of `b` -/
  | run (a b : Fm)
  /-- guess a bit -/
  | guess
  /-- reject -/
  | fail
  /-- multiply the weight by the constant of `A` that is named by the value of `a` -/
  | theta (a : Fm)
  /-- multiply the weight by the constant that is named by the value of `a` -/
  | mul (a : Fm)

namespace Fm

/-- Formulas as trees. -/
def code : Fm → Tree
  | quote c => .cons (num 0) c
  | id => .cons (num 1) .nil
  | hd a => .cons (num 2) a.code
  | tl a => .cons (num 3) a.code
  | cons a b => .cons (num 4) (.cons a.code b.code)
  | ite a b c => .cons (num 5) (.cons a.code (.cons b.code c.code))
  | run a b => .cons (num 6) (.cons a.code b.code)
  | guess => .cons (num 7) .nil
  | fail => .cons (num 8) .nil
  | theta a => .cons (num 9) a.code
  | mul a => .cons (num 10) a.code

/-- Every tree is read as a formula. -/
def ofTree : Tree → Fm
  | .nil => quote .nil
  | .cons o a =>
    match o.len with
    | 0 => quote a
    | 1 => id
    | 2 => hd (ofTree a)
    | 3 => tl (ofTree a)
    | 4 => cons (ofTree a.hd) (ofTree a.tl)
    | 5 => ite (ofTree a.hd) (ofTree a.tl.hd) (ofTree a.tl.tl)
    | 6 => run (ofTree a.hd) (ofTree a.tl)
    | 7 => guess
    | 8 => fail
    | 9 => theta (ofTree a)
    | 10 => mul (ofTree a)
    | _ => fail
  termination_by x => x.size
  decreasing_by
    all_goals
      have h1 := size_hd_le a
      have h2 := size_tl_le a
      have h3 := size_hd_le a.tl
      have h4 := size_tl_le a.tl
      simp only [Tree.size]
      omega

end Fm

variable {A : Type} [CommRing A]

/-- An accepting run: its cost, its weight, the names of the constants it wants, its value. -/
structure Run (A : Type) where
  /-- number of steps -/
  cost : ℕ
  /-- weight -/
  th : A
  /-- names of constants that the run multiplies by -/
  bill : List (List Bool)
  /-- value -/
  out : Tree

namespace Run

/-- One run after the other. -/
def seq (r s : Run A) : Run A := ⟨r.cost + s.cost, r.th * s.th, r.bill ++ s.bill, s.out⟩

/-- One more step, with value `o`. -/
def tick (r : Run A) (o : Tree) : Run A := ⟨r.cost + 1, r.th, r.bill, o⟩

/-- A run without guesses and weights. -/
def det (k : ℕ) (o : Tree) : Run A := ⟨k, 1, [], o⟩

end Run

/-- All runs of the formula at the tree stop; the list of the accepting runs. -/
inductive Ev (θ : List Bool → A) : Fm → Tree → List (Run A) → Prop
  | quote (c x : Tree) : Ev θ (.quote c) x [.det 1 c]
  | id (x : Tree) : Ev θ .id x [.det 1 x]
  | hd {a : Fm} {x : Tree} {l : List (Run A)} : Ev θ a x l → Ev θ (.hd a) x (l.map fun r => r.tick r.out.hd)
  | tl {a : Fm} {x : Tree} {l : List (Run A)} : Ev θ a x l → Ev θ (.tl a) x (l.map fun r => r.tick r.out.tl)
  | cons {a b : Fm} {x : Tree} {la lb : List (Run A)} : Ev θ a x la → Ev θ b x lb →
      Ev θ (.cons a b) x (la.flatMap fun r => lb.map fun s => (r.seq s).tick (.cons r.out s.out))
  | ite {a b c : Fm} {x : Tree} {la : List (Run A)} {L : Run A → List (Run A)} : Ev θ a x la →
      (∀ r ∈ la, r.out ≠ .nil → Ev θ b x (L r)) → (∀ r ∈ la, r.out = .nil → Ev θ c x (L r)) →
      Ev θ (.ite a b c) x (la.flatMap fun r => (L r).map fun s => (r.seq s).tick s.out)
  | run {a b : Fm} {x : Tree} {la lb : List (Run A)} {L : Run A → Run A → List (Run A)} : Ev θ a x la → Ev θ b x lb →
      (∀ r ∈ la, ∀ s ∈ lb, Ev θ (Fm.ofTree r.out) s.out (L r s)) →
      Ev θ (.run a b) x (la.flatMap fun r => lb.flatMap fun s => (L r s).map fun t => ((r.seq s).seq t).tick t.out)
  | guess (x : Tree) : Ev θ .guess x [.det 1 .nil, .det 1 Tree.one]
  | fail (x : Tree) : Ev θ .fail x []
  | theta {a : Fm} {x : Tree} {l : List (Run A)} : Ev θ a x l →
      Ev θ (.theta a) x (l.map fun r => ⟨r.cost + 1, r.th * θ r.out.path, r.bill, .nil⟩)
  | mul {a : Fm} {x : Tree} {l : List (Run A)} : Ev θ a x l →
      Ev θ (.mul a) x (l.map fun r => ⟨r.cost + 1, r.th, r.bill ++ [r.out.path], .nil⟩)

variable {θ : List Bool → A}

variable (θ) in
/-- All runs stop. -/
def Hl (F : Fm) (x : Tree) : Prop := ∃ l, Ev θ F x l

open Classical in
variable (θ) in
/-- The accepting runs (if all runs stop). -/
noncomputable def evl (F : Fm) (x : Tree) : List (Run A) := if h : Hl θ F x then h.choose else []


section Tries
variable {R : Type} [CommRing R]
inductive KT (R : Type) where
  /-- no constant -/
  | none
  /-- one constant -/
  | leaf (c : R)
  /-- constants whose names begin with 0, constants whose names begin with 1 -/
  | node (l r : KT R)

namespace KT

/-- The number of nodes. -/
def nds : KT R → ℕ
  | none => 1
  | leaf _ => 1
  | node l r => l.nds + r.nds + 1

/-- The height: a bound for the length of names. -/
def ht : KT R → ℕ
  | none => 0
  | leaf _ => 0
  | node l r => max l.ht r.ht + 1

/-- The power of `c` that has a given name. -/
def combVal (c : R) : List Bool → R
  | [] => 0
  | [false] => c
  | false :: _ :: _ => 0
  | true :: p => combVal (c ^ 2) p

/-- The constant with a given name: `l ++ 1^b ++ 0` names the power `2 ^ b` of the constant with the name `l`. -/
def lk : KT R → List Bool → R
  | none, _ => 0
  | leaf c, p => combVal c p
  | node _ _, [] => 0
  | node _ r, true :: p => r.lk p
  | node l _, false :: p => l.lk p

/-- The name of the power `2 ^ b`. -/
def pw (b : ℕ) : List Bool := List.replicate b true ++ [false]

/-- Names of powers `2 ^ b`, `b < B`, of the constants. -/
def InB (B : ℕ) : KT R → List Bool → Prop
  | none, _ => False
  | leaf _, p => ∃ b < B, p = pw b
  | node _ _, [] => False
  | node _ r, true :: p => r.InB B p
  | node l _, false :: p => l.InB B p

end KT
section Weights

variable [Algebra A R]

/-- The weight of a run, if the named constants are `κ`. -/
def wt (κ : List Bool → R) (r : Run A) : R := algebraMap A R r.th * (r.bill.map κ).prod

/-- The value of a list of runs. -/
def val (κ : List Bool → R) (l : List (Run A)) : R := (l.map (wt κ)).sum

/-- The value of a list of runs without named constants. -/
def pval (l : List (Run A)) : A := (l.map Run.th).sum

end Weights
end Tries
/-- The number of binary digits. -/
def lg (n : ℕ) : ℕ := Nat.log 2 n + 1

/-- The program `z.hd` at the argument `z.tl`: all runs stop, the accepting ones within `T` steps and without named
constants. -/
def Plain (θ : List Bool → A) (T : ℕ) (z : Tree) : Prop :=
  Hl θ (Fm.ofTree z.hd) z.tl ∧ ∀ r ∈ evl θ (Fm.ofTree z.hd) z.tl, r.bill = [] ∧ r.cost ≤ T

/-- The universal plain sum: the sum of the weights of all accepting runs of the program `z.hd` at `z.tl`. -/
noncomputable def pv (θ : List Bool → A) (z : Tree) : A := pval (evl θ (Fm.ofTree z.hd) z.tl)


open LaurentPolynomial
variable {E : Type} [CommRing E] [Algebra A E]
/-- All coefficients of exponents below `r` are 0: the polynomial lies in ε^r E[ε]. -/
def OrdGE (r : ℤ) (P : E[T;T⁻¹]) : Prop := ∀ i < r, P.coeff i = 0

/-- **Paper: the definition of an approximate accelerator.** The program `D`, with constants in E[ε,ε⁻¹], has values in pv z + ε E[ε], in `t`
steps, on the instances of size `v ^ (H - 32)` of the universal plain sums of `v ^ H` steps. -/
structure IsAccA (θ : List Bool → A) (H v t : ℕ) (K : KT E[T;T⁻¹]) (B : ℕ) (D : Tree) : Prop where
  run : ∀ z, z.size ≤ v ^ (H - 32) → Hl θ (Fm.ofTree D) z ∧ ∀ r ∈ evl θ (Fm.ofTree D) z, r.cost ≤ t ∧
    ∀ p ∈ r.bill, K.InB B p
  val : ∀ z, z.size ≤ v ^ (H - 32) → Plain θ (v ^ H) z →
    OrdGE 1 (val K.lk (evl θ (Fm.ofTree D) z) - algebraMap A E[T;T⁻¹] (pv θ z))

/-- **Paper: the definition of an approximate accelerator, with its size.** An approximate accelerator of size `s` at the scale `V = v ^ H`
over E: a trie of at most `s` nodes with constants in E[ε,ε⁻¹], and a program of size at most `s` whose values lie in
the universal plain sums + ε E[ε]. -/
def HasAccA (θ : List Bool → A) (E : Type) [CommRing E] [Algebra A E] (H v s : ℕ) : Prop :=
  ∃ (K : KT E[T;T⁻¹]) (B : ℕ) (D : Tree), IsAccA θ H v (v ^ (H - 16)) K B D ∧ K.nds ≤ s ∧ D.size ≤ s ∧
    K.ht ≤ lg (max (v ^ H) s) ^ 2 ∧ B ≤ lg (max (v ^ H) s) ^ 3

end NS1


