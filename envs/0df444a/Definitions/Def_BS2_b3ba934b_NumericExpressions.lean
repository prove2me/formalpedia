-- Prove2me | Definitions.Def_BS2_b3ba934b_NumericExpressions
-- name    : BS2_b3ba934b_NumericExpressions
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T04:06:48.442996+00:00
-- url     : https://prove2.me/theorems/8268a258-ab29-42bf-9dd4-0e34b1ba4230
-- title:
--   Sensitivity separation: NumericExpressions (complete source module)
-- statement:
--   Complete Lean source module `NumericExpressions` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/NumericExpressions.lean; original SHA-256 bb8da8ba34dea1a3830c7beb7dc2133385685978f6dc21a16e09ff9385dff8b3; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Homogeneous arithmetic expressions for the exact sensitivity transfer.
Every operation is interpreted in Nat. In particular subtraction is truncated
subtraction, which commutes with multiplication by every natural scalar. -/
import Definitions.Def_BS2_b3ba934b_FullProfileClosure
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace ThreeBoundNumeric
open ThreeBoundFullProfile

inductive Expr (n : ℕ) where
  | zero : Expr n
  | var : Coord n → Expr n
  | add : Expr n → Expr n → Expr n
  | scale : ℕ → Expr n → Expr n
  | sub : Expr n → Expr n → Expr n
  | min : Expr n → Expr n → Expr n
  | max : Expr n → Expr n → Expr n

def Expr.eval {n : ℕ} (v : Profile n) : Expr n → ℕ
  | .zero => 0
  | .var c => v c
  | .add a b => a.eval v + b.eval v
  | .scale k a => k * a.eval v
  | .sub a b => a.eval v - b.eval v
  | .min a b => Nat.min (a.eval v) (b.eval v)
  | .max a b => Nat.max (a.eval v) (b.eval v)

theorem Expr.eval_homogeneous {n : ℕ} (e : Expr n) (v : Profile n) (c : ℕ) :
    e.eval (fun i => c * v i) = c * e.eval v := by
  induction e with
  | zero => simp [eval]
  | var i => rfl
  | add a b ha hb => simp only [eval, ha, hb, Nat.mul_add]
  | scale k a ha => simp only [eval, ha]; ring
  | sub a b ha hb => simp only [eval, ha, hb, Nat.mul_sub_left_distrib]
  | min a b ha hb => simp only [eval, ha, hb, Nat.mul_min_mul_left]
  | max a b ha hb => simp only [eval, ha, hb, Nat.mul_max_mul_left]

def Expr.maximum {n : ℕ} (es : List (Expr n)) : Expr n :=
  es.foldr .max .zero

def Expr.minimum {n : ℕ} (first : Expr n) (es : List (Expr n)) : Expr n :=
  es.foldl .min first

def Expr.sum {n : ℕ} (es : List (Expr n)) : Expr n :=
  es.foldr .add .zero

def maximum (xs : List ℕ) : ℕ := xs.foldr max 0

@[simp] theorem maximum_nil : maximum [] = 0 := rfl
@[simp] theorem maximum_cons (x : ℕ) (xs : List ℕ) :
    maximum (x::xs) = max x (maximum xs) := rfl

theorem le_maximum_of_mem {xs : List ℕ} {x : ℕ} (h : x ∈ xs) :
    x ≤ maximum xs := by
  induction xs with
  | nil => simp at h
  | cons y ys ih =>
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · exact le_max_left _ _
      · exact (ih h).trans (le_max_right _ _)

theorem maximum_le {xs : List ℕ} {k : ℕ} (h : ∀ x ∈ xs, x ≤ k) :
    maximum xs ≤ k := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons x xs ih =>
      exact max_le (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

theorem Expr.eval_maximum {n : ℕ} (es : List (Expr n)) (v : Profile n) :
    (Expr.maximum es).eval v = ThreeBoundNumeric.maximum (es.map (fun e => e.eval v)) := by
  induction es with
  | nil => rfl
  | cons e es ih => simpa only [Expr.maximum, List.foldr_cons, Expr.eval,
      List.map_cons, maximum_cons] using congrArg (Nat.max (e.eval v)) ih

theorem Expr.eval_sum {n : ℕ} (es : List (Expr n)) (v : Profile n) :
    (Expr.sum es).eval v = (es.map (fun e=>e.eval v)).sum := by
  induction es with
  | nil => rfl
  | cons e es ih => simpa only [Expr.sum,List.foldr_cons,Expr.eval,List.map_cons,
      List.sum_cons] using congrArg (fun z=>e.eval v+z) ih

theorem Expr.eval_minimum {n : ℕ} (es : List (Expr n)) (first : Expr n) (v : Profile n) :
    (Expr.minimum first es).eval v =
      (es.map (fun e=>e.eval v)).foldl Nat.min (first.eval v) := by
  induction es generalizing first with
  | nil => rfl
  | cons e es ih =>
      simpa only [Expr.minimum,List.foldl_cons,Expr.eval,List.map_cons] using
        ih (.min first e)

def interval (a b : ℕ) : List ℕ := (List.range (b-a)).map (a+·)

theorem mem_interval {a b k : ℕ} : k ∈ interval a b ↔ a ≤ k ∧ k < b := by
  simp only [interval, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i,hi,rfl⟩
    omega
  · rintro ⟨ha,hb⟩
    exact ⟨k-a,by omega,by omega⟩

def aExpr (n i j : ℕ) : Expr n :=
  if hi : i < n then if hj : j < n then .var (.a ⟨i,hi⟩ ⟨j,hj⟩) else .zero else .zero
def bExpr (n i j : ℕ) : Expr n :=
  if hi : i < n then if hj : j < n then .var (.b ⟨i,hi⟩ ⟨j,hj⟩) else .zero else .zero
def mExpr (n i j : ℕ) : Expr n :=
  if hi : i < n then if hj : j < n then .var (.m ⟨i,hi⟩ ⟨j,hj⟩) else .zero else .zero
def pExpr (n j l : ℕ) : Expr n :=
  if hj : j < n then if hl : l < n then .var (.p ⟨j,hj⟩ ⟨l,hl⟩) else .zero else .zero
def dExpr (n i j l : ℕ) : Expr n :=
  if hi : i < n then if hj : j < n then if hl : l < n then
    .var (.d ⟨i,hi⟩ ⟨j,hj⟩ ⟨l,hl⟩) else .zero else .zero else .zero

def minusExpr (n i j k : ℕ) : Expr n :=
  if i ≤ j ∧ j < k then Expr.maximum ((interval j k).map (mExpr n i)) else .zero
def plusExpr (n i j k : ℕ) : Expr n :=
  if i < j ∧ j ≤ k then Expr.maximum ((interval i j).map (fun m => pExpr n m k)) else .zero
def unionExpr (n i j k l : ℕ) : Expr n :=
  if i ≤ j ∧ j < k ∧ k ≤ l then
    Expr.maximum ((interval j k).map (fun m => dExpr n i m l)) else .zero

end ThreeBoundNumeric

#print axioms ThreeBoundNumeric.Expr.eval_homogeneous


