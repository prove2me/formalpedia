-- Prove2me | Definitions.Def_Sensitivity213981Formal_NumericExpressions
-- name    : Sensitivity213981Formal_NumericExpressions
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T17:11:15.389637+00:00
-- url     : https://prove2.me/theorems/77a05acb-d502-4cbe-807d-5862679f8195
-- title:
--   Numeric Expressions — sensitivity certificate definitions
-- statement:
--   The definitions for Numeric Expressions in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundNumeric.Expr.maximum`, `ThreeBoundNumeric.Expr.sum`, `ThreeBoundNumeric.maximum`, `ThreeBoundNumeric.interval`, `ThreeBoundNumeric.aExpr`, `ThreeBoundNumeric.bExpr`, `ThreeBoundNumeric.Expr`, `ThreeBoundNumeric.mExpr`, `ThreeBoundNumeric.pExpr`, `ThreeBoundNumeric.dExpr`, `ThreeBoundNumeric.minusExpr`, `ThreeBoundNumeric.plusExpr`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; NumericExpressions.lean, lines 1–129.

import Definitions.Def_Sensitivity213981Formal_FullProfileClosure
import Definitions.Def_Sensitivity213981Formal_Namespaces
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
/- Homogeneous arithmetic expressions for the exact sensitivity transfer.
Every operation is interpreted in Nat. In particular subtraction is truncated
subtraction, which commutes with multiplication by every natural scalar. -/


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



def Expr.maximum {n : ℕ} (es : List (Expr n)) : Expr n :=
  es.foldr .max .zero



def Expr.sum {n : ℕ} (es : List (Expr n)) : Expr n :=
  es.foldr .add .zero

def maximum (xs : List ℕ) : ℕ := xs.foldr max 0














def interval (a b : ℕ) : List ℕ := (List.range (b-a)).map (a+·)



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



end
end Sensitivity213981Formal


