-- Prove2me | Definitions.Def_Sensitivity213303_NumericExpressions
-- name    : Sensitivity213303_NumericExpressions
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-25T21:58:41.448384+00:00
-- url     : https://prove2.me/theorems/02f08cf2-c944-4d66-a088-4a8cc57cd916
-- title:
--   Arithmetic expressions for sensitivity-profile transitions
-- statement:
--   Expr is a natural-valued expression language with profile variables, zero, addition, truncated subtraction, minimum, maximum and multiplication by a natural constant. Evaluation substitutes a numerical profile for its variables. Named A, B, M, P and D expressions and interval expressions select or combine valid profile coordinates, including conditional bounds across more than one adjacent gap. Raw transition formulas and closure certificates are built from this language so their numeric evaluation can be related to semantic sensitivity bounds.
-- source:
--   Original Lean formalization for the Prove2Me block-sensitivity-versus-sensitivity campaign, module NumericExpressions; source SHA256 bb8da8ba34dea1a3830c7beb7dc2133385685978f6dc21a16e09ff9385dff8b3.

/- Homogeneous arithmetic expressions for the exact sensitivity transfer.
Every operation is interpreted in Nat. In particular subtraction is truncated
subtraction, which commutes with multiplication by every natural scalar. -/
import Definitions.Def_Sensitivity213303_FullProfileClosure
import Definitions.Def_Sensitivity213303_ProfileClosures
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Finset.Union
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Ring
namespace ThreeBoundFullProfile
end ThreeBoundFullProfile


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

def Expr.minimum {n : ℕ} (first : Expr n) (es : List (Expr n)) : Expr n :=
  es.foldl .min first

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


