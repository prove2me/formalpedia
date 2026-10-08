-- Prove2me | Definitions.Def_FormulaHitting
-- name    : FormulaHitting
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:11.874496+00:00
-- url     : https://prove2.me/theorems/06ab5d7b-3f7b-43b3-8830-a580bbf83696
-- statement:
--   Words of length n are finite lists of indices from {0,…,n−1}, and a word series over a semiring F is any function from words to F, i.e. a noncommutative formal power series in n variables. The convolution of two series f and g is the noncommutative (Cauchy) product: at the empty word it is f(∅)g(∅), and at a word i·w it is f(∅)g(i·w) plus the convolution of the shifted series v↦f(i·v) with g evaluated at w. A Formula over F in n variables is a tree built from scalars in F, variables x_i, binary sums and binary products. Its size counts one for each leaf and one more for each addition or multiplication node. Its coefficient series sends a scalar a to the series that is a at the empty word and 0 elsewhere, and a variable x_i to the series that is 1 at the single-letter word [i] and 0 elsewhere. Sums add coefficients pointwise and products take the convolution of the coefficient series. Given a scalar map F→A into a semiring A and an assignment T of an element of A to each variable, the evaluation of a formula interprets scalars through the map, variables through T, and sums and products in A. The block also defines a concrete family of rational matrices. The dimension is 1 when n=s=1 and otherwise 2ns². The auxiliary entry matrixEntry(i,r,q) is (−1)^(r−q−1)/(r·i^(r−q)) when q<r and 0 otherwise, so it is strictly lower triangular in (r,q). The generator for variable index i is the matrix of that dimension whose (r,q) entry is matrixEntry(i+1,r,q), except that in the degenerate case n=s=1 it is the 1×1 matrix with entry 1. No theorem is proved in this block.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/FormulaHitting.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/FormulaHitting.lean; bytes 63..1741
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Defs

namespace OAI

namespace NCHitting

abbrev Word (n : ℕ) := List (Fin n)
abbrev WordSeries (F : Type*) (n : ℕ) := Word n → F

def convolution {F : Type*} {n : ℕ} [Semiring F]
    (f g : WordSeries F n) : Word n → F
  | [] => f [] * g []
  | i :: w => f [] * g (i :: w) + convolution (fun v => f (i :: v)) g w

inductive Formula (F : Type*) (n : ℕ) where
  | scalar : F → Formula F n
  | var : Fin n → Formula F n
  | add : Formula F n → Formula F n → Formula F n
  | mul : Formula F n → Formula F n → Formula F n

namespace Formula

def size {F : Type*} {n : ℕ} : Formula F n → ℕ
  | scalar _ => 1
  | var _ => 1
  | add f g => f.size + g.size + 1
  | mul f g => f.size + g.size + 1

noncomputable def coeff {F : Type*} {n : ℕ} [Semiring F] :
    Formula F n → WordSeries F n
  | scalar a => fun w => if w = [] then a else 0
  | var i => fun w => if w = [i] then 1 else 0
  | add f g => fun w => coeff f w + coeff g w
  | mul f g => convolution (coeff f) (coeff g)

def eval {F A : Type*} {n : ℕ} [Semiring A]
    (scalarMap : F → A) (T : Fin n → A) : Formula F n → A
  | scalar a => scalarMap a
  | var i => T i
  | add f g => eval scalarMap T f + eval scalarMap T g
  | mul f g => eval scalarMap T f * eval scalarMap T g

end Formula

def dimension (n s : ℕ) : ℕ := if n = 1 ∧ s = 1 then 1 else 2 * n * s ^ 2

def matrixEntry (i r q : ℕ) : ℚ :=
  if q < r then (-1 : ℚ) ^ (r - q - 1) / ((r : ℚ) * (i : ℚ) ^ (r - q))
  else 0

def generator (n s : ℕ) : Fin n → Matrix (Fin (dimension n s)) (Fin (dimension n s)) ℚ :=
  fun i r q => if n = 1 ∧ s = 1 then 1 else matrixEntry (i.val + 1) r.val q.val

universe u_2



end NCHitting
end OAI


