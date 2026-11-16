-- Prove2me | Definitions.Def_ZLIPPadding_Padding_Supplement_Counting
-- name    : ZLIPPadding_Padding_Supplement_Counting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:16:56.78257+00:00
-- url     : https://prove2.me/theorems/5adaa58b-31b6-485a-bb88-65056a55256d
-- title:
--   Executable shell counting with integer arithmetic traces
-- statement:
--   The shell-counting algorithm constructs all rows of the dynamic-programming table in increasing dimension, then computes the weighted sums and signed rational moments from the last two rows. Its recurrence is
--
--   $$R_0(t)=\mathbf1_{t=0},\qquad R_j(t)=R_{j-1}(t)+2\sum_{k=1}^{\lfloor\sqrt t\rfloor}R_{j-1}(t-k^2).$$
--
--   Each executed integer addition, subtraction, multiplication or exact quotient logs its operands and result. The algorithm returns failure exactly when its final count vanishes. No correctness, arithmetic-operation bound or intermediate-bit bound is part of the data: Proposition 4.3 asserts those properties. Loop and table indexing use the usual arithmetic-operation model; the source's arithmetic bound is distinct from binary bit complexity.
-- source:
--   Shengmao Jiang, STOC 2027 submission #496 (October 2026), printed pp. 17–18 (PDF pp. 18–19), Proposition 4.3 and equations (4.9)–(4.11)

import Definitions.Def_ZLIPPadding_Padding_Supplement_Programs

namespace ZLIPPadding.Padding.Supplement
open scoped BigOperators

/-- All integer arithmetic in the table and weighted sums is logged. Array indexing is
not counted as an integer arithmetic operation; bit complexity is a separate claim. -/
structure ArithmeticLog where
  values : List ℤ := []
  operations : ℕ := 0
def arithmetic (f : ℤ → ℤ → ℤ) (a b : ℤ) : StateM ArithmeticLog ℤ := do
  let v := f a b
  modify fun s => { values := a :: b :: v :: s.values, operations := s.operations+1 }
  return v
def nextRow (m : ℕ) (prev : Array ℤ) : StateM ArithmeticLog (Array ℤ) := do
  let mut row := #[]
  for t in List.range (m+1) do
    let mut v := prev[t]!
    for k in List.range (Nat.sqrt t) do
      let kk ← arithmetic (· * ·) (k+1) (k+1)
      let index ← arithmetic (· - ·) t kk
      let term ← arithmetic (· * ·) 2 prev[index.toNat]!
      v ← arithmetic (· + ·) v term
    row := row.push v
  return row
abbrev FractionTriple := (ℤ × ℤ) × (ℤ × ℤ) × (ℤ × ℤ)
/-- Output fractions need not be reduced: no uncharged rational-normalization algorithm. -/
def countAlgorithm (n m : ℕ) : StateM ArithmeticLog (Option FractionTriple) := do
  let initialRow := ((List.range (m+1)).map (fun t => if t = 0 then (1 : ℤ) else 0)).toArray
  let mut rows := #[initialRow]
  for _ in List.range n do
    let row ← nextRow m rows[rows.size-1]!
    rows := rows.push row
  let r := (rows[n]!)[m]!
  let mut q4 := 0
  for k in List.range (Nat.sqrt m) do
    let kk ← arithmetic (· * ·) (k+1) (k+1)
    let k4 ← arithmetic (· * ·) kk kk
    let index ← arithmetic (· - ·) m kk
    let term ← arithmetic (· * ·) k4 ((rows[n-1]!)[index.toNat]!)
    q4 ← arithmetic (· + ·) q4 term
  q4 ← arithmetic (· * ·) 2 q4
  let m2 ← arithmetic (· * ·) m m
  let m2r ← arithmetic (· * ·) m2 r
  let nq4 ← arithmetic (· * ·) n q4
  let num ← arithmetic (· - ·) m2r nq4
  let nm1 ← arithmetic (· - ·) n 1
  let den ← arithmetic (· * ·) n nm1
  let q22 ← arithmetic (· / ·) num den
  let threeQ ← arithmetic (· * ·) 3 q22
  let kNum ← arithmetic (· - ·) q4 threeQ
  return if r = 0 then none else some ((q4,r), (q22,r), (kNum,r))
def interpretFractions (v : FractionTriple) : ℚ × ℚ × ℚ :=
  ((v.1.1 : ℚ)/v.1.2, (v.2.1.1 : ℚ)/v.2.1.2, (v.2.2.1 : ℚ)/v.2.2.2)
def countResult (n m : ℕ) : Option (ℚ × ℚ × ℚ) :=
  ((countAlgorithm n m).run {}).1.map interpretFractions
def countLog (n m : ℕ) : ArithmeticLog := ((countAlgorithm n m).run {}).2
def integerBits (v : ℤ) : ℕ := v.natAbs.bits.length+1

end ZLIPPadding.Padding.Supplement


