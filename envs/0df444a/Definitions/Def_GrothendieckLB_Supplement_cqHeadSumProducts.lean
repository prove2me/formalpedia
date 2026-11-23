-- Prove2me | Definitions.Def_GrothendieckLB_Supplement_cqHeadSumProducts
-- name    : GrothendieckLB_Supplement_cqHeadSumProducts
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-23T21:10:35.49695+00:00
-- url     : https://prove2.me/theorems/cc75f4cb-229c-4c34-a4fb-224d9420a176
-- title:
--   Integer center polynomials for the cubic–quintic finite coefficient test
-- statement:
--   Clear the signs and factor of two from the midpoints of the packed Hermite weights and primary powers. Zero padding embeds the triangular coefficient sum into 252 ordinary polynomial products, evaluated as integers at base 2^384. Store the 252 products and the balanced digits of their sum as independently checkable numerical witnesses.
-- source:
--   Saha et al., arXiv:2608.11158v2, Appendix C.1 and the degree-251 cubic–quintic coefficient certificate.

import Definitions.Def_GrothendieckLB_Supplement_cqReplaySums
import Mathlib.Tactic.Eval

namespace GrothendieckLB.Supplement.CQHeadSum
open CQHeadCertificate CQHeadArithmetic

def base : ℤ := 2^384
def w (a b : ℕ) : Interval := if a+b ≤ 251 then weight a b else zeroInterval
def p (a k : ℕ) : Interval := if a ≤ k then power a k else zeroInterval
def center (x : Interval) := x.lo+x.hi
def width (x : Interval) := x.hi-x.lo
def wc (a b : ℕ) : ℤ := (-1)^b*center (w a b)
def pc (a b : ℕ) : ℤ := center (p a b)

def pack (B : ℤ) (f : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | n+1 => f 0+B*pack B (fun k => f (k+1)) n

def rowProduct (a : ℕ) := pack base (wc a) 252*pack base (pc a) 252
def rowsData : Array ℤ := eval% tab 252 rowProduct
def row (a : ℕ) := entry 0 rowsData a
def valuesData : Array ℤ := eval% Id.run do
  let mut x := rowsData.foldl (·+·) 0
  let mut out := #[]
  for _ in [:252] do
    let next := (x+base/2)/base
    out := out.push (x-base*next)
    x := next
  return out
def value (m : ℕ) := entry 0 valuesData m

def good (a j : ℕ) : Bool := decide (|center (w a j)| ≤ 2^148 ∧ 0 ≤ width (w a j) ∧ width (w a j) ≤ 1 ∧
  |center (p a j)| ≤ 2^146 ∧ 0 ≤ width (p a j) ∧ width (p a j) ≤ 256)
def rowHolds (a : ℕ) : Prop := row a=rowProduct a ∧ (List.range 252).all (good a)=true

end GrothendieckLB.Supplement.CQHeadSum


