-- Prove2me | Definitions.Def_MasulloRH_CentralInterval
-- name    : MasulloRH_CentralInterval
-- status  : Definition
-- author  : @scuba8684
-- created : 2026-11-26T14:03:05.624804+00:00
-- url     : https://prove2.me/theorems/091c2199-357e-59c3-8ed3-c6cd523ce351
-- title:
--   Signed rational intervals with outward-rounded binary powers and an exponential enclosure
-- statement:
--   A box has two rational endpoints. It encloses a real number if that real number lies between its endpoints. The arithmetic operations include signed products, squares, reciprocals of positive intervals, and binary powers rounded outward on an integer grid of spacing $2^{-96}$. The exponential uses steps of $2^{-40}$ together with a small upper enclosure below $-64$. The structure Sound lists the semantic assertions for these operations.
-- source:
--   The Masullo height-two certificate https://prove2.me/theorems/cc487734-5ed4-5457-b10a-df505d0aef9e and its central curvature-row theorem https://prove2.me/theorems/b0533253-e9c5-595e-be4f-d607f9549942.

import Mathlib.Data.Rat.Floor
import Mathlib.Analysis.SpecialFunctions.Exp

namespace MasulloRH.CentralInterval

abbrev Box := ℚ × ℚ

def Covers (a : Box) (x : ℝ) : Prop := (a.1:ℝ) ≤ x ∧ x ≤ (a.2:ℝ)
def point (r : ℚ) : Box := (r,r)
def negB (a : Box) : Box := (-a.2,-a.1)
def subB (a b : Box) := a + negB b
def mag (a : Box) := max (-a.1) a.2
def absB (a : Box) : Box := (max 0 (max a.1 (-a.2)),mag a)
def sqB (a : Box) : Box := ((absB a).1^2,(absB a).2^2)
def mulB (a b : Box) : Box :=
  (min (min (a.1*b.1) (a.1*b.2)) (min (a.2*b.1) (a.2*b.2)),
   max (max (a.1*b.1) (a.1*b.2)) (max (a.2*b.1) (a.2*b.2)))
def invB (a : Box) : Box := (1/a.2,1/a.1)

/-- Fixed-point denominator for integer arithmetic with 96 fractional bits. -/
def S : ℕ := 79228162514264337593543950336
def valQ (n : ℕ) : ℚ := n/(S:ℚ)
def times (up : Bool) (a b : ℕ) : ℕ := (a*b)/S + (if up then 1 else 0)
def bin (up : Bool) (a : ℕ) : ℕ → ℕ → ℕ
  | 0,_ => S
  | k+1,n => if n = 0 then S else
      let y := bin up a k (n/2)
      let t := times up y y
      if n%2=0 then t else times up t a
/-- Enclose signed powers by outward-rounded binary powering on natural numbers. -/
def powB (a : Box) (n : ℕ) : Box :=
  let lo := ⌊(absB a).1 * (S:ℚ)⌋₊
  let hi := ⌈(absB a).2 * (S:ℚ)⌉₊
  let l := valQ (bin false lo (n.log2+1) n)
  let u := valQ (bin true hi (n.log2+1) n)
  if n%2=0 ∨ 0 ≤ a.1 then (l,u) else if a.2 ≤ 0 then (-u,-l) else (-u,u)

def ticks : ℚ := 1099511627776
def step : ℚ := 1/ticks
def pbase : Box := (1+step,1/(1-step))
def nbase : Box := (1-step,1/(1+step))

/-- Enclose a rational exponential using a single microscopic step and binary powers. -/
def expPoint (t : ℚ) : Box :=
  if t ≤ -64 then (0,1/(2:ℚ)^64) else
    let n := ⌊|t| * ticks⌋₊
    if t < 0 then
      let a := powB nbase n
      ((mulB a nbase).1,a.2)
    else
      let a := powB pbase n
      (a.1,(mulB a pbase).2)
def expB (a : Box) : Box := ((expPoint a.1).1,(expPoint a.2).2)

/-- Semantic contract for outward-rounded real operations over rational endpoints. -/
structure Sound : Prop where
  point_ok : ∀ t, Covers (point t) (t:ℝ)
  add_ok : ∀ {a b x y}, Covers a x → Covers b y → Covers (a+b) (x+y)
  sub_ok : ∀ {a b x y}, Covers a x → Covers b y → Covers (subB a b) (x-y)
  neg_ok : ∀ {a x}, Covers a x → Covers (negB a) (-x)
  mul_ok : ∀ {a b x y}, Covers a x → Covers b y → Covers (mulB a b) (x*y)
  abs_ok : ∀ {a x}, Covers a x → Covers (absB a) |x|
  sq_ok : ∀ {a x}, Covers a x → Covers (sqB a) (x^2)
  inv_ok : ∀ {a x}, 0 < a.1 → Covers a x → Covers (invB a) (1/x)
  pow_ok : ∀ {a x}, Covers a x → ∀ n, Covers (powB a n) (x^n)
  exp_ok : ∀ {a x}, Covers a x → Covers (expB a) (Real.exp x)
  sum_ok : ∀ {ι : Type} [Fintype ι] (a : ι → Box) (f : ι → ℝ),
    (∀ i, Covers (a i) (f i)) → Covers (∑ i, a i) (∑ i, f i)
end MasulloRH.CentralInterval


