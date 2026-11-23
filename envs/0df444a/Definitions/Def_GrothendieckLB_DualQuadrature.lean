-- Prove2me | Definitions.Def_GrothendieckLB_DualQuadrature
-- name    : GrothendieckLB_DualQuadrature
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-23T16:30:40.580879+00:00
-- url     : https://prove2.me/theorems/90df1793-5ae9-4373-9703-9dd22313ef0a
-- title:
--   Rational quadrature for the Gaussian dual cubic bound
-- statement:
--   A finite certificate for bounding the Gaussian expectation of a priced Hermite cubic. Each mesh node encloses the Gaussian density and the even and odd Hermite factors. Adjacent nodes give an upper trapezoidal sum with a cubic interpolation allowance. A binary tree covers the coefficient directions, and two endpoint tests bound a full price interval by convexity. Coordinate and height tests use integer arithmetic at scale $2^{23}$.
-- source:
--   R. Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158v2, Appendix D.3, Lemma D.4 and Eq. (57), pp. 50–52. The interpolation-based quadrature and rational certificate adapt the construction by Igor Valuev in Prove2Me submission c940ceea-7150-49f4-b2ff-e3ae1aac955b.

import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Nat.Factorial.Basic

section

namespace GrothendieckLB.DualQuadrature

def scale : Int := 8388608

structure Node where
  pos : Int
  dens : Int
  lo : Int
  hi : Int
  even : Int
  odd : Int
  err : Int
  deriving Repr, DecidableEq, Inhabited

structure Box where
  full : Bool
  e : Int
  d : Int
  xmin : Int
  xmax : Int
  ymin : Int
  ymax : Int
  deriving Repr, DecidableEq, Inhabited

def xbound (b : Box) (n : Node) : Int :=
  if b.full then
    let p := b.ymin*n.lo
    let q := b.ymin*n.hi
    let r := b.ymax*n.lo
    let s := b.ymax*n.hi
    let hi := b.xmax*scale + max (max p q) (max r s)
    let lo := b.xmin*scale + min (min p q) (min r s)
    b.e * max hi (-lo)
  else b.e*n.even*scale

def height (b : Box) (c : Int) (n : Node) : Int :=
  let x := xbound b n
  let y := b.d*n.odd*scale
  let t := (c*n.pos - n.err*scale)*scale
  max 0 (max (x+y-t) (2*(max x y-t)))

def segments (b : Box) (c : Int) (n : Node) : List Node → Int
  | [] => 0
  | m::ns => (height b c n + height b c m)*(m.pos-n.pos)*n.dens + segments b c m ns

def total (b : Box) (c : Int) : List Node → Int
  | [] => 0
  | n::ns => segments b c n ns

def endpoint (nodes : List Node) (b : Box) (c lim : Int) : Bool :=
  decide (total b c nodes ≤ 2*scale^4*lim)

end GrothendieckLB.DualQuadrature

end

section

namespace GrothendieckLB.DualQuadrature

def qval (n : Int) : ℚ := (n:ℚ)/8388608
def qprice (c : Int) : ℚ := (c:ℚ)/1000000
def taylorSum (x : ℚ) : Nat → ℚ
  | 0 => 0
  | n+1 => taylorSum x n + x^n / (n.factorial : ℚ)

def taylor (x : ℚ) : ℚ := taylorSum x 21

def nodeCheck (n : Node) : Bool :=
  let s := qval n.pos
  let z := s^2-1
  let A := z*qval 5931641
  let B := z*qval 5931642
  decide (0 ≤ n.pos ∧ 0 ≤ n.even ∧ 0 ≤ n.odd ∧ 0 ≤ n.dens ∧
    qval n.lo ≤ min A B ∧ max A B ≤ qval n.hi ∧
    1+z^2/2 ≤ (qval n.even)^2 ∧ s^2+(s^3-3*s)^2/6 ≤ (qval n.odd)^2 ∧
    1 ≤ qval n.dens * taylor (s^2/2))

def edgeCheck (n m : Node) : Bool :=
  let l := qval n.pos
  let h := qval m.pos
  let err := (1+2*h)*(h-l)^2/4
  decide (l<h ∧ err ≤ qval n.err ∧ err ≤ qval m.err)

def chainCheck : List Node → Bool
  | [] => false
  | [n] => nodeCheck n && decide (n.pos=8*scale)
  | n::m::ns => nodeCheck n && edgeCheck n m && chainCheck (m::ns)

structure Span where
  dl : Int
  du : Int
  yl : Int
  yu : Int
  deriving Repr, Inhabited, DecidableEq

def entire : Span := ⟨0,scale,-scale,scale⟩

def geom (w : Span) (b : Box) : Bool :=
  let yminabs := max 0 (max w.yl (-w.yu))
  let ymaxabs := max (-w.yl) w.yu
  decide (0≤w.dl ∧ 0≤b.e ∧ scale^2≤b.e^2+w.dl^2 ∧ w.du≤b.d ∧
    0≤b.xmax ∧ scale^2 ≤ b.xmax^2+yminabs^2 ∧ b.xmin^2+ymaxabs^2≤ scale^2 ∧
    b.ymin≤w.yl ∧ w.yu≤b.ymax)

structure Band where
  lo : Int
  hi : Int
  u : Int
  v : Int
  clo : Int
  chi : Int
  L : Int
  H : Int
  deriving Repr, Inhabited, DecidableEq

def bandCheck (v : Band) : Bool := decide
  (v.lo<v.hi ∧ 0≤v.lo ∧ 0≤v.u ∧ 0≤v.v ∧ v.u^2+v.v^2≤ scale^2 ∧
   qval v.clo ≤ qprice v.lo ∧ qval v.chi ≤ qprice v.hi ∧
   qval v.L+1/100000000 ≤ 3*(qval v.u+(qval v.v-1)*qprice v.lo) ∧
   qval v.H+1/100000000 ≤ 3*(qval v.u+(qval v.v-1)*qprice v.hi))

inductive Tree where
  | leaf (b : Box)
  | d (cut : Int) (left right : Tree)
  | y (cut : Int) (left right : Tree)
  deriving Inhabited

def treeCheck (ns : List Node) (v : Band) (w : Span) : Tree → Bool
  | .leaf b => geom w b && endpoint ns b v.clo v.L && endpoint ns b v.chi v.H
  | .d k l r => treeCheck ns v {w with du:=k} l && treeCheck ns v {w with dl:=k} r
  | .y k l r => treeCheck ns v {w with yu:=k} l && treeCheck ns v {w with yl:=k} r

end GrothendieckLB.DualQuadrature

end

namespace GrothendieckLB.DualQuadrature

def start : List Node → Bool
  | n::_ => decide (n.pos=0)
  | [] => false

end GrothendieckLB.DualQuadrature


