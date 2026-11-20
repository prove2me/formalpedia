-- Prove2me | Definitions.Def_Buchstab4DT_Core
-- name    : Buchstab4DT_Core
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-19T11:29:23.55402+00:00
-- url     : https://prove2.me/theorems/82681863-f74a-43bc-80cb-f7820e0c2476
-- title:
--   Core data structures and evaluators for 4D triangular Buchstab integral certificates
-- statement:
--   Core data structures, cell geometries, and exact integer evaluators for bounding four-dimensional Buchstab integrals over domains of the form $$\Omega_{A,B,C} = \{(x_0,x_1,x_2,x_3) \in \mathbb{R}^4 : A \le x_0 \le x_1 \le x_2 \le B \le x_3 \le C\}.$$
--
--   The module defines the parameter record `Params4DT` (grid denominators $D_x, D_p$, integer endpoints $A_n < B_n < C_n$, and fixed-point scales $S_v, S_3, S_4$), the core Buchstab predicate `IsBuchstabCore`, the 3D and 4D cell families (`box`, `tri01`, `tri12`, `simp`) together with their adaptive binary/diagonal refinement trees (`BoxTree3`, `BoxTree4`), exact inclusion-exclusion volume and ramp numerators (`cut3Num`, `ramp3Num`, `cut4Num`), and certified leaf/tree evaluators for the 4D integral $I(\varphi)$ (`eval4Leaf`, `eval4TransLeaf`, `evalTree4`) and for the 3D difference-quotient bounds (`evalMpLeaf`, `evalMmLeaf`, `evalTree3`).
--
--   These definitions serve as a reusable, parameter-independent foundation for verifying explicit numerical upper bounds on Wu's four-dimensional Buchstab integrals.
-- source:
--   Wu (2004), Chen's double sieve, Goldbach's conjecture and the twin prime problem, Acta Arith. 114 (2004), 215-273; supporting infrastructure for 4D Buchstab integral bounds in LL_Decomp587j and LL_Decomp587l.

import Mathlib

open Real Set MeasureTheory
open scoped Classical

namespace Buchstab4DT

structure Params4DT where
  D_x : Nat
  D_p : Nat
  A_n : Nat
  B_n : Nat
  C_n : Nat
  S_v : Nat
  S_3 : Nat
  S_4 : Nat
  D_x2 : Nat
  D_x4 : Nat
  D_x5 : Nat
  D_x6 : Nat
  D_p2 : Nat
  D_p3 : Nat
  D_p4 : Nat
  B_sc : Nat
  C_sc : Nat

def Params4DT.Valid (p : Params4DT) : Prop :=
  0 < p.D_x ∧ 0 < p.D_p ∧ 0 < p.A_n ∧ p.A_n < p.B_n ∧ p.B_n < p.C_n ∧
  0 < p.S_v ∧ 0 < p.S_3 ∧ 0 < p.S_4 ∧ p.S_4 = p.S_3 * 100 ∧
  p.D_x2 = p.D_x * p.D_x ∧ p.D_x4 = p.D_x2 * p.D_x2 ∧
  p.D_x5 = p.D_x4 * p.D_x ∧ p.D_x6 = p.D_x4 * p.D_x2 ∧
  p.D_p2 = p.D_p * p.D_p ∧ p.D_p3 = p.D_p2 * p.D_p ∧
  p.D_p4 = p.D_p2 * p.D_p2 ∧ p.B_sc = p.D_p * p.B_n ∧ p.C_sc = p.D_p * p.C_n

def ceilDiv (a b : Nat) : Nat := (a + b - 1) / b

def subPow3 (r h : Nat) : Nat :=
  let t := r - h
  t * t * t

def subPow4 (r h : Nat) : Nat :=
  let t := r - h
  let t2 := t * t
  t2 * t2

def cut3Pos (h0 h1 h2 r : Nat) : Nat :=
  subPow3 r 0 + subPow3 r (h0 + h1) + subPow3 r (h0 + h2) + subPow3 r (h1 + h2)

def cut3Neg (h0 h1 h2 r : Nat) : Nat :=
  subPow3 r h0 + subPow3 r h1 + subPow3 r h2 + subPow3 r (h0 + h1 + h2)

def cut3Num (p : Params4DT) (dx0 dx1 dx2 r : Nat) : Nat :=
  if r == 0 then 0
  else
    let h0 := p.D_p * dx0
    let h1 := p.D_p * dx1
    let h2 := 2 * p.D_p * dx2
    if h0 + h1 + h2 ≤ r then 12 * p.D_p3 * dx0 * dx1 * dx2
    else cut3Pos h0 h1 h2 r - cut3Neg h0 h1 h2 r

def ramp3Pos (h0 h1 h2 r : Nat) : Nat :=
  subPow4 r 0 + subPow4 r (h0 + h1) + subPow4 r (h0 + h2) + subPow4 r (h1 + h2)

def ramp3Neg (h0 h1 h2 r : Nat) : Nat :=
  subPow4 r h0 + subPow4 r h1 + subPow4 r h2 + subPow4 r (h0 + h1 + h2)

def ramp3Num (p : Params4DT) (dx0 dx1 dx2 r : Nat) : Nat :=
  if r == 0 then 0
  else
    let h0 := p.D_p * dx0
    let h1 := p.D_p * dx1
    let h2 := 2 * p.D_p * dx2
    ramp3Pos h0 h1 h2 r - ramp3Neg h0 h1 h2 r

def cut4Pos (h0 h1 h2 h3 r : Nat) : Nat :=
  subPow4 r 0 +
  subPow4 r (h0 + h1) + subPow4 r (h0 + h2) + subPow4 r (h0 + h3) +
  subPow4 r (h1 + h2) + subPow4 r (h1 + h3) + subPow4 r (h2 + h3) +
  subPow4 r (h0 + h1 + h2 + h3)

def cut4Neg (h0 h1 h2 h3 r : Nat) : Nat :=
  subPow4 r h0 + subPow4 r h1 + subPow4 r h2 + subPow4 r h3 +
  subPow4 r (h0 + h1 + h2) + subPow4 r (h0 + h1 + h3) +
  subPow4 r (h0 + h2 + h3) + subPow4 r (h1 + h2 + h3)

def cut4Num (p : Params4DT) (dx0 dx1 dx2 dx3 r : Nat) : Nat :=
  if r == 0 then 0
  else
    let h0 := p.D_p * dx0
    let h1 := p.D_p * dx1
    let h2 := 2 * p.D_p * dx2
    let h3 := p.D_p * dx3
    if h0 + h1 + h2 + h3 ≤ r then 48 * p.D_p4 * dx0 * dx1 * dx2 * dx3
    else cut4Pos h0 h1 h2 h3 r - cut4Neg h0 h1 h2 h3 r

inductive CellKind where
  | box | tri01 | tri12 | simp
  deriving DecidableEq

inductive BoxTree3 where
  | lf
  | s0 (l r : BoxTree3)
  | s1 (l r : BoxTree3)
  | s2 (l r : BoxTree3)
  | sd01 (c0 m c1 : BoxTree3)
  | sd12 (c0 m c1 : BoxTree3)
  | sd012 (c0 m01 m12 c1 : BoxTree3)

inductive BoxTree4 where
  | lf
  | s0 (l r : BoxTree4)
  | s1 (l r : BoxTree4)
  | s2 (l r : BoxTree4)
  | s3 (l r : BoxTree4)
  | sd01 (c0 m c1 : BoxTree4)
  | sd12 (c0 m c1 : BoxTree4)
  | sd012 (c0 m01 m12 c1 : BoxTree4)

def tree3Valid : CellKind → BoxTree3 → Bool
  | _, .lf => true
  | .box, .s0 l r => tree3Valid .box l && tree3Valid .box r
  | .tri12, .s0 l r => tree3Valid .tri12 l && tree3Valid .tri12 r
  | .box, .s1 l r => tree3Valid .box l && tree3Valid .box r
  | .box, .s2 l r => tree3Valid .box l && tree3Valid .box r
  | .tri01, .s2 l r => tree3Valid .tri01 l && tree3Valid .tri01 r
  | .tri01, .sd01 c0 m c1 => tree3Valid .tri01 c0 && tree3Valid .box m && tree3Valid .tri01 c1
  | .tri12, .sd12 c0 m c1 => tree3Valid .tri12 c0 && tree3Valid .box m && tree3Valid .tri12 c1
  | .simp, .sd012 c0 m01 m12 c1 =>
      tree3Valid .simp c0 && tree3Valid .tri01 m01 && tree3Valid .tri12 m12 && tree3Valid .simp c1
  | _, _ => false

def tree4Valid : CellKind → BoxTree4 → Bool
  | _, .lf => true
  | .box, .s0 l r => tree4Valid .box l && tree4Valid .box r
  | .tri12, .s0 l r => tree4Valid .tri12 l && tree4Valid .tri12 r
  | .box, .s1 l r => tree4Valid .box l && tree4Valid .box r
  | .box, .s2 l r => tree4Valid .box l && tree4Valid .box r
  | .tri01, .s2 l r => tree4Valid .tri01 l && tree4Valid .tri01 r
  | knd, .s3 l r => tree4Valid knd l && tree4Valid knd r
  | .tri01, .sd01 c0 m c1 => tree4Valid .tri01 c0 && tree4Valid .box m && tree4Valid .tri01 c1
  | .tri12, .sd12 c0 m c1 => tree4Valid .tri12 c0 && tree4Valid .box m && tree4Valid .tri12 c1
  | .simp, .sd012 c0 m01 m12 c1 =>
      tree4Valid .simp c0 && tree4Valid .tri01 m01 && tree4Valid .tri12 m12 && tree4Valid .simp c1
  | _, _ => false

def facDen : CellKind → Nat
  | .box => 1
  | .tri01 => 2
  | .tri12 => 2
  | .simp => 6

def nVerts3 : CellKind → Nat
  | .box => 8
  | .tri01 => 6
  | .tri12 => 6
  | .simp => 4

def sumVerts3 (f : Nat → Nat → Nat → Nat) :
    CellKind → Nat → Nat → Nat → Nat → Nat → Nat → Nat
  | .box, a0, b0, a1, b1, a2, b2 =>
      f a0 a1 a2 + f a0 a1 b2 + f a0 b1 a2 + f a0 b1 b2 +
      f b0 a1 a2 + f b0 a1 b2 + f b0 b1 a2 + f b0 b1 b2
  | .tri01, a0, b0, _, _, a2, b2 =>
      f a0 a0 a2 + f a0 a0 b2 + f a0 b0 a2 + f a0 b0 b2 + f b0 b0 a2 + f b0 b0 b2
  | .tri12, a0, b0, a1, b1, _, _ =>
      f a0 a1 a1 + f b0 a1 a1 + f a0 a1 b1 + f b0 a1 b1 + f a0 b1 b1 + f b0 b1 b1
  | .simp, a0, b0, _, _, _, _ =>
      f a0 a0 a0 + f a0 a0 b0 + f a0 b0 b0 + f b0 b0 b0

def eval4Leaf (p : Params4DT) (p_n : Nat) (knd : CellKind)
    (n0a n0b n1a n1b n2a n2b n3a n3b : Nat) : Nat :=
  let s_min := p.D_p * (n0a + n1a + 2 * n2a + n3a)
  let s_max := p.D_p * (n0b + n1b + 2 * n2b + n3b)
  let p_sc := p_n * p.D_x
  if p_sc ≤ s_min then 0
  else
    let dx0 := n0b - n0a
    let dx1 := n1b - n1a
    let dx2 := n2b - n2a
    let dx3 := n3b - n3a
    let fd := facDen knd
    if s_max ≤ p_sc then
      let f3 (a0 a1 a2 : Nat) : Nat :=
        ceilDiv (p.S_v * p.D_x5 * p.D_p) (a0 * a1 * a2 * n3a * (p_sc - p.D_p * (a0 + a1 + a2 + n3a))) +
        ceilDiv (p.S_v * p.D_x5 * p.D_p) (a0 * a1 * a2 * n3b * (p_sc - p.D_p * (a0 + a1 + a2 + n3b)))
      let sv := sumVerts3 f3 knd n0a n0b n1a n1b n2a n2b
      ceilDiv (p.S_4 * dx0 * dx1 * dx2 * dx3 * sv) (fd * (2 * nVerts3 knd) * p.D_x4 * p.S_v)
    else
      let vc := cut4Num p dx0 dx1 dx2 dx3 (p_sc - s_min)
      ceilDiv (p.S_4 * p.D_x * vc) (48 * fd * p.D_p4 * n0a * n1a * n2a * n2a * n3a)

def eval4TransLeaf (p : Params4DT) (pa_n : Nat) (knd : CellKind)
    (n0a n0b n1a n1b n2a n2b n3a n3b : Nat) : Nat :=
  let dx0 := n0b - n0a
  let dx1 := n1b - n1a
  let dx2 := n2b - n2a
  let dx3 := n3b - n3a
  let fd := facDen knd
  let num_u := pa_n * p.D_x - p.D_p * (n0b + n1b + n2b + n3b)
  let den_u := p.D_p * n2b
  let om_ub := if 2 * num_u ≤ 3 * den_u then ceilDiv (p.S_v * den_u) num_u else ceilDiv (2 * p.S_v) 3
  let f3 (a0 a1 a2 : Nat) : Nat :=
    ceilDiv (p.S_v * p.D_x5) (a0 * a1 * a2 * a2 * n3a) +
    ceilDiv (p.S_v * p.D_x5) (a0 * a1 * a2 * a2 * n3b)
  let sv := sumVerts3 f3 knd n0a n0b n1a n1b n2a n2b
  let wm := ceilDiv (p.S_4 * dx0 * dx1 * dx2 * dx3 * sv) (fd * (2 * nVerts3 knd) * p.D_x4 * p.S_v)
  ceilDiv (om_ub * wm) p.S_v

def evalTree4 (lfFn : CellKind → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) :
    CellKind → BoxTree4 → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat
  | knd, .lf, a0, b0, a1, b1, a2, b2, a3, b3 => lfFn knd a0 b0 a1 b1 a2 b2 a3 b3
  | knd, .s0 l r, a0, b0, a1, b1, a2, b2, a3, b3 =>
      let m := (a0 + b0) / 2
      evalTree4 lfFn knd l a0 m a1 b1 a2 b2 a3 b3 + evalTree4 lfFn knd r m b0 a1 b1 a2 b2 a3 b3
  | knd, .s1 l r, a0, b0, a1, b1, a2, b2, a3, b3 =>
      let m := (a1 + b1) / 2
      evalTree4 lfFn knd l a0 b0 a1 m a2 b2 a3 b3 + evalTree4 lfFn knd r a0 b0 m b1 a2 b2 a3 b3
  | knd, .s2 l r, a0, b0, a1, b1, a2, b2, a3, b3 =>
      let m := (a2 + b2) / 2
      evalTree4 lfFn knd l a0 b0 a1 b1 a2 m a3 b3 + evalTree4 lfFn knd r a0 b0 a1 b1 m b2 a3 b3
  | knd, .s3 l r, a0, b0, a1, b1, a2, b2, a3, b3 =>
      let m := (a3 + b3) / 2
      evalTree4 lfFn knd l a0 b0 a1 b1 a2 b2 a3 m + evalTree4 lfFn knd r a0 b0 a1 b1 a2 b2 m b3
  | _, .sd01 c0 md c1, a, b, _, _, a2, b2, a3, b3 =>
      let m := (a + b) / 2
      evalTree4 lfFn .tri01 c0 a m a m a2 b2 a3 b3 +
      evalTree4 lfFn .box md a m m b a2 b2 a3 b3 +
      evalTree4 lfFn .tri01 c1 m b m b a2 b2 a3 b3
  | _, .sd12 c0 md c1, a0, b0, a, b, _, _, a3, b3 =>
      let m := (a + b) / 2
      evalTree4 lfFn .tri12 c0 a0 b0 a m a m a3 b3 +
      evalTree4 lfFn .box md a0 b0 a m m b a3 b3 +
      evalTree4 lfFn .tri12 c1 a0 b0 m b m b a3 b3
  | _, .sd012 c0 m01 m12 c1, a, b, _, _, _, _, a3, b3 =>
      let m := (a + b) / 2
      evalTree4 lfFn .simp c0 a m a m a m a3 b3 +
      evalTree4 lfFn .tri01 m01 a m a m m b a3 b3 +
      evalTree4 lfFn .tri12 m12 a m m b m b a3 b3 +
      evalTree4 lfFn .simp c1 m b m b m b a3 b3

def addPair (x y : Nat × Nat) : Nat × Nat := (x.1 + y.1, x.2 + y.2)

def evalMpLeaf (p : Params4DT) (pa_n pb_n : Nat) (knd : CellKind)
    (n0a n0b n1a n1b n2a n2b : Nat) : Nat × Nat :=
  let fd := facDen knd
  let dx0 := n0b - n0a
  let dx1 := n1b - n1a
  let dx2 := n2b - n2a
  let s_min := p.D_p * (n0a + n1a + 2 * n2a)
  let s_max := p.D_p * (n0b + n1b + 2 * n2b)
  let pa_sc := pa_n * p.D_x
  let pb_sc := pb_n * p.D_x
  let pos :=
    if s_max + p.C_sc ≤ pa_sc || pb_sc ≤ s_min + p.B_sc then 0
    else
      let denom_sc := max p.B_sc (pa_sc - s_max)
      match knd with
      | .box =>
          let v_slab := cut3Num p dx0 dx1 dx2 (pb_sc - p.B_sc - s_min) - cut3Num p dx0 dx1 dx2 (pa_sc - p.C_sc - s_min)
          ceilDiv (p.S_3 * p.D_x2 * v_slab) (12 * p.D_p2 * n0a * n1a * n2a * n2a * denom_sc)
      | _ =>
          ceilDiv (p.S_3 * p.D_x2 * p.D_p * dx0 * dx1 * dx2) (fd * n0a * n1a * n2a * n2a * denom_sc)
  let m_lo_sc := max p.B_sc (min p.C_sc (pa_sc - s_max))
  let neg :=
    if m_lo_sc ≤ p.B_sc then 0
    else
      let (c0, c1, c2) :=
        match knd with
        | .box => (6 * (n0a + n0b), 6 * (n1a + n1b), 6 * (n2a + n2b))
        | .tri01 => (4 * (2 * n0a + n0b), 4 * (n0a + 2 * n0b), 6 * (n2a + n2b))
        | .tri12 => (6 * (n0a + n0b), 4 * (2 * n1a + n1b), 4 * (n1a + 2 * n1b))
        | .simp => (3 * (3 * n0a + n0b), 6 * (n0a + n0b), 3 * (n0a + 3 * n0b))
      let xm2_sc := p.B_sc + m_lo_sc
      let rem12_sc := 12 * pb_sc - p.D_p * (c0 + c1 + c2) - 6 * xm2_sc
      (p.S_3 * 497664 * p.D_x2 * p.D_p2 * dx0 * dx1 * dx2 * (m_lo_sc - p.B_sc)) /
        (fd * c0 * c1 * c2 * xm2_sc * rem12_sc * rem12_sc)
  (pos, neg)

def evalMmLeaf (p : Params4DT) (pa_n pb_n : Nat) (knd : CellKind)
    (n0a n0b n1a n1b n2a n2b : Nat) : Nat × Nat :=
  let fd := facDen knd
  let dx0 := n0b - n0a
  let dx1 := n1b - n1a
  let dx2 := n2b - n2a
  let s_min := p.D_p * (n0a + n1a + 2 * n2a)
  let s_max := p.D_p * (n0b + n1b + 2 * n2b)
  let pa_sc := pa_n * p.D_x
  let pb_sc := pb_n * p.D_x
  let pos :=
    if pb_sc ≤ s_min + p.B_sc then 0
    else if s_max + p.C_sc ≤ pa_sc then
      let f3 (a0 a1 a2 : Nat) : Nat :=
        let rb := pa_sc - p.D_p * (a0 + a1 + a2 + p.B_n)
        let rc := pa_sc - p.D_p * (a0 + a1 + a2 + p.C_n)
        ceilDiv (p.S_v * p.D_x6 * p.D_p2) (a0 * a1 * a2 * p.B_n * rb * rb) +
        ceilDiv (p.S_v * p.D_x6 * p.D_p2) (a0 * a1 * a2 * p.C_n * rc * rc)
      let sv := sumVerts3 f3 knd n0a n0b n1a n1b n2a n2b
      ceilDiv (p.S_3 * dx0 * dx1 * dx2 * (p.C_n - p.B_n) * sv) (2 * fd * nVerts3 knd * p.D_x4 * p.S_v)
    else
      let rn := ramp3Num p dx0 dx1 dx2 (pb_sc - p.B_sc - s_min) - ramp3Num p dx0 dx1 dx2 (pb_sc - p.C_sc - s_min)
      ceilDiv (p.S_3 * p.D_x2 * rn) (48 * fd * p.D_p4 * n0a * n1a * n2a * n2a * n2a * p.B_n)
  let neg :=
    if s_max + p.C_sc ≤ pb_sc || pa_sc ≤ s_min + p.B_sc then 0
    else
      let denom_x3_sc := min p.C_sc (pb_sc - s_min)
      let denom_x2_sc := p.D_p * n2b + (pb_sc - pa_sc)
      match knd with
      | .box =>
          let v_slab := cut3Num p dx0 dx1 dx2 (pa_sc - p.B_sc - s_min) - cut3Num p dx0 dx1 dx2 (pb_sc - p.C_sc - s_min)
          (p.S_3 * p.D_x2 * v_slab) / (12 * p.D_p * n0b * n1b * n2b * denom_x3_sc * denom_x2_sc)
      | _ =>
          if pb_sc ≤ s_min + p.C_sc && s_max + p.B_sc ≤ pa_sc then
            (p.S_3 * p.D_x2 * p.D_p2 * dx0 * dx1 * dx2) / (fd * n0b * n1b * n2b * denom_x3_sc * denom_x2_sc)
          else 0
  (pos, neg)

def evalTree3 (lfFn : CellKind → Nat → Nat → Nat → Nat → Nat → Nat → Nat × Nat) :
    CellKind → BoxTree3 → Nat → Nat → Nat → Nat → Nat → Nat → Nat × Nat
  | knd, .lf, a0, b0, a1, b1, a2, b2 => lfFn knd a0 b0 a1 b1 a2 b2
  | knd, .s0 l r, a0, b0, a1, b1, a2, b2 =>
      let m := (a0 + b0) / 2
      addPair (evalTree3 lfFn knd l a0 m a1 b1 a2 b2) (evalTree3 lfFn knd r m b0 a1 b1 a2 b2)
  | knd, .s1 l r, a0, b0, a1, b1, a2, b2 =>
      let m := (a1 + b1) / 2
      addPair (evalTree3 lfFn knd l a0 b0 a1 m a2 b2) (evalTree3 lfFn knd r a0 b0 m b1 a2 b2)
  | knd, .s2 l r, a0, b0, a1, b1, a2, b2 =>
      let m := (a2 + b2) / 2
      addPair (evalTree3 lfFn knd l a0 b0 a1 b1 a2 m) (evalTree3 lfFn knd r a0 b0 a1 b1 m b2)
  | _, .sd01 c0 md c1, a, b, _, _, a2, b2 =>
      let m := (a + b) / 2
      addPair (addPair (evalTree3 lfFn .tri01 c0 a m a m a2 b2)
                       (evalTree3 lfFn .box md a m m b a2 b2))
              (evalTree3 lfFn .tri01 c1 m b m b a2 b2)
  | _, .sd12 c0 md c1, a0, b0, a, b, _, _ =>
      let m := (a + b) / 2
      addPair (addPair (evalTree3 lfFn .tri12 c0 a0 b0 a m a m)
                       (evalTree3 lfFn .box md a0 b0 a m m b))
              (evalTree3 lfFn .tri12 c1 a0 b0 m b m b)
  | _, .sd012 c0 m01 m12 c1, a, b, _, _, _, _ =>
      let m := (a + b) / 2
      addPair (addPair (evalTree3 lfFn .simp c0 a m a m a m)
                       (evalTree3 lfFn .tri01 m01 a m a m m b))
              (addPair (evalTree3 lfFn .tri12 m12 a m m b m b)
                       (evalTree3 lfFn .simp c1 m b m b m b))

noncomputable section

def IsBuchstabCore (ω : ℝ → ℝ) : Prop :=
  ContinuousOn ω (Set.Ici 1) ∧
  (∀ u, 1 ≤ u → u ≤ 2 → ω u = 1 / u) ∧
  (∀ u, 2 < u → HasDerivAt (fun t => t * ω t) (ω (u - 1)) u) ∧
  (∀ u, u < 1 → ω u = 0)

def Params4DT.A_R (p : Params4DT) : ℝ := (p.A_n : ℝ) / p.D_x
def Params4DT.B_R (p : Params4DT) : ℝ := (p.B_n : ℝ) / p.D_x
def Params4DT.C_R (p : Params4DT) : ℝ := (p.C_n : ℝ) / p.D_x

def cell3Set (knd : CellKind) (a0 b0 a1 b1 a2 b2 : ℝ) : Set (Fin 3 → ℝ) :=
  match knd with
  | .box   => {x | x 0 ∈ Icc a0 b0 ∧ x 1 ∈ Icc a1 b1 ∧ x 2 ∈ Icc a2 b2}
  | .tri01 => {x | x 0 ∈ Icc a0 b0 ∧ x 1 ∈ Icc a0 b0 ∧ x 2 ∈ Icc a2 b2 ∧ x 0 ≤ x 1}
  | .tri12 => {x | x 0 ∈ Icc a0 b0 ∧ x 1 ∈ Icc a1 b1 ∧ x 2 ∈ Icc a1 b1 ∧ x 1 ≤ x 2}
  | .simp  => {x | x 0 ∈ Icc a0 b0 ∧ x 1 ∈ Icc a0 b0 ∧ x 2 ∈ Icc a0 b0 ∧ x 0 ≤ x 1 ∧ x 1 ≤ x 2}

def cell4Set (knd : CellKind) (a0 b0 a1 b1 a2 b2 a3 b3 : ℝ) : Set (Fin 4 → ℝ) :=
  match knd with
  | .box   => {x | x 0 ∈ Icc a0 b0 ∧ x 1 ∈ Icc a1 b1 ∧ x 2 ∈ Icc a2 b2 ∧ x 3 ∈ Icc a3 b3}
  | .tri01 => {x | x 0 ∈ Icc a0 b0 ∧ x 1 ∈ Icc a0 b0 ∧ x 2 ∈ Icc a2 b2 ∧ x 3 ∈ Icc a3 b3 ∧ x 0 ≤ x 1}
  | .tri12 => {x | x 0 ∈ Icc a0 b0 ∧ x 1 ∈ Icc a1 b1 ∧ x 2 ∈ Icc a1 b1 ∧ x 3 ∈ Icc a3 b3 ∧ x 1 ≤ x 2}
  | .simp  => {x | x 0 ∈ Icc a0 b0 ∧ x 1 ∈ Icc a0 b0 ∧ x 2 ∈ Icc a0 b0 ∧ x 3 ∈ Icc a3 b3 ∧ x 0 ≤ x 1 ∧ x 1 ≤ x 2}

def equivFin4_3 : (Fin 4 → ℝ) ≃ᵐ ℝ × (Fin 3 → ℝ) :=
  MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) 3

def sumVerts3R (f : (Fin 3 → ℝ) → ℝ) :
    CellKind → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ
  | .box, a0, b0, a1, b1, a2, b2 =>
      f ![a0, a1, a2] + f ![a0, a1, b2] + f ![a0, b1, a2] + f ![a0, b1, b2] +
      f ![b0, a1, a2] + f ![b0, a1, b2] + f ![b0, b1, a2] + f ![b0, b1, b2]
  | .tri01, a0, b0, _, _, a2, b2 =>
      f ![a0, a0, a2] + f ![a0, a0, b2] + f ![a0, b0, a2] + f ![a0, b0, b2] +
      f ![b0, b0, a2] + f ![b0, b0, b2]
  | .tri12, a0, b0, a1, b1, _, _ =>
      f ![a0, a1, a1] + f ![b0, a1, a1] + f ![a0, a1, b1] + f ![b0, a1, b1] +
      f ![a0, b1, b1] + f ![b0, b1, b1]
  | .simp, a0, b0, _, _, _, _ =>
      f ![a0, a0, a0] + f ![a0, a0, b0] + f ![a0, b0, b0] + f ![b0, b0, b0]

def centroid3R : CellKind → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → (Fin 3 → ℝ)
  | .box, a0, b0, a1, b1, a2, b2 => ![(a0 + b0) / 2, (a1 + b1) / 2, (a2 + b2) / 2]
  | .tri01, a0, b0, _, _, a2, b2 => ![(2 * a0 + b0) / 3, (a0 + 2 * b0) / 3, (a2 + b2) / 2]
  | .tri12, a0, b0, a1, b1, _, _ => ![(a0 + b0) / 2, (2 * a1 + b1) / 3, (a1 + 2 * b1) / 3]
  | .simp, a0, b0, _, _, _, _ => ![(3 * a0 + b0) / 4, (a0 + b0) / 2, (a0 + 3 * b0) / 4]

def cell3Ok (knd : CellKind) (a0 b0 a1 b1 a2 b2 : ℝ) : Prop :=
  a0 ≤ b0 ∧ a1 ≤ b1 ∧ a2 ≤ b2 ∧
  match knd with
  | .box => True
  | .tri01 => a0 = a1 ∧ b0 = b1
  | .tri12 => a1 = a2 ∧ b1 = b2
  | .simp => a0 = a1 ∧ b0 = b1 ∧ a1 = a2 ∧ b1 = b2

def cut3SumR (h0 h1 h2 R : ℝ) : ℝ :=
  ((max 0 R) ^ 3 + (max 0 (R - h0 - h1)) ^ 3 + (max 0 (R - h0 - h2)) ^ 3 + (max 0 (R - h1 - h2)) ^ 3) -
  ((max 0 (R - h0)) ^ 3 + (max 0 (R - h1)) ^ 3 + (max 0 (R - h2)) ^ 3 + (max 0 (R - h0 - h1 - h2)) ^ 3)

def ramp3SumR (h0 h1 h2 R : ℝ) : ℝ :=
  ((max 0 R) ^ 4 + (max 0 (R - h0 - h1)) ^ 4 + (max 0 (R - h0 - h2)) ^ 4 + (max 0 (R - h1 - h2)) ^ 4) -
  ((max 0 (R - h0)) ^ 4 + (max 0 (R - h1)) ^ 4 + (max 0 (R - h2)) ^ 4 + (max 0 (R - h0 - h1 - h2)) ^ 4)

def cut4SumR (h0 h1 h2 h3 R : ℝ) : ℝ :=
  ((max 0 R) ^ 4 + (max 0 (R - h0 - h1)) ^ 4 + (max 0 (R - h0 - h2)) ^ 4 + (max 0 (R - h0 - h3)) ^ 4 +
   (max 0 (R - h1 - h2)) ^ 4 + (max 0 (R - h1 - h3)) ^ 4 + (max 0 (R - h2 - h3)) ^ 4 +
   (max 0 (R - h0 - h1 - h2 - h3)) ^ 4) -
  ((max 0 (R - h0)) ^ 4 + (max 0 (R - h1)) ^ 4 + (max 0 (R - h2)) ^ 4 + (max 0 (R - h3)) ^ 4 +
   (max 0 (R - h0 - h1 - h2)) ^ 4 + (max 0 (R - h0 - h1 - h3)) ^ 4 +
   (max 0 (R - h0 - h2 - h3)) ^ 4 + (max 0 (R - h1 - h2 - h3)) ^ 4)

def cell3Valid (p : Params4DT) (knd : CellKind) (n0a n0b n1a n1b n2a n2b : ℕ) : Prop :=
  p.A_n ≤ n0a ∧ n0a ≤ n0b ∧ n0b ≤ p.B_n ∧
  p.A_n ≤ n1a ∧ n1a ≤ n1b ∧ n1b ≤ p.B_n ∧
  p.A_n ≤ n2a ∧ n2a ≤ n2b ∧ n2b ≤ p.B_n ∧
  (knd = .tri01 → n0a = n1a ∧ n0b = n1b) ∧
  (knd = .tri12 → n1a = n2a ∧ n1b = n2b) ∧
  (knd = .simp → n0a = n1a ∧ n0b = n1b ∧ n1a = n2a ∧ n1b = n2b)

def cell4Valid (p : Params4DT) (knd : CellKind) (n0a n0b n1a n1b n2a n2b n3a n3b : ℕ) : Prop :=
  cell3Valid p knd n0a n0b n1a n1b n2a n2b ∧ p.B_n ≤ n3a ∧ n3a ≤ n3b ∧ n3b ≤ p.C_n

def I_fn (p : Params4DT) (ω : ℝ → ℝ) (φ : ℝ) : ℝ :=
  ∫ x in cell4Set .simp p.A_R p.B_R p.A_R p.B_R p.A_R p.B_R p.B_R p.C_R,
    ω ((φ - ∑ j, x j) / x 2) / ((∏ j, x j) * x 2)

def G_fn (p : Params4DT) (φ : ℝ) (y : Fin 3 → ℝ) : ℝ :=
  ∫ x3 in p.B_R..(max p.B_R (min p.C_R (φ - y 0 - y 1 - 2 * y 2))),
    1 / (x3 * (φ - (y 0 + y 1 + y 2) - x3))

end

end Buchstab4DT


