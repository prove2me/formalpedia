-- Prove2me | Definitions.Def_Submission_ThreeSum_Karatsuba
-- name    : Submission_ThreeSum_Karatsuba
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T06:38:32.037199+00:00
-- url     : https://prove2.me/theorems/31b50fb6-c384-4ac3-82c3-4bbd8a97a6f2
-- title:
--   Karatsuba
-- statement:
--   Definitions and structural lemmas for Karatsuba, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Karatsuba.lean

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
namespace ThreeSum.Karatsuba
open Polynomial
noncomputable def asPolynomial : List ℤ → Polynomial ℤ
  | [] => 0
  | a :: as => C a + X * asPolynomial as
def plus : List ℤ → List ℤ → List ℤ
  | [], bs => bs
  | as, [] => as
  | a :: as, b :: bs => (a + b) :: plus as bs
def negate (as : List ℤ) : List ℤ := as.map (fun a => -a)
def minus (as bs : List ℤ) : List ℤ := plus as (negate bs)
def shift (n : ℕ) (as : List ℤ) : List ℤ := List.replicate n 0 ++ as
def multiply : ℕ → List ℤ → List ℤ → List ℤ
  | 0, as, bs => [as.headD 0 * bs.headD 0]
  | k + 1, as, bs =>
    let n := 2 ^ k
    let a0 := as.take n
    let a1 := as.drop n
    let b0 := bs.take n
    let b1 := bs.drop n
    let z0 := multiply k a0 b0
    let z2 := multiply k a1 b1
    let z1 := minus (minus (multiply k (plus a0 a1) (plus b0 b1)) z0) z2
    plus z0 (shift n (plus z1 (shift n z2)))
def plusWork (as bs : List ℤ) : ℕ := 2 * min as.length bs.length + 1
def negateWork (as : List ℤ) : ℕ := 2 * as.length + 1
def minusWork (as bs : List ℤ) : ℕ := negateWork bs + plusWork as (negate bs) + 1
def shiftWork (n : ℕ) : ℕ := 2 * n + 1
def splitWork (n : ℕ) (as : List ℤ) : ℕ := 2 * min n as.length + 2
def nodeWork (k : ℕ) (as bs : List ℤ) : ℕ :=
  let n := 2 ^ k
  let a0 := as.take n
  let a1 := as.drop n
  let b0 := bs.take n
  let b1 := bs.drop n
  let z0 := multiply k a0 b0
  let z2 := multiply k a1 b1
  let p := multiply k (plus a0 a1) (plus b0 b1)
  let q := minus p z0
  let z1 := minus q z2
  splitWork n as + splitWork n bs + plusWork a0 a1 + plusWork b0 b1 +
    minusWork p z0 + minusWork q z2 + shiftWork n + plusWork z1 (shift n z2) +
    shiftWork n + plusWork z0 (shift n (plus z1 (shift n z2))) + 2 * k + 20
def multiplyWork : ℕ → List ℤ → List ℤ → ℕ
  | 0, _, _ => 3
  | k + 1, as, bs =>
    let n := 2 ^ k
    multiplyWork k (as.take n) (bs.take n) +
      multiplyWork k (as.drop n) (bs.drop n) +
      multiplyWork k (plus (as.take n) (as.drop n))
        (plus (bs.take n) (bs.drop n)) + nodeWork k as bs
end ThreeSum.Karatsuba


