-- Prove2me | Definitions.Def_HodgeComputerFormal_PairAlgebra
-- name    : HodgeComputerFormal_PairAlgebra
-- status  : Definition
-- author  : @benediamond
-- created : 2026-11-24T03:31:01.739823+00:00
-- url     : https://prove2.me/theorems/b936d11c-079b-439b-9a9c-8edce9327982
-- title:
--   Polymorphic quadratic pair algebra `PairAlg R` and Sylvester resultant `syl5`
-- statement:
--   Polymorphic quadratic algebra `PairAlg R` representing elements $c_0 + c_1 W$ modulo $W^2 + b W + c = 0$ over any commutative ring $R$, equipped with ring operations, norm $\operatorname{nm}(c_0 + c_1 W) = c_0^2 - b c_0 c_1 + c c_1^2$, functorial base change `PairAlg.map`, Vieta norm factorization `evalAt_nm`, and the $5 \times 5$ Sylvester resultant `syl5` for a degree-2 and degree-3 polynomial pair.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/formal/lean/QuadraticCovers/PairAlgebra.lean

import Mathlib.Tactic

set_option autoImplicit false

/-! Polymorphic quadratic quotient algebra `PairAlg R = R[W] / (W^2 + bW * W + cW)`
and the explicit 13-term 5×5 Sylvester resultant `syl5` of a quadratic and a cubic
over any commutative ring `R`, together with its lifted pair version `syl5Pair` and
the quadratic Euler trace cancellation lemma `PairAlg.eulerTr_div`.

Extracted from the `symmetric-sextic-residual` construction (`benediamond`). -/

namespace QuadraticCovers

/-- Element `c0 + c1 * W` of the quadratic quotient `R[W] / (W^2 + bW * W + cW)`. -/
@[ext]
structure PairAlg (R : Type*) where
  c0 : R
  c1 : R

namespace PairAlg

section RingOps
variable {R : Type*} [CommRing R]

def zero : PairAlg R := ⟨0, 0⟩
def one : PairAlg R := ⟨1, 0⟩
def W : PairAlg R := ⟨0, 1⟩
def ofScalar (s : R) : PairAlg R := ⟨s, 0⟩
def add (x y : PairAlg R) : PairAlg R := ⟨x.c0 + y.c0, x.c1 + y.c1⟩
def sub (x y : PairAlg R) : PairAlg R := ⟨x.c0 - y.c0, x.c1 - y.c1⟩
def neg (x : PairAlg R) : PairAlg R := ⟨-x.c0, -x.c1⟩
def smul (s : R) (x : PairAlg R) : PairAlg R := ⟨s * x.c0, s * x.c1⟩

def mul (bW cW : R) (x y : PairAlg R) : PairAlg R :=
  ⟨x.c0 * y.c0 - x.c1 * y.c1 * cW, x.c0 * y.c1 + x.c1 * y.c0 - x.c1 * y.c1 * bW⟩

def conj (bW : R) (x : PairAlg R) : PairAlg R := ⟨x.c0 - x.c1 * bW, -x.c1⟩

def nm (bW cW : R) (x : PairAlg R) : R :=
  x.c0 ^ 2 - x.c0 * x.c1 * bW + x.c1 ^ 2 * cW

def evalAt (w : R) (x : PairAlg R) : R := x.c0 + x.c1 * w

def map {S : Type*} [CommRing S] (f : R →+* S) (x : PairAlg R) : PairAlg S := ⟨f x.c0, f x.c1⟩

lemma evalAt_zero (w : R) : evalAt w (zero : PairAlg R) = 0 := by simp [evalAt, zero]
lemma evalAt_one (w : R) : evalAt w (one : PairAlg R) = 1 := by simp [evalAt, one]
lemma evalAt_W (w : R) : evalAt w (W : PairAlg R) = w := by simp [evalAt, W]
lemma evalAt_ofScalar (w s : R) : evalAt w (ofScalar s) = s := by simp [evalAt, ofScalar]
lemma evalAt_add (w : R) (x y : PairAlg R) : evalAt w (add x y) = evalAt w x + evalAt w y := by
  simp only [evalAt, add]; ring
lemma evalAt_sub (w : R) (x y : PairAlg R) : evalAt w (sub x y) = evalAt w x - evalAt w y := by
  simp only [evalAt, sub]; ring
lemma evalAt_neg (w : R) (x : PairAlg R) : evalAt w (neg x) = -evalAt w x := by
  simp only [evalAt, neg]; ring
lemma evalAt_smul (w s : R) (x : PairAlg R) : evalAt w (smul s x) = s * evalAt w x := by
  simp only [evalAt, smul]; ring

lemma evalAt_mul (bW cW w : R) (hw : w ^ 2 + bW * w + cW = 0) (x y : PairAlg R) :
    evalAt w (mul bW cW x y) = evalAt w x * evalAt w y := by
  simp only [evalAt, mul]
  linear_combination -x.c1 * y.c1 * hw

lemma evalAt_nm (bW cW w1 w2 : R) (hsum : w1 + w2 = -bW) (hprod : w1 * w2 = cW) (x : PairAlg R) :
    nm bW cW x = evalAt w1 x * evalAt w2 x := by
  simp only [nm, evalAt]
  linear_combination -x.c0 * x.c1 * hsum - x.c1 ^ 2 * hprod

lemma nm_mul (bW cW : R) (x y : PairAlg R) :
    nm bW cW (mul bW cW x y) = nm bW cW x * nm bW cW y := by
  simp only [nm, mul]; ring

lemma nm_smul (bW cW s : R) (x : PairAlg R) :
    nm bW cW (smul s x) = s ^ 2 * nm bW cW x := by
  simp only [nm, smul]; ring

lemma nm_ofScalar (bW cW s : R) : nm bW cW (ofScalar s) = s ^ 2 := by
  simp only [nm, ofScalar]; ring

lemma nm_W (bW cW : R) : nm bW cW (W : PairAlg R) = cW := by
  simp only [nm, W]; ring

lemma map_zero {S : Type*} [CommRing S] (f : R →+* S) : map f (zero : PairAlg R) = zero := by
  ext <;> simp [map, zero]
lemma map_one {S : Type*} [CommRing S] (f : R →+* S) : map f (one : PairAlg R) = one := by
  ext <;> simp [map, one]
lemma map_W {S : Type*} [CommRing S] (f : R →+* S) : map f (W : PairAlg R) = W := by
  ext <;> simp [map, W]
lemma map_ofScalar {S : Type*} [CommRing S] (f : R →+* S) (s : R) :
    map f (ofScalar s) = ofScalar (f s) := by ext <;> simp [map, ofScalar]
lemma map_add {S : Type*} [CommRing S] (f : R →+* S) (x y : PairAlg R) :
    map f (add x y) = add (map f x) (map f y) := by ext <;> simp [map, add]
lemma map_sub {S : Type*} [CommRing S] (f : R →+* S) (x y : PairAlg R) :
    map f (sub x y) = sub (map f x) (map f y) := by ext <;> simp [map, sub]
lemma map_neg {S : Type*} [CommRing S] (f : R →+* S) (x : PairAlg R) :
    map f (neg x) = neg (map f x) := by ext <;> simp [map, neg]
lemma map_smul {S : Type*} [CommRing S] (f : R →+* S) (s : R) (x : PairAlg R) :
    map f (smul s x) = smul (f s) (map f x) := by ext <;> simp [map, smul]
lemma map_mul {S : Type*} [CommRing S] (f : R →+* S) (bW cW : R) (x y : PairAlg R) :
    map f (mul bW cW x y) = mul (f bW) (f cW) (map f x) (map f y) := by
  ext <;> simp [map, mul]
lemma map_nm {S : Type*} [CommRing S] (f : R →+* S) (bW cW : R) (x : PairAlg R) :
    f (nm bW cW x) = nm (f bW) (f cW) (map f x) := by
  simp [map, nm]

lemma evalAt_map {S : Type*} [CommRing S] (f : R →+* S) (w : R) (x : PairAlg R) :
    evalAt (f w) (map f x) = f (evalAt w x) := by
  simp [evalAt, map]

end RingOps

/-- The quadratic Euler trace identity: cancels the discriminant `bW^2 - 4 * cW` identically. -/
theorem eulerTr_div {F : Type*} [Field F] (bW cW w1 w2 : F) (x y : PairAlg F)
    (hsum : w1 + w2 = -bW) (hprod : w1 * w2 = cW) (hsep : w1 ≠ w2)
    (hy1 : evalAt w1 y ≠ 0) (hy2 : evalAt w2 y ≠ 0) :
    evalAt w1 x / (evalAt w1 y * (2 * w1 + bW)) +
      evalAt w2 x / (evalAt w2 y * (2 * w2 + bW)) =
    (x.c1 * y.c0 - x.c0 * y.c1) / nm bW cW y := by
  have hd1 : 2 * w1 + bW = w1 - w2 := by linear_combination hsum
  have hd2 : 2 * w2 + bW = -(w1 - w2) := by linear_combination hsum
  have hne : w1 - w2 ≠ 0 := sub_ne_zero.mpr hsep
  have hnm : nm bW cW y = evalAt w1 y * evalAt w2 y := evalAt_nm bW cW w1 w2 hsum hprod y
  rw [hd1, hd2, hnm]
  field_simp [hy1, hy2, hne]
  simp only [evalAt]
  ring

end PairAlg

/-- Explicit 13-term 5×5 Sylvester resultant of a quadratic `q2 z^2 + q1 z + q0` and
cubic `e3 z^3 + e2 z^2 + e1 z + e0` over any commutative ring. -/
def syl5 {R : Type*} [CommRing R] (q2 q1 q0 e3 e2 e1 e0 : R) : R :=
  q0 ^ 3 * e3 ^ 2
  - q1 * q0 ^ 2 * e3 * e2
  + q2 * q0 ^ 2 * e2 ^ 2
  + q1 ^ 2 * q0 * e3 * e1
  - 2 * q2 * q0 ^ 2 * e3 * e1
  - q2 * q1 * q0 * e2 * e1
  + q2 ^ 2 * q0 * e1 ^ 2
  - q1 ^ 3 * e3 * e0
  + 3 * q2 * q1 * q0 * e3 * e0
  + q2 * q1 ^ 2 * e2 * e0
  - 2 * q2 ^ 2 * q0 * e2 * e0
  - q2 ^ 2 * q1 * e1 * e0
  + q2 ^ 3 * e0 ^ 2

lemma map_syl5 {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (q2 q1 q0 e3 e2 e1 e0 : R) :
    f (syl5 q2 q1 q0 e3 e2 e1 e0) = syl5 (f q2) (f q1) (f q0) (f e3) (f e2) (f e1) (f e0) := by
  simp only [syl5, map_add, map_sub, map_mul, map_pow, map_ofNat]

lemma syl5_affine {R : Type*} [CommRing R] (q2 q1 q0 e3 e2 e1 e0 α β : R) :
    syl5 (q2 * α ^ 2) (2 * q2 * α * β + q1 * α) (q2 * β ^ 2 + q1 * β + q0)
      (e3 * α ^ 3) (3 * e3 * α ^ 2 * β + e2 * α ^ 2)
      (3 * e3 * α * β ^ 2 + 2 * e2 * α * β + e1 * α)
      (e3 * β ^ 3 + e2 * β ^ 2 + e1 * β + e0) =
    α ^ 6 * syl5 q2 q1 q0 e3 e2 e1 e0 := by
  simp only [syl5]; ring

lemma syl5_scale {R : Type*} [CommRing R] (q2 q1 q0 e3 e2 e1 e0 s t : R) :
    syl5 (s * q2) (s * q1) (s * q0) (t * e3) (t * e2) (t * e1) (t * e0) =
      s ^ 3 * t ^ 2 * syl5 q2 q1 q0 e3 e2 e1 e0 := by
  simp only [syl5]; ring

/-- Lifted 5×5 Sylvester resultant in the quadratic quotient `PairAlg R`. -/
def syl5Pair {R : Type*} [CommRing R] (bW cW : R)
    (q2 q1 q0 e3 e2 e1 e0 : PairAlg R) : PairAlg R :=
  let m := PairAlg.mul bW cW
  let a := PairAlg.add; let s := PairAlg.sub; let sc := PairAlg.smul
  let q0_2 := m q0 q0; let q0_3 := m q0_2 q0
  let q1_2 := m q1 q1; let q1_3 := m q1_2 q1
  let q2_2 := m q2 q2; let q2_3 := m q2_2 q2
  let e3_2 := m e3 e3; let e2_2 := m e2 e2; let e1_2 := m e1 e1; let e0_2 := m e0 e0
  a (s (s (a (a (s (a (s (s (a (a (s (m q0_3 e3_2)
    (m (m q1 q0_2) (m e3 e2)))
    (m (m q2 q0_2) e2_2))
    (m (m q1_2 q0) (m e3 e1)))
    (sc 2 (m (m q2 q0_2) (m e3 e1))))
    (m (m q2 (m q1 q0)) (m e2 e1)))
    (m (m q2_2 q0) e1_2))
    (m q1_3 (m e3 e0)))
    (sc 3 (m (m q2 (m q1 q0)) (m e3 e0))))
    (m (m q2 q1_2) (m e2 e0)))
    (sc 2 (m (m q2_2 q0) (m e2 e0))))
    (m (m q2_2 q1) (m e1 e0)))
    (m q2_3 e0_2)

lemma evalAt_syl5Pair {R : Type*} [CommRing R] (bW cW : R)
    (q2 q1 q0 e3 e2 e1 e0 : PairAlg R) (w : R) (hw : w ^ 2 + bW * w + cW = 0) :
    PairAlg.evalAt w (syl5Pair bW cW q2 q1 q0 e3 e2 e1 e0) =
      syl5 (PairAlg.evalAt w q2) (PairAlg.evalAt w q1) (PairAlg.evalAt w q0)
        (PairAlg.evalAt w e3) (PairAlg.evalAt w e2) (PairAlg.evalAt w e1) (PairAlg.evalAt w e0) := by
  simp only [syl5Pair, PairAlg.evalAt_add, PairAlg.evalAt_sub, PairAlg.evalAt_smul,
    PairAlg.evalAt_mul bW cW w hw, syl5]
  ring

lemma map_syl5Pair {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (bW cW : R)
    (q2 q1 q0 e3 e2 e1 e0 : PairAlg R) :
    PairAlg.map f (syl5Pair bW cW q2 q1 q0 e3 e2 e1 e0) =
      syl5Pair (f bW) (f cW) (PairAlg.map f q2) (PairAlg.map f q1) (PairAlg.map f q0)
        (PairAlg.map f e3) (PairAlg.map f e2) (PairAlg.map f e1) (PairAlg.map f e0) := by
  simp only [syl5Pair, PairAlg.map_add, PairAlg.map_sub, PairAlg.map_smul, PairAlg.map_mul, map_ofNat]

lemma syl5_eq_prod_roots {R : Type*} [CommRing R] (q2 e3 e2 e1 e0 z1 z2 : R) :
    syl5 q2 (-q2 * (z1 + z2)) (q2 * z1 * z2) e3 e2 e1 e0 =
      q2 ^ 3 * (e3 * z1 ^ 3 + e2 * z1 ^ 2 + e1 * z1 + e0) *
               (e3 * z2 ^ 3 + e2 * z2 ^ 2 + e1 * z2 + e0) := by
  simp only [syl5]; ring

lemma q2_sq_mul_syl5 {R : Type*} [CommRing R] (q2 q1 q0 e3 e2 e1 e0 : R) :
    let t2 := q2 * e2 - q1 * e3
    let t1 := q2 * e1 - q0 * e3
    let t0 := q2 * e0
    let d1 := q2 * t1 - q1 * t2
    let d0 := q2 * t0 - q0 * t2
    q2 ^ 2 * syl5 q2 q1 q0 e3 e2 e1 e0 = q2 * d0 ^ 2 - d0 * d1 * q1 + d1 ^ 2 * q0 := by
  simp only [syl5]; ring

end QuadraticCovers


