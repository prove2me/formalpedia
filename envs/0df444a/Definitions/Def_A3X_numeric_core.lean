-- Prove2me | Definitions.Def_A3X_numeric_core
-- name    : A3X_numeric_core
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-24T23:53:14.634678+00:00
-- url     : https://prove2.me/theorems/ce26ee10-2e84-4636-bb09-b5c8db39b099
-- title:
--   Exact rational polynomial operations for the A3X certificate
-- statement:
--   The source uses finite lists of exact rational coefficients to represent Laurent polynomials in $L$, sparse polynomials in $\sigma$, and coefficient lists in $t$. This bundle preserves the original addition, multiplication, truncation, rational interval bounds, and Taylor-model record and remainder operations. It asserts no numerical certificate or analytic inequality.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA3X/Poly.lean#L17-L248

import Mathlib.Data.Rat.Floor

set_option maxRecDepth 100000

namespace CKLaneA3X
abbrev LPoly := List (ℤ × ℚ)

abbrev SPoly := List (ℕ × LPoly)

abbrev TPoly := List SPoly

/-- merge-add (sorted by exponent). Soundness does not depend on sortedness. -/
noncomputable def LPoly.add (l1 : LPoly) : LPoly → LPoly :=
  @List.rec (ℤ × ℚ) (fun _ => LPoly → LPoly) (fun l2 => l2)
    (fun m1 t1 rec => fun l2 =>
      @List.rec (ℤ × ℚ) (fun _ => LPoly) (m1 :: t1)
        (fun m2 t2 ih =>
          if m1.1 < m2.1 then m1 :: rec (m2 :: t2)
          else if m2.1 < m1.1 then m2 :: ih
          else if m1.2 + m2.2 = 0 then rec t2 else (m1.1, m1.2 + m2.2) :: rec t2) l2) l1

/-- multiply every term by `q * L^c` -/
noncomputable def LPoly.mulMono (c : ℤ) (q : ℚ) (l : LPoly) : LPoly :=
  @List.rec (ℤ × ℚ) (fun _ => LPoly) [] (fun m _ ih => (c + m.1, q * m.2) :: ih) l

noncomputable def LPoly.mul (l1 l2 : LPoly) : LPoly :=
  @List.rec (ℤ × ℚ) (fun _ => LPoly) [] (fun m _ ih => LPoly.add (LPoly.mulMono m.1 m.2 l2) ih) l1

noncomputable def SPoly.add (s1 : SPoly) : SPoly → SPoly :=
  @List.rec (ℕ × LPoly) (fun _ => SPoly → SPoly) (fun s2 => s2)
    (fun m1 t1 rec => fun s2 =>
      @List.rec (ℕ × LPoly) (fun _ => SPoly) (m1 :: t1)
        (fun m2 t2 ih =>
          if m1.1 < m2.1 then m1 :: rec (m2 :: t2)
          else if m2.1 < m1.1 then m2 :: ih
          else if LPoly.add m1.2 m2.2 = [] then rec t2
          else (m1.1, LPoly.add m1.2 m2.2) :: rec t2) s2) s1

/-- multiply every entry by `σ^b * l` (entries whose product is `[]` are dropped). -/
noncomputable def SPoly.mulMono (b : ℕ) (l : LPoly) (s : SPoly) : SPoly :=
  @List.rec (ℕ × LPoly) (fun _ => SPoly) []
    (fun m _ ih => if LPoly.mul l m.2 = [] then ih else (b + m.1, LPoly.mul l m.2) :: ih) s

noncomputable def SPoly.mul (s1 s2 : SPoly) : SPoly :=
  @List.rec (ℕ × LPoly) (fun _ => SPoly) [] (fun m _ ih => SPoly.add (SPoly.mulMono m.1 m.2 s2) ih) s1

noncomputable def TPoly.add (P1 : TPoly) : TPoly → TPoly :=
  @List.rec SPoly (fun _ => TPoly → TPoly) (fun P2 => P2)
    (fun s1 t1 rec => fun P2 =>
      @List.rec SPoly (fun _ => TPoly) (s1 :: t1)
        (fun s2 t2 _ => SPoly.add s1 s2 :: rec t2) P2) P1

/-- `s * P`, keeping only the first `k` t-coefficients. -/
noncomputable def TPoly.scaleSTake (s : SPoly) (P : TPoly) : ℕ → TPoly :=
  @List.rec SPoly (fun _ => ℕ → TPoly) (fun _ => [])
    (fun p _ ih => fun k => Nat.rec (motive := fun _ => TPoly) []
      (fun k' _ => SPoly.mul s p :: ih k') k) P

/-- truncated product: t-coefficients of index `< n` of `P * Q`. -/
noncomputable def TPoly.mulT (P Q : TPoly) : ℕ → TPoly :=
  @List.rec SPoly (fun _ => ℕ → TPoly) (fun _ => [])
    (fun s _ ih => fun n => Nat.rec (motive := fun _ => TPoly) []
      (fun n' _ => TPoly.add (TPoly.scaleSTake s Q (n' + 1)) ([] :: ih n')) n) P

def Llo : ℚ := 6931471803 / 10000000000

def Lhi : ℚ := 6931471808 / 10000000000

def Tq : ℚ := 3 / 10

noncomputable def qpow (x : ℚ) (k : ℕ) : ℚ := Nat.rec (motive := fun _ => ℚ) 1 (fun _ ih => ih * x) k

/-- lower/upper bounds for `L^c`, `L ∈ [Llo, Lhi]`. -/
noncomputable def Lpow : ℤ → ℚ × ℚ
  | Int.ofNat k => (qpow Llo k, qpow Lhi k)
  | Int.negSucc k => (qpow (1 / Lhi) (k + 1), qpow (1 / Llo) (k + 1))

/-- interval `[lo, hi]` for `q * L^c`. -/
noncomputable def termIntv (c : ℤ) (q : ℚ) : ℚ × ℚ :=
  if 0 ≤ q then (q * (Lpow c).1, q * (Lpow c).2) else (q * (Lpow c).2, q * (Lpow c).1)

/-- interval enclosure of an `LPoly` over `L ∈ [Llo, Lhi]`. -/
noncomputable def LPoly.intv (l : LPoly) : ℚ × ℚ :=
  @List.rec (ℤ × ℚ) (fun _ => ℚ × ℚ) (0, 0)
    (fun m _ ih => ((termIntv m.1 m.2).1 + ih.1, (termIntv m.1 m.2).2 + ih.2)) l

noncomputable def LPoly.absB (l : LPoly) : ℚ := max (|(LPoly.intv l).1|) (|(LPoly.intv l).2|)

/-- `|σ| ≤ 1/2` bound for an `SPoly`. -/
noncomputable def SPoly.absB (s : SPoly) : ℚ :=
  @List.rec (ℕ × LPoly) (fun _ => ℚ) 0 (fun m _ ih => qpow (1 / 2) m.1 * LPoly.absB m.2 + ih) s

/-- `Σ β_i T^i` (Horner). -/
noncomputable def bsum (β : List ℚ) : ℚ := @List.rec ℚ (fun _ => ℚ) 0 (fun b _ ih => b + Tq * ih) β

noncomputable def ldrop (β : List ℚ) : ℕ → List ℚ :=
  @List.rec ℚ (fun _ => ℕ → List ℚ) (fun _ => [])
    (fun b β' ih => fun k => Nat.rec (motive := fun _ => List ℚ) (b :: β') (fun k' _ => ih k') k) β

noncomputable def zeroPrefix (P : TPoly) : ℕ → Bool :=
  @List.rec SPoly (fun _ => ℕ → Bool) (fun _ => true)
    (fun s _ ih => fun k => Nat.rec (motive := fun _ => Bool) true
      (fun k' _ => s.isEmpty && ih k') k) P

noncomputable def HB (β γ : List ℚ) : ℕ → ℚ :=
  @List.rec ℚ (fun _ => ℕ → ℚ) (fun _ => 0)
    (fun b β' ih => fun n => Nat.rec (motive := fun _ => ℚ) (bsum (b :: β') * bsum γ)
      (fun n' _ => b * bsum (ldrop γ (n' + 1)) + ih n') n) β

structure TMd where
  P : TPoly
  r : ℚ
  n : ℕ

noncomputable def rup (x : ℚ) : ℚ := ((⌈x * 1099511627776⌉ : ℤ) : ℚ) / 1099511627776

noncomputable def entryBounds (P : TPoly) : List ℚ :=
  @List.rec SPoly (fun _ => List ℚ) [] (fun s _ ih => rup (SPoly.absB s) :: ih) P

noncomputable def mulRem (β γ : List ℚ) (r1 r2 : ℚ) (n1 n2 v1 v2 n : ℕ) : ℚ :=
  HB β γ n + (bsum (ldrop β v1) + r1 * Tq ^ (n1 - v1)) * r2 * Tq ^ (v1 + n2 - n)
    + bsum (ldrop γ v2) * r1 * Tq ^ (v2 + n1 - n)

noncomputable def TMd.mul (a b : TMd) (va vb n : ℕ) : TMd :=
  ⟨TPoly.mulT a.P b.P n, rup (mulRem (entryBounds a.P) (entryBounds b.P) a.r b.r a.n b.n va vb n), n⟩

end CKLaneA3X


