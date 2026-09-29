-- Prove2me | Definitions.Def_Freiman_lowerInitialAlgebra
-- name    : Freiman_lowerInitialAlgebra
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T11:50:27.73895+00:00
-- url     : https://prove2.me/theorems/7a64721a-819c-4eab-8c37-bcfaa083a4d2
-- title:
--   Freiman initial contacts: lowerInitialAlgebra
-- statement:
--   Actual source matrix products, recurrence ratios and exact finite Q(sqrt3) polynomial coefficient data for the eight H seam parameter boxes and three period contacts.
-- source:
--   Freiman report, prop:lc-H-contacts; certificates/initial_covers/parametric_h_seams.json and parametric_h_nseams.json; independent validator validate_h_seams_independent.py. Exact source hashes in INITIAL_CERTIFICATE_BINDING.json.

import Definitions.Def_Freiman_lowerCertificates
import Definitions.Def_Freiman_certificates
import Mathlib.Data.Fin.VecNotation

open scoped BigOperators
namespace Freiman

abbrev LowerInitialPoly := Fin 3 → Fin 3 → Fin 3 → CertField
noncomputable def lowerInitialPolyEval (P : LowerInitialPoly) (x y z : ℝ) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, certFieldVal (P i j k) * x^i.val * y^j.val * z^k.val

def lowerInitialBernstein (P : LowerInitialPoly) : LowerInitialPoly := fun i j k =>
  certQuadBlend 0 (1/85) (fun a =>
    certQuadBlend 0 (1/3) (fun b => certQuadBlend 0 (1/3) (P a b) k) j) i
noncomputable def lowerInitialWeight (x y z : ℝ) (i j k : Fin 3) : ℝ :=
  certBernsteinBasis i (85*x) * certBernsteinBasis j (3*y) * certBernsteinBasis k (3*z)
noncomputable def lowerInitialBernsteinEval (C : LowerInitialPoly) (x y z : ℝ) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
    certFieldVal (C i j k) * lowerInitialWeight x y z i j k

def lowerInitialBox (x y z : ℝ) : Prop :=
  x ∈ Set.Icc (0:ℝ) (1/85) ∧ y ∈ Set.Icc (0:ℝ) (1/3) ∧ z ∈ Set.Icc (0:ℝ) (1/3)

structure LowerInitialMatrix where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
noncomputable def lowerInitialMatMul (u v : LowerInitialMatrix) : LowerInitialMatrix :=
  ⟨u.a*v.a+u.b*v.c,u.a*v.b+u.b*v.d,u.c*v.a+u.d*v.c,u.c*v.b+u.d*v.d⟩
noncomputable def lowerInitialMatScale (r : ℝ) (u : LowerInitialMatrix) : LowerInitialMatrix :=
  ⟨r*u.a,r*u.b,r*u.c,r*u.d⟩
noncomputable def lowerInitialWordMatrix (w : List ℕ+) : LowerInitialMatrix :=
  w.foldl (fun m d => lowerInitialMatMul m ⟨0,1,1,(d:ℕ)⟩) ⟨1,0,0,1⟩
noncomputable def lowerInitialMatDen (m : LowerInitialMatrix) (t : ℝ) : ℝ := m.c*t+m.d
noncomputable def lowerInitialMatEval (m : LowerInitialMatrix) (t : ℝ) : ℝ := (m.a*t+m.b)/(m.c*t+m.d)
def lowerInitialU : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n+2 => 86*lowerInitialU (n+1)-lowerInitialU n
def lowerInitialV : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n+2 => 3*lowerInitialV (n+1)+lowerInitialV n
noncomputable def lowerInitialX (n : ℕ) : ℝ := (lowerInitialU (n-1):ℝ)/(lowerInitialU n:ℝ)
noncomputable def lowerInitialY (k : ℕ) : ℝ := (lowerInitialV k:ℝ)/(lowerInitialV (k+1):ℝ)
noncomputable def lowerInitialP (zero : Bool) (x : ℝ) : LowerInitialMatrix :=
  if zero then ⟨1,0,0,1⟩ else ⟨14-x,19,53,72-x⟩
noncomputable def lowerInitialK (y : ℝ) : LowerInitialMatrix := ⟨y,1,1,3+y⟩
noncomputable def lowerInitialKPrev (y : ℝ) : LowerInitialMatrix := ⟨1-3*y,y,y,1⟩

inductive LowerInitialSeamCase where
  | aZero | aPos | cZero | cPos | b18Zero | b18Pos | b19Zero | b19Pos
  deriving DecidableEq

def lowerInitialSeamFamily : LowerInitialSeamCase → LowerInitialFamily
  | .aZero | .aPos => .A
  | .cZero | .cPos => .C
  | _ => .B
def lowerInitialSeamZero : LowerInitialSeamCase → Bool
  | .aZero | .cZero | .b18Zero | .b19Zero => true
  | _ => false
def lowerInitialSeamWords : LowerInitialSeamCase → (List ℕ+ × List ℕ+) × (List ℕ+ × List ℕ+)
  | .aZero | .aPos | .cZero | .cPos =>
    (([3,3,1,2,1,3],[3,1,2,1,3]),([3,3,1,2,1,3],[2,1,3]))
  | .b18Zero | .b18Pos =>
    (([3,1,3,3,1,2,1,3],[3,1,2,1,3]),([2,1,3,3,1,2,1,3],[2,1,3]))
  | .b19Zero | .b19Pos =>
    (([3,3,1,2,1,3],[3,1,3,1,2,1,3]),([3,3,1,2,1,3],[2,1,3,1,2,1,3]))
noncomputable def lowerInitialSeamMatrices (c : LowerInitialSeamCase) (x y z : ℝ) :
    LowerInitialMatrix × LowerInitialMatrix :=
  let mul := lowerInitialMatMul
  let M := lowerInitialWordMatrix
  let P := lowerInitialP (lowerInitialSeamZero c) x
  let K := lowerInitialK y
  let J := lowerInitialK z
  match lowerInitialSeamFamily c with
  | .A => (mul (mul (M [4,3,2,2]) P) K,
           mul (mul (mul (M [3,2,1,1]) P) (M [3,1])) K)
  | .B => (mul (mul (mul (M [3,2,1,1]) P) (M [3,1,3,1,2])) (lowerInitialKPrev y),
           mul (mul (mul (M [4,3,2,2]) P) (M [3,1])) K)
  | .C => (mul (mul (mul (mul (mul (M [4,3,2,2]) P) (M [3,1])) K) (M [2,1])) J,
           mul (mul (mul (mul (mul (M [3,2,1,1]) P) (M [3,1,3,1,2])) K) (M [1])) J)
  | .auxB => (⟨1,0,0,1⟩,⟨1,0,0,1⟩)
noncomputable def lowerInitialSeamNumerator (c : LowerInitialSeamCase) (x y z : ℝ) : ℝ :=
  let m := lowerInitialSeamMatrices c x y z
  let w := lowerInitialSeamWords c
  let u := prefixEval w.1.1 lowerTau
  let v := prefixEval w.1.2 lowerTau
  let a := prefixEval w.2.1 lowerTau
  let b := prefixEval w.2.2 lowerTau
  (u-v) * lowerInitialMatDen m.2 a * lowerInitialMatDen m.2 b +
  (a-b) * lowerInitialMatDen m.1 u * lowerInitialMatDen m.1 v
noncomputable def lowerInitialSeamDenPositive (c : LowerInitialSeamCase) (x y z : ℝ) : Prop :=
  let m := lowerInitialSeamMatrices c x y z
  let w := lowerInitialSeamWords c
  0 < lowerInitialMatDen m.1 (prefixEval w.1.1 lowerTau) ∧
  0 < lowerInitialMatDen m.1 (prefixEval w.1.2 lowerTau) ∧
  0 < lowerInitialMatDen m.2 (prefixEval w.2.1 lowerTau) ∧
  0 < lowerInitialMatDen m.2 (prefixEval w.2.2 lowerTau)
noncomputable def lowerInitialSeamLink (c : LowerInitialSeamCase) (n k p : ℕ) : Prop :=
  let q := lowerNormalize (lowerFamilyPair (lowerInitialSeamFamily c) n k p)
  let m := lowerInitialSeamMatrices c (lowerInitialX n) (lowerInitialY k) (lowerInitialY p)
  q.1.length % 2 = q.2.length % 2 ∧ ∃ s : ℝ, 0 < s ∧
    lowerInitialWordMatrix q.1 = lowerInitialMatScale s m.1 ∧
    lowerInitialWordMatrix q.2 = lowerInitialMatScale s m.2
noncomputable def lowerInitialSeamHolds (c : LowerInitialSeamCase) (n k p : ℕ) : Prop :=
  let w := lowerInitialSeamWords c
  lowerContact (lowerNormalize (lowerFamilyPair (lowerInitialSeamFamily c) n k p))
    w.1.1 w.1.2 w.2.1 w.2.2

end Freiman


