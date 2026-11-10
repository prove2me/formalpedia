-- Prove2me | Definitions.Def_GEPPGrowth_Main_Covariance
-- name    : GEPPGrowth_Main_Covariance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T23:35:13.921782+00:00
-- url     : https://prove2.me/theorems/18a04054-7553-41f6-92a1-eee5ad593f45
-- title:
--   The residual covariance update and growth cone
-- statement:
--   Let $y\in\mathbb R^D$ with $D\ge1$. Select the smallest coordinate index $i$ maximizing $|y_i|$ and set $r=y/y_i$. Let $D_i=\Pi_1P_{1,i}$ first swap coordinate $i$ with the first coordinate and then delete that first coordinate. Define
--
--   $$F_y=I_D-re_i^\top,\quad B_y=D_iF_y,\quad \mathcal U(S,y)=B_ySB_y^\top.$$
--
--   The same operator maps a square residual matrix to its next residual matrix after deletion of its first column. Squared vector length is $\sum_jv_j^2$ and the deleted inner product is $\sum_{j\ne i}v_jr_j$, so no function sup norm is used. For a unit vector $v$, the growth cone is
--
--   $$E_v=\{y:v_i^2\ge1/D,\ \|r\|_2^2\ge D/2,\ v_i\langle v[-i],r[-i]\rangle\le0\}.$$
--
--   The fold explicitly selects the smallest maximizer. Division at $y=0$ returns zero; the nondegenerate source formulas exclude it or apply almost surely under a positive definite Gaussian law. No covariance tail or growth assertion is part of these definitions.
--
--   The ratio, elimination, compression, covariance update and growth event also have explicit selected-pivot versions. These take any valid maximizing coordinate, including every tie choice. The smallest-index versions remain the concrete process implementation.
-- source:
--   Daniel Spielman, Xifan Yu, STOC 2027 submission #1176 (October 2026), §3, printed pp.6–7, PDF pp.7–8; Proposition 5.1, printed p.16, PDF p.17

import Definitions.Def_GEPPGrowth_Main_Gaussian
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

noncomputable section

namespace GEPPGrowth.Main

/-- Smallest index among maximizers of |y|, implemented by a finite fold. -/
noncomputable def pivot {d : ℕ} (y : Vec (d+1)) : Fin (d+1) :=
  (List.finRange (d+1)).foldl (fun b j =>
    if |y b| < |y j| ∨ (|y b| = |y j| ∧ j < b) then j else b) 0

def IsMaxPivot {d : ℕ} (y : Vec (d+1)) (i : Fin (d+1)) : Prop :=
  ∀ j, |y j| ≤ |y i|

def ratiosAt {d : ℕ} (y : Vec (d+1)) (i : Fin (d+1)) : Vec (d+1) :=
  fun j => y j / y i

def ratios {d : ℕ} (y : Vec (d+1)) : Vec (d+1) := ratiosAt y (pivot y)

/-- Π₁P₁ᵢ: first swap the pivot with coordinate zero, then delete coordinate zero. -/
def deletion {d : ℕ} (i : Fin (d+1)) : Matrix (Fin d) (Fin (d+1)) ℝ :=
  fun a b => if Equiv.swap (0 : Fin (d+1)) i a.succ = b then 1 else 0

def basisVector {d : ℕ} (i : Fin d) : Vec d := fun j => if j = i then 1 else 0

/-- I - r eᵢᵀ for any selected pivot coordinate. -/
def eliminationAt {d : ℕ} (y : Vec (d+1)) (i : Fin (d+1)) : Mat (d+1) :=
  1 - Matrix.vecMulVec (ratiosAt y i) (basisVector i)

def elimination {d : ℕ} (y : Vec (d+1)) : Mat (d+1) := eliminationAt y (pivot y)

def compressionAt {d : ℕ} (y : Vec (d+1)) (i : Fin (d+1)) :
    Matrix (Fin d) (Fin (d+1)) ℝ := deletion i * eliminationAt y i

def compression {d : ℕ} (y : Vec (d+1)) : Matrix (Fin d) (Fin (d+1)) ℝ :=
  compressionAt y (pivot y)

/-- The source update for any maximizing choice, including tied columns. -/
def updateAt {d : ℕ} (S : Mat (d+1)) (y : Vec (d+1)) (i : Fin (d+1)) : Mat d :=
  compressionAt y i * S * (compressionAt y i).transpose

/-- Concrete smallest-index covariance transition used for the process. -/
def update {d : ℕ} (S : Mat (d+1)) (y : Vec (d+1)) : Mat d := updateAt S y (pivot y)

def residualStepWith {d : ℕ} (p : Vec (d+1) → Fin (d+1)) (M : Mat (d+1)) : Mat d :=
  (compressionAt (fun i => M i 0) (p (fun i => M i 0)) * M).submatrix id Fin.succ

def residualStep {d : ℕ} (M : Mat (d+1)) : Mat d := residualStepWith pivot M

/-- Squared Euclidean length; avoids the sup norm of the plain function type. -/
def sqLength {d : ℕ} (v : Vec d) : ℝ := ∑ i, v i ^ 2

/-- Inner product after deleting the pivot coordinate, without changing carriers. -/
def deletedInner {d : ℕ} (i : Fin d) (v r : Vec d) : ℝ :=
  ∑ j, if j = i then 0 else v j * r j

def growthConeWith {d : ℕ} (p : Vec (d+1) → Fin (d+1))
    (v : Vec (d+1)) : Set (Vec (d+1)) :=
  {y | (v (p y)) ^ 2 ≥ 1 / ((d+1 : ℕ) : ℝ) ∧
    sqLength (ratiosAt y (p y)) ≥ ((d+1 : ℕ) : ℝ) / 2 ∧
    v (p y) * deletedInner (p y) v (ratiosAt y (p y)) ≤ 0}

def growthCone {d : ℕ} (v : Vec (d+1)) : Set (Vec (d+1)) := growthConeWith pivot v

end GEPPGrowth.Main


