-- Prove2me | Definitions.Def_EuclideanCRHardness_Covering_Quadratic
-- name    : EuclideanCRHardness_Covering_Quadratic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:51:29.809387+00:00
-- url     : https://prove2.me/theorems/75af99eb-98ca-46ef-822d-50b5c1287c03
-- title:
--   Quadratic lattice distances and localization quantities
-- statement:
--   For a symmetric positive-definite real matrix $Q$, define
--   $$d_Q(x)=\inf_{z\in\mathbb Z^n}(x-z)^TQ(x-z),\quad \mu_Q^2=\sup_x d_Q(x),\quad h=\tfrac12\mathbf1,\quad a_Q=\tfrac14\min_{s\in\{-1,1\}^n}s^TQs.$$
--   Closest points minimize over all integer vectors. A maximizer dominates every real target. The induced row norm is $\max_i\sum_j|M_{ij}|$, and $\kappa=\|D^{-1}Q-I\|_\infty$. Fractional coordinates subtract coordinatewise integer floors.
--
--   The separate semantic target asserts attainment, continuity, periodicity, and boundedness under positive definiteness. Empty coordinate maxima have value zero. Signs are represented by booleans, with true meaning $+1$.
-- source:
--   Zhijie Zheng, Yucong He, Chengzhi Xie, STOC 2027 submission #38 (October 2026), equations (2.1)–(2.3) and Theorem 2.1, printed p. 3 / PDF p. 4; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/38.pdf

import Mathlib

namespace EuclideanCRHardness.Covering

open scoped BigOperators
abbrev Vec (n : ℕ) := Fin n → ℝ
abbrev RMat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

def bilinear {n : ℕ} (Q : RMat n) (v w : Vec n) : ℝ :=
  ∑ i, ∑ j, v i * Q i j * w j

def quad {n : ℕ} (Q : RMat n) (x : Vec n) : ℝ := bilinear Q x x

def SPD {n : ℕ} (Q : RMat n) : Prop :=
  Q.transpose = Q ∧ ∀ v : Vec n, v ≠ 0 → 0 < quad Q v

def residual {n : ℕ} (x : Vec n) (z : Fin n → ℤ) : Vec n := fun i => x i - z i
noncomputable def dQ {n : ℕ} (Q : RMat n) (x : Vec n) : ℝ :=
  sInf (Set.range (fun z : Fin n → ℤ => quad Q (residual x z)))

def Closest {n : ℕ} (Q : RMat n) (x : Vec n) (z : Fin n → ℤ) : Prop :=
  ∀ w : Fin n → ℤ, quad Q (residual x z) ≤ quad Q (residual x w)
noncomputable def muQ2 {n : ℕ} (Q : RMat n) : ℝ := sSup (Set.range (dQ Q))

def Maximizer {n : ℕ} (Q : RMat n) (x : Vec n) : Prop := ∀ y, dQ Q y ≤ dQ Q x

def signVal (b : Bool) : ℝ := if b then 1 else -1

noncomputable def center (n : ℕ) : Vec n := fun _ => 1/2
noncomputable def aQ {n : ℕ} (Q : RMat n) : ℝ :=
  (1/4 : ℝ) * sInf (Set.range (fun s : Fin n → Bool => quad Q (fun i => signVal (s i))))
noncomputable def rowNorm {n : ℕ} (M : RMat n) : ℝ :=
  sSup (insert 0 (Set.range (fun i => ∑ j, |M i j|)))
noncomputable def vecMax {n : ℕ} (x : Vec n) : ℝ :=
  sSup (insert 0 (Set.range (fun i => |x i|)))
noncomputable def kappa {n : ℕ} (D : Vec n) (Q : RMat n) : ℝ :=
  rowNorm (fun i j => Q i j / D i - if i = j then 1 else 0)

noncomputable def fracVector {n : ℕ} (x : Vec n) : Vec n := fun i => x i - (⌊x i⌋ : ℤ)

end EuclideanCRHardness.Covering


