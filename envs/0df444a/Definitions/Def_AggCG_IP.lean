-- Prove2me | Definitions.Def_AggCG_IP
-- name    : AggCG_IP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:06:19.415375+00:00
-- url     : https://prove2.me/theorems/51767f6d-871f-4c00-9742-ab059e972ba2
-- title:
--   A rational integer program with a structural box; the cut (19) and the node LPs
-- statement:
--   A **program** of the model has $m$ rows and $n$ variables: a matrix $A\in\mathbb Q^{m\times n}$, a right-hand side $b\in\mathbb Q^m$, an objective $c\in\mathbb Q^n$, and for each variable an optional structural upper bound. It stands for
--   $$\max\{c^\top z : Az\le b,\ z\in\mathbb Z^n_{\ge 0}\}.$$
--   For a multiplier vector $u\in[0,1]^m$ (real), the **rank-one Chvátal–Gomory cut** is
--   $$\lfloor u^\top A\rfloor z\le\lfloor u^\top b\rfloor,\tag{19}$$
--   with floors of the signed combinations taken over all $m$ rows. A **node LP** has as feasible region the points $z\in\mathbb R^n$ with $z\ge 0$, the structural bounds, $Az\le b$, an optional appended cut with integer data, and a list of branching bounds $z_j\le k$ or $z_j\ge k$ with $k\in\mathbb Z$.
--
--   These are the objects on which branch and bound, the gap and the gadgets are defined.
--
--   **Formalization Note** The structural box is outside the rows, "enforced in each LP relaxation but … not among the m rows being aggregated" (p.49); this settles Remark D.10, p.26. Data are rational, which holds both the integral data of §I.1 and the arbitrary rational programs of p.51.
-- source:
--   Sharma, Computational Complexity of Data-Driven Configuration for Integer Programming, Clustering, and Learning Algorithms, STOC 2027 submission (manuscript sha256 f7ea0248…), §I.1, p.49 (PDF p.50), eq. (19); Remark D.10, p.26 (PDF p.27)

import Mathlib

namespace AggCG

/-- A program of the model, with `m` rows and `n` variables (Sharma, *Computational Complexity of Data-Driven Configuration for Integer Programming, Clustering, and Learning Algorithms*, STOC 2027 submission (manuscript sha256 f7ea0248…), §I.1, p.49, PDF p.50):
`max {c⊤z : Az ≤ b, z ∈ ℤⁿ_{≥0}}`, with a structural upper bound `ub j` on a variable where one is given.

**Formalization Note** The structural box (`x, y ∈ {0, 1}` on the gadgets) is a field of its own, "enforced in
each LP relaxation but … not among the m rows being aggregated" (p.49; this settles Remark D.10, p.26, PDF p.27).
Data are rational, which holds the integral data of §I.1 and the "arbitrary rational input IPs" of p.51. -/
structure IP (m n : ℕ) where
  /-- The row matrix `A`. -/
  A : Matrix (Fin m) (Fin n) ℚ
  /-- The right-hand side `b`. -/
  b : Fin m → ℚ
  /-- The objective `c`, to be maximized. -/
  c : Fin n → ℚ
  /-- The structural upper bound of each variable, outside the rows. -/
  ub : Fin n → Option ℚ

/-- The parameter domain `u ∈ [0, 1]^m` of (19), p.49 (real multipliers). -/
def InUnitBox {m : ℕ} (u : Fin m → ℝ) : Prop := ∀ t, 0 ≤ u t ∧ u t ≤ 1

/-- An inequality `coeff⊤z ≤ rhs` with integer data, the shape of the cut (19). -/
@[ext] structure IntCut (n : ℕ) where
  /-- The integer coefficients. -/
  coeff : Fin n → ℤ
  /-- The integer right-hand side. -/
  rhs : ℤ

/-- A branching bound of a node: `z_j ≤ k` or `z_j ≥ k`. -/
inductive BranchCon (n : ℕ) where
  | le (j : Fin n) (k : ℤ)
  | ge (j : Fin n) (k : ℤ)

/-- The point `z` obeys the branching bound. -/
def BranchCon.Holds {n : ℕ} : BranchCon n → (Fin n → ℝ) → Prop
  | .le j k, z => z j ≤ k
  | .ge j k, z => (k : ℝ) ≤ z j

namespace IP

variable {m n : ℕ}

/-- The rank-one cut (19), p.49: `⌊u⊤A⌋z ≤ ⌊u⊤b⌋`, with floors of the signed combinations over all `m` rows. -/
noncomputable def cutOf (I : IP m n) (u : Fin m → ℝ) : IntCut n where
  coeff := fun j => ⌊∑ t, u t * (I.A t j : ℝ)⌋
  rhs := ⌊∑ t, u t * (I.b t : ℝ)⌋

/-- The feasible region of the LP at a B&B node: `z ≥ 0`, the structural bounds, `Az ≤ b`, the appended cut
if any, and the branching bounds `B`. -/
def nodeRegion (I : IP m n) (cut : Option (IntCut n)) (B : List (BranchCon n)) : Set (Fin n → ℝ) :=
  {z | (∀ j, 0 ≤ z j) ∧ (∀ j q, I.ub j = some q → z j ≤ (q : ℝ)) ∧
      (∀ t, ∑ j, (I.A t j : ℝ) * z j ≤ (I.b t : ℝ)) ∧
      (∀ C ∈ cut, ∑ j, (C.coeff j : ℝ) * z j ≤ (C.rhs : ℝ)) ∧
      ∀ r ∈ B, r.Holds z}

/-- The objective `c⊤z`. -/
def objective (I : IP m n) (z : Fin n → ℝ) : ℝ := ∑ j, (I.c j : ℝ) * z j

/-- `z` is an optimum of the node LP. -/
def IsLPOpt (I : IP m n) (cut : Option (IntCut n)) (B : List (BranchCon n)) (z : Fin n → ℝ) : Prop :=
  z ∈ I.nodeRegion cut B ∧ ∀ z' ∈ I.nodeRegion cut B, I.objective z' ≤ I.objective z

end IP

/-- All coordinates of `z` are integers. -/
def IsIntegralPt {n : ℕ} (z : Fin n → ℝ) : Prop := ∀ j, ∃ k : ℤ, z j = k

end AggCG


