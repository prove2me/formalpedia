-- Prove2me | Definitions.Def_NuclearTensor_Membership_Geometry
-- name    : NuclearTensor_Membership_Geometry
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T22:13:47.04197+00:00
-- url     : https://prove2.me/theorems/d9a34195-e181-4064-9a92-e5151c03ec1d
-- title:
--   Real tensor coordinates, nuclear infimum, and Frobenius distance
-- statement:
--   A real tensor with local dimensions $d_1,\ldots,d_k$ is its complete row-major coefficient array. Local and tensor spaces carry the Euclidean inner product and norm; for local vectors $x_j$, the product array has entries $\prod_j x_j(i_j)$. Write $A$ for products of feasible local vectors and $C=\operatorname{conv}(A)$.
--
--   The nuclear norm is defined before any convex-hull identity:
--   $$\|M\|_*=\inf\left\{\sum_{i=1}^r|\lambda_i|:M=\sum_{i=1}^r\lambda_i\bigotimes_j x_{j,i},\ \|x_{j,i}\|_2=1\right\}.$$
--   The lengths are arbitrary finite natural numbers, and the coefficients are signed real numbers. Its unit ball is $K^*=\{M:\|M\|_*\le1\}$. Frobenius distance is $\inf_{Y\in C}\|M-Y\|_F$. Weak membership accepts inside points and rejects distance at least the positive requested gap, with no condition in between. These definitions separate the two norms throughout the development.
--
--   **Formalization Note** Infima use nonnegative extended reals; empty domains have value infinity. Local tuples at indices outside the dimension list are zero-dimensional vectors and are never tested. Source results use positive order; no zero-order nuclear claim is made.
-- source:
--   Martino Bernasconi, Giulio Malavolta, STOC 2027 submission #945 (October 2026), p.9, Section 2; pp.3 and 21, nuclear-norm definitions

import Mathlib

set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal

namespace NuclearTensor.Membership

/-- Explicit Euclidean coordinates; the norm is the sum-of-squares norm. -/
abbrev Vec (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- A rectangular array, with its Frobenius norm supplied separately below. -/
abbrev Mat (a b : ℕ) := Matrix (Fin a) (Fin b) ℝ

/-- Zero extension is used only for reshaping finite arrays. -/
def entry {n : ℕ} (x : Vec n) (i : ℕ) : ℝ := if h : i < n then x ⟨i, h⟩ else 0

def matEntry {a b : ℕ} (U : Mat a b) (i j : ℕ) : ℝ :=
  if h : i < a ∧ j < b then U ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

def outer {a b : ℕ} (x : Vec a) (y : Vec b) : Vec (a * b) :=
  WithLp.toLp 2 (fun i => entry x (i.val / b) * entry y (i.val % b))

def mv {a b : ℕ} (U : Mat a b) (x : Vec b) : Vec a :=
  WithLp.toLp 2 (fun i => ∑ j, U i j * x j)

def mtv {a b : ℕ} (U : Mat a b) (x : Vec a) : Vec b :=
  WithLp.toLp 2 (fun j => ∑ i, U i j * x i)

def frobenius {a b : ℕ} (U : Mat a b) : ℝ := Real.sqrt (∑ i, ∑ j, U i j ^ 2)

def orthonormalColumns {a b : ℕ} (U : Mat a b) : Prop :=
  ∀ i j, (∑ t, U t i * U t j) = if i = j then 1 else 0

/-- Mixed-radix, row-major coordinates, with the last local coordinate varying fastest. -/
abbrev Tensor (ds : List ℕ) := Vec ds.prod
abbrev Tuple (ds : List ℕ) := (j : ℕ) → Vec (ds.getD j 0)

def product {ds : List ℕ} (x : Tuple ds) : Tensor ds :=
  WithLp.toLp 2 (fun I => ∏ j : Fin ds.length,
    entry (x j.val) ((I.val / (ds.drop (j.val + 1)).prod) % ds.getD j.val 0))

def feasible {ds : List ℕ} (K : (j : ℕ) → Set (Vec (ds.getD j 0))) : Set (Tuple ds) :=
  {x | ∀ j < ds.length, x j ∈ K j}

def atoms {ds : List ℕ} (K : (j : ℕ) → Set (Vec (ds.getD j 0))) : Set (Tensor ds) :=
  product '' feasible K

def productHull {ds : List ℕ} (K : (j : ℕ) → Set (Vec (ds.getD j 0))) : Set (Tensor ds) :=
  convexHull ℝ (atoms K)

def unitBall (n : ℕ) : Set (Vec n) := {x | ‖x‖ ≤ 1}

def unitFactors {ds : List ℕ} (x : Tuple ds) : Prop := ∀ j < ds.length, ‖x j‖ = 1

/-- Finite signed decompositions, with arbitrary length (including the empty decomposition). -/
def decompositionCosts {ds : List ℕ} (M : Tensor ds) : Set ℝ≥0∞ :=
  {c | ∃ (r : ℕ) (lam : Fin r → ℝ) (x : Fin r → Tuple ds),
    (∀ t, unitFactors (x t)) ∧ M = ∑ t, lam t • product (x t) ∧
    c = ENNReal.ofReal (∑ t, |lam t|)}

/-- The source infimum, before any convex-hull characterization. Empty domain has value ∞. -/
def nuclearNorm {ds : List ℕ} (M : Tensor ds) : ℝ≥0∞ := sInf (decompositionCosts M)

def nuclearBall (ds : List ℕ) : Set (Tensor ds) := {M | nuclearNorm M ≤ 1}

/-- Frobenius distance. Empty feasible sets have distance ∞; no real empty-infimum default. -/
def distance {n : ℕ} (M : Vec n) (K : Set (Vec n)) : ℝ≥0∞ :=
  ⨅ Y ∈ K, ENNReal.ofReal ‖M - Y‖

def weakMembership {n : ℕ} (K : Set (Vec n)) (ε : ℝ) (M : Vec n) (b : Bool) : Prop :=
  (M ∈ K → b = true) ∧ (ENNReal.ofReal ε ≤ distance M K → b = false)

/-- Real supremum is used only with feasible tuples nonempty and factors in unit balls. -/
def optimum {ds : List ℕ} (M : Tensor ds)
    (K : (j : ℕ) → Set (Vec (ds.getD j 0))) : ℝ :=
  sSup ((fun x => inner ℝ M (product x)) '' feasible K)

/-- Fixed, explicit finite array serialization. -/
def encodeVec {n : ℕ} (x : Vec n) : List ℝ := List.ofFn x

def decodeVec (n : ℕ) (xs : List ℝ) : Vec n :=
  WithLp.toLp 2 (fun i => xs[i.val]?.getD 0)

def encodeMat {a b : ℕ} (U : Mat a b) : List ℝ :=
  (List.ofFn fun i => List.ofFn fun j => U i j).flatten

end NuclearTensor.Membership


