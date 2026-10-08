-- Prove2me | Definitions.Def_InputSparsity_Embed_SparseEmbedding
-- name    : InputSparsity_Embed_SparseEmbedding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T10:17:17.106746+00:00
-- url     : https://prove2.me/theorems/a6c0c6fa-0a37-485d-9354-4420da676e5b
-- title:
--   §§2–3, pp. 7–9 — sparse embedding, squared norms, leverage scores, and heavy/light events
-- statement:
--   A sparse embedding of an input vector in $\mathbb R^n$ into $\mathbb R^t$ is specified by a bucket map $h:[n]\to[t]$ and independent signs $\sigma_i\in\{-1,1\}$. The matrix $\Phi$ has its sole nonzero in column $i$ at row $h(i)$, and $D$ is diagonal with entries $\sigma_i$. The sketch is $S=\Phi D$. The probability space is the uniform product of all bucket maps and sign assignments.
--
--   For a vector $v$ and matrix $M$, the squared Euclidean and Frobenius norms are the sums of squared coordinates. If $U$ has orthonormal columns, its leverage score at row $i$ is $u_i=\sum_j U_{ij}^2$. At threshold $T>0$, the light coordinates have $u_i\le T$ and the heavy coordinates have $u_i>T$. The bucket event bounds the total light leverage in every bucket by $W$; the heavy event requires distinct heavy coordinates to land in distinct buckets.
--
--   These objects give one common model for the concentration and norm-preservation statements in §3.
--
--   **Formalization Note** Rows use zero-based `Fin` indices. The uniform law is a counting ratio on a finite type; results using a free bucket count assume $t>0$. The source sorts rows by decreasing leverage before writing the heavy and light ranges. This definition uses the equivalent threshold predicates, without a sorting permutation. The conditions $n>d$ and no zero rows or columns in §2 concern running times and are not properties of the sketch.
-- source:
--   Clarkson and Woodruff, Low Rank Approximation and Regression in Input Sparsity Time, arXiv:1207.6365v4, pp. 7–9, §§2–3 (sparse embedding and leverage scores p. 7; bucket event p. 8; heavy event p. 9)

import Mathlib

namespace InputSparsity.Embed
open Matrix

/-- The finite product sample space for the bucket map and independent signs. -/
abbrev Omega (n t : ℕ) := (Fin n → Fin t) × (Fin n → Bool)

def sgn (b : Bool) : ℝ := if b then 1 else -1

def Phi {n t : ℕ} (h : Fin n → Fin t) : Matrix (Fin t) (Fin n) ℝ :=
  fun a i => if h i = a then 1 else 0

def Dmat {n : ℕ} (σ : Fin n → Bool) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun i => sgn (σ i))

def sketch {n t : ℕ} (h : Fin n → Fin t) (σ : Fin n → Bool) :
    Matrix (Fin t) (Fin n) ℝ := Phi h * Dmat σ

/-- Uniform probability on a finite type; `Nat.card` counts even nondecidable events. -/
noncomputable def unifProb (α : Type*) [Fintype α] (s : Set α) : ℝ :=
  (Nat.card s : ℝ) / Fintype.card α

def sqNorm {n : ℕ} (v : Fin n → ℝ) : ℝ := ∑ i, v i ^ 2

def frobSq {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, M i j ^ 2

def HasOrthonormalCols {n r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ) : Prop :=
  Uᵀ * U = 1

def lev {n r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ) (i : Fin n) : ℝ :=
  ∑ j, U i j ^ 2

noncomputable def light {n r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ) (T : ℝ)
    (y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => if lev U i ≤ T then y i else 0

noncomputable def heavy {n r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ) (T : ℝ)
    (y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => if T < lev U i then y i else 0

def BucketBound {n r t : ℕ} (U : Matrix (Fin n) (Fin r) ℝ)
    (T W : ℝ) (h : Fin n → Fin t) : Prop :=
  ∀ j : Fin t,
    ∑ i ∈ Finset.univ.filter (fun i => h i = j ∧ lev U i ≤ T), lev U i ≤ W

def PerfectOnHeavy {n r t : ℕ} (U : Matrix (Fin n) (Fin r) ℝ)
    (T : ℝ) (h : Fin n → Fin t) : Prop :=
  ∀ i i' : Fin n, T < lev U i → T < lev U i' → i ≠ i' → h i ≠ h i'

end InputSparsity.Embed


