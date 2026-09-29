-- Prove2me | Definitions.Def_SparseApprox_Hardness_Basic
-- name    : SparseApprox_Hardness_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:26:19.451896+00:00
-- url     : https://prove2.me/theorems/9bafe0aa-4892-447b-a412-36aa6e6c9669
-- title:
--   Exact cover by 3-sets and its SAS instance: exact covers, incidence matrix, all-ones vector, number of nonzeros
-- statement:
--   This file fixes the objects of the reduction from Exact Cover by 3-sets (X3C) to the sparse approximate solution problem (SAS) in Natarajan's hardness proof.
--
--   1. **X3C instance.** The ground set is $S=\{s_1,\dots,s_m\}$, identified with $\{1,\dots,m\}$, and the collection is a list $C=c_1,\dots,c_n$ of subsets of $S$; the same set may occur more than once in the list.
--   2. **Exact cover.** For an index set $J\subseteq\{1,\dots,n\}$, the sub-collection $\hat C=\{c_j : j\in J\}$ is an *exact cover* of $S$ when every element of $S$ occurs in exactly one of its sets:
--   $$\forall i\in\{1,\dots,m\}\ \exists!\, j\ \bigl(j\in J\ \text{and}\ s_i\in c_j\bigr).$$
--   3. **Incidence matrix.** $A\in\mathbb R^{m\times n}$ has one column per set of $C$: $A_{ij}=1$ if $s_i\in c_j$ and $A_{ij}=0$ otherwise.
--   4. **Right-hand side.** $b=(1,1,\dots,1)\in\mathbb R^m$, the vector of $m$ ones.
--   5. **Number of nonzeros.** For $x\in\mathbb R^n$, $\|x\|_0=|\{j : x_j\neq 0\}|$.
--   6. **Indicator vector.** For $J\subseteq\{1,\dots,n\}$, $\mathbf 1_J\in\mathbb R^n$ has $(\mathbf 1_J)_j=1$ if $j\in J$ and $0$ otherwise.
--
--   Together with the tolerance $\varepsilon=1/2$, the pair $(A,b)$ is the SAS instance that the proof of Theorem 1 builds from an X3C instance.
--
--   **Formalization Note** Vectors live in `EuclideanSpace ℝ (Fin m)` and `EuclideanSpace ℝ (Fin n)`, so that `‖·‖` is the Euclidean norm $\|\cdot\|_2$ of the paper. The collection is indexed (`C : Fin n → Finset (Fin m)`) rather than a set of sets, so repeated sets stay distinct, and an exact cover is a set of indices; the SAS side counts one nonzero entry per index, so both sides treat duplicates the same way. The 3-element condition on the sets is not part of these definitions; it is a hypothesis of each theorem that needs it.
-- source:
--   Natarajan, Sparse Approximate Solutions to Linear Systems, SIAM J. Comput. 24 (1995), p. 228, §2 (Problem SAS; Exact Cover by 3-sets; the transformation in the proof of Theorem 1)

import Mathlib

namespace SparseApprox.Hardness

/-- An instance of Exact Cover by 3-sets is a ground set `S = {s₁, …, s_m}`, encoded as `Fin m`,
and an indexed collection `C = c₁, …, c_n` of subsets of `S`, encoded as `C : Fin n → Finset (Fin m)`
(repeated sets are allowed). A sub-collection `Ĉ = {c_j | j ∈ J}`, given by its index set `J`, is an
*exact cover* of `S` when every element of `S` occurs in exactly one set of `Ĉ`. -/
def IsExactCover {m n : ℕ} (C : Fin n → Finset (Fin m)) (J : Finset (Fin n)) : Prop :=
  ∀ i : Fin m, ∃! j : Fin n, j ∈ J ∧ i ∈ C j

/-- The incidence matrix of the collection `C`: an `m × n` real matrix whose column `j` has entry
`1` in row `i` if `s_i ∈ c_j` and `0` otherwise. -/
def incidence {m n : ℕ} (C : Fin n → Finset (Fin m)) : Matrix (Fin m) (Fin n) ℝ :=
  Matrix.of fun i j => if i ∈ C j then 1 else 0

/-- The all-ones vector `b = (1, 1, …, 1)` of `ℝ^m`, with the Euclidean norm. -/
def onesVec (m : ℕ) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun _ => 1)

/-- The number of nonzero entries of a vector `x ∈ ℝ^n`. -/
noncomputable def nnz {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : ℕ :=
  (Finset.univ.filter (fun j => x j ≠ 0)).card

/-- The indicator vector of an index set `J ⊆ {1, …, n}`: `x_j = 1` if `j ∈ J` and `x_j = 0`
otherwise. -/
def indicatorVec {n : ℕ} (J : Finset (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun j => if j ∈ J then 1 else 0)

end SparseApprox.Hardness


