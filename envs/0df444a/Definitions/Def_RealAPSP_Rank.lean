-- Prove2me | Definitions.Def_RealAPSP_Rank
-- name    : RealAPSP_Rank
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:57:42.212288+00:00
-- url     : https://prove2.me/theorems/7060008b-60dc-4269-a6ea-a642df40e1e1
-- title:
--   $\Delta$-approximate select-plus rank decompositions
-- statement:
--   A **$\Delta$-approximate rank-$r$ decomposition** of $A\in(\mathbb R\cup\{\bot\})^{n\times n}$ consists of $U\in\mathbb R^{n\times r}$, $V\in\mathbb R^{r\times n}$ and $S\in([r]\cup\{\bot\})^{n\times n}$ such that for all $(i,j)$ with $A[i,j]\ne\bot$, $k=S[i,j]$ is an index in $[r]$ with
--
--   $$A[i,j]=U[i,k]+V[k,j]\pm\Delta.$$
--
--   Low rank is what makes the Fredman-type and additive-combinatorics steps of the reduction possible.
--
--   **Formalization Note** The page assumes access to the decomposition whenever a rank bound is assumed, so it is part of the input. A real output cell may hold $D\cdot x$ for a stated integer $D$, as the machine computes only integer combinations of its input reals.
-- source:
--   Fischer, Polak, Schmidt, Real-to-Integer Reduction for All-Pairs Shortest Paths, arXiv:2611.04847 (held file sha256 a3dc0096…), §4.1, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_RealAPSP_Triangles

namespace RealAPSP

/-!
# Approximate select-plus rank decompositions, and how they are stored

Fischer, Polak, Schmidt, arXiv:2611.04847 (held file sha256 a3dc0096…), §4.1, p.11 (PDF p.13): "the ∆-approximate
select-plus rank (or just ∆-approximate rank) of a matrix A ∈ (R ∪ {⊥})^{n×n} is the smallest integer r ≥ 0 such that
there are matrices U ∈ R^{n×r} and V ∈ R^{r×n} satisfying the following: For all (i, j) ∈ [n]² with A[i, j] ≠ ⊥ there is a
k ∈ [r] such that: A[i, j] = U[i, k] + V[k, j] ± ∆. When S ∈ ([r] ∪ {⊥})^{n×n} is a matrix such that S[i, j] = k, we call
(U, V, S) a ∆-approximate rank-r decomposition of A. Whenever we say that a matrix A has ∆-approximate rank at most r, we
assume that we also have access to a ∆-approximate rank-r decomposition of A."

**Formalization Note.**
* The decomposition is therefore part of the input of every algorithmic statement that has a rank hypothesis.
* Input: `S` row-major (`0` for ⊥, `k+1` for `k`) in integer cells, `U` then `V` row-major in real cells.
* Output: the rank at `outCell 0`; `S` at `outCell (1 + i·n + j)`, same code; `U[i,k]` at `routCell (i·r + k)`;
  `V[k,j]` at `routCell (n·r + k·n + j)`. Real output cells may hold a multiple `D•x` of the real `x`, since the machine
  computes only integer combinations of its inputs: `HasRankOutput` divides by `D`.
-/

/-- `(U, V, S)` is a `∆`-approximate rank-`r` decomposition of `A` (p.11). -/
def IsRankDecomp {n : ℕ} (Δ : ℝ) (A : Mat ℝ n) (r : ℕ) (U : Fin n → Fin r → ℝ) (V : Fin r → Fin n → ℝ)
    (S : Fin n → Fin n → Option (Fin r)) : Prop :=
  ∀ i j a, A i j = some a → ∃ k, S i j = some k ∧ |a - (U i k + V k j)| ≤ Δ

/-- Integer input cells of a decomposition. -/
def decompInts {n r : ℕ} (S : Fin n → Fin n → Option (Fin r)) : List ℤ :=
  rowMajor fun i j =>
    match S i j with
    | none => 0
    | some k => ((k : ℕ) : ℤ) + 1

/-- Real input cells of a decomposition. -/
def decompReals {n r : ℕ} (U : Fin n → Fin r → ℝ) (V : Fin r → Fin n → ℝ) : List ℝ :=
  rowMajor U ++ rowMajor V

/-- The matrix `U` read from the output cells, divided by `D`. -/
noncomputable def outU (σ : State) (n r D : ℕ) : Fin n → Fin r → ℝ :=
  fun i k => σ.rmem (routCell ((i : ℕ) * r + k)) / D

/-- The matrix `V` read from the output cells, divided by `D`. -/
noncomputable def outV (σ : State) (n r D : ℕ) : Fin r → Fin n → ℝ :=
  fun k j => σ.rmem (routCell (n * r + (k : ℕ) * n + j)) / D

/-- The matrix `S` read from the output cells. -/
def outS (σ : State) (n r : ℕ) : Fin n → Fin n → Option (Fin r) :=
  fun i j =>
    let v := σ.imem (outCell (1 + (i : ℕ) * n + j))
    if h : 1 ≤ v ∧ (v - 1).toNat < r then some ⟨(v - 1).toNat, h.2⟩ else none

/-- The final state holds a `∆`-approximate rank-`r` decomposition of `A`, with real cells scaled by `D`. -/
def HasRankOutput {n : ℕ} (Δ : ℝ) (A : Mat ℝ n) (r D : ℕ) (σ : State) : Prop :=
  σ.imem (outCell 0) = (r : ℤ) ∧ IsRankDecomp Δ A r (outU σ n r D) (outV σ n r D) (outS σ n r)

end RealAPSP


