-- Prove2me | Definitions.Def_LpSubspaceCoreset_SmallP_Cost
-- name    : LpSubspaceCoreset_SmallP_Cost
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:46:26.680784+00:00
-- url     : https://prove2.me/theorems/e6f1916a-cc02-493a-a755-34e5d7025010
-- title:
--   The ℓp subspace-approximation cost, subspaces of dimension at most k, OPT and strong row coresets
-- statement:
--   For a matrix $A\in\mathbb R^{n\times d}$ with rows $a_1^\top,\dots,a_n^\top$, a real $p$ and a linear subspace $F\subseteq\mathbb R^d$, let $P_F$ be the orthogonal projector onto $F$ and $Q_F=I-P_F$. The **ℓp subspace-approximation cost** is
--   $$\mathrm{cost}_A(F)=\|AQ_F\|_{p,2}^p=\sum_{i=1}^n\|Q_Fa_i\|_2^p .$$
--   $\mathcal F_k$ is the set of all subspaces of $\mathbb R^d$ of dimension at most $k$ (the zero subspace included), and $\mathrm{OPT}_A=\min_{F\in\mathcal F_k}\mathrm{cost}_A(F)$.
--
--   A **reweighted row subset** is a matrix $S\in\mathbb R^{s\times n}$ with exactly one nonzero entry in each row; $SA$ then consists of rescaled rows of $A$, repeated indices may be merged, and the size is the number of distinct retained rows. $S$ is a **$(1\pm\varepsilon)$ strong row coreset** of $A$ (Definition 2.1) if
--   $$(1-\varepsilon)\,\mathrm{cost}_A(F)\le\mathrm{cost}_{SA}(F)\le(1+\varepsilon)\,\mathrm{cost}_A(F)\qquad\text{for every }F\in\mathcal F_k.$$
--   These are the objects every statement of the mission is about.
--
--   **Formalization Note** Rows are vectors of `EuclideanSpace ℝ (Fin d)`, $P_F$ is `Submodule.starProjection`, powers are `Real.rpow` of nonnegative norms. `OPT` is the infimum of the nonempty, bounded-below set of costs over $\mathcal F_k$ (the minimum is attained, so this is its value). `support S` is the set of distinct retained rows; `norm2` is the Euclidean norm of a coordinate vector.
-- source:
--   Lin, Mirrokni, Woodruff, Nearly Optimal Strong Coresets for ℓp Subspace Approximation, arXiv:2608.26047 (held PDF of 2026-11-03, sha256 4c61606e…), pp. 1, 8–9, §2.1 and Definition 2.1

import Mathlib

namespace LpSubspaceCoreset.SmallP

/-!
# The ℓp subspace-approximation cost, `F_k`, `OPT_A` and strong row coresets

Lin, Mirrokni, Woodruff, *Nearly Optimal Strong Coresets for ℓp Subspace Approximation*,
arXiv:2608.26047, p. 1, §2.1 (p. 8) and Definition 2.1 (p. 9).

* A matrix `A ∈ ℝ^{n×d}` is a `Matrix (Fin n) (Fin d) ℝ`; its row `a_i` is the vector
  `rowVec A i` of the Euclidean space `ℝ^d` (`EuclideanSpace ℝ (Fin d)`).
* For a linear subspace `F ⊆ ℝ^d`, `P_F` is the orthogonal projector (`F.starProjection`) and
  `Q_F = I − P_F`.
* `cost p A F = Σ_i ‖Q_F a_i‖₂^p` (real power `p`, Euclidean norm).
* `F_k` is the set of all subspaces of dimension at most `k` (the zero subspace included).
* `OPT p k A = min_{F ∈ F_k} cost p A F`, written as an infimum over the nonempty set `F_k` of
  nonnegative reals (the minimum is attained; the infimum is its value).
* A reweighted row subset is a matrix `S ∈ ℝ^{s×n}` with exactly one nonzero entry in each row
  (Definition 2.1); its size is the number of distinct retained rows (columns of `S` that carry a
  nonzero entry). `SA` is the matrix product `S * A`.
-/

/-- Row `i` of `A`, as a vector of the Euclidean space `ℝ^d`. -/
noncomputable def rowVec {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (i : Fin n) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (A i)

/-- `Q_F x = x − P_F x`, the component of `x` orthogonal to the subspace `F`. -/
noncomputable def resid {d : ℕ} (F : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  x - F.starProjection x

/-- The ℓp subspace-approximation cost `cost_A(F) = Σ_i ‖Q_F a_i‖₂^p`. -/
noncomputable def cost {n d : ℕ} (p : ℝ) (A : Matrix (Fin n) (Fin d) ℝ)
    (F : Submodule ℝ (EuclideanSpace ℝ (Fin d))) : ℝ :=
  ∑ i, ‖resid F (rowVec A i)‖ ^ p

/-- `F ∈ F_k`: the subspace `F ⊆ ℝ^d` has dimension at most `k`. -/
def InFk {d : ℕ} (k : ℕ) (F : Submodule ℝ (EuclideanSpace ℝ (Fin d))) : Prop :=
  Module.finrank ℝ F ≤ k

/-- `OPT_A = min_{F ∈ F_k} cost_A(F)` (the infimum over the nonempty, bounded-below set of
costs of subspaces of dimension at most `k`). -/
noncomputable def OPT {n d : ℕ} (p : ℝ) (k : ℕ) (A : Matrix (Fin n) (Fin d) ℝ) : ℝ :=
  sInf {c : ℝ | ∃ F : Submodule ℝ (EuclideanSpace ℝ (Fin d)), InFk k F ∧ c = cost p A F}

/-- Definition 2.1: `S ∈ ℝ^{s×n}` is a reweighted row subset (row-sampling matrix): every row
of `S` has exactly one nonzero entry. -/
def IsRowSampling {s n : ℕ} (S : Matrix (Fin s) (Fin n) ℝ) : Prop :=
  ∀ j : Fin s, ∃! i : Fin n, S j i ≠ 0

/-- The retained rows of `A` under `S`: the indices `i` with a nonzero entry in column `i`. -/
noncomputable def support {s n : ℕ} (S : Matrix (Fin s) (Fin n) ℝ) : Finset (Fin n) :=
  by classical exact Finset.univ.filter fun i => ∃ j : Fin s, S j i ≠ 0

/-- Definition 2.1: `S` is a `(1 ± ε)` strong row coreset of `A` for rank-at-most-`k`
ℓp subspace approximation: `S` is a reweighted row subset and
`(1 − ε) cost_A(F) ≤ cost_{SA}(F) ≤ (1 + ε) cost_A(F)` for every `F ∈ F_k`. -/
def IsStrongCoreset {s n d : ℕ} (p : ℝ) (k : ℕ) (ε : ℝ) (A : Matrix (Fin n) (Fin d) ℝ)
    (S : Matrix (Fin s) (Fin n) ℝ) : Prop :=
  IsRowSampling S ∧
    ∀ F : Submodule ℝ (EuclideanSpace ℝ (Fin d)), InFk k F →
      (1 - ε) * cost p A F ≤ cost p (S * A) F ∧ cost p (S * A) F ≤ (1 + ε) * cost p A F

/-- The Euclidean norm `‖v‖₂` of a coordinate vector. -/
noncomputable def norm2 {ι : Type*} [Fintype ι] (v : ι → ℝ) : ℝ :=
  ‖(WithLp.toLp 2 v : EuclideanSpace ℝ ι)‖

end LpSubspaceCoreset.SmallP


