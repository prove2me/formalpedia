-- Prove2me | Definitions.Def_MatrixSenseRank_Testing_Geometry
-- name    : MatrixSenseRank_Testing_Geometry
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T13:46:19.947194+00:00
-- url     : https://prove2.me/theorems/f9ed144d-1599-4954-b7ca-b0ed58a68cb1
-- title:
--   Normalized rank distance and relative sparsity distance
-- statement:
--   For a real $n\times m$ matrix $A$, its Frobenius norm is the Euclidean norm of its entries. For a natural rank parameter $k$, set
--   $$\mathcal R_k^1=\{B:\operatorname{rank}(B)\le k,\ \|B\|_F=1\},\qquad
--   \operatorname{dist}_k(A)=\inf_{B\in\mathcal R_k^1}\|A-B\|_F.$$
--   The singular tail is $\tau_k(A)=\sum_{i=k+1}^{\min(n,m)}\sigma_i(A)^2$, with singular values in nonincreasing order. A real vector $w\in\mathbb R^n$ is $k$-sparse when at most $k$ of its coordinates are nonzero; for nonzero $w$ define
--   $$\operatorname{dist}(w,k\text{-sparse})=\inf_{v\ k\text{-sparse}}\frac{\|w-v\|_2}{\|w\|_2}.$$
--   There is no norm restriction on $v$. These are the two distinct distance notions used in the matrix and linear testing promises.
--
--   **Formalization Note** Dimensions use `Fin n`. The published rank-at-most set and Euclidean singular values are reused. Singular position $i$ in a zero-based sum is the published one-based value at $i+1$, never at zero. Matrix distance is used only for positive dimensions and $1\le k\le\min(n,m)$, where the feasible set is nonempty; both infima are bounded below by zero. Relative distance is used only at nonzero vectors, where its infimum is attained (there are finitely many coordinate supports). No singular-tail identity is built into the distance definition.
-- source:
--   Yiqiao Bao, Anindya De, Shivam Nadimpalli, Rocco A. Servedio, Chenyang Sun, Nathan White, STOC 2027 submission #380 (October 2026), §1.2, Eqs. (3)–(4), printed p. 2 / PDF p. 3; §3.2, printed p. 12 / PDF p. 13; §6, Eq. (22), printed p. 26 / PDF p. 27; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/380.pdf; PDF SHA-256 6e4e46ced4dfe65bbe94e4cec3e8230032914efef9d87b0f544bbea151a00c3b.

import Mathlib
import Definitions.Def_ProjLikeRetr_FixedRank_SVD
import Definitions.Def_ProjLikeRetr_FixedRank_rankSet

set_option autoImplicit false
open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace MatrixSenseRank.Testing

/-- Euclidean norm of all matrix entries, independent of matrix norm instances. -/
noncomputable def frobenius {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, (A i j) ^ 2)

/-- Equation (3) includes unit norm on the approximant. -/
def unitRankSet (n m k : ℕ) : Set (Matrix (Fin n) (Fin m) ℝ) :=
  {B | B ∈ ProjLikeRetr.FixedRank.rankLeSet k ∧ frobenius B = 1}

noncomputable def rankDistance {n m : ℕ} (k : ℕ) (A : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  sInf ((fun B => frobenius (A - B)) '' unitRankSet n m k)

/-- The published `sv` is one-based; `i+1` never evaluates it at zero. -/
noncomputable def singularTail {n m : ℕ} (k : ℕ) (A : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  ∑ i ∈ Finset.range (min n m),
    if k ≤ i then (ProjLikeRetr.FixedRank.sv A (i + 1)) ^ 2 else 0

noncomputable def vectorNorm {n : ℕ} (w : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i, (w i) ^ 2)

def IsSparse {n : ℕ} (k : ℕ) (w : Fin n → ℝ) : Prop :=
  (Finset.univ.filter (fun i => w i ≠ 0)).card ≤ k

/-- Equation (22): approximants have arbitrary norm, including the zero vector. -/
noncomputable def sparseDistance {n : ℕ} (k : ℕ) (w : Fin n → ℝ) : ℝ :=
  sInf {d | ∃ v : Fin n → ℝ, IsSparse k v ∧ d = vectorNorm (w - v) / vectorNorm w}

end MatrixSenseRank.Testing


