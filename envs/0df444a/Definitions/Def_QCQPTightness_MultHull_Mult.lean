-- Prove2me | Definitions.Def_QCQPTightness_MultHull_Mult
-- name    : QCQPTightness_MultHull_Mult
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T18:20:54.509294+00:00
-- url     : https://prove2.me/theorems/35f52645-4825-411e-ad7b-7097ced98861
-- title:
--   Definition 3, p. 11 — the quadratic eigenvalue multiplicity k: A_i = I_k ⊗ 𝔸_i for all i ∈ ⟦0, m⟧
-- statement:
--   For $k\ge 1$ and $\mathbb A\in\mathbb S^n$, $I_k\otimes\mathbb A$ is the block-diagonal $kn\times kn$ matrix with $k$ copies of $\mathbb A$ on the diagonal; the $j$-th block of $n$ coordinates of $\mathbb R^{kn}$ is coordinates $(j-1)n+1,\dots,jn$.
--
--   A QCQP of the form (1) **has multiplicity $k$** if $N = kn$ for some $n$ and for every $i\in[\![0,m]\!]$ there is a symmetric $\mathbb A_i\in\mathbb S^n$ with
--
--   $$A_i = I_k\otimes\mathbb A_i .$$
--
--   **Definition 3.** The *quadratic eigenvalue multiplicity* of the QCQP is the largest integer $k$ with this property.
--
--   The parameter $k$ measures how much block symmetry the quadratic forms share. Every QCQP has multiplicity $1$, and $k$ divides $N$; the paper's results without polyhedrality (Theorems 7 and 8) need $k$ large compared with the number of constraints.
--
--   **Formalization Note** $I_k\otimes\mathbb A$ is Mathlib's Kronecker product `kroneckerMap (· * ·) 1 𝔸`, indexed by pairs $(j, s)$, and is transported to $\{0,\dots,N-1\}$ by $(j, s)\mapsto s + nj$ (the paper's block convention, 0-based). `IsQuadEigMult k` says $k$ is the greatest element of the set of multiplicities. For $N=0$ this set is unbounded and no $k$ qualifies; for $N\ge1$ it is a subset of $\{1,\dots,N\}$ containing $1$, so its largest element exists.
-- source:
--   arXiv:1911.09195v3, Definition 3, p. 11

import Mathlib
import Definitions.Def_QCQPTightness_MultHull_QCQP

noncomputable section

namespace QCQPTightness.MultHull

open Matrix

/-- `I_k ⊗ 𝔸`, indexed by `Fin k × Fin n`. -/
def kronId (k : ℕ) {n : ℕ} (𝔸 : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin k × Fin n) (Fin k × Fin n) ℝ :=
  Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin k) (Fin k) ℝ) 𝔸

/-- The block identification `ℝ^k ⊗ ℝ^n ≅ ℝ^N` (`N = kn`): block `j`, entry `s` is coordinate
`(j − 1)n + s` of the paper, i.e. `finProdFinEquiv (j, s) = s + n * j`. -/
def blockEquiv {k n N : ℕ} (h : k * n = N) : Fin k × Fin n ≃ Fin N :=
  finProdFinEquiv.trans (finCongr h)

namespace QCQP

variable {N m : ℕ} (P : QCQP N m)

/-- Every `A_i`, `i ∈ ⟦0, m⟧`, is `I_k ⊗ 𝔸_i` for some `𝔸_i ∈ 𝕊^n`, `N = kn`. -/
def HasMultiplicity (k : ℕ) : Prop :=
  ∃ (n : ℕ) (h : k * n = N),
    (∃ 𝔸 : Matrix (Fin n) (Fin n) ℝ, 𝔸.IsSymm ∧
      P.A₀ = Matrix.reindex (blockEquiv h) (blockEquiv h) (kronId k 𝔸)) ∧
    ∀ i, ∃ 𝔸 : Matrix (Fin n) (Fin n) ℝ, 𝔸.IsSymm ∧
      P.A i = Matrix.reindex (blockEquiv h) (blockEquiv h) (kronId k 𝔸)

/-- Definition 3: `k` is the quadratic eigenvalue multiplicity, the largest such integer. -/
def IsQuadEigMult (k : ℕ) : Prop := IsGreatest {k' | P.HasMultiplicity k'} k

end QCQP

end QCQPTightness.MultHull


