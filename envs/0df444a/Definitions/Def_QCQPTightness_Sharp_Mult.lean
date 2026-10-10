-- Prove2me | Definitions.Def_QCQPTightness_Sharp_Mult
-- name    : QCQPTightness_Sharp_Mult
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T18:20:12.707665+00:00
-- url     : https://prove2.me/theorems/4bf089f0-2b47-470b-a091-799774208feb
-- title:
--   Definition 3, p. 11 — the quadratic eigenvalue multiplicity
-- statement:
--   The **quadratic eigenvalue multiplicity** of a QCQP is the largest integer $k$ such that for every $i\in[\![0,m]\!]$ there is $\mathbb A_i\in\mathbb S^n$ with
--   $$
--   A_i=I_k\otimes\mathbb A_i ,
--   $$
--   where $N=kn$. Equivalently, after splitting $\mathbb R^N$ into $k$ consecutive blocks of length $n$, every quadratic form is the same $n\times n$ form applied blockwise.
--
--   This parameter drives the sufficient conditions of Theorems 1 and 2 for the exactness of the SDP relaxation.
--
--   **Formalization Note** $\mathbb R^k\otimes\mathbb R^n$ is identified with $\mathbb R^N$ by sending block $j$, entry $s$ (0-based) to coordinate $s+nj$; `HasMultiplicity k` states the block form for one $k$, and `IsQuadEigMult k` says $k$ is the greatest such integer.
-- source:
--   arXiv:1911.09195v3, Definition 3, p. 11

import Mathlib
import Definitions.Def_QCQPTightness_Sharp_QCQP

noncomputable section

namespace QCQPTightness.Sharp

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

end QCQPTightness.Sharp


