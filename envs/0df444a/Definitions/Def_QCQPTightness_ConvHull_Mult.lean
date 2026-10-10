-- Prove2me | Definitions.Def_QCQPTightness_ConvHull_Mult
-- name    : QCQPTightness_ConvHull_Mult
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T17:26:50.297774+00:00
-- url     : https://prove2.me/theorems/94595c40-1a18-458c-bae1-886b8ee9e84e
-- title:
--   Definition 3, p. 11 — the quadratic eigenvalue multiplicity k: the largest k with A_i = I_k ⊗ 𝔸_i for every i ∈ ⟦0, m⟧
-- statement:
--   **Definition 3 (p. 11).** The *quadratic eigenvalue multiplicity* of the QCQP (1) is the largest integer $k$ such that for every $i\in\{0,1,\dots,m\}$ there is $\mathbb A_i\in\mathbb S^n$ with
--   $$A_i=I_k\otimes\mathbb A_i ,$$
--   where $N=kn$. Every QCQP has $k\ge1$ (take $k=1$), and $k$ divides $N$.
--
--   The multiplicity measures a block symmetry of the quadratic forms; large $k$ forces large shared zero eigenspaces on semidefinite faces of $\Gamma$ (Lemma 6), which is how the multiplicity form of the convex hull theorem (Theorem 2) is derived.
--
--   **Formalization Note.** $\mathbb R^N$ is identified with $\mathbb R^k\otimes\mathbb R^n$ by sending block $j$, entry $s$ to coordinate $(j-1)n+s$ (`finProdFinEquiv`). The predicate `HasMultiplicity k` asks for the factorisation of $A_0$ and every $A_i$; `IsQuadEigMult k` says $k$ is the greatest such integer. For $N=0$ every $k$ factors and no greatest one exists, so statements assuming `IsQuadEigMult k` are vacuous at $N=0$; the paper's $x\in\mathbb R^N$ has $N\ge1$.
-- source:
--   arXiv:1911.09195v3, Definition 3, p. 11

import Mathlib
import Definitions.Def_QCQPTightness_ConvHull_QCQP

noncomputable section

namespace QCQPTightness.ConvHull

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

end QCQPTightness.ConvHull


