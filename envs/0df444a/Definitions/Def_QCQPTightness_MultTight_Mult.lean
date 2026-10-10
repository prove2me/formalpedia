-- Prove2me | Definitions.Def_QCQPTightness_MultTight_Mult
-- name    : QCQPTightness_MultTight_Mult
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T18:20:40.259436+00:00
-- url     : https://prove2.me/theorems/9cb81e3e-5607-49b2-9a13-94626e668e01
-- title:
--   Definition 3, p. 11 — the quadratic eigenvalue multiplicity k: every A_i = I_k ⊗ 𝔸_i
-- statement:
--   For $k$, $n$ with $N = kn$, identify $\mathbb R^k\otimes\mathbb R^n$ with $\mathbb R^N$ so that block $j\in\{1,\dots,k\}$ and entry $s\in\{1,\dots,n\}$ correspond to coordinate $(j-1)n+s$. A QCQP has **multiplicity $k$** if for every $i\in[\![0,m]\!]$ there is a symmetric $\mathbb A_i\in\mathbb S^n$ with
--
--   $$A_i = I_k\otimes\mathbb A_i .$$
--
--   **Definition 3** (Wang–Kılınç-Karzan): the **quadratic eigenvalue multiplicity** of the QCQP is the largest integer $k$ with this property.
--
--   A large multiplicity says the quadratic parts of all constraints share $k$ identical copies of one $n\times n$ form; Theorems 7 and 8 of the paper turn this symmetry into exactness of the SDP relaxation.
--
--   **Formalization Note** $I_k\otimes\mathbb A$ is the Kronecker product indexed by `Fin k × Fin n`, reindexed to `Fin N` by `finProdFinEquiv` (block `j`, entry `s` ↦ `s + n * j`, the 0-based form of the paper's convention). "The largest integer" is `IsGreatest`. When $N = 0$ every $k$ qualifies, so no largest exists; the paper's QCQPs have $N\ge 1$.
-- source:
--   arXiv:1911.09195v3, Definition 3, p. 11

import Mathlib
import Definitions.Def_QCQPTightness_MultTight_QCQP

noncomputable section

namespace QCQPTightness.MultTight

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

end QCQPTightness.MultTight


