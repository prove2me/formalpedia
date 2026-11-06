-- Prove2me | Definitions.Def_SKWeakPoincare_OmegaEnd
-- name    : SKWeakPoincare_OmegaEnd
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:39:23.761566+00:00
-- url     : https://prove2.me/theorems/f9bc0184-837d-489b-9d29-6ff6be83913f
-- title:
--   The matrix event $\Omega_n^{\mathrm{end}}$: $\|A\|_{\mathrm{op}}\le3$ and small principal submatrices
-- statement:
--   For a disorder $A$ (a symmetric zero-diagonal $n\times n$ matrix), $\beta_1>0$ and $\delta>0$, the event $\Omega_n^{\mathrm{end}}$ is
--   $$
--   \Omega_n^{\mathrm{end}}=\Big\{A:\ \|A\|_{\mathrm{op}}\le3,\ \max_{|I|\le\delta n}\|\beta_1A_{I,I}\|_{\mathrm{op}}\le\tfrac15\Big\},
--   $$
--   where $A_{I,I}$ is the principal submatrix on $I\subseteq[n]$ and $\|\cdot\|_{\mathrm{op}}$ is the Euclidean operator norm. The module also defines the symmetric matrix $A$ of a disorder (`symMat`) and the operator norm (`opNorm`).
--
--   On this event the strong-field estimates of Appendix D apply.
--
--   **Formalization Note** The maximum over $|I|\le\delta n$ is written as a bound for every such $I$; the empty $I$ gives a $0\times0$ matrix of norm $0$. The operator norm follows the published `lawCovNorm` convention.
-- source:
--   Hou–Liu–Yu, Simulated annealing and Weak Poincaré inequalities with inverse-polynomial accuracy for the Sherrington–Kirkpatrick model, arXiv:2610.09882, Appendix D.1, p.83

import Mathlib
import Definitions.Def_CriticalSK

open OAI.CriticalSK

namespace SKWeakPoincare

/-- The symmetric zero-diagonal `n × n` matrix `A` of a disorder `W` (edges `i < j`):
`A_{ij} = A_{ji} = W_{ij}` for `i < j`, `A_{ii} = 0`. -/
noncomputable def symMat {n : ℕ} (W : Disorder n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i k =>
    if h : i < k then W ⟨(i, k), h⟩
    else if h' : k < i then W ⟨(k, i), h'⟩
    else 0

/-- Euclidean operator norm `‖M‖_op` of a square real matrix (the convention of the published
`OAI.CriticalSK.covarianceNorm` and `SKAnnealing.Sampling.lawCovNorm`). -/
noncomputable def opNorm {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) : ℝ :=
  ‖(Matrix.toEuclideanLin M).toContinuousLinearMap‖

/-- **The matrix event `Ω_n^end`**:
`Ω_n^end = {A : ‖A‖_op ≤ 3, max_{|I| ≤ δn} ‖β₁ A_{I,I}‖_op ≤ 1/5}`.
Hou–Liu–Yu, arXiv:2610.09882, Appendix D.1, p. 83.

**Formalization Note.** `A = symMat W`; `A_{I,I}` is the principal submatrix on `I ⊆ [n]`, indexed by
the elements of `I`; the maximum over `|I| ≤ δn` is a bound for every such `I` (the empty `I` gives the
`0 × 0` matrix, of norm `0`). -/
def OmegaEnd (β₁ δ : ℝ) (n : ℕ) : Set (Disorder n) :=
  {W | opNorm (symMat W) ≤ 3 ∧
    ∀ I : Finset (Fin n), (I.card : ℝ) ≤ δ * n →
      opNorm (β₁ • (symMat W).submatrix (Subtype.val : I → Fin n) (Subtype.val : I → Fin n))
        ≤ 1 / 5}

end SKWeakPoincare


