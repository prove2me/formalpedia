-- Prove2me | Definitions.Def_L22EigEst_eventE4
-- name    : L22EigEst_eventE4
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:23:21.338878+00:00
-- url     : https://prove2.me/theorems/39d6ed6c-2007-4016-897e-fb7de110cbc8
-- title:
--   Event E4 (Definition 4.2) — small off-diagonal row norms of $SA'S^\top$
-- statement:
--   Fix a constant $c$, $\varepsilon\in(0,1/4)$, a symmetric $A\in\mathbb R^{n\times n}$, and let $s=\lceil c\log(1/\varepsilon)/\varepsilon^2\rceil$, $p_i=s\|A_i\|_2^2/\|A\|_F^2$, $S$ the sampling matrix of a pattern $\delta$ and $A'$ the matrix of equation (2). **Event E4** holds when
--
--   $$\max_i\sum_{j\ne i}(SA'S^\top)_{ij}^2\le\frac{1000\,\varepsilon^2\|A\|_F^2}{c\log(1/\varepsilon)}.$$
--
--   E4 bounds the row-norm parameter $\sigma$ of the error matrix $SA'S^\top-M$ in Lemma 4.7; Claim 4.8 shows that it holds with probability at least $0.95$.
--
--   **Formalization Note** In the $n\times n$ view the rows of $SA'S^\top$ off the sample are zero, so the maximum over sampled rows and the bound for every $i$ coincide.
-- source:
--   Menand, Waingarten, Dimension-Free ℓ₂²-Sampling Algorithms for Eigenvalue Estimation, STOC 2027 submission (manuscript sha256 b1f6adce…), Definition 4.2 (Event E4), p.14

import Definitions.Def_L22EigEst_BoundedRowNorm
import Definitions.Def_L22EigEst_sampMat
import Definitions.Def_L22EigEst_zeroed

namespace L22EigEst

/-- **Event E4** (Definition 4.2, p.14), Menand, Waingarten, STOC 2027 submission (manuscript
sha256 b1f6adce…): "The off-diagonal parts of the row norms of the sampled principal sub-matrix
SA′S⊺ satisfy max_i Σ_{j≠i} (SA′S⊺)²_ij ≤ 1000 ε²∥A∥F²/(c log(1/ε))."

**Formalization Note.** `S` is the sampling matrix of Algorithm 1 for the pattern `δ`, with
`p_i = s‖A_i‖₂²/‖A‖_F²` and `s = ⌈c log(1/ε)/ε²⌉` (`sParam c ε`); `A′` is `zeroed A ε`. In the
`n × n` view the rows of `SA′S⊺` off the sample are zero, so the maximum over sampled rows and the
bound for every `i` coincide. -/
noncomputable def eventE4 {n : ℕ} (c ε : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (δ : Fin n → Bool) :
    Prop :=
  let S := sampMat (rowProb (sParam c ε) A) δ
  ∀ i, ∑ j ∈ Finset.univ.filter (fun j => j ≠ i), ((S * zeroed A ε * S) i j) ^ 2 ≤
    1000 * ε ^ 2 * frobSq A / (c * Real.log (1 / ε))

end L22EigEst


