-- Prove2me | Definitions.Def_QuerySampleRev_IsQuasiMHR
-- name    : QuerySampleRev_IsQuasiMHR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:35:35.521082+00:00
-- url     : https://prove2.me/theorems/705a2000-b795-48ed-8c85-4ef738d2b310
-- title:
--   Quasi-MHR distributions (Definition 4, $\lambda=0$)
-- statement:
--   A distribution with sale probability $Q$ is **quasi-MHR** if the ratio
--   $$
--   p\;\mapsto\;\frac{-\log Q(p)}{p},\qquad\text{with value }+\infty\text{ when }Q(p)=0,
--   $$
--   is nondecreasing for $p>0$ (natural logarithm). This is Definition 4 of the paper ($\lambda$-quasi-regular distributions) with $\lambda=0$. Quasi-MHR distributions contain the MHR distributions and are contained in the quasi-regular ones; they are the distribution family of the paper's Theorems 20 and 21.
--
--   **Formalization Note** The ratio takes values in the extended reals: it is $+\infty$ where $Q(p)=\mu([p,\infty))=0$ and the real number $-\log Q(p)/p$ otherwise; monotonicity is required on $(0,\infty)$.
-- source:
--   Jin, Tang, Wang, Zhang, Query-Sample Tradeoffs for Revenue Maximization (manuscript, sha256 c31ea3d3…), Definition 4 and the following paragraph, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_QuerySampleRev_rStar

open MeasureTheory
open scoped ENNReal

namespace QuerySampleRev

/-- **The quasi-MHR ratio `−log Q(p)/p`.** Jin, Tang, Wang, Zhang, *Query-Sample Tradeoffs for Revenue
Maximization* (manuscript, sha256 c31ea3d3…), Definition 4 with `λ = 0`, p.12 (PDF 14): the function
"`p ↦ − log Q(p)/p` … with value `+∞` when `Q(p) = 0`".

**Formalization Note.** Valued in `EReal`: it is `⊤` when `Q(p) = μ([p, ∞)) = 0`, and the real number
`−log Q(p)/p` otherwise (natural logarithm, §2, p.11). For a probability measure `Q(p) ≤ 1` is finite, so
`toReal` is exact. -/
noncomputable def qmhrRatio (μ : Measure ℝ) (p : ℝ) : EReal :=
  if saleProb μ p = 0 then ⊤ else ((-Real.log (saleProb μ p).toReal / p : ℝ) : EReal)

/-- **Quasi-MHR distribution.** Same source, Definition 4 (λ-quasi-regular, `λ = 0`), p.12 (PDF 14):
"a distribution `F` is λ-quasi-regular if the function … `p ↦ − log Q(p)/p` for `λ = 0` is nondecreasing
for `p > 0`, with value `+∞` when `Q(p) = 0`", and "quasi-MHR requires the ratio `− log Q(p)/p` to be
nondecreasing."

`IsQuasiMHR μ` says that `p ↦ −log Q(p)/p` (with value `+∞` where `Q(p) = 0`) is nondecreasing on
`(0, ∞)`. -/
def IsQuasiMHR (μ : Measure ℝ) : Prop := MonotoneOn (qmhrRatio μ) (Set.Ioi 0)

end QuerySampleRev


