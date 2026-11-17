-- Prove2me | Definitions.Def_QuerySampleRev_Supplement_IsQuasiRegular
-- name    : QuerySampleRev_Supplement_IsQuasiRegular
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:16:31.881682+00:00
-- url     : https://prove2.me/theorems/c2de14ec-b9c6-4f55-8401-f0dca892c8f0
-- title:
--   Quasi-regular distributions (Definition 4, $\lambda=1$)
-- statement:
--   A value distribution with sale probability $Q(p)=\mathbb P_{v\sim F}[v\ge p]$ is **quasi-regular** if the ratio
--   $$
--   p\;\mapsto\;\frac{Q(p)^{-1}-1}{p},\qquad\text{with value }+\infty\text{ when }Q(p)=0,
--   $$
--   is nondecreasing for $p>0$. This is Definition 4 of the paper ($\lambda$-quasi-regular distributions) with $\lambda=1$. Quasi-regular distributions contain the regular and the quasi-MHR distributions; they are the family of Theorems 3, 11 and 36.
--
--   **Formalization Note** The ratio takes values in the extended reals, exactly like the published quasi-MHR ratio: it is $+\infty$ where $Q(p)=\mu([p,\infty))=0$ and the real number $(Q(p)^{-1}-1)/p$ otherwise. The paper's equivalent form ($pQ(p)/F(p)$ nonincreasing) is not used as the definition.
-- source:
--   Jin, Tang, Wang, Zhang, Query-Sample Tradeoffs for Revenue Maximization (manuscript, sha256 c31ea3d3…), Definition 4 and the following paragraph, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_QuerySampleRev_rStar

open MeasureTheory
open scoped ENNReal

namespace QuerySampleRev.Supplement

open QuerySampleRev

/-- **The quasi-regular ratio `(Q(p)⁻¹ − 1)/p`.** Jin, Tang, Wang, Zhang, *Query-Sample Tradeoffs for
Revenue Maximization* (manuscript, sha256 c31ea3d3…), Definition 4 with `λ = 1`, p.12 (PDF 14): the function
"`p ↦ (Q(p)^{−λ} − 1)/p` … with value `+∞` when `Q(p) = 0`".

**Formalization Note.** Valued in `EReal`, exactly like the published `QuerySampleRev.qmhrRatio`: it is `⊤`
when `Q(p) = μ([p, ∞)) = 0`, and the real number `(Q(p)⁻¹ − 1)/p` otherwise. For a probability measure
`Q(p) ≤ 1` is finite, so `toReal` is exact. -/
noncomputable def qregRatio (μ : Measure ℝ) (p : ℝ) : EReal :=
  if saleProb μ p = 0 then ⊤ else ((((saleProb μ p).toReal)⁻¹ - 1) / p : ℝ)

/-- **Quasi-regular distribution.** Same source, Definition 4 (λ-quasi-regular, `λ = 1`), p.12 (PDF 14):
"a distribution `F` is λ-quasi-regular if the function `p ↦ (Q(p)^{−λ} − 1)/p` … is nondecreasing for
`p > 0`, with value `+∞` when `Q(p) = 0`"; "The parameter values … `λ = 1` recover … quasi-regular
distributions".

`IsQuasiRegular μ` says that `p ↦ (Q(p)⁻¹ − 1)/p` (with value `+∞` where `Q(p) = 0`) is nondecreasing on
`(0, ∞)`.

**Formalization Note.** The paper's equivalent form `B(p) = pQ(p)/F(p)` nonincreasing is not used as the
definition. -/
def IsQuasiRegular (μ : Measure ℝ) : Prop := MonotoneOn (qregRatio μ) (Set.Ioi 0)

end QuerySampleRev.Supplement


