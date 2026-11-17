-- Prove2me | Definitions.Def_QuerySampleRev_Supplement_IsRegular
-- name    : QuerySampleRev_Supplement_IsRegular
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:17:22.215114+00:00
-- url     : https://prove2.me/theorems/b151ed47-df94-49d9-b94f-283da02a9335
-- title:
--   Regular distributions (Definition 1): concave revenue-quantile curve $R_{\mathrm{qt}}(q)=qQ^{-1}(q)$
-- statement:
--   For a value distribution with sale probability $Q$, the **generalized inverse** and the **revenue-quantile curve** are
--   $$
--   Q^{-1}(q)=\sup\{p\ge0:\ Q(p)\ge q\},\qquad R_{\mathrm{qt}}(q)=q\,Q^{-1}(q),\qquad q\in(0,1].
--   $$
--   The distribution is **regular** if $R_{\mathrm{qt}}$ is concave on $(0,1]$. Regular distributions contain the MHR distributions and are contained in the quasi-regular ones; they are the family of Theorems 15, 16 and 37.
--
--   **Formalization Note** The supremum is a real supremum; for a probability measure with no mass on $(-\infty,0)$ and $q\in(0,1]$ the set is nonempty ($Q(0)=1$) and bounded ($Q(p)\to0$), so no default value arises on the paper's distributions. The right-limit extension of $R_{\mathrm{qt}}$ to $q=0$ is not part of the condition. No density is assumed (the virtual-value formulation is only an equivalent form for laws with a positive density).
-- source:
--   Jin, Tang, Wang, Zhang, Query-Sample Tradeoffs for Revenue Maximization (manuscript, sha256 c31ea3d3…), §2.1, p.11 (PDF p.13), display defining Q⁻¹ and R_qt; Definition 1, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_QuerySampleRev_rStar

open MeasureTheory
open scoped ENNReal

namespace QuerySampleRev.Supplement

open QuerySampleRev

/-- **Generalized inverse `Q⁻¹(q)`.** Jin, Tang, Wang, Zhang, *Query-Sample Tradeoffs for Revenue
Maximization* (manuscript, sha256 c31ea3d3…), §2.1, p.11 (PDF 13):
"`Q⁻¹(q) ≜ sup {p ≥ 0 ∶ Q(p) ≥ q}`, `q ∈ (0, 1]`".

**Formalization Note.** A real supremum. For a probability measure with no mass on `(−∞, 0)` and
`q ∈ (0, 1]` the set is nonempty (`Q(0) = 1 ≥ q`) and bounded above (`Q(p) → 0` as `p → ∞`), so no junk
value arises on the distribution families of the paper. -/
noncomputable def genInv (μ : Measure ℝ) (q : ℝ) : ℝ :=
  sSup {p : ℝ | 0 ≤ p ∧ ENNReal.ofReal q ≤ saleProb μ p}

/-- **Revenue-quantile curve `R_qt(q) = q Q⁻¹(q)`.** Same source, §2.1, p.11 (PDF 13):
"`R_qt(q) ≜ qQ⁻¹(q)`, `q ∈ (0, 1]`". -/
noncomputable def revQuantile (μ : Measure ℝ) (q : ℝ) : ℝ := q * genInv μ q

/-- **Regular distribution.** Same source, Definition 1 (Regular Distributions [Mye81]), p.12 (PDF 14):
"A distribution `F` is regular if its revenue-quantile curve `R_qt` is concave."

`IsRegular μ` says that `q ↦ R_qt(q) = q Q⁻¹(q)` is concave on `(0, 1]`.

**Formalization Note.** Concavity is required on the domain `(0, 1]` on which §2.1 defines `R_qt`; the
right-limit extension to `q = 0` is not part of the condition. No density is assumed (the paper's density
formulation via the virtual value is only an equivalent form for laws with a positive density). -/
def IsRegular (μ : Measure ℝ) : Prop := ConcaveOn ℝ (Set.Ioc 0 1) (revQuantile μ)

end QuerySampleRev.Supplement


