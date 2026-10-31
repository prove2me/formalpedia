-- Prove2me | Definitions.Def_KallMayerSLP_SimpleRecourse_mixtureCdf
-- name    : KallMayerSLP_SimpleRecourse_mixtureCdf
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:13:09.817192+00:00
-- url     : https://prove2.me/theorems/0f614b57-e825-4e1e-88a7-b07b6b339cb8
-- title:
--   The mixture distribution function $G=H/W$, (2.58)/(2.62)
-- statement:
--   With $W:=\sum_{k=0}^{K-1}(\alpha_k+\beta_k)$,
--
--   $$
--   G(\xi) := \frac{H(\xi)}{W} = \frac{\sum_{k=0}^{K-1}\alpha_k F_{\tilde\xi}(\xi+u_k) + \sum_{k=0}^{K-1}\beta_k F_{\tilde\xi}(\xi-l_k)}{\sum_{k=0}^{K-1}(\alpha_k+\beta_k)} .
--   $$
--
--   Under Definition 2.4, $G$ is a distribution function: the mixture of the laws of $\tilde\xi-u_k$ and $\tilde\xi+l_k$ with weights $\alpha_k/W$ and $\beta_k/W$. Theorem 2.8 uses it to rewrite the expected MSRT function as an expected SRT function.
--
--   **Formalization Note** $G$ is defined by the formula. That it is a distribution function is a theorem (`eq_2_57_2_58`), not part of the definition.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, (2.58), p.240 (PDF 249) and (2.62), p.242 (PDF 251)

import Mathlib
import Definitions.Def_KallMayerSLP_SimpleRecourse_mixtureH

open MeasureTheory

namespace KallMayerSLP.SimpleRecourse

/-- **The mixture distribution function `G`, (2.58) = (2.62).**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, (2.58), p.240 (PDF 249), and
(2.62), p.242 (PDF 251):
`G(ξ) := H(ξ)/W = [Σ_{k=0}^{K−1} α_k F_ξ̃(ξ + u_k) + Σ_{k=0}^{K−1} β_k F_ξ̃(ξ − l_k)] / Σ_{k=0}^{K−1} (α_k + β_k)`.

**Formalization Note.** Defined by the formula, not by any property it is later shown to have.
`W = Σ_k (α_k + β_k) > 0` under Definition 2.4 (`IsMSRTData`); this definition does not assume it. -/
noncomputable def mixtureCdf {K : ℕ} (α β u l : Fin K → ℝ) (P : Measure ℝ) (ξ : ℝ) : ℝ :=
  mixtureH α β u l P ξ / ∑ k, (α k + β k)

end KallMayerSLP.SimpleRecourse


