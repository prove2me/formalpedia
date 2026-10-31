-- Prove2me | Definitions.Def_DuanCV_Gauss_IsQuadratureLaw
-- name    : DuanCV_Gauss_IsQuadratureLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:55:28.021006+00:00
-- url     : https://prove2.me/theorems/7540860b-78db-423f-961d-0b68c52b1799
-- title:
--   The law of the quadrature $w\cdot\hat r$ in a two-mode state
-- statement:
--   Write $\hat r=(\hat x_1,\hat p_1,\hat x_2,\hat p_2)$ with $[\hat x_j,\hat p_{j'}]=i\delta_{jj'}$, and let $w\in\mathbb R^4$. A Borel probability measure $\mu$ on $\mathbb R$ is the **law of the observable** $w\cdot\hat r=\sum_k w_k\hat r_k$ in the state $\rho$ when, for every $t\in\mathbb R$,
--
--   $$\int_{\mathbb R} e^{itx}\,d\mu(x)=\operatorname{tr}\bigl[\rho\,\exp(it\,w\cdot\hat r)\bigr].$$
--
--   This is the probability distribution of a measurement of $w\cdot\hat r$. The characteristic function determines $\mu$, so there is at most one such law. The paper's averages $\langle\cdot\rangle_\rho$ of quadratures are moments of this law.
--
--   **Formalization Note** The right side is the published Weyl trace `multimodeWeylTrace`, and its convergence is required at every $t$, so that a default value of an infinite sum can never produce a law.
-- source:
--   Duan, Giedke, Cirac, Zoller, Inseparability criterion for continuous variable systems, arXiv:quant-ph/9908056v2, Eq. (3), p. 2, and Eq. (5), p. 2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P19

open MeasureTheory
open QAlgorithms.Papers.Independent.Claimed50.P19 (DensityKernel CharacteristicSummable multimodeWeylTrace)
open QAlgorithms.Papers.Independent.Frontier30.P08 (QuadratureIndex)

namespace DuanCV.Gauss

/-- **The probability law of a quadrature observable in a state.**
Duan, Giedke, Cirac, Zoller, *Inseparability criterion for continuous variable systems*, arXiv:quant-ph/9908056v2, p. 1 (the averages `⟨·⟩_ρ` of Eq. (3)) and Eq. (5), p. 2.

`IsQuadratureLaw ρ w μ` says that `μ` is the distribution of the observable
`w·r̂ = ∑ₖ wₖ r̂ₖ` (with `r̂ = (x̂₁, p̂₁, x̂₂, p̂₂)`, `[x̂ⱼ, p̂ⱼ'] = iδⱼⱼ'`) in the state `ρ`: `μ` is a
probability measure on `ℝ` whose characteristic function at `t` is `tr ρ exp(i t w·r̂)`, the Weyl
trace `multimodeWeylTrace ρ (t • w)`.

**Formalization Note.** The trace pairing is required to converge at every `t`, so a default-zero
`tsum` can never produce a spurious law. On a trace-class `ρ` it always converges. By the
uniqueness of characteristic functions there is at most one such `μ`. -/
def IsQuadratureLaw (ρ : DensityKernel 2) (w : QuadratureIndex 2 → ℝ) (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧
    ∀ t : ℝ, CharacteristicSummable ρ (t • w) ∧ charFun μ t = multimodeWeylTrace ρ (t • w)

end DuanCV.Gauss


