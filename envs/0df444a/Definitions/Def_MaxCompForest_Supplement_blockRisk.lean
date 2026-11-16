-- Prove2me | Definitions.Def_MaxCompForest_Supplement_blockRisk
-- name    : MaxCompForest_Supplement_blockRisk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:11:01.02701+00:00
-- url     : https://prove2.me/theorems/4d9aea2d-df33-4015-b613-b75affdb3c02
-- title:
--   Risk $\mathbb E\|P_QY-f\|_D^2$ of independent block averaging
-- statement:
--   Let $\mu$ be a law on partitions of $V$, fixed independently of the signal and the noise. For a signal $f$, draw $Q\sim\mu$ and $\xi\sim N(0,\sigma^2D^{-1})$ independently, observe $Y=f+\xi$ and estimate $\hat f=P_QY$. The **risk** at $f$ is
--
--   $$\mathbb E\,\|P_QY-f\|_D^2=\sum_Q\mu(Q)\int\|P_Q(f+\xi)-f\|_D^2\,dN(0,\sigma^2D^{-1})(\xi).$$
--
--   **Formalization Note** The expectation is a finite sum over partitions of a lower Lebesgue integral with values in $[0,\infty]$, so no integrability condition is needed and no junk value $0$ can occur.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), Theorem 5.2 and (5.5), p.30 (PDF p.32)

import Mathlib
import Definitions.Def_EffResSparsify_ResistanceSketch_Graph
import Definitions.Def_MaxCompForest_deg
import Definitions.Def_MaxCompForest_Supplement_noise
import Definitions.Def_MaxCompForest_Supplement_blockAvgMat
import Definitions.Def_MaxCompForest_Supplement_dNormSq
open EffResSparsify.ResistanceSketch
open MeasureTheory
open Matrix
set_option autoImplicit false

namespace MaxCompForest.Supplement

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- **The risk of independent block averaging** `E‖P_Q Y − f‖²_D` at the signal `f`, where `Y = f + ξ`,
`ξ ∼ N(0, σ²D⁻¹)` and `Q ∼ μ` is drawn independently of `ξ` (and fixed before `f` and `ξ`).
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), Theorem 5.2 and (5.5), p.30; the estimator `f̂ = P_Q Y`, p.30.

**Formalization Note.** The expectation is over the product of `μ` and the noise law: a finite sum over
partitions of a lower Lebesgue integral in `ℝ≥0∞`, so it needs no integrability side condition and is never a
junk `0`. -/
noncomputable def blockRisk (G : WGraph V E) (σ : ℝ) (μ : PMF (Finpartition (Finset.univ : Finset V)))
    (f : V → ℝ) : ENNReal :=
  ∑ Q, μ Q * ∫⁻ ξ, ENNReal.ofReal
    (dNormSq (MaxCompForest.deg G) (blockAvgMat (MaxCompForest.deg G) Q *ᵥ (f + ξ) - f)) ∂ noise G σ

end MaxCompForest.Supplement


