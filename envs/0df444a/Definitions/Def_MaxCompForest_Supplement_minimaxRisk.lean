-- Prove2me | Definitions.Def_MaxCompForest_Supplement_minimaxRisk
-- name    : MaxCompForest_Supplement_minimaxRisk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:11:38.575207+00:00
-- url     : https://prove2.me/theorems/1c6faf8f-1b05-46a3-b9ec-872ddc99479b
-- title:
--   Minimax risk $R^*$ of graph-Sobolev Gaussian denoising
-- statement:
--   Let $G$ be a graph with Laplacian $L$ and degrees $d_v$, $R\ge0$, $\sigma>0$, and $H_R=\{f\in\mathbb R^V: f^{\top}Lf\le R^2\}$. In the model $Y=f+\xi$, $\xi\sim N(0,\sigma^2D^{-1})$, the **minimax risk** is
--
--   $$R^*=\inf_{\hat f}\ \sup_{f\in H_R}\ \mathbb E\,\|\hat f(Y)-f\|_D^2,$$
--
--   the infimum over all measurable estimators of $f$ from $Y$, independently randomized estimators included. It is the benchmark against which block-average estimators are compared in Section 5.
--
--   **Formalization Note** An estimator is a Markov kernel from observations to estimates; deterministic measurable estimators are the Dirac kernels. The risk is a lower integral with values in $[0,\infty]$, so a supremum equal to $+\infty$ is represented without a junk value. $f^{\top}Lf$ is the published `fnEnergy`.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), §5, p.28 (PDF p.30)

import Mathlib
import Definitions.Def_EffResSparsify_ResistanceSketch_Graph
import Definitions.Def_MaxCompForest_deg
import Definitions.Def_MaxCompForest_fnEnergy
import Definitions.Def_MaxCompForest_Supplement_noise
import Definitions.Def_MaxCompForest_Supplement_dNormSq
open EffResSparsify.ResistanceSketch
open MeasureTheory
open ProbabilityTheory
set_option autoImplicit false

namespace MaxCompForest.Supplement

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- **The minimax risk** `R* = inf_{f̂} sup_{f ∈ H_R} E‖f̂ − f‖²_D` over the class `H_R = {f : fᵀ L f ≤ R²}`, the
infimum taken over all measurable estimators of `f` from `Y = f + ξ`, `ξ ∼ N(0, σ²D⁻¹)`, independently
randomized ones included.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), §5, p.28 ("Let R∗ be the minimax expected error over HR among all measurable estimators …, allowing
independent randomization").

**Formalization Note.** An estimator is a Markov kernel `κ` from observations to estimates (a measurable,
possibly randomized rule; deterministic measurable estimators are the Dirac kernels). The risk is a lower
integral in `ℝ≥0∞`, so the supremum over the class may be `+∞` without a junk value. `fᵀ L f` is the published
`fnEnergy`. -/
noncomputable def minimaxRisk (G : WGraph V E) (σ R : ℝ) : ENNReal :=
  ⨅ κ : {κ : Kernel (V → ℝ) (V → ℝ) // IsMarkovKernel κ},
    ⨆ f : V → ℝ, ⨆ _ : MaxCompForest.fnEnergy G f ≤ R ^ 2,
      ∫⁻ ξ, ∫⁻ g, ENNReal.ofReal (dNormSq (MaxCompForest.deg G) (g - f)) ∂(κ.1 (f + ξ)) ∂ noise G σ

end MaxCompForest.Supplement


