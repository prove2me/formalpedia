-- Prove2me | Definitions.Def_MaxCompForest_Supplement_partRisk
-- name    : MaxCompForest_Supplement_partRisk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:12:16.667356+00:00
-- url     : https://prove2.me/theorems/17c57ac3-5b8e-4a95-b503-e7dab1b4ce38
-- title:
--   Best independent block-average risk $R_{\mathrm{part},b}$
-- statement:
--   For a budget $b\ge1$, $R_{\mathrm{part},b}$ is the infimum, over laws $\mu$ supported on partitions of $V$ with at most $b$ blocks and drawn independently of $f$ and $Y$, of the worst-case risk over $H_R=\{f:f^{\top}Lf\le R^2\}$ of the block-average estimator $P_QY$:
--
--   $$R_{\mathrm{part},b}=\inf_{\mu}\ \sup_{f\in H_R}\ \mathbb E_{Q\sim\mu,\ \xi}\,\|P_Q(f+\xi)-f\|_D^2 .$$
--
--   **Formalization Note** Values in $[0,\infty]$. At $b=0$ no law qualifies and the infimum is $+\infty$; every statement has $b\ge1$.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), Appendix K.2, p.62 (PDF p.64)

import Mathlib
import Definitions.Def_EffResSparsify_ResistanceSketch_Graph
import Definitions.Def_MaxCompForest_fnEnergy
import Definitions.Def_MaxCompForest_Supplement_blockRisk
open EffResSparsify.ResistanceSketch
set_option autoImplicit false

namespace MaxCompForest.Supplement

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- **The best independent block-average risk** `R_part,b`: the infimum, over partition laws supported on
partitions with at most `b` blocks (drawn independently of `f` and `Y`), of the worst-case risk of `P_Q Y` on
`H_R = {f : fᵀ L f ≤ R²}`.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), Appendix K.2, p.62.

**Formalization Note.** Values in `ℝ≥0∞`. At `b = 0` no law qualifies and the infimum is `⊤`; every statement has
`b ≥ 1`. -/
noncomputable def partRisk (G : WGraph V E) (σ R : ℝ) (b : ℕ) : ENNReal :=
  ⨅ μ : {μ : PMF (Finpartition (Finset.univ : Finset V)) // ∀ Q ∈ μ.support, Q.parts.card ≤ b},
    ⨆ f : V → ℝ, ⨆ _ : MaxCompForest.fnEnergy G f ≤ R ^ 2, blockRisk G σ μ.1 f

end MaxCompForest.Supplement


