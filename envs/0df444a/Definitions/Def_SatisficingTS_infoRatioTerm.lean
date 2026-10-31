-- Prove2me | Definitions.Def_SatisficingTS_infoRatioTerm
-- name    : SatisficingTS_infoRatioTerm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:24:21.743988+00:00
-- url     : https://prove2.me/theorems/da098d3b-df16-4a54-9e5e-10426945555c
-- title:
--   Single-period information ratio $\Gamma_t$
-- statement:
--   For a benchmark action $\tilde A$ with reward $\tilde R=\mu(\tilde A,\theta)$, the single-period information ratio in period $t$ is
--   $$
--   \Gamma_t=\frac{\bigl(\mathbb E[\tilde R-R_t]\bigr)^2}{I\bigl(\tilde A;(A_t,Y_t)\mid\mathcal H_{t-1}\bigr)},
--   $$
--   the squared expected shortfall relative to the benchmark divided by the information the next observation carries about the benchmark. $I(\cdot;\cdot\mid\mathcal H_{t-1})$ is the conditional mutual information averaged over histories.
--
--   It relates the current performance gap to the amount of information acquired about $\tilde A$.
--
--   **Formalization Note** In $[0,\infty]$, in nats: $x/0=\infty$ for $x>0$ and $0/0=0$. The numerator is written $(\mathbb E[\tilde R]-\mathbb E[R_t])^2$, equal to $(\mathbb E[\tilde R-R_t])^2$ under integrability. The conditional mutual information is the published `ThompsonTutorial.InfoRatio.condMutualInfo`.
-- source:
--   Russo & Van Roy, Satisficing in Time-Sensitive Bandit Learning, arXiv:1803.02855v2, §4.1, p.8 (single period information ratio, R̃ = µ(Ã, θ)); proof of Theorem 1, p.9 (Γt ≡ (E[R̃ − Rt])²/I(Ã; (At, Yt)|Ht−1))

import Mathlib
import Definitions.Def_ThompsonTutorial_InfoRatio_condMutualInfo
import Definitions.Def_SatisficingTS_obs
import Definitions.Def_SatisficingTS_hist
import Definitions.Def_ThompsonTutorial_InfoRatio_meanReward
open MeasureTheory ThompsonTutorial.InfoRatio
open scoped ENNReal

namespace SatisficingTS

/-- **The single-period information ratio `Γ_t`** (Russo & Van Roy, *Satisficing in
Time-Sensitive Bandit Learning*, arXiv:1803.02855v2, §4.1, p.8, and proof of Theorem 1, p.9):
"For a benchmark action Ã we consider the single period information ratio
(E[R̃ − Rt])² / I(Ã; (At, Yt) | Ht−1) where R̃ = µ(Ã, θ)."

`infoRatioTerm P θ W ξ g R ψ Ã t
  = (E[µ(Ã, θ)] − E[R(Y_t)])² / I(Ã; (A_t, Y_t) | H_{t−1})`,
with the conditional mutual information of the published
`ThompsonTutorial.InfoRatio.condMutualInfo` (averaged over histories, as on p.6:
"E[It(X; Z)] = I(X; Z|Ht−1)").

**Formalization Note.** The ratio is taken in `ℝ≥0∞`, in nats: `x / 0 = ⊤` for `x > 0` and
`0 / 0 = 0`. `E[R̃ − R_t]` is written `E[R̃] − E[R_t]` (equal under integrability, which theorems
assume). The history `H_{t−1}` is `hist t` (0-based) and `(A_t, Y_t)` is `obs … t`. -/
noncomputable def infoRatioTerm {Ω Θ 𝒲 Ξ 𝒜 𝒴 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒲]
    [MeasurableSpace 𝒜] [StandardBorelSpace 𝒜] [Nonempty 𝒜]
    [MeasurableSpace 𝒴] [StandardBorelSpace 𝒴] [Nonempty 𝒴]
    (P : Measure Ω) [IsFiniteMeasure P] (θ : Ω → Θ) (W : ℕ → Ω → 𝒲) (ξ : Ω → Ξ)
    (g : 𝒜 → Θ → 𝒲 → 𝒴) (R : 𝒴 → ℝ) (ψ : (t : ℕ) → (Fin t → 𝒜 × 𝒴) → Ξ → 𝒜)
    (Ã : Ω → 𝒜) (t : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((∫ ω, meanReward g R (P.map (W 0)) (Ã ω) (θ ω) ∂P
      - ∫ ω, R (obs ψ g θ W ξ t ω).2 ∂P) ^ 2) /
    ThompsonTutorial.InfoRatio.condMutualInfo P Ã (obs ψ g θ W ξ t) (hist ψ g θ W ξ t)

end SatisficingTS


