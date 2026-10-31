-- Prove2me | Definitions.Def_SatisficingTS_infoRatio
-- name    : SatisficingTS_infoRatio
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:25:22.512624+00:00
-- url     : https://prove2.me/theorems/dd059b80-eadc-4b07-a4e7-bac7fe2f1c70
-- title:
--   Discounted information ratio $\Gamma(\tilde A,\psi)$, display (4)
-- statement:
--   The discounted average of the single-period information ratios of a policy $\psi$ against a benchmark $\tilde A$ is
--   $$
--   \Gamma(\tilde A,\psi)=(1-\alpha^2)\sum_{t=0}^{\infty}\alpha^{2t}\,\frac{\bigl(\mathbb E[\tilde R-R_t]\bigr)^2}{I\bigl(\tilde A;(A_t,Y_t)\mid\mathcal H_{t-1}\bigr)},
--   $$
--   where the actions $A_t$ are chosen by $\psi$. The weights $(1-\alpha^2)\alpha^{2t}$ sum to one for $\alpha\in[0,1)$.
--
--   Theorem 1 bounds the satisficing regret by $\sqrt{\Gamma(\tilde A,\psi)\,I(\tilde A;\theta)/(1-\alpha^2)}$.
--
--   **Formalization Note** Computed in $[0,\infty]$: the series of nonnegative terms always has a value, possibly $\infty$, and $0\cdot\infty=0$.
-- source:
--   Russo & Van Roy, Satisficing in Time-Sensitive Bandit Learning, arXiv:1803.02855v2, §4.1, p.8, display (4)

import Mathlib
import Definitions.Def_SatisficingTS_infoRatioTerm
open MeasureTheory
open scoped ENNReal

namespace SatisficingTS

/-- **The discounted information ratio `Γ(Ã, ψ)`, display (4)** (Russo & Van Roy, *Satisficing in
Time-Sensitive Bandit Learning*, arXiv:1803.02855v2, §4.1, p.8):
`Γ(Ã, ψ) = (1 − α²) ∑_{t=0}^∞ α^{2t} ( (E[R̃ − Rt])² / I(Ã; (At, Yt)|Ht−1) )`,
"where the actions (At)t∈N0 are chosen under ψ".

`infoRatio P θ W ξ g R ψ Ã α = (1 − α²) · ∑'_{t≥0} α^{2t} · Γ_t` with `Γ_t = infoRatioTerm … t`.

**Formalization Note.** Computed in `ℝ≥0∞` (`ENNReal.ofReal` of the real weights): the series of
nonnegative terms always has a value, possibly `⊤`, and `0 · ⊤ = 0`. For `α ∈ [0, 1)` the weights
are those of (4). -/
noncomputable def infoRatio {Ω Θ 𝒲 Ξ 𝒜 𝒴 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒲]
    [MeasurableSpace 𝒜] [StandardBorelSpace 𝒜] [Nonempty 𝒜]
    [MeasurableSpace 𝒴] [StandardBorelSpace 𝒴] [Nonempty 𝒴]
    (P : Measure Ω) [IsFiniteMeasure P] (θ : Ω → Θ) (W : ℕ → Ω → 𝒲) (ξ : Ω → Ξ)
    (g : 𝒜 → Θ → 𝒲 → 𝒴) (R : 𝒴 → ℝ) (ψ : (t : ℕ) → (Fin t → 𝒜 × 𝒴) → Ξ → 𝒜)
    (Ã : Ω → 𝒜) (α : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 - α ^ 2) *
    ∑' t, ENNReal.ofReal (α ^ (2 * t)) * infoRatioTerm P θ W ξ g R ψ Ã t

end SatisficingTS


