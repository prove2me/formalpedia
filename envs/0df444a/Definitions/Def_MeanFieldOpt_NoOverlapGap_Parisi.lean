-- Prove2me | Definitions.Def_MeanFieldOpt_NoOverlapGap_Parisi
-- name    : MeanFieldOpt_NoOverlapGap_Parisi
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T03:26:52.563471+00:00
-- url     : https://prove2.me/theorems/ef409676-f736-4040-bac3-71d0b1cde9a1
-- title:
--   $\Phi^\gamma$ on $\mathscr L$ by continuity, and the Parisi functional $\mathsf P(\gamma)$ (1.6)
-- statement:
--   Let $\xi$ be a mixture and $\gamma \in \mathscr L$. Equip order parameters with the weighted $L^1$ distance
--
--   $$\|\gamma_1 - \gamma_2\|_{1,\xi''} = \int_0^1 \xi''(t)\, |\gamma_1(t) - \gamma_2(t)|\, dt .$$
--
--   **$\Phi^\gamma$ on $\mathscr L$.** By the Lipschitz estimate $\|\Phi^{\gamma_1} - \Phi^{\gamma_2}\|_\infty \le \|\xi''(\gamma_1 - \gamma_2)\|_1$ for step functions (Proposition 6.1(c)), $\Phi^\gamma$ is defined by continuity: for step functions $\gamma_n \in \mathrm{SF}_+$ with $\gamma_n \to \gamma$ in $L^1_\xi$,
--
--   $$\Phi^\gamma(t,x) = \lim_{n\to\infty} \Phi^{\gamma_n}(t,x).$$
--
--   **Parisi functional.** For $\gamma \in \mathscr L$,
--
--   $$\mathsf P(\gamma) = \Phi^\gamma(0,0) - \frac12 \int_0^1 t\, \xi''(t)\, \gamma(t)\, dt .$$
--
--   On $\mathscr U$ this is the zero-temperature Parisi functional (1.6), whose infimum over $\mathscr U$ is the asymptotic ground-state energy of the mixed $p$-spin model (Auffinger–Chen); the extension to $\mathscr L$ is the paper's extended variational principle.
--
--   **Formalization Note** $\Phi^\gamma(t,x)$ is the limit (`limUnder`) of the Cole–Hopf solutions $\Phi^{d}(t,x)$ along the filter of step-function data $d$ whose $L^1_\xi$ distance to $\gamma$ tends to $0$; this is the limit along every approximating sequence at once. For $\gamma \in \mathscr L$ the limit exists and does not depend on the sequence; outside $\mathscr L$ the value is a junk value that no statement uses. The terminal condition is $|x|$ throughout.
-- source:
--   El Alaoui, Montanari, Sellke, Optimization of Mean-field Spin Glasses, arXiv:2001.00904v1, p. 24 (definition of Φ^γ for γ ∈ L by continuity); p. 7 (the L^1_ξ metric); p. 3, Eq. (1.6)

import Mathlib
import Definitions.Def_MeanFieldOpt_NoOverlapGap_Mixture
import Definitions.Def_MeanFieldOpt_NoOverlapGap_ColeHopf

open MeasureTheory Set Filter Topology

namespace MeanFieldOpt.NoOverlapGap

/-- The weighted `L¹_ξ` distance `‖ξ''(γ₁ − γ₂)‖₁ = ∫_0^1 ξ''(t) |γ₁(t) − γ₂(t)| dt` (p. 7). -/
noncomputable def distL1xi (ξ : Mixture) (γ₁ γ₂ : ℝ → ℝ) : ℝ :=
  ∫ s in Ico (0 : ℝ) 1, ξ.xi'' s * |γ₁ s - γ₂ s|

/-- `Φ^γ` for `γ ∈ ℒ`, defined by continuity (p. 24): the limit of `Φ^{γ_n}(t, x)` along
step functions `γ_n ∈ SF₊` with `γ_n → γ` in `L¹_ξ`. Formally, the limit of `PhiSF ξ d t x`
along the filter of `SF₊` data whose `L¹_ξ` distance to `γ` tends to `0`. -/
noncomputable def PhiL (ξ : Mixture) (γ : ℝ → ℝ) (t x : ℝ) : ℝ :=
  limUnder (Filter.comap (fun d : SFData => distL1xi ξ d.toFun γ) (𝓝 0))
    (fun d : SFData => PhiSF ξ d t x)

/-- The Parisi functional (1.6), p. 3, extended to `ℒ` (Section 6.1):
`P(γ) = Φ^γ(0, 0) − (1/2) ∫_0^1 t ξ''(t) γ(t) dt`, with terminal condition `Φ(1, x) = |x|`. -/
noncomputable def P (ξ : Mixture) (γ : ℝ → ℝ) : ℝ :=
  PhiL ξ γ 0 0 - (1 / 2) * ∫ t in Ico (0 : ℝ) 1, t * ξ.xi'' t * γ t

end MeanFieldOpt.NoOverlapGap


