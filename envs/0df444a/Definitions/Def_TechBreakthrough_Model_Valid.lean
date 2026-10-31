-- Prove2me | Definitions.Def_TechBreakthrough_Model_Valid
-- name    : TechBreakthrough_Model_Valid
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:35:53.618322+00:00
-- url     : https://prove2.me/theorems/84954003-8167-4115-b1f3-188c6805b1b4
-- title:
--   The standing assumptions, A1–A8, and the threshold $x_R$
-- statement:
--   A model is valid when $r>0$, the diffusion of §4.1 holds, and:
--
--   * $R\in C^2(\mathcal I)$ with: **A1** $\mathbf E_x[\sup_{t\ge0}e^{-rt}|R(X_t)|]<\infty$; **A2** $e^{-rt}R(X_t)\to0$ $P_x$-a.s.; **A3** there is $x_0\in\mathcal I$ with $\mathcal LR-rR>0$ on $(\alpha,x_0)$ and $\mathcal LR-rR<0$ on $(x_0,\beta)$.
--   * $G\in C^1(\mathcal I)$ is piecewise $C^2$ with: **A4** $\mathbf E_x[\sup_{t\ge0}e^{-rt}G(X_t)]<\infty$; **A5** $e^{-rt}G(X_t)\to0$ $P_x$-a.s.; **A6** $G>V_R$ on $\mathcal I$; **A7** $\mathcal LG-rG\le0$ everywhere $G''$ is defined.
--   * **A8** $Q$ has a locally Lipschitz density $f>0$ on $\mathcal I$.
--
--   A number $x_R\in\mathcal I$ is a **threshold** when $\{x\in\mathcal I:V_R(x)=R(x)\}=[x_R,\beta)$.
--
--   **Formalization Note** "Piecewise $C^2$", undefined in the paper, reads: $C^2$ off a subset of $\mathcal I$ with no accumulation point in $\mathcal I$. A1 and A4 use lower Lebesgue integrals. The threshold is a predicate and not a chosen number, because the paper's sentence that A3 guarantees it is false without $R>0$ somewhere (`lemma_1`).
-- source:
--   Décamps, Gensbittel & Mariotti, Investment Timing and Technological Breakthroughs, arXiv:2106.05112v1, r > 0, p.4; A1–A8, pp.11–12; x_R, p.11

import Definitions.Def_TechBreakthrough_Model_V
import Definitions.Def_TechBreakthrough_IsDiffusionFamily

open MeasureTheory Filter
open scoped NNReal Topology ENNReal

namespace TechBreakthrough

namespace Model

variable (M : Model)

/-- The standing assumptions of arXiv:2106.05112v1, §4, pp.4, 9–12: `r > 0`, the diffusion of
§4.1, `R ∈ C²(𝓘)` with A1–A3, `G ∈ C¹(𝓘)` piecewise `C²` with A4–A7, and A8 for the law of `Y`.

**Formalization Note**
* A1 and A4 are stated with lower Lebesgue integrals, so that "`< ∞`" is meaningful; in A4,
  `ENNReal.ofReal` changes nothing because A6 forces `G > 0` on `𝓘`.
* "Piecewise `C²`" (undefined in the paper) is read as `C²` off a subset of `𝓘` with no
  accumulation point in `𝓘`, with no condition on one-sided limits of `G″`; this is the weakest
  natural reading.
* A7 is imposed at each point where `G″ = (G′)′` exists.
* A8 and the fact that `Q` has total mass one are stated on the density `f`. -/
structure Valid : Prop where
  r_pos : 0 < M.r
  diffusion : IsDiffusionFamily M.α M.β M.μ M.σ M.P
  R_contDiffOn : ContDiffOn ℝ 2 M.R M.I
  A1 : ∀ x ∈ M.I, ∫⁻ ω, ⨆ t : ℝ≥0, ENNReal.ofReal (Real.exp (-M.r * t) * |M.R (M.X t ω)|) ∂M.P x < ⊤
  A2 : ∀ x ∈ M.I, ∀ᵐ ω ∂M.P x,
    Tendsto (fun t : ℝ≥0 => Real.exp (-M.r * t) * M.R (M.X t ω)) atTop (𝓝 0)
  A3 : ∃ x₀ ∈ M.I, (∀ x ∈ M.I, x < x₀ → 0 < M.gen M.R x - M.r * M.R x) ∧
    (∀ x ∈ M.I, x₀ < x → M.gen M.R x - M.r * M.R x < 0)
  G_contDiffOn : ContDiffOn ℝ 1 M.G M.I
  G_piecewise : ∃ B ⊆ M.I, (∀ x ∈ M.I, ¬ AccPt x (𝓟 B)) ∧ ContDiffOn ℝ 2 M.G (M.I \ B)
  A4 : ∀ x ∈ M.I, ∫⁻ ω, ⨆ t : ℝ≥0, ENNReal.ofReal (Real.exp (-M.r * t) * M.G (M.X t ω)) ∂M.P x < ⊤
  A5 : ∀ x ∈ M.I, ∀ᵐ ω ∂M.P x,
    Tendsto (fun t : ℝ≥0 => Real.exp (-M.r * t) * M.G (M.X t ω)) atTop (𝓝 0)
  A6 : ∀ x ∈ M.I, M.VR x < M.G x
  A7 : ∀ x ∈ M.I, DifferentiableAt ℝ (deriv M.G) x → M.gen M.G x - M.r * M.G x ≤ 0
  f_lipschitz : LocallyLipschitzOn M.I M.f
  f_pos : ∀ x ∈ M.I, 0 < M.f x
  f_integrable : IntegrableOn M.f M.I
  f_mass : ∫ y in M.I, M.f y = 1

/-- `x_R` is the threshold of the stand-alone problem: the optimal stopping region
`{x ∈ 𝓘 : V_R(x) = R(x)}` is `[x_R, β)`, arXiv:2106.05112v1, p.11. -/
def IsThreshold (xR : ℝ) : Prop := xR ∈ M.I ∧ ∀ x ∈ M.I, M.VR x = M.R x ↔ xR ≤ x

end Model

end TechBreakthrough


