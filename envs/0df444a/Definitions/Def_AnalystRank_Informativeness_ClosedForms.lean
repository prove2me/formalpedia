-- Prove2me | Definitions.Def_AnalystRank_Informativeness_ClosedForms
-- name    : AnalystRank_Informativeness_ClosedForms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T09:15:09.078223+00:00
-- url     : https://prove2.me/theorems/182ca4fa-1503-4249-b3ef-879a4372c83c
-- title:
--   Appendix B thresholds and strategies: ρ̄, φ̄, q̌max, σ̌ˡ₀, σ̌ˡ, σ̌ʰ, σ̇ʰ, σ̇ˡ, Ψ of (A.7), g_l, g_h of (B.5), σ̈ˡ of (B.6), q̄ of (B.33)
-- statement:
--   This file collects the explicit thresholds and strategies that Appendix B uses to describe the most informative equilibrium of the rank game. Throughout, $\chi=\rho\gamma(1-\gamma)$ and $\varphi=W_1/W_2$.
--
--   1. **Thresholds.** $\bar\rho=1-\dfrac1{2\gamma}$ (B.3); $\bar\varphi=\dfrac{\chi+\gamma(\gamma-\frac12)}{\chi-(1-\gamma)(\gamma-\frac12)}$ (B.4), used only when $\rho>\bar\rho$; $\check q_{\max}=\dfrac{\varphi\gamma}{1-\gamma+\varphi\gamma}$ (B.22).
--   2. **Semi-separating strategies.** Without correlation, (B.21),
--   $$\check\sigma^l_0(q)=1-\frac{\frac{(1-\gamma)\varphi+\gamma}{\varphi-1}(q-\gamma)}{q(1-\gamma)^2+(1-q)\gamma^2},\qquad \check\sigma^h_0(q)=\check\sigma^l_0(1-q).$$
--   With correlation, (B.30) and (B.42),
--   $$\check\sigma^l(q)=1-\frac{\frac{(1-\gamma)\varphi+\gamma}{\varphi-1}(q-\gamma)+\chi}{q(1-\gamma)^2+(1-q)\gamma^2+\chi},\qquad \check\sigma^h(q)=\check\sigma^l(1-q).$$
--   3. **Fully mixed strategy** (B.34). With $A=q(\gamma^2+\chi)+(1-q)((1-\gamma)^2+\chi)$, $B=q((1-\gamma)^2+\chi)+(1-q)(\gamma^2+\chi)$ and $C=\gamma(1-\gamma)-\chi$,
--   $$\dot\sigma^h(q)=\frac{[q\gamma\varphi-(1-q)(1-\gamma)]B-[q(1-\gamma)\varphi-(1-q)\gamma]C}{(\varphi-1)(AB-C^2)},$$
--   $$\dot\sigma^l(q)=1-\frac{[q(1-\gamma)\varphi-(1-q)\gamma]A-[q\gamma\varphi-(1-q)(1-\gamma)]C}{(\varphi-1)(AB-C^2)}.$$
--   4. **The ratios Ψ** (A.7). For a signal $s$ and a state $\omega$, $\Delta U^{\omega s}$ is the expected gain, conditional on the signal $s$ and on the state $\omega$, from forecasting $\omega$ rather than the other forecast, against the opponent's $\sigma$ and under the rank payoff. Then $\Psi^h=\Delta U^{Lh}/\Delta U^{Hh}$ and $\Psi^l=\Delta U^{Ll}/\Delta U^{Hl}$.
--   5. **The functions $g$** (B.5): $g_l=\dfrac{\gamma}{1-\gamma}\Psi^l$ and $g_h=\dfrac{1-\gamma}{\gamma}\Psi^h$.
--   6. **The root $\ddot\sigma^l$** (B.6) is the supremum of the $\sigma^l\in[0,1]$ with $g_h(1,\sigma^l)\le g_l(1,\sigma^l)$. Claim 3 (B.2) shows this set is $[0,\ddot\sigma^l]$ and that $g_l(1,\ddot\sigma^l)=g_h(1,\ddot\sigma^l)$.
--   7. **The threshold $\bar q$** (B.33): $\bar q=\dfrac{g_l(1,\ddot\sigma^l)}{1+g_l(1,\ddot\sigma^l)}$.
--
--   These quantities appear only in the milestone statements; the goal theorem uses none of them.
--
--   **Formalization Note** The conditional law of the other signal given the own signal and the state is $\Pr(s_j\mid s,\omega)=\Pr(s,s_j\mid\omega)/\Pr(s\mid\omega)$, from the joint law of the model file. The paper defines $\ddot\sigma^l$ only implicitly and never defines $\ddot\sigma^h$; it is taken equal to $\ddot\sigma^l$ by the $h\leftrightarrow l$, $q\leftrightarrow 1-q$ symmetry. If the defining set were empty, `sSup ∅ = 0` would apply; Claim 3 (B.2) rules this out in the regime where $\ddot\sigma^l$ is used. $\bar\varphi$ is a plain quotient and is meaningful only for $\rho>\bar\rho$, where its denominator is positive. A zero denominator in $\check\sigma$ or $\dot\sigma$ (only at $\varphi=1$) gives Lean's value $0$, and no statement uses $\varphi=1$.
-- source:
--   Banerjee, Does Competition Improve Analysts’ Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (13 Nov 2017), pp. 32, 34–35, 42, 44–47, 50, (A.7), (B.3)–(B.6), (B.21)–(B.22), (B.28), (B.30), (B.33), (B.34), (B.42)

import Mathlib
import Definitions.Def_AnalystRank_Informativeness_Model

namespace AnalystRank.Informativeness

open Set

/-! Thresholds and equilibrium strategies of Appendix B (B.3), (B.4), (B.5), (B.6), (B.21)–(B.22),
(B.28), (B.30), (B.33), (B.34), (B.42), and the ratios Ψ of (A.7). -/

/-- Correlation threshold (B.3): `ρ̄ = 1 - 1 / (2γ)`. -/
noncomputable def rhoBar (γ : ℝ) : ℝ := 1 - 1 / (2 * γ)

/-- Convexity threshold (B.4): `φ̄ = (χ + γ(γ - 1/2)) / (χ - (1 - γ)(γ - 1/2))`. Its denominator is
positive exactly when `ρ > ρ̄`; outside that range the value is not used. -/
noncomputable def phiBar (γ ρ : ℝ) : ℝ :=
  (chi γ ρ + γ * (γ - 1 / 2)) / (chi γ ρ - (1 - γ) * (γ - 1 / 2))

/-- Pooling threshold for a convex payoff, (B.22): `q̌_max = φγ / (1 - γ + φγ)`. -/
noncomputable def qmaxCheck (γ φ : ℝ) : ℝ := φ * γ / (1 - γ + φ * γ)

/-- Semi-separating strategy without correlation, (B.21):
`σ̌ˡ₀(q) = 1 - [((1-γ)φ + γ)/(φ - 1)] (q - γ) / [q(1-γ)² + (1-q)γ²]`. -/
noncomputable def sigmaCheckL0 (γ φ q : ℝ) : ℝ :=
  1 - ((1 - γ) * φ + γ) / (φ - 1) * (q - γ) / (q * (1 - γ) ^ 2 + (1 - q) * γ ^ 2)

/-- (B.28): `σ̌ʰ₀(q) = σ̌ˡ₀(1 - q)`. -/
noncomputable def sigmaCheckH0 (γ φ q : ℝ) : ℝ := sigmaCheckL0 γ φ (1 - q)

/-- Semi-separating strategy with correlation, (B.30)/(B.42):
`σ̌ˡ(q) = 1 - ([((1-γ)φ + γ)/(φ - 1)](q - γ) + χ) / ([q(1-γ)² + (1-q)γ²] + χ)`. -/
noncomputable def sigmaCheckL (γ ρ φ q : ℝ) : ℝ :=
  1 - (((1 - γ) * φ + γ) / (φ - 1) * (q - γ) + chi γ ρ) /
    (q * (1 - γ) ^ 2 + (1 - q) * γ ^ 2 + chi γ ρ)

/-- (B.42): `σ̌ʰ(q) = σ̌ˡ(1 - q)`. -/
noncomputable def sigmaCheckH (γ ρ φ q : ℝ) : ℝ := sigmaCheckL γ ρ φ (1 - q)

/-- `A = q(γ² + χ) + (1-q)((1-γ)² + χ)` of (B.34). -/
noncomputable def coefA (γ ρ q : ℝ) : ℝ := q * (γ ^ 2 + chi γ ρ) + (1 - q) * ((1 - γ) ^ 2 + chi γ ρ)

/-- `B = q((1-γ)² + χ) + (1-q)(γ² + χ)` of (B.34). -/
noncomputable def coefB (γ ρ q : ℝ) : ℝ := q * ((1 - γ) ^ 2 + chi γ ρ) + (1 - q) * (γ ^ 2 + chi γ ρ)

/-- `C = γ(1-γ) - χ` of (B.34). -/
noncomputable def coefC (γ ρ : ℝ) : ℝ := γ * (1 - γ) - chi γ ρ

/-- Fully mixed strategy, (B.34a):
`σ̇ʰ(q) = ([qγφ - (1-q)(1-γ)] B - [q(1-γ)φ - (1-q)γ] C) / ((φ - 1)[AB - C²])`. -/
noncomputable def sigmaDotH (γ ρ φ q : ℝ) : ℝ :=
  ((q * γ * φ - (1 - q) * (1 - γ)) * coefB γ ρ q - (q * (1 - γ) * φ - (1 - q) * γ) * coefC γ ρ) /
    ((φ - 1) * (coefA γ ρ q * coefB γ ρ q - coefC γ ρ ^ 2))

/-- Fully mixed strategy, (B.34b):
`σ̇ˡ(q) = 1 - ([q(1-γ)φ - (1-q)γ] A - [qγφ - (1-q)(1-γ)] C) / ((φ - 1)[AB - C²])`. -/
noncomputable def sigmaDotL (γ ρ φ q : ℝ) : ℝ :=
  1 - ((q * (1 - γ) * φ - (1 - q) * γ) * coefA γ ρ q - (q * γ * φ - (1 - q) * (1 - γ)) * coefC γ ρ) /
    ((φ - 1) * (coefA γ ρ q * coefB γ ρ q - coefC γ ρ ^ 2))

/-- Expected payoff `Uᵢ(m | sᵢ = s, ω)` conditional on the own signal *and* the state, against `σ`:
`Σ_{sⱼ} Pr(sⱼ | s, ω) Σ_{mⱼ} Pr(mⱼ | sⱼ) u(m, mⱼ, ω)`, with
`Pr(sⱼ | s, ω) = Pr(s, sⱼ | ω) / Pr(s | ω)` from the joint law (1). -/
noncomputable def condPayState (pay : Bool → Bool → Bool → ℝ) (γ ρ : ℝ) (σ : ℝ × ℝ) (s ω m : Bool) :
    ℝ :=
  ∑ sj : Bool, sigLaw γ ρ ω s sj / (∑ sj' : Bool, sigLaw γ ρ ω s sj') *
    ∑ mj : Bool, fcast σ sj mj * pay m mj ω

/-- State-conditional net payoff `ΔU^{ωs}` of (A.3)–(A.6): the gain, in state `ω` and with signal `s`,
from forecasting the state (`m = ω`) rather than the other forecast. -/
noncomputable def netState (pay : Bool → Bool → Bool → ℝ) (γ ρ : ℝ) (σ : ℝ × ℝ) (s ω : Bool) : ℝ :=
  condPayState pay γ ρ σ s ω ω - condPayState pay γ ρ σ s ω (!ω)

/-- The ratios (A.7) for the rank payoff: `Ψʰ = ΔU^{Lh} / ΔU^{Hh}` (`s = true`) and
`Ψˡ = ΔU^{Ll} / ΔU^{Hl}` (`s = false`). -/
noncomputable def Psi (w1 w0 w2 γ ρ : ℝ) (σ : ℝ × ℝ) (s : Bool) : ℝ :=
  netState (rankPay w1 w0 w2) γ ρ σ s false / netState (rankPay w1 w0 w2) γ ρ σ s true

/-- (B.5a): `g_l(σʰ, σˡ) = (γ / (1 - γ)) Ψˡ(σʰ, σˡ)`. -/
noncomputable def gL (w1 w0 w2 γ ρ : ℝ) (σ : ℝ × ℝ) : ℝ := γ / (1 - γ) * Psi w1 w0 w2 γ ρ σ false

/-- (B.5b): `g_h(σʰ, σˡ) = ((1 - γ) / γ) Ψʰ(σʰ, σˡ)`. -/
noncomputable def gH (w1 w0 w2 γ ρ : ℝ) (σ : ℝ × ℝ) : ℝ := (1 - γ) / γ * Psi w1 w0 w2 γ ρ σ true

/-- `σ̈ˡ` of Claim 3 (B.2) and (B.6), made explicit as the supremum of the `σˡ ∈ [0, 1]` with
`g_h(1, σˡ) ≤ g_l(1, σˡ)` (Claim 3 (B.2) says that this set is `[0, σ̈ˡ]`). The paper never defines
`σ̈ʰ`; by the `h ↔ l`, `q ↔ 1 - q` symmetry it is taken equal to `σ̈ˡ`. -/
noncomputable def sigmaDDotL (w1 w0 w2 γ ρ : ℝ) : ℝ :=
  sSup {x : ℝ | x ∈ Icc (0 : ℝ) 1 ∧ gH w1 w0 w2 γ ρ (1, x) ≤ gL w1 w0 w2 γ ρ (1, x)}

/-- (B.33): `q̄ = g_l(1, σ̈ˡ) / (1 + g_l(1, σ̈ˡ))`. -/
noncomputable def qBar (w1 w0 w2 γ ρ : ℝ) : ℝ :=
  gL w1 w0 w2 γ ρ (1, sigmaDDotL w1 w0 w2 γ ρ) / (1 + gL w1 w0 w2 γ ρ (1, sigmaDDotL w1 w0 w2 γ ρ))

end AnalystRank.Informativeness


