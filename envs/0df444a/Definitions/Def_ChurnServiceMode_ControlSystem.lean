-- Prove2me | Definitions.Def_ChurnServiceMode_ControlSystem
-- name    : ChurnServiceMode_ControlSystem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:52:50.494181+00:00
-- url     : https://prove2.me/theorems/ba272e39-98b7-4974-9b5f-13f8cf79ccdf
-- title:
--   Control systems (weak formulation of admissible policies), survival, lifetime $T$, CLV and $V^*$
-- statement:
--   A **control system started at satisfaction $x$** consists of a filtered probability space $(\Omega,\mathcal F,(\mathcal F_t)_{t\ge0},P)$ carrying a standard Brownian motion $B$, a progressively measurable action process $u_t\in\{R,S\}$, and a continuous adapted satisfaction process $H$ such that, almost surely, for all $t\ge0$,
--   $$H_t=x+\int_0^t(\mu_{u_s}-H_s)\,ds+\int_0^t\sigma_{u_s}\,dB_s .$$
--   This is display (3), $dH_t=dY_t-H_t\,dt$, with the reward $dY_t=\mu_{u_t}dt+\sigma_{u_t}dB_t$ of (1); $Y_t=H_t-x+\int_0^tH_s\,ds$.
--
--   For such a system:
--   1. the **survival process** is $S_t=e^{-\int_0^tQ(H_s)\,ds}$ (display (5));
--   2. on the product space $P\otimes U[0,1]$ of footnote 5, with $z$ the uniform coordinate, the **lifetime** is $T=\inf\{t\ge0:S_t=z\}$ (display (6)), with $\inf\emptyset=+\infty$;
--   3. the **customer lifetime value** is $\mathrm{CLV}=\mathbb E\bigl[\int_0^\infty\mu_{u_t}\mathbb 1\{t<T\}\,dt\bigr]\in[0,\infty]$, and the **expected lifetime** is $\mathbb E[T]\in[0,\infty]$;
--   4. the system **follows the feedback policy** $\pi$ if $u_t=\pi(H_t)$ at all times.
--
--   The **optimal CLV** is $V^*(x)=\sup\mathrm{CLV}$, the supremum over all control systems started at $x$ (display (8)).
--
--   **Formalization Note** This is the weak formulation of Definition 1: the competitor class contains every admissible policy, without requiring uniqueness in law. The stochastic integral is the published `HasMartingaleIntegral` with respect to the time clock $t\mapsto t$. The CLV drops the zero-mean stochastic-integral term of (7), as footnote 6 does. Every path of $H$ is continuous. The sample space is in the lowest universe.
-- source:
--   Y. Kanoria, I. Lobel, J. Lu, Managing Customer Churn via Service Mode Control, SSRN 3188226 (version of December 1, 2022), https://ssrn.com/abstract=3188226, §3, pp.5–7: displays (1)–(3), (5)–(8), Definition 1, footnotes 5–6

import Mathlib
import Definitions.Def_PeskirShiryaev_LocalTime_Diffusion
import Definitions.Def_ChurnServiceMode_Params

open MeasureTheory ProbabilityTheory PeskirShiryaev.LocalTime
open scoped NNReal ENNReal

namespace ChurnServiceMode

/-- **A control system started at satisfaction `x`** (Kanoria, Lobel & Lu, SSRN 3188226,
§3, pp.5–6, displays (1)–(3) and Definition 1): a filtered probability space `(Ω, ℱ, P)`
carrying a standard Brownian motion `B`, a progressively measurable action process
`u_t ∈ {R, S}`, and a continuous adapted satisfaction process `H` solving
`dH_t = dY_t − H_t dt` with `dY_t = μ_{u_t} dt + σ_{u_t} dB_t`, i.e.

`H_t = x + ∫₀ᵗ (μ_{u_s} − H_s) ds + ∫₀ᵗ σ_{u_s} dB_s`   for all `t`, almost surely.

The field `M` is the Itô integral `∫₀^· σ_{u_s} dB_s`, characterized by the published
`HasMartingaleIntegral` (brackets against `B` with the time clock `t ↦ t`).

**Formalization Note.** This is the weak formulation (reading R2): the competitor class is every
such system on any filtered probability space, which contains every admissible policy of
Definition 1 (it does not require uniqueness in law, nor the existence of the integrals in (7),
which are automatic for the nonnegative reward rate used in the CLV). Every path of `H` (and of
`B`) is continuous. The reward process `Y` of (1) is recovered as `Y_t = H_t − x + ∫₀ᵗ H_s ds`
(`ControlSystem.reward`). -/
structure ControlSystem (p : Params) (x : ℝ) where
  /-- The sample space. -/
  Ω : Type
  [mΩ : MeasurableSpace Ω]
  /-- The probability measure. -/
  P : Measure Ω
  [isProb : IsProbabilityMeasure P]
  /-- The filtration `𝔽 = (ℱ_t)_{t ≥ 0}`. -/
  ℱ : Filtration ℝ≥0 mΩ
  /-- The standard Brownian motion `B`. -/
  B : ℝ≥0 → Ω → ℝ
  /-- The action process `u_t`. -/
  u : ℝ≥0 → Ω → Mode
  /-- The satisfaction process `H_t`. -/
  H : ℝ≥0 → Ω → ℝ
  /-- The stochastic integral `∫₀ᵗ σ_{u_s} dB_s`. -/
  M : ℝ≥0 → Ω → ℝ
  brownian : FilteredBrownian P ℱ B
  progressive : IsProgressive ℱ u
  adapted : Adapted ℱ H
  continuous : ∀ ω, Continuous (fun t => H t ω)
  noise : HasMartingaleIntegral P ℱ B (timeClock Ω) (fun t ω => p.sig (u t ω)) M
  drift : ClockIntegrable P (timeClock Ω) (fun t ω => p.mu (u t ω) - H t ω)
  dynamics : ∀ᵐ ω ∂P, ∀ t, H t ω =
    x + clockIntegral (timeClock Ω) (fun s w => p.mu (u s w) - H s w) t ω + M t ω

attribute [instance] ControlSystem.mΩ ControlSystem.isProb

namespace ControlSystem

variable {p : Params} {x : ℝ} (S : ControlSystem p x)

/-- The survival probability `S_t = e^{−∫₀ᵗ Q(H_s) ds}` of display (5), p.6. -/
noncomputable def survival (t : ℝ≥0) (ω : S.Ω) : ℝ :=
  Real.exp (-∫ s in (0 : ℝ)..(t : ℝ), p.hazard (S.H s.toNNReal ω))

/-- The reward process `Y_t` of display (1) (`Y₀ = 0`), recovered from (3) as
`Y_t = H_t − x + ∫₀ᵗ H_s ds`. -/
noncomputable def reward (t : ℝ≥0) (ω : S.Ω) : ℝ :=
  S.H t ω - x + ∫ s in (0 : ℝ)..(t : ℝ), S.H s.toNNReal ω

/-- The product probability space of footnote 5 (p.6): `P ⊗ U[0, 1]`, the second coordinate being
the uniform variable `z`. -/
noncomputable def lawZ : Measure (S.Ω × ℝ) :=
  S.P.prod (volume.restrict (Set.Icc (0 : ℝ) 1))

/-- The customer lifetime `T = inf{t ≥ 0 : e^{−∫₀ᵗ Q(H_s) ds} = z}` of display (6), p.6, on the
product space (`ωz = (ω, z)`), with `inf ∅ = +∞`. -/
noncomputable def lifetime (ωz : S.Ω × ℝ) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : S.survival t ωz.1 = ωz.2), (t : ℝ≥0∞)

/-- The customer lifetime value `E[∫₀^∞ μ_{u_t} 1{t < T} dt]` of display (7), p.6, on the product
space of footnote 5.

**Formalization Note.** (Reading R3.) The stochastic-integral term of (7) is dropped, as footnote 6
(p.7) does ("zero expectation since the integrand is bounded"); the value is in `[0, ∞]`, so it
exists for every control system. -/
noncomputable def clv : ℝ≥0∞ :=
  ∫⁻ ωz, (∫⁻ t in Set.Ici (0 : ℝ),
    (if ENNReal.ofReal t < S.lifetime ωz then ENNReal.ofReal (p.mu (S.u t.toNNReal ωz.1)) else 0))
    ∂S.lawZ

/-- The expected customer lifetime `E[T]` in `[0, ∞]`. -/
noncomputable def expectedLifetime : ℝ≥0∞ :=
  ∫⁻ ωz, S.lifetime ωz ∂S.lawZ

/-- The system follows the stationary Markov (feedback) policy `π`: `u_t = π(H_t)` for every
time and sample point. -/
def IsFeedback (π : ℝ → Mode) : Prop :=
  ∀ t ω, S.u t ω = π (S.H t ω)

end ControlSystem

/-- The optimal CLV `V*(x) = sup_{π ∈ Π} V(x, π)` of display (8), p.6, the supremum being over
every control system started at `x` (weak formulation, reading R2). -/
noncomputable def optimalCLV (p : Params) (x : ℝ) : ℝ≥0∞ :=
  ⨆ S : ControlSystem p x, S.clv

end ChurnServiceMode


