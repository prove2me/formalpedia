-- Prove2me | Definitions.Def_MasterVisc_MKV_Setting
-- name    : MasterVisc_MKV_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T16:33:00.163625+00:00
-- url     : https://prove2.me/theorems/9bd456e6-a4bd-4555-9b91-baab0af78404
-- title:
--   §2.2, §2.4, §4.1 — path space Ω, 𝒫₂, 𝒲₂ and the pseudometric (2.5), semimartingale representations, 𝒫_L(t, μ), generators
-- statement:
--   This file fixes the canonical setting of Wu and Zhang (§2.2) and the class $\mathcal P_L(t,\mu)$ of §4.1.
--
--   1. **Paths.** $\Omega = C([0,T],\mathbb R^d)$ with the uniform norm $\|\omega\| = \sup_{t\le T}|\omega_t|$ and its Borel $\sigma$-algebra. The canonical process is $X_s(\omega)=\omega_{s\wedge T}$, the stopped path is $\omega_{t\wedge\cdot}$, and $\mathcal F_t=\sigma(X_s: s\le t)$ is the natural filtration.
--   2. **Laws.** $\mathcal P_2$ is the set of probability measures $\mu$ on $\Omega$ with $\mathbb E^\mu[\|X\|^2]<\infty$; $\mu_{[0,t]}$ is the law of $X_{t\wedge\cdot}$ under $\mu$. $\mathcal W_2$ is the 2-Wasserstein distance (2.1) on laws of paths, and on $\Theta=[0,T]\times\mathcal P_2$ the pseudometric (2.5) is
--   $$\mathcal W_2\big((t,\mu),(t',\mu')\big)=\Big(|t-t'|+\mathcal W_2^2\big(\mu_{[0,t]},\mu'_{[0,t']}\big)\Big)^{1/2}.$$
--   A function $V$ on $\Theta$ is in $C^0(\Theta)$ if it is continuous at every point of $\Theta$ for this pseudometric. For $d\times d$ matrices, $|\sigma|^2=\sum_{i,j}\sigma_{ij}^2$ (Frobenius) and $A:B=\sum_{i,j}A_{ij}B_{ij}$.
--   3. **Semimartingale representations (§2.4).** A law $P$ is represented from time $t$ by a filtered probability space $(\tilde\Omega,\tilde{\mathbb F},\tilde{\mathbb P})$ carrying a $d$-dimensional $(\tilde{\mathbb F},\tilde{\mathbb P})$-Brownian motion $\tilde B$ (adapted, with increments after $s$ independent of $\tilde{\mathcal F}_s$), bounded progressively measurable $\tilde b,\tilde\sigma$, and an adapted continuous process $\tilde X$ with $\tilde{\mathbb P}\circ\tilde X^{-1}=P$ and
--   $$\tilde X_s=\tilde X_t+\int_t^s\tilde b_r\,dr+\int_t^s\tilde\sigma_r\,d\tilde B_r,\qquad t\le s\le T,\ \tilde{\mathbb P}\text{-a.s.}$$
--   4. **$\mathcal P_L(t,\mu)$ (§4.1).** For $L>0$, $P\in\mathcal P_L(t,\mu)$ if $P\in\mathcal P_2$, $P_{[0,t]}=\mu_{[0,t]}$, and $P$ has such a representation from $t$ with $|\tilde b|\le L$ and $\tfrac12|\tilde\sigma|^2\le L$. Nothing is required of $X$ on $[0,t]$.
--   5. **Generators.** A generator is a function $G(t,\mu,y,Z,\Gamma)\in\mathbb R$ of $t$, a law $\mu$, $y\in\mathbb R$ and functions $Z:\Omega\to\mathbb R^d$, $\Gamma:\Omega\to\mathbb R^{d\times d}$, as in the master equation (3.1).
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** Time is $\mathbb R_{\ge0}$ and every statement quantifies over $t\le T$; $\Theta$ is not a type. The stochastic integral $\int_t^s\tilde\sigma\,d\tilde B$ is $J(s)-J(t)$ for Itô integrals $J_{ij}=\int_0^\cdot\tilde\sigma_{ij}\,d\tilde B_j$ in the sense of the published `EthierKurtz.HasBrownianItoIntegral`. "$X_{[t,T]}$ is a $P$-semimartingale with drift and diffusion characteristics bounded by $L$" is read as "$P$ has such a representation from $t$", the paper's own §2.4 description. $\mathcal W_2$ is the published `WassersteinDRO.Duality.wassersteinDistance` with $p=2$, converted to a real number (finite on $\mathcal P_2$).
-- source:
--   Wu, Zhang, Viscosity solutions to parabolic master equations and McKean–Vlasov SDEs with closed-loop controls, Ann. Appl. Probab. 30(2) (2020), §2.2, §2.4 and §4.1, pp. 940, 944, 947, 958, (2.1), (2.5), (3.1)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_WassersteinDRO_Duality_wassersteinDistance
import Definitions.Def_MasterVisc_Comparison_Setting
import Definitions.Def_MasterVisc_Ito_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MasterVisc.MKV

open EthierKurtz

variable {d : ℕ} {T : ℝ≥0}

instance instBorelSpacePath : BorelSpace (MasterVisc.Comparison.Path d T) := ⟨rfl⟩

/-- The 2-Wasserstein distance (2.1) on laws of paths, as a real number (finite on `𝒫₂`). -/
noncomputable def W2 (μ ν : Measure (MasterVisc.Comparison.Path d T)) : ℝ :=
  (WassersteinDRO.Duality.wassersteinDistance 2 μ ν).toReal

/-- `V ∈ C⁰(Θ)`: continuity at every point of `Θ` for the pseudometric `𝒲₂` of (2.5). -/
def IsC0Θ (V : ℝ≥0 → Measure (MasterVisc.Comparison.Path d T) → ℝ) : Prop :=
  ∀ t μ, t ≤ T → MasterVisc.Comparison.IsP2 μ → ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ t' μ', t' ≤ T → MasterVisc.Comparison.IsP2 μ' →
    MasterVisc.Comparison.W2Θ t μ t' μ' < δ → |V t' μ' - V t μ| < ε

/-- A representation `(Ω̃, F̃, ℙ̃, B̃, b̃, σ̃, X̃)` of a law of paths as a semimartingale
(§2.4, p. 944): a filtered probability space carrying a `d`-dimensional Brownian motion `B`,
drift and diffusion processes `b`, `σ`, and a path-valued random variable `Y` (the process `X̃`). -/
structure Rep (d : ℕ) (T : ℝ≥0) where
  Ω : Type
  [ms : MeasurableSpace Ω]
  P : Measure Ω
  F : Filtration ℝ≥0 ms
  B : ℝ≥0 → Ω → SDEState d
  b : ℝ≥0 → Ω → SDEState d
  σ : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ
  Y : Ω → MasterVisc.Comparison.Path d T

attribute [instance] Rep.ms

/-- `R` represents the law `P` as a semimartingale on `[t, T]`:
`P = ℙ̃ ∘ Y⁻¹`, `B` is an `(F̃, ℙ̃)`-Brownian motion, `b`, `σ` are bounded and progressively
measurable, `Y` is adapted, and `Y_s = Y_t + ∫_t^s b dr + ∫_t^s σ dB` for `s ∈ [t, T]`, a.s.
The stochastic integral `∫_t^s σ dB` is `J(s) − J(t)` for the Itô integrals `J_{ij} = ∫_0^· σ_{ij} dB_j`. -/
def IsRepFrom (t : ℝ≥0) (P : Measure (MasterVisc.Comparison.Path d T)) (R : Rep d T) : Prop :=
  IsProbabilityMeasure R.P ∧
  Measurable R.Y ∧
  R.P.map R.Y = P ∧
  IsStandardBrownian R.P R.B ∧
  (∀ s, Measurable[R.F s] (R.B s)) ∧
  (∀ s, Indep (R.F s)
    (MeasurableSpace.comap (fun ω (r : Set.Ici s) => R.B r.val ω - R.B s ω) inferInstance) R.P) ∧
  IsStronglyProgressive R.F R.b ∧
  (∀ i j, IsStronglyProgressive R.F (fun s ω => R.σ s ω i j)) ∧
  (∃ C : ℝ, ∀ s ω, ‖R.b s ω‖ ≤ C ∧ MasterVisc.Comparison.frob2 (R.σ s ω) ≤ C) ∧
  (∀ s, Measurable[R.F s] (fun ω => MasterVisc.Comparison.evalAt s (R.Y ω))) ∧
  ∃ J : Fin d → Fin d → ℝ≥0 → R.Ω → ℝ,
    (∀ i j, HasBrownianItoIntegral R.P R.F (fun s ω => R.B s ω j)
      (fun s ω => R.σ s ω i j) (J i j)) ∧
    ∀ᵐ ω ∂(R.P), ∀ s, t ≤ s → s ≤ T → ∀ i,
      MasterVisc.Comparison.evalAt s (R.Y ω) i = MasterVisc.Comparison.evalAt t (R.Y ω) i
        + (∫ r in (t : ℝ)..(s : ℝ), R.b r.toNNReal ω i)
        + ∑ j, (J i j s ω - J i j t ω)

/-- Drift and diffusion characteristics bounded by `L`: `|b̃| ≤ L` and `½|σ̃|² ≤ L`. -/
def RepBound (L : ℝ) (R : Rep d T) : Prop :=
  ∀ s ω, ‖R.b s ω‖ ≤ L ∧ MasterVisc.Comparison.frob2 (R.σ s ω) / 2 ≤ L

/-- `P ∈ 𝒫_L(t, μ)` (§4.1, p. 958): `P ∈ 𝒫₂`, `P_{[0,t]} = μ_{[0,t]}`, and `X_{[t,T]}` is a
`P`-semimartingale with drift and diffusion characteristics bounded by `L`. -/
def InPL (L : ℝ) (t : ℝ≥0) (μ P : Measure (MasterVisc.Comparison.Path d T)) : Prop :=
  MasterVisc.Comparison.IsP2 P ∧ MasterVisc.Comparison.restr t P = MasterVisc.Comparison.restr t μ ∧ ∃ R : Rep d T, IsRepFrom t P R ∧ RepBound L R

end MasterVisc.MKV


