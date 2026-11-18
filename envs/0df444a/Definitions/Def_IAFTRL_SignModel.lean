-- Prove2me | Definitions.Def_IAFTRL_SignModel
-- name    : IAFTRL_SignModel
-- status  : Definition
-- author  : @Canzhe Zhao
-- created : 2026-11-18T04:20:22.909183+00:00
-- url     : https://prove2.me/theorems/daa99bb4-7151-46ac-a205-ea03adf4c190
-- title:
--   Sign feedback, consistency, sharp instances, and the sharpness modulus (lower-bound setting)
-- statement:
--   Objects for the regret lower bounds of Section 3.3 and Section 4.
--
--   **Sign observations.** For $\mu\in[-1,1]$, `signObs μ` is the law $Q_\mu$ of a sign $Y\in\{-1,1\}$ with
--   $$
--   Q_\mu(Y=1)=\frac{1+\mu}{2},\qquad Q_\mu(Y=-1)=\frac{1-\mu}{2},
--   $$
--   so that $\mathbb E[Y]=\mu$ and $|Y|\le1$ (the sign laws of Lemma J.6). For other real inputs the mean is first clamped to $[-1,1]$. `signKernel θ` is the Markov kernel $a\mapsto Q_{a^\top\theta}$.
--
--   **Stochastic sign environment.** `signEnv θ` is the stochastic linear bandit environment with fixed loss vector $\theta$: in every round $\theta_t=\theta$, and the feedback for the action $a$ is a sign with mean $a^\top\theta$. These are the "sign observations of the linear mean" of Proposition H.1.
--
--   **Consistency.** A policy $\pi$ is consistent on a class $\Theta$ of stochastic sign instances on the action set $\mathcal A$ (`IsConsistentOn 𝒜 Θ π`) if for every $\theta\in\Theta$ and every $\alpha>0$,
--   $$
--   \lim_{T\to\infty}\frac{\mathrm{Reg}_{T,\theta}}{T^\alpha}=0 .
--   $$
--
--   **Sharp instances.** `sharpInstances 𝒜` is the set of loss vectors $\theta$ with $\|\theta\|_{\mathcal A}\le1$ that have a unique optimal action $a^*\in\mathcal A$ and are geometrically sharp (Definition 1.1, with generator $\mathcal B=\mathcal A$).
--
--   **Sharpness modulus.** With $\mathcal K=\mathrm{Conv}\,\mathcal B$ and $\|\cdot\|_{\mathcal S}$ the gauge of $\mathcal S=\mathrm{Conv}(\mathcal B\cup(-\mathcal B))$,
--   $$
--   \varsigma=\inf_{a\in\mathcal K\setminus\{a^*\}}\frac{(a-a^*)^\top\theta}{\|a-a^*\|_{\mathcal S}}\qquad(\texttt{sharpModulus}),
--   $$
--   which is (1.3).
--
--   These definitions state Theorem 3.2: the consistency class and the feedback model of its first part, and the sharpness modulus of its second part.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits: The Interplay of Information Acquisition, Corruption, and Geometry (STOC submission version; arXiv:2611.01299), Section 1.1 (pp.5–6), Definition 1.1 (1.3) (p.6), Section 3.3 (p.25), Proposition H.1 (p.193), Lemma J.6

import Mathlib
import Definitions.Def_LinearBanditProtocol
import Definitions.Def_IAFTRL_LinEnv
import Definitions.Def_IAFTRL_GIAFTRL

/-!
# Sign feedback, consistency, and the sharpness modulus (lower-bound setting of Section 3.3)

Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits: The Interplay of Information Acquisition,
Corruption, and Geometry* (STOC submission version), Section 1.1 (pp.5–6), Definition 1.1 (1.3)
(p.6), Section 3.3 (p.25), Proposition H.1 (p.193) and Lemma J.6.

* `signObs μ` is the law of a sign `Y ∈ {−1, 1}` with mean `μ` (clamped to `[−1, 1]`).
* `signEnv θ` is the stochastic linear bandit environment with fixed loss vector `θ` and sign
  feedback: in every round the feedback for the action `a` is a sign with mean `aᵀθ`
  ("sign observations of the linear mean", Proposition H.1).
* `IsConsistentOn 𝒜 Θ π`: the policy `π` is consistent on the class `Θ` of stochastic sign
  instances on `𝒜`, i.e. `Reg_{T,θ} = o(T^α)` for every `θ ∈ Θ` and every `α > 0` (Section 3.3).
* `sharpInstances 𝒜`: the sharp stochastic instances on `𝒜` (Definition 1.1 with generator
  `ℬ = 𝒜`): `‖θ‖_𝒜 ≤ 1`, a unique optimal action `a*`, and geometric sharpness.
* `sharpModulus ℬ θ a*`: the sharpness modulus
  `ς = inf_{a ∈ K∖{a*}} (a − a*)ᵀθ / ‖a − a*‖_S` of (1.3), with `K = Conv ℬ`, `S = Conv(ℬ ∪ −ℬ)`.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

namespace IAFTRL

variable {d : ℕ}

/-- clamp to `[-1, 1]` -/
noncomputable def clampOne (x : ℝ) : ℝ := max (-1 : ℝ) (min (1 : ℝ) x)

lemma clampOne_continuous : Continuous clampOne := by
  unfold clampOne; fun_prop

lemma clampOne_mem (x : ℝ) : -1 ≤ clampOne x ∧ clampOne x ≤ 1 := by
  unfold clampOne
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

/-- **Sign observation law.** The law of a sign `Y ∈ {−1, 1}` with mean `μ ∈ [−1, 1]`:
`P(Y = 1) = (1 + μ)/2`, `P(Y = −1) = (1 − μ)/2` (Lemma J.6). The mean is clamped to `[−1, 1]`
so that the law is a probability measure for every real input. -/
noncomputable def signObs (μ : ℝ) : Measure ℝ :=
  ENNReal.ofReal ((1 + clampOne μ) / 2) • Measure.dirac 1 +
    ENNReal.ofReal ((1 - clampOne μ) / 2) • Measure.dirac (-1)

lemma signObs_apply (μ : ℝ) (s : Set ℝ) (hs : MeasurableSet s) :
    signObs μ s = ENNReal.ofReal ((1 + clampOne μ) / 2) * s.indicator 1 1 +
      ENNReal.ofReal ((1 - clampOne μ) / 2) * s.indicator 1 (-1) := by
  unfold signObs
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, Measure.dirac_apply' _ hs,
    Measure.dirac_apply' _ hs]
  rfl

/-- The sign-feedback kernel `a ↦ signObs (aᵀθ)`. -/
noncomputable def signKernel (θ : Fin d → ℝ) : Kernel (Fin d → ℝ) ℝ where
  toFun a := signObs (a ⬝ᵥ θ)
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    have hc : Continuous fun a : Fin d → ℝ => clampOne (a ⬝ᵥ θ) :=
      clampOne_continuous.comp (continuous_id.dotProduct continuous_const)
    have e : (fun a : Fin d → ℝ => signObs (a ⬝ᵥ θ) s) = fun a =>
        ENNReal.ofReal ((1 + clampOne (a ⬝ᵥ θ)) / 2) * s.indicator 1 1 +
          ENNReal.ofReal ((1 - clampOne (a ⬝ᵥ θ)) / 2) * s.indicator 1 (-1) := by
      funext a; exact signObs_apply _ _ hs
    rw [e]
    refine Measurable.add ?_ ?_
    · exact (ENNReal.measurable_ofReal.comp
        ((continuous_const.add hc).div_const _).measurable).mul_const _
    · exact (ENNReal.measurable_ofReal.comp
        ((continuous_const.sub hc).div_const _).measurable).mul_const _

instance signKernel.instIsMarkovKernel (θ : Fin d → ℝ) : IsMarkovKernel (signKernel θ) :=
  ⟨fun a => ⟨by
    show signObs (a ⬝ᵥ θ) Set.univ = 1
    rw [signObs_apply _ _ MeasurableSet.univ]
    simp only [Set.indicator_univ, Pi.one_apply, mul_one]
    obtain ⟨h1, h2⟩ := clampOne_mem (a ⬝ᵥ θ)
    rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
    have e : (1 + clampOne (a ⬝ᵥ θ)) / 2 + (1 - clampOne (a ⬝ᵥ θ)) / 2 = 1 := by ring
    rw [e, ENNReal.ofReal_one]⟩⟩

/-- **The stochastic sign-feedback environment** with fixed loss vector `θ` (Proposition H.1):
`θ_t = θ` in every round, and the feedback for the action `a` is a sign with mean `aᵀθ`. -/
noncomputable def signEnv (θ : Fin d → ℝ) : LinEnv d where
  θs _ := θ
  fb _ := signKernel θ
  markov _ := inferInstance

/-- **Consistency** (Section 3.3, following [LS17]): the policy `π` is consistent on the class `Θ`
of stochastic sign instances on the action set `𝒜` if `Reg_{T,θ} = o(T^α)` for every `θ ∈ Θ` and
every `α > 0`. -/
def IsConsistentOn (𝒜 : Set (Fin d → ℝ)) (Θ : Set (Fin d → ℝ))
    (π : BanditAlgorithm.LinearBanditPolicy d) : Prop :=
  ∀ θ ∈ Θ, ∀ α : ℝ, 0 < α →
    Tendsto (fun T : ℕ => (signEnv θ).regret 𝒜 π T / (T : ℝ) ^ α) atTop (𝓝 0)

/-- **The sharp stochastic instances on `𝒜`** (Definition 1.1, generator `ℬ = 𝒜`): loss vectors
`θ` with `‖θ‖_𝒜 ≤ 1` that have a unique optimal action `a* ∈ 𝒜` and are geometrically sharp. -/
def sharpInstances (𝒜 : Set (Fin d → ℝ)) : Set (Fin d → ℝ) :=
  {θ | setNorm 𝒜 θ ≤ 1 ∧ ∃ astar ∈ 𝒜, (∀ a ∈ 𝒜, a ≠ astar → astar ⬝ᵥ θ < a ⬝ᵥ θ) ∧
    IsSharp 𝒜 θ astar}

/-- **The sharpness modulus** (1.3): `ς = inf_{a ∈ K∖{a*}} (a − a*)ᵀθ / ‖a − a*‖_S`, with
`K = Conv ℬ` and `‖·‖_S` the gauge of `S = Conv(ℬ ∪ −ℬ)`. -/
noncomputable def sharpModulus (ℬ : Set (Fin d → ℝ)) (θ astar : Fin d → ℝ) : ℝ :=
  sInf ((fun a => ((a - astar) ⬝ᵥ θ) / sNorm ℬ (a - astar)) '' (Kset ℬ \ {astar}))

end IAFTRL


