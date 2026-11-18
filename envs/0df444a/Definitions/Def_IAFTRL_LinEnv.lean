-- Prove2me | Definitions.Def_IAFTRL_LinEnv
-- name    : IAFTRL_LinEnv
-- status  : Definition
-- author  : @Canzhe Zhao
-- created : 2026-11-17T06:21:36.332936+00:00
-- url     : https://prove2.me/theorems/987eff37-134d-4ed9-93ca-91d9b48dc45c
-- title:
--   Oblivious corrupted stochastic linear bandit environments, history law and regret (Section 1.1)
-- statement:
--   This file fixes the protocol objects of the corrupted stochastic regime used by the lower bounds of the source (Section 1.1, pp. 5–6).
--
--   **Setting.** A learner faces a known action set $\mathcal A\subseteq\mathbb R^d$. In round $t$ the environment fixes a loss vector $\theta_t\in\mathbb R^d$ with $\|\theta_t\|_{\mathcal A}=\sup_{a\in\mathcal A}|a^\top\theta_t|\le1$. The learner chooses $A_t\in\mathcal A$ and observes a feedback $Y_t$ with $|Y_t|\le1$ and $\mathbb E[Y_t\mid\mathcal F_{t-1},\theta_t,A_t]=A_t^\top\theta_t$. The regret over $T$ rounds is
--   $$
--   \mathrm{Reg}_T=\sup_{u\in\mathcal A}\mathbb E\Big[\sum_{t=1}^T(A_t-u)^\top\theta_t\Big].
--   $$
--   In the corrupted stochastic regime there is a fixed loss vector $\theta$ with $\|\theta\|_{\mathcal A}\le1$, and $\theta_t=\theta+c_t$ with total corruption $\sum_{t\le T}\|c_t\|_{\mathcal A}\le C$.
--
--   **Objects.**
--   1. $\|z\|_{\mathcal A}$ (`setNorm`) is the supremum of $|a^\top z|$ over $a\in\mathcal A$.
--   2. An *oblivious environment* (`LinEnv`) consists of a loss vector $\theta_t$ for each round and a feedback law $\nu_t(a)$ for each round and action. The corruption is therefore deterministic, and the feedback depends on the past only through the action played.
--   3. `IsCorruptedStoch E 𝒜 θ C T` states that, over the horizon $T$, the environment is a corrupted stochastic environment for $\mathcal A$ with fixed loss vector $\theta$ and budget $C$. That is, $\|\theta\|_{\mathcal A}\le1$, $\|\theta_t\|_{\mathcal A}\le1$, every feedback law $\nu_t(a)$ with $a\in\mathcal A$ is supported in $[-1,1]$ with mean $a^\top\theta_t$, and $\sum_{t<T}\|\theta_t-\theta\|_{\mathcal A}\le C$.
--   4. `histMeasure E π n` is the law $\mathbb P_{E,\pi}^n$ of the history $(A_1,Y_1),\dots,(A_n,Y_n)$ when a (possibly randomized) policy $\pi$, given by Markov kernels from histories to actions, interacts with the environment.
--   5. `regret E 𝒜 π T` is $\mathrm{Reg}_T$ computed under $\mathbb P_{E,\pi}^T$.
--
--   These objects let lower bounds quantify over *every* policy while exhibiting concrete corrupted environments.
--
--   **Formalization Note.** Rounds are 0-based in Lean. Policies are the platform's `BanditAlgorithm.LinearBanditPolicy d`; that a policy plays only actions of $\mathcal A$ is the separate hypothesis `IsSupportedLinearPolicy 𝒜 π`. The source allows adaptive environments. Lower bounds that exhibit oblivious environments are therefore at least as strong as the source's statements.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits: The Interplay of Information Acquisition, Corruption, and Geometry (STOC submission version; arXiv:2611.01299), Section 1.1 Preliminaries, pp. 5–6 (pseudo-regret, Regime of the Environment)

import Mathlib
import Definitions.Def_LinearBanditProtocol

/-!
# Oblivious (corrupted) stochastic linear bandit environments

Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits: The Interplay of Information Acquisition,
Corruption, and Geometry* (STOC submission version), Section 1.1 "Preliminaries", p.5–6.

In round `t` the environment fixes a loss vector `θ_t ∈ ℝ^d`; the learner chooses `A_t ∈ 𝒜` and
observes a feedback `Y_t` with `E[Y_t | F_{t-1}, θ_t, A_t] = A_tᵀθ_t` and `|Y_t| ≤ 1`, and
`‖θ_t‖_𝒜 = sup_{a∈𝒜} |aᵀθ_t| ≤ 1`. The (pseudo-)regret is
`Reg_T = sup_{u ∈ 𝒜} E[∑_{t=1}^T (A_t − u)ᵀθ_t]`. In the corrupted stochastic regime
`θ_t = θ + c_t` with a fixed `θ`, `‖θ‖_𝒜 ≤ 1`, and `∑_{t ≤ T} ‖c_t‖_𝒜 ≤ C`.

* `LinEnv d` is an *oblivious* environment: the loss vectors `θs t` and the feedback law
  `fb t a` of each round `t` (0-based) and action `a` are fixed in advance (deterministic
  corruption, feedback independent of the past given the action).
* `LinEnv.IsCorruptedStoch E 𝒜 θ C T` says that, over the horizon `T`, `E` is a corrupted
  stochastic environment for the action set `𝒜` with fixed loss vector `θ` and corruption
  budget `C`.
* `LinEnv.histMeasure E π n` is the law of the history `(A_1, Y_1), …, (A_n, Y_n)` when the
  policy `π` (a `BanditAlgorithm.LinearBanditPolicy`, i.e. Markov kernels from histories to
  actions, which may randomize) interacts with `E`.
* `LinEnv.regret E 𝒜 π T` is `Reg_T = sup_{u∈𝒜} E[∑_{t<T} (A_t − u)ᵀθ_t]`.
-/

open MeasureTheory ProbabilityTheory Matrix

namespace IAFTRL

/-- The action-set seminorm `‖z‖_𝒜 = sup_{a ∈ 𝒜} |aᵀz|` (Section 1.1). -/
noncomputable def setNorm {d : ℕ} (𝒜 : Set (Fin d → ℝ)) (z : Fin d → ℝ) : ℝ :=
  sSup ((fun a => |a ⬝ᵥ z|) '' 𝒜)

/-- An oblivious linear bandit environment: the actual loss vector `θs t` of round `t`
(0-based) and the feedback law `fb t a` of round `t` when action `a` is played. -/
structure LinEnv (d : ℕ) where
  /-- The actual loss vector `θ_{t+1}` of round `t`. -/
  θs : ℕ → Fin d → ℝ
  /-- The law of the feedback `Y_{t+1}` given the action played in round `t`. -/
  fb : ℕ → Kernel (Fin d → ℝ) ℝ
  /-- Each feedback law is a probability measure. -/
  markov : ∀ t, IsMarkovKernel (fb t)

attribute [instance] LinEnv.markov

/-- `E` is a corrupted stochastic environment over the horizon `T` for the action set `𝒜`, with
fixed loss vector `θ` and corruption budget `C` (Section 1.1): `‖θ‖_𝒜 ≤ 1`; for every round
`t < T`, `‖θ_t‖_𝒜 ≤ 1` and, for every action `a ∈ 𝒜`, the feedback lies in `[-1, 1]` and has mean
`aᵀθ_t`; and the total corruption is `∑_{t<T} ‖θ_t − θ‖_𝒜 ≤ C`. -/
def LinEnv.IsCorruptedStoch {d : ℕ} (E : LinEnv d) (𝒜 : Set (Fin d → ℝ)) (θ : Fin d → ℝ)
    (C : ℝ) (T : ℕ) : Prop :=
  setNorm 𝒜 θ ≤ 1 ∧
    (∀ t < T, setNorm 𝒜 (E.θs t) ≤ 1) ∧
    (∀ t < T, ∀ a ∈ 𝒜, E.fb t a (Set.Icc (-1 : ℝ) 1)ᶜ = 0 ∧ ∫ y, y ∂(E.fb t a) = a ⬝ᵥ E.θs t) ∧
    ∑ t ∈ Finset.range T, setNorm 𝒜 (E.θs t - θ) ≤ C

/-- Appending a round `(a, y)` to a linear bandit history is measurable. -/
lemma measurable_histSnoc {d n : ℕ} :
    Measurable (fun p : (BanditAlgorithm.LinearBanditHistory d n × (Fin d → ℝ)) × ℝ ↦
      Fin.snoc (α := fun _ ↦ (Fin d → ℝ) × ℝ) p.1.1 (p.1.2, p.2)) := by
  rw [measurable_pi_iff]
  intro t
  by_cases ht : (t : ℕ) < n
  · have : (fun p : (BanditAlgorithm.LinearBanditHistory d n × (Fin d → ℝ)) × ℝ ↦
        Fin.snoc (α := fun _ ↦ (Fin d → ℝ) × ℝ) p.1.1 (p.1.2, p.2) t) =
        fun p ↦ p.1.1 (Fin.castLT t ht) := by
      funext p
      simp [Fin.snoc, ht]
    rw [this]
    exact (measurable_pi_apply _).comp (measurable_fst.comp measurable_fst)
  · have : (fun p : (BanditAlgorithm.LinearBanditHistory d n × (Fin d → ℝ)) × ℝ ↦
        Fin.snoc (α := fun _ ↦ (Fin d → ℝ) × ℝ) p.1.1 (p.1.2, p.2) t) =
        fun p ↦ (p.1.2, p.2) := by
      funext p
      simp [Fin.snoc, ht]
    rw [this]
    exact (measurable_snd.comp measurable_fst).prodMk measurable_snd

/-- The law of the history after `n` rounds of the interaction of the policy `π` with the
oblivious environment `E`: round `n + 1` samples `A ~ π.select n (history)` and then
`Y ~ E.fb n A`, and appends `(A, Y)`. -/
noncomputable def LinEnv.histMeasure {d : ℕ} (E : LinEnv d)
    (π : BanditAlgorithm.LinearBanditPolicy d) :
    (n : ℕ) → Measure (BanditAlgorithm.LinearBanditHistory d n)
  | 0 => Measure.dirac (fun t ↦ t.elim0)
  | n + 1 =>
      (((E.histMeasure π n).compProd (π.select n)).compProd
          ((E.fb n).comap Prod.snd measurable_snd)).map
        (fun p ↦ Fin.snoc (α := fun _ ↦ (Fin d → ℝ) × ℝ) p.1.1 (p.1.2, p.2))

instance LinEnv.histMeasure.instIsProbabilityMeasure {d : ℕ} (E : LinEnv d)
    (π : BanditAlgorithm.LinearBanditPolicy d) (n : ℕ) :
    IsProbabilityMeasure (E.histMeasure π n) := by
  induction n with
  | zero => exact Measure.dirac.isProbabilityMeasure
  | succ n ih =>
      rw [LinEnv.histMeasure]
      haveI := ih
      exact Measure.isProbabilityMeasure_map measurable_histSnoc.aemeasurable

/-- The regret `Reg_T = sup_{u ∈ 𝒜} E[∑_{t=1}^T (A_t − u)ᵀθ_t]` of the policy `π` in the
environment `E` over the horizon `T` (Section 1.1; rounds are 0-based in Lean). -/
noncomputable def LinEnv.regret {d : ℕ} (E : LinEnv d) (𝒜 : Set (Fin d → ℝ))
    (π : BanditAlgorithm.LinearBanditPolicy d) (T : ℕ) : ℝ :=
  sSup ((fun u => ∫ h, ∑ t : Fin T, ((h t).1 - u) ⬝ᵥ E.θs t ∂(E.histMeasure π T)) '' 𝒜)

end IAFTRL


