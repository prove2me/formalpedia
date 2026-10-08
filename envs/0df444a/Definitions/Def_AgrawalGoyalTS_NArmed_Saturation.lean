-- Prove2me | Definitions.Def_AgrawalGoyalTS_NArmed_Saturation
-- name    : AgrawalGoyalTS_NArmed_Saturation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T17:48:21.807372+00:00
-- url     : https://prove2.me/theorems/535b0c27-351f-41aa-b74e-3e7f70577314
-- title:
--   Saturated arms C(t), events E(t) and M(t), intervals I_j and I_j(ℓ), γ_j and V_j^{ℓ,a} (§4)
-- statement:
--   These are the objects of the $N$-armed analysis (§4, pp. 8–9) for a Thompson Sampling run with horizon $T$. Arm $1$ (Lean arm $0$) is the optimal arm, $\Delta_i=\mu_1-\mu_i$, and $k_i(t)$ is the number of plays of arm $i$ before round $t$.
--
--   1. **Saturation threshold** $L_i=24\ln T/\Delta_i^2$, a real number.
--   2. **Saturated set** $C(t)=\{i\ne 1: k_i(t)\ge L_i\}$.
--   3. **Event $E(t)$:** $\theta_i(t)\in[\mu_i-\Delta_i/2,\ \mu_i+\Delta_i/2]$ for all $i\in C(t)$.
--   4. **Event $M(t)$** (Eq. (2)): $\theta_1(t)>\mu_i+\Delta_i/2$ for every $i\in C(t)$; it holds trivially when $C(t)=\emptyset$.
--   5. **Interval $I_j$:** the rounds strictly between the $j$-th and the $(j+1)$-th plays of arm $1$, with $t_0=0$ (so $I_0$ is the rounds before the first play of arm $1$). If arm $1$ is not played a $(j+1)$-th time within the horizon, $I_j$ runs to round $T$.
--   6. $\gamma_j=|\{t\in I_j: M(t)\}|$ (Eq. (3)).
--   7. **Sub-intervals** $I_j(\ell)$, $\ell=1,\dots,\gamma_j+1$: the occurrences of $M$ cut $I_j$ into pieces; $I_j(1)$ is before the first occurrence, $I_j(\ell)$ between the $(\ell-1)$-th and $\ell$-th occurrences, and $I_j(\gamma_j+1)$ after the last one. The occurrence rounds themselves belong to no sub-interval.
--   8. $V_j^{\ell,a}=|\{t\in I_j(\ell): \mu_a=\max_{i\in C(t)}\mu_i\}|$ (Eq. (4)): the number of rounds of $I_j(\ell)$ at which $a$ is the best saturated arm, ties among best saturated arms being resolved by a fixed ordering of the arms.
--
--   These objects state Lemma 4 and Lemma 5, the two probabilistic ingredients of the proof of Theorem 2.
--
--   **Formalization Note** In Lean, $t\in I_j$ means a round $t<T$ with $k_1(t)=j$ at which arm $1$ is not played; $t\in I_j(\ell)$ means $t\in I_j$, $M(t)$ fails, and exactly $\ell-1$ rounds of $I_j$ before $t$ satisfy $M$. The fixed ordering of arms is the index order: among the saturated arms of largest mean the smallest index is the best saturated arm. The paper leaves open what $I_j$ is when arm $1$ has no $(j+1)$-th play within the horizon; it is taken to run to the horizon, consistent with App. C.5's "or if we reach time $T$".
-- source:
--   Agrawal and Goyal, Analysis of Thompson Sampling for the Multi-armed Bandit Problem, arXiv:1111.1797v3, p. 8 (§4: L_i, C(t), I_j, Eq. (2) M(t), Eq. (3) γ_j, I_j(ℓ)), p. 9 (E(t), Eq. (4) V_j^{ℓ,a})

import Mathlib
import Definitions.Def_StochasticBandit
import Definitions.Def_AgrawalGoyalTS_NArmed_ThompsonSampling

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace AgrawalGoyalTS.NArmed

variable {N : ℕ} [NeZero N]

/-- `L_i = 24 ln T / Δ_i²` (p. 8), a real threshold. -/
noncomputable def satThreshold (ν : StochasticBandit N) (T : ℕ) (i : Fin N) : ℝ :=
  24 * Real.log T / gapTo0 ν i ^ 2

open Classical in
/-- The saturated set `C(t) = {i ≠ 1 : k_i(t) ≥ L_i}` (p. 8): suboptimal arms played at least
`L_i` times before round `t` (arm `0` is the paper's arm 1). -/
noncomputable def saturated (ν : StochasticBandit N) (T : ℕ) (ω : AgrawalGoyalTS.TwoArmed.TSOmega N) (t : ℕ) :
    Finset (Fin N) :=
  Finset.univ.filter (fun i => i ≠ 0 ∧ satThreshold ν T i ≤ (AgrawalGoyalTS.TwoArmed.tsPlays ω t i : ℝ))

/-- The event `E(t)`: `θ_i(t) ∈ [μ_i - Δ_i/2, μ_i + Δ_i/2]` for all `i ∈ C(t)` (p. 9). -/
def eventE (ν : StochasticBandit N) (T : ℕ) (ω : AgrawalGoyalTS.TwoArmed.TSOmega N) (t : ℕ) : Prop :=
  ∀ i ∈ saturated ν T ω t, AgrawalGoyalTS.TwoArmed.tsTheta ω t i ∈
    Set.Icc (banditArmMean ν i - gapTo0 ν i / 2) (banditArmMean ν i + gapTo0 ν i / 2)

/-- The event `M(t)`: `θ_1(t) > μ_i + Δ_i/2` for every saturated arm `i ∈ C(t)` (Eq. (2), p. 8);
it holds trivially when `C(t)` is empty. -/
def eventM (ν : StochasticBandit N) (T : ℕ) (ω : AgrawalGoyalTS.TwoArmed.TSOmega N) (t : ℕ) : Prop :=
  ∀ i ∈ saturated ν T ω t, banditArmMean ν i + gapTo0 ν i / 2 < AgrawalGoyalTS.TwoArmed.tsTheta ω t 0

open Classical in
/-- The interval `I_j` (p. 8): the rounds strictly between the `j`-th and the `(j+1)`-th play of
arm `0` (with `t_0 = 0`, so `I_0` is the rounds before the first play), within the horizon
`T` (rounds `0, …, T-1`). If arm `0` is not played a `(j+1)`-th time before the horizon, `I_j`
runs to the last round. -/
noncomputable def interval (T : ℕ) (ω : AgrawalGoyalTS.TwoArmed.TSOmega N) (j : ℕ) : Finset ℕ :=
  (Finset.range T).filter (fun t => AgrawalGoyalTS.TwoArmed.tsPlays ω t 0 = j ∧ AgrawalGoyalTS.TwoArmed.tsArm ω t ≠ 0)

open Classical in
/-- `γ_j = |{t ∈ I_j : M(t)}|` (Eq. (3), p. 8). -/
noncomputable def gammaCount (ν : StochasticBandit N) (T : ℕ) (ω : AgrawalGoyalTS.TwoArmed.TSOmega N) (j : ℕ) : ℕ :=
  ((interval T ω j).filter (fun t => eventM ν T ω t)).card

open Classical in
/-- The sub-interval `I_j(ℓ)`, `ℓ = 1, …, γ_j + 1` (p. 8): the rounds of `I_j` at which `M(t)`
does not hold and which are preceded, within `I_j`, by exactly `ℓ - 1` occurrences of `M`.
So `I_j(1)` is before the first occurrence, `I_j(ℓ)` lies between the `(ℓ-1)`-th and `ℓ`-th
occurrences and `I_j(γ_j+1)` after the last one; the occurrences themselves are excluded. -/
noncomputable def subinterval (ν : StochasticBandit N) (T : ℕ) (ω : AgrawalGoyalTS.TwoArmed.TSOmega N) (j ℓ : ℕ) :
    Finset ℕ :=
  (interval T ω j).filter (fun t => ¬ eventM ν T ω t ∧
    ((interval T ω j).filter (fun t' => t' < t ∧ eventM ν T ω t')).card + 1 = ℓ)

open Classical in
/-- The best saturated arm at round `t`: the arm of `C(t)` of largest mean, ties resolved by the
fixed ordering of arms (smallest index). Junk value `0` when `C(t)` is empty. -/
noncomputable def bestSaturated (ν : StochasticBandit N) (T : ℕ) (ω : AgrawalGoyalTS.TwoArmed.TSOmega N) (t : ℕ) :
    Fin N :=
  let C := saturated ν T ω t
  if h : (C.filter (fun i => ∀ i' ∈ C, banditArmMean ν i' ≤ banditArmMean ν i)).Nonempty then
    (C.filter (fun i => ∀ i' ∈ C, banditArmMean ν i' ≤ banditArmMean ν i)).min' h
  else 0

open Classical in
/-- `V_j^{ℓ,a} = |{t ∈ I_j(ℓ) : μ_a = max_{i ∈ C(t)} μ_i}|` (Eq. (4), p. 9): the number of rounds
of `I_j(ℓ)` at which `a` is the best saturated arm (ties resolved by the fixed ordering). -/
noncomputable def Vcount (ν : StochasticBandit N) (T : ℕ) (ω : AgrawalGoyalTS.TwoArmed.TSOmega N) (j ℓ : ℕ) (a : Fin N) :
    ℕ :=
  ((subinterval ν T ω j ℓ).filter
    (fun t => a ∈ saturated ν T ω t ∧ bestSaturated ν T ω t = a)).card

end AgrawalGoyalTS.NArmed


