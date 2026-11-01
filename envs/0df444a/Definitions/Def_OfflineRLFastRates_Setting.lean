-- Prove2me | Definitions.Def_OfflineRLFastRates_Setting
-- name    : OfflineRLFastRates_Setting
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:26:51.231167+00:00
-- url     : https://prove2.me/theorems/29dc7cff-8a4f-490a-aaf9-c3fe10c9370e
-- title:
--   Offline RL fast rates: $V^\pi$, $Q^*$, $V^*$, greedy policies, the margin $\Delta$, $x^\alpha$ with $x^\infty$, Condition 1 and the corrected Condition 2
-- statement:
--   Fix a discounted Markov decision process with a measurable state space $\mathcal S$, a finite nonempty action set $\mathcal A$, a transition kernel $P_s(\cdot\mid s,a)$, a reward distribution $P_r(\cdot\mid s,a)$ with mean $r(s,a)$, an initial distribution $\mu$ and a discount factor $\gamma$ (the reused bundle `OffPolicyDRL.CrossFit.MDP` provides $Q^\pi$, $V^\pi(s)$ and the average state occupancy $d^\pi=(1-\gamma)\sum_{t\ge0}\gamma^t\,\mathbb P^\pi(s_t\in\cdot)$). This module defines the objects of Theorem 1 of Hu, Kallus and Uehara.
--
--   1. **Policies.** A Markov policy is a Markov kernel $\pi(a\mid s)$; a deterministic policy is a measurable map $\pi:\mathcal S\to\mathcal A$, identified with the Dirac kernel at $\pi(s)$.
--   2. **Values.** $V^\pi=\mathbb E_{s_0\sim\mu}[V^\pi(s_0)]$, and
--   $$Q^*(s,a)=\sup_\pi Q^\pi(s,a),\qquad V^*(s)=\sup_\pi V^\pi(s),\qquad V^*=\sup_\pi V^\pi,$$
--   the suprema over Markov policies.
--   3. **Greedy policies.** $\pi$ is greedy for $f$ if $\pi(s)\in\arg\max_{a\in\mathcal A}f(s,a)$ for every $s$, with any tie-breaking.
--   4. **Margin.** $\Delta(s)=\max_{a}Q^*(s,a)-\max_{a\notin\arg\max Q^*(s,\cdot)}Q^*(s,a)$ if the argmax is not all of $\mathcal A$, and $\Delta(s)=0$ otherwise.
--   5. **Powers.** For $x\ge0$ and $\alpha\in[0,\infty]$, $x^\alpha$ is the usual power for finite $\alpha$, and $x^\infty$ is $0$ for $x\in[0,1)$, $1$ for $x=1$ and $\infty$ for $x>1$.
--   6. **Condition 1 (Margin).** For a class $\Pi$ of deterministic policies: $\delta_0>0$ and, for all $\delta>0$,
--   $$\sup_{\pi\in\Pi}\mathbb P_{s\sim d^\pi}\big(0<\Delta(s)\le\delta\big)\le(\delta/\delta_0)^\alpha .$$
--   7. **Condition 2, corrected (uniform error bound).** The data is a probability space $(\Omega,\mathbb P_{\mathcal D})$ and $\hat f_\omega$ is the estimate of $Q^*$ from the outcome $\omega$. $C>0$, $a_n>0$, and for every $\delta\ge a_n$ there is an event $E$ with $\mathbb P_{\mathcal D}(E)\le C\exp(-\delta^2/a_n^2)$ such that for every $\omega\notin E$, every $\pi\in\Pi$, $d^\pi$-almost every $s$ and every $a$, $|\hat f_\omega(s,a)-Q^*(s,a)|<\delta$.
--   8. **Peeling events.** For a gap function $g$: $B_0=\{0<g\le2a_n\}$, $B_i=\{2^ia_n<g\le2^{i+1}a_n\}$ for $i\ge1$, and $B'=\{2^{i_{\max}+1}a_n<g\}$; the paper uses $g(s)=Q^*(s,\pi^*(s))-Q^*(s,\hat\pi(s))$.
--
--   These are the vocabulary of every statement of the mission.
--
--   **Formalization Note** The printed Condition 2 bounds $\mathbb P_{\mathcal D}(|\hat f(s,a)-Q^*(s,a)|\ge\delta)$ at each $(s,a)$ separately; with it Theorem 1 is false, because the data-driven policy can steer its occupancy measure to the states where the given dataset erred. The uniform event above is implied by the bound $\mathbb P_{\mathcal D}(\sup_{s,a}|\hat f-Q^*|\ge\delta)\le C\exp(-\delta^2/a_n^2)$ that the paper proves for linear FQI (Theorem 8). The power $x^\alpha$ is a function into $[0,\infty]$ written out by cases, since Lean's real powers have no exponent $\infty$.
-- source:
--   Hu, Kallus, Uehara, Fast Rates for the Regret of Offline Reinforcement Learning, arXiv:2102.00479v2, §1.1, pp.2–3 (MDP, policies, Q^π, V^π, d^π, V*, V*(s), Q*); §1.2, p.4 (Q-greedy policies, any tie-breaking); §2, p.6 (margin Δ, Condition 1 with the x^∞ convention, Condition 2 (corrected)); §7.1, p.16 (events B₀, Bᵢ, B′)

import Mathlib
import Definitions.Def_OffPolicyDRL_CrossFit_MDP

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace OfflineRLFastRates

open OffPolicyDRL.CrossFit

/-- A (stationary, possibly stochastic) policy `π(a | s)`: a Markov kernel from `S` to `A`
(Hu, Kallus, Uehara, Fast Rates for the Regret of Offline Reinforcement Learning,
arXiv:2102.00479v2, §1.1, p.2).

**Formalization Note** These are the policies over which `V*`, `V*(s)` and `Q*` take their
maximum (`max_π` on p.3). -/
abbrev MarkovPolicy (S A : Type*) [MeasurableSpace S] [MeasurableSpace A] :=
  {π : ProbabilityTheory.Kernel S A // IsMarkovKernel π}

/-- A deterministic policy `π : S → A` (arXiv:2102.00479v2, §1.1, p.2, "we also identify maps
`π : S → A` with the deterministic policy given by Dirac at `π(s)`").

**Formalization Note** The map is required to be measurable, so that the Dirac kernel
`s ↦ δ_{π(s)}` is a Markov kernel. -/
abbrev DetPolicy (S A : Type*) [MeasurableSpace S] [MeasurableSpace A] :=
  {π : S → A // Measurable π}

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]

/-- The Dirac kernel `s ↦ δ_{π(s)}` of a deterministic policy (arXiv:2102.00479v2, p.2). -/
noncomputable def DetPolicy.kernel (π : DetPolicy S A) : ProbabilityTheory.Kernel S A :=
  ProbabilityTheory.Kernel.deterministic π.1 π.2

/-- The reward of a policy, `V^π = E^π[∑_t γ^t r_t] = E_{s₀∼µ}[V^π(s₀)]` (arXiv:2102.00479v2,
§1.1, p.3).

**Formalization Note** `V^π(s)` is `M.vFun γ π s` of the reused bundle
`OffPolicyDRL.CrossFit.MDP`: the series `∑_k γ^k E[r(s_k, a_k) | s_0 = s, a_0 = a]` averaged over
`a ∼ π(· | s)`. -/
noncomputable def policyValue (M : MDP S A) (γ : ℝ) (μ : Measure S)
    (π : ProbabilityTheory.Kernel S A) : ℝ :=
  ∫ s, M.vFun γ π s ∂μ

/-- The optimal `Q`-function `Q*(s, a) = max_π Q^π(s, a)` (arXiv:2102.00479v2, §1.1, p.3).

**Formalization Note** The maximum is the supremum over all Markov policies `π(a | s)` of
`Q^π(s, a) = M.qFun γ π (s, a)`. Under a bounded mean reward and `0 < γ < 1` the family is
bounded above, and the supremum is attained by an optimal deterministic policy. -/
noncomputable def QStar (M : MDP S A) (γ : ℝ) (x : S × A) : ℝ :=
  ⨆ π : MarkovPolicy S A, M.qFun γ π.1 x

/-- The optimal `V`-function `V*(s) = max_π V^π(s)` (arXiv:2102.00479v2, §1.1, p.3), as the
supremum over Markov policies. -/
noncomputable def VStarFun (M : MDP S A) (γ : ℝ) (s : S) : ℝ :=
  ⨆ π : MarkovPolicy S A, M.vFun γ π.1 s

/-- The optimal value `V* = max_π V^π` (arXiv:2102.00479v2, §1.1, p.3), as the supremum over
Markov policies. -/
noncomputable def VStar (M : MDP S A) (γ : ℝ) (μ : Measure S) : ℝ :=
  ⨆ π : MarkovPolicy S A, policyValue M γ μ π.1

/-- `π` is greedy for `f`: `π(s) ∈ argmax_{a ∈ A} f(s, a)` for every state `s`
(arXiv:2102.00479v2, §1.2, p.4, the `Q`-greedy policy `π_f`; p.3 for `π*` and `Q*`).

**Formalization Note** No tie-breaking rule is fixed: every selection from the argmax is greedy,
as in "results will hold for any choice of tie breaking" (p.4). -/
def IsGreedy (f : S × A → ℝ) (π : S → A) : Prop :=
  ∀ s a, f (s, a) ≤ f (s, π s)

open scoped Classical in
/-- The margin (arXiv:2102.00479v2, §2, p.6):
`Δ(s) = max_{a ∈ A} Q(s, a) − max_{a ∉ argmax Q(s, ·)} Q(s, a)` if `argmax_a Q(s, a) ≠ A`, and
`Δ(s) = 0` if `argmax_a Q(s, a) = A`. The paper applies it to `Q = Q*`.

**Formalization Note** The actions outside the argmax are those with `Q(s, a)` strictly below the
maximum; the second branch is the case where that set is empty. -/
noncomputable def margin [Fintype A] [Nonempty A] (Q : S × A → ℝ) (s : S) : ℝ :=
  let m := Finset.univ.sup' Finset.univ_nonempty (fun a => Q (s, a))
  let T := Finset.univ.filter (fun a => Q (s, a) < m)
  if h : T.Nonempty then m - T.sup' h (fun a => Q (s, a)) else 0

/-- The power `x^α` for `x ≥ 0` and `α ∈ [0, ∞]`, with the convention of Condition 1
(arXiv:2102.00479v2, §2, p.6): "`x^∞` is understood as `0` for `x ∈ [0, 1)`, `1` for `x = 1`, and
`∞` for `x > 1`".

**Formalization Note** The value is in `ℝ≥0∞`. For finite `α` it is `x^α` (real power). The
exponent `α = ∞` is the explicit three-case rule above; Lean's own powers have no such case. -/
noncomputable def marginPow (α : ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  if α = ⊤ then (if x < 1 then 0 else if x = 1 then 1 else ⊤)
  else ENNReal.ofReal (x ^ α.toReal)

/-- Condition 1 (Margin) (arXiv:2102.00479v2, §2, p.6): for the class `Π` of deterministic
policies, `δ₀ > 0` and, for all `δ > 0`,
`sup_{π ∈ Π} P_{s ∼ d^π}(0 < Δ(s) ≤ δ) ≤ (δ/δ₀)^α`, where `Δ` is the margin of `Q*` and `d^π` is
the average state occupancy distribution `d^π(·) = (1 − γ) ∑_t γ^t P^π(s_t ∈ ·)` with
`s₀ ∼ µ` (p.3).

**Formalization Note** `d^π` is `M.discVisitation γ µ π` of the reused bundle. The supremum
bound is stated for each `π ∈ Π`. The power is `marginPow`, which carries the `x^∞` convention. -/
def MarginCondition [Fintype A] [Nonempty A] (M : MDP S A) (γ : ℝ) (μ : Measure S)
    (Pclass : Set (DetPolicy S A)) (δ₀ : ℝ) (α : ℝ≥0∞) : Prop :=
  0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → ∀ π ∈ Pclass,
    M.discVisitation γ μ π.kernel
        {s | 0 < margin (QStar M γ) s ∧ margin (QStar M γ) s ≤ δ} ≤ marginPow α (δ / δ₀)

/-- Condition 2 (arXiv:2102.00479v2, §2, p.6), **corrected to a uniform error event**: `C > 0`,
`aₙ > 0`, and for every `δ ≥ aₙ` there is an event `E` of the data with
`P_D(E) ≤ C exp(−δ²/aₙ²)` such that, for every outcome `ω ∉ E`, every `π ∈ Π`, `d^π`-almost every
state `s` and every action `a`, `|f̂(s, a) − Q*(s, a)| < δ`.

**Formalization Note** The printed Condition 2 bounds `P_D(|f̂(s, a) − Q*(s, a)| ≥ δ)` at each
`(s, a)` separately; with that condition Theorem 1 is false (the data-driven policy can steer its
occupancy measure towards the states where this dataset erred). The uniform event is implied by
`P_D(sup_{s,a} |f̂ − Q*| ≥ δ) ≤ C exp(−δ²/aₙ²)`, the bound the paper proves for linear FQI
(Theorem 8). The data is an arbitrary probability space `(Ω, P_D)`, and `f̂ ω` is the estimate
computed from the outcome `ω`. -/
def UniformErrorBound {Ω : Type*} [MeasurableSpace Ω] (M : MDP S A) (γ : ℝ) (μ : Measure S)
    (Pclass : Set (DetPolicy S A)) (P_D : Measure Ω) (fhat : Ω → S × A → ℝ) (C aₙ : ℝ) : Prop :=
  0 < C ∧ 0 < aₙ ∧ ∀ δ : ℝ, aₙ ≤ δ → ∃ E : Set Ω,
    P_D E ≤ ENNReal.ofReal (C * Real.exp (-(δ ^ 2 / aₙ ^ 2))) ∧
    ∀ ω ∉ E, ∀ π ∈ Pclass, ∀ᵐ s ∂(M.discVisitation γ μ π.kernel),
      ∀ a, |fhat ω (s, a) - QStar M γ (s, a)| < δ

/-- The gap `Q(s, π*(s)) − Q(s, π(s))` of the action chosen by `π` (arXiv:2102.00479v2, §7.1,
p.16, with `Q = Q*` and `π = π̂`). -/
def gapFun (Q : S × A → ℝ) (πs π : S → A) (s : S) : ℝ :=
  Q (s, πs s) - Q (s, π s)

/-- The peeling events of the proof of Theorem 1 (arXiv:2102.00479v2, §7.1, p.16), for a gap
function `g`: `B₀ = {0 < g ≤ 2aₙ}` and `Bᵢ = {2^i aₙ < g ≤ 2^{i+1} aₙ}` for `i ≥ 1`. -/
def peelEvent (g : S → ℝ) (aₙ : ℝ) (i : ℕ) : Set S :=
  if i = 0 then {s | 0 < g s ∧ g s ≤ 2 * aₙ}
  else {s | 2 ^ i * aₙ < g s ∧ g s ≤ 2 ^ (i + 1) * aₙ}

/-- The last peeling event `B' = {2^{i_max+1} aₙ < g}` (arXiv:2102.00479v2, §7.1, p.16). -/
def peelTail (g : S → ℝ) (aₙ : ℝ) (imax : ℕ) : Set S :=
  {s | 2 ^ (imax + 1) * aₙ < g s}

end OfflineRLFastRates


