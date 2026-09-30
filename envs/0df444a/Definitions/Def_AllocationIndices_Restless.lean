-- Prove2me | Definitions.Def_AllocationIndices_Restless
-- name    : AllocationIndices_Restless
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-24T02:58:58.889375+00:00
-- url     : https://prove2.me/theorems/9d978071-04ad-462b-ba88-a8416c789bc7
-- title:
--   Chapter 6: restless bandits, average reward with a passive subsidy, the passive set E₀(W), indexability and the Whittle index; the spinning plates and vigour models, ϕ, ψ, R, W* and W**
-- statement:
--   The objects of Chapter 6, restless bandits and Whittle indices, in discrete time.
--
--   **Restless bandits and the subsidy problem (§6.2–6.3).** A `RestlessBandit S` is a `DecisionProcess S Bool` of Mission III: two actions, `true` (active, $u = 1$) and `false` (passive, $u = 0$), each with its own Markov kernel and reward. Under a deterministic stationary Markov policy $g : S \to \{0, 1\}$ with a **passive subsidy** $W$, the reward in state $x$ is $r(x, g(x)) + W(1 - g(x))$ (`subsidizedReward`), the chain has kernel $x \mapsto P(\cdot \mid x, g(x))$ (`stationaryKernel`), and the **average reward** from $x$ is
--   $$\limsup_{T \to \infty} \frac{1}{T}\sum_{t < T} \mathbb{E}\big[r(x(t), g(x(t))) + W(1 - g(x(t))) \mid x(0) = x\big] \quad (\texttt{avgReward}),$$
--   a limit on a finite state space. The **optimal average reward** $g(W)$ (`optimalAvg`) is the supremum over deterministic stationary Markov policies and initial states; a policy is **average-optimal** (`IsAvgOptimal`) if it attains $g(W)$ from every initial state (the reading of "attains the maximum in the DP equation (6.6) at every state"). The **passive set** $E_0(W)$ (`passiveSet`) is the set of states in which some average-optimal policy takes the passive action; the bandit is **indexable** (`Indexable`) if $W \le W'$ implies $E_0(W) \subseteq E_0(W')$; and the **Whittle index** is $W(x) = \inf\{W : x \in E_0(W)\}$ (`whittleIndex`, a real infimum).
--
--   **Bi-directional models on `Fin k` (§6.5).** `driftKernel p f` moves from $x$ to $f(x)$ with probability $p(x)$ and otherwise stays (the uniformized transition of a rate-$p$ move; Markov for $p \in [0, 1]$). States $1, \dots, k$ of the book are `0, …, k−1`; thresholds $1, \dots, k+1$ are `0, …, k`.
--
--   *Spinning plates* (`spinningPlates lam mu r`): active moves up (`upState`, clamped at the top) with probability $\lambda(x)$, passive moves down (`downState`, clamped at the bottom) with probability $\mu(x)$, both earn $r(x)$. The monotone policy $(y)$ (`plateThreshold y`) is passive exactly in the states $x \ge y$; $\phi(y) = \lambda(y-1)/(\lambda(y-1) + \mu(y))$ for $0 < y < k$ with $\phi(0) = 1$, $\phi(k) = 0$ (`plateShare`, the book's conventions $\lambda(0) > 0 = \mu(1)$, $\lambda(k) = 0 < \mu(k+1)$); $R(y) = r(y)\phi(y) + r(y-1)(1 - \phi(y))$ (`plateReturn`, with $r$ extended by $0$ where its coefficient vanishes); `plateEnvelope W` $= \max_{0 \le y \le k}[W\phi(y) + R(y)]$ (6.10); and $W^*(x) = (R(x+1) - R(x))/(\phi(x) - \phi(x+1))$ (`plateIndex`, (6.11)).
--
--   *Vigour bandit* (`vigourBandit nu rho r`, Example 6.1 in the form of p. 158): active moves down with probability $\nu(x)$ and earns $r(x)$, passive moves up with probability $\rho(x)$ and earns nothing. The monotone policy (`vigourThreshold y`) is active exactly in the states $x \ge y$; $\psi(y) = \nu(y)/(\nu(y) + \rho(y-1))$ for $0 < y < k$ with $\psi(0) = 0$, $\psi(k) = 1$ (`vigourShare`); `vigourValue W y` $= W\psi(y) + r(y)(1 - \psi(y))$; and $W^{**}(x) = (r(x)(1 - \psi(x)) - r(x+1)(1 - \psi(x+1)))/(\psi(x+1) - \psi(x))$ (`vigourIndex`).
--
--   **Conventions.** Times are $0, 1, 2, \dots$; rates are uniformized so that every rate is at most $1$ (the book takes the maximal rate equal to $1$); the model assumptions $\lambda(k) = \mu(1) = 0$ and $\nu(1) = \rho(k) = 0$ are hypotheses of the theorems.
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, Chapter 6: §6.2 restless bandits (p. 150), §6.3 the subsidy problem (6.6), E_0, indexability and the Whittle index (pp. 153-154), §6.5 the spinning plates model, monotone policies (6.8), ϕ, R (6.9)-(6.10) and W* (6.11) (pp. 156-157), the vigour bandit, ψ and W** (pp. 158-159)

import Definitions.Def_AllocationIndices_Achievable

/-!
# Multi-armed Bandit Allocation Indices, Chapter 6: restless bandits and Lagrangian relaxation

Gittins, Glazebrook and Weber, *Multi-armed Bandit Allocation Indices*, 2nd ed., Wiley 2011,
Chapter 6 (pp. 149–172).

**Restless bandits (§6.2–6.3).** A restless bandit is a Markov decision process with two actions,
the *active* action `u = 1` and the *passive* action `u = 0`, under which the state evolves by
different laws; in discrete time every time `0, 1, …` is a decision time. Whittle's Lagrangian
relaxation replaces the constraint that `m` of `n` bandits be active by a *subsidy* `W` paid
whenever the passive action is taken, and asks, for a single bandit, for the policy maximizing
the long-run average of `r(x, u) + W(1 − u)` (the DP equation (6.6), p. 153). `E₀(W)` is the set of
states in which the passive action is optimal; the bandit is **indexable** if `E₀(W)` increases
with `W`, and its **Whittle index** is `W(x) = inf{W : x ∈ E₀(W)}` (p. 154).

Following the book's discussion of (6.6), which restricts attention to deterministic stationary
Markov policies and (for a finite state space) equates their best average reward with the value
`g` of the DP equation, the optimal average reward `g(W)` is here the supremum over
deterministic stationary Markov policies and initial states, and a policy is optimal if it
attains `g(W)` from every initial state (which is what attaining the maximum in (6.6) at every
state means). The chapter's models have finite state spaces; the definitions are stated for any
countable state space with a `Fintype` instance where the supremum is taken.

**The spinning plates model (§6.5, p. 156).** An asset moves on `E = {1, …, k}`; under the active
action it moves from `x` to `x + 1` at rate `λ(x)`, under the passive action from `x` to `x − 1` at
rate `μ(x)`, with `λ(k) = μ(1) = 0`, and earns `r(x)` under both actions, `r` increasing.
Uniformized so that all rates are at most `1`, this is the discrete-time restless bandit whose
active kernel moves up with probability `λ(x)` and otherwise stays, and whose passive kernel
moves down with probability `μ(x)` and otherwise stays. The monotone policy `(y)` is passive
exactly in the states `x ≥ y`; its average reward from any initial state is `Wϕ(y) + R(y)` with
`ϕ(y) = λ(y−1)/(λ(y−1) + μ(y))` and `R(y) = r(y)ϕ(y) + r(y−1)(1 − ϕ(y))` (6.10), and
`W*(x) = (R(x+1) − R(x))/(ϕ(x) − ϕ(x+1))` (6.11) is the candidate index. The states are encoded
as `Fin k` (state `x` of the book is `x − 1` here), thresholds `y` of the book's `1, …, k + 1` as
`0, …, k`.

**The vigour model (Example 6.1 in the form of p. 158).** Under the active action the bandit
moves from `x` to `x − 1` at rate `ν(x)` and earns `r(x)`; under the passive action it moves to
`x + 1` at rate `ρ(x)` and earns nothing; `ν(1) = ρ(k) = 0`. The monotone policy is active
exactly in the states `x ≥ y`, with average reward `Wψ(y) + r(y)(1 − ψ(y))`,
`ψ(y) = ν(y)/(ν(y) + ρ(y−1))`, and candidate index
`W**(x) = (r(x)(1−ψ(x)) − r(x+1)(1−ψ(x+1)))/(ψ(x+1) − ψ(x))`.
-/

open MeasureTheory ProbabilityTheory BanditAlgorithm Finset Filter

namespace AllocationIndices

/-! ### Average reward with a passive subsidy, indexability and the Whittle index -/

section Restless

variable {S : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

/-- A **restless bandit** (§6.2): a decision process with the two actions `true` (active,
`u = 1`) and `false` (passive, `u = 0`); the models of this chapter have both actions available
in every state. -/
abbrev RestlessBandit (S : Type*) [MeasurableSpace S] := DecisionProcess S Bool

/-- The reward `r(x, u) + W(1 − u)` earned under the deterministic stationary Markov policy `g`
in state `x` when the passive action carries the subsidy `W` (the DP equation (6.6), p. 153). -/
def subsidizedReward (D : RestlessBandit S) (W : ℝ) (g : S → Bool) (x : S) : ℝ :=
  D.reward x (g x) + if g x then 0 else W

/-- `E[r(x(t), g(x(t))) + W(1 − g(x(t))) | x(0) = x]`, the expected subsidized reward at time `t`
under the stationary policy `g` from `x`, over the law of the chain with kernel `x ↦ P(· | x, g(x))`. -/
noncomputable def stationaryExpectedReward (D : RestlessBandit S) (W : ℝ) (g : S → Bool) (x : S)
    (t : ℕ) : ℝ :=
  ∫ ω, subsidizedReward D W g (ω t) ∂markovChainMeasure (stationaryKernel D g) x

/-- The long-run average subsidized reward of the stationary policy `g` from `x`:
`limsup_{T → ∞} T⁻¹ ∑_{t<T} E[r(x(t), g(x(t))) + W(1 − g(x(t)))]`. (For a finite state space
the Cesàro limit exists, so this is the limit.) -/
noncomputable def avgReward (D : RestlessBandit S) (W : ℝ) (g : S → Bool) (x : S) : ℝ :=
  limsup (fun T : ℕ ↦ (T : ℝ)⁻¹ * ∑ t ∈ range T, stationaryExpectedReward D W g x t) atTop

/-- The optimal average reward `g(W)` of the single bandit with passive subsidy `W` (p. 153):
the supremum over deterministic stationary Markov policies and initial states of the average
reward. -/
noncomputable def optimalAvg [Fintype S] (D : RestlessBandit S) (W : ℝ) : ℝ :=
  ⨆ (g : S → Bool) (x : S), avgReward D W g x

/-- `g` is average-optimal for subsidy `W`: it attains `g(W)` from every initial state. -/
def IsAvgOptimal [Fintype S] (D : RestlessBandit S) (W : ℝ) (g : S → Bool) : Prop :=
  ∀ x, avgReward D W g x = optimalAvg D W

/-- `E₀(W)`: the states in which the passive action is optimal under subsidy `W` (p. 153): some
average-optimal deterministic stationary Markov policy takes the passive action there. -/
def passiveSet [Fintype S] (D : RestlessBandit S) (W : ℝ) : Set S :=
  {x | ∃ g, IsAvgOptimal D W g ∧ g x = false}

/-- **Indexability** (p. 154): `E₀(W)` increases monotonically with the subsidy `W`. -/
def Indexable [Fintype S] (D : RestlessBandit S) : Prop :=
  ∀ W W' : ℝ, W ≤ W' → passiveSet D W ⊆ passiveSet D W'

/-- The **Whittle index** `W(x) = inf{W : x ∈ E₀(W)}` (p. 154), the least subsidy for which the
passive action is optimal in `x` (a real infimum; `0` by convention if the set is empty or
unbounded below, which does not occur in the indexable models below). -/
noncomputable def whittleIndex [Fintype S] (D : RestlessBandit S) (x : S) : ℝ :=
  sInf {W : ℝ | x ∈ passiveSet D W}

end Restless

/-! ### Bi-directional bandits on `Fin k` -/

section Monotone

variable {k : ℕ}

/-- The state above `x` (clamped at the top state). -/
def upState (x : Fin k) : Fin k :=
  ⟨min (x.val + 1) (k - 1), by have := x.isLt; omega⟩

/-- The state below `x` (clamped at the bottom state). -/
def downState (x : Fin k) : Fin k :=
  ⟨x.val - 1, by have := x.isLt; omega⟩

/-- The kernel that moves from `x` to `f x` with probability `p x` and otherwise stays at `x`
(the uniformized transition of a rate-`p` move). -/
noncomputable def driftKernel (p : Fin k → ℝ) (f : Fin k → Fin k) : Kernel (Fin k) (Fin k) where
  toFun x := ENNReal.ofReal (p x) • Measure.dirac (f x) + ENNReal.ofReal (1 - p x) • Measure.dirac x
  measurable' := measurable_of_countable _

lemma driftKernel_isMarkovKernel (p : Fin k → ℝ) (f : Fin k → Fin k)
    (hp : ∀ x, p x ∈ Set.Icc (0 : ℝ) 1) : IsMarkovKernel (driftKernel p f) := by
  refine ⟨fun x ↦ ⟨?_⟩⟩
  simp only [driftKernel, Kernel.coe_mk, Measure.coe_add, Measure.coe_smul, Pi.add_apply,
    Pi.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (hp x).1 (by linarith [(hp x).2])]
  simp

/-- The reward vector extended by `0` outside `{0, …, k − 1}` (used only in products with a zero
coefficient at the boundary thresholds). -/
def extendReward (r : Fin k → ℝ) (y : ℕ) : ℝ :=
  if h : y < k then r ⟨y, h⟩ else 0

/-! #### The spinning plates model (§6.5) -/

/-- The **spinning plates** asset (p. 156) as a discrete-time restless bandit on `Fin k`: active
moves up with probability `λ(x)`, passive moves down with probability `μ(x)`, both earn `r(x)`.
The rates are uniformized to lie in `[0, 1]`; the model's `λ(k) = μ(1) = 0` are hypotheses of
the theorems. -/
noncomputable def spinningPlates (lam mu r : Fin k → ℝ) (hlam : ∀ x, lam x ∈ Set.Icc (0 : ℝ) 1)
    (hmu : ∀ x, mu x ∈ Set.Icc (0 : ℝ) 1) : RestlessBandit (Fin k) where
  step u := if u then driftKernel lam upState else driftKernel mu downState
  reward x _ := r x
  avail _ := univ
  avail_nonempty _ := univ_nonempty
  markov u := by
    cases u
    · simpa using driftKernel_isMarkovKernel mu downState hmu
    · simpa using driftKernel_isMarkovKernel lam upState hlam

/-- The monotone policy `(y)` of the class `A` (6.8): passive exactly in the states `x ≥ y`
(`y ∈ {0, …, k}`; `y = k` is "always active", `y = 0` "always passive"). -/
def plateThreshold (y : ℕ) : Fin k → Bool :=
  fun x ↦ decide (x.val < y)

/-- `ϕ(y) = λ(y − 1)/(λ(y − 1) + μ(y))` (p. 157), the long-run fraction of time the asset spends
in state `y` under the monotone policy `(y)`, for thresholds `0 < y < k`; `ϕ(0) = 1` and
`ϕ(k) = 0` (the book's conventions `λ(0) > 0`, `μ(1) = 0`, `λ(k) = 0`, `μ(k+1) > 0`). -/
noncomputable def plateShare (lam mu : Fin k → ℝ) (y : ℕ) : ℝ :=
  if h : 0 < y ∧ y < k then
    lam ⟨y - 1, by omega⟩ / (lam ⟨y - 1, by omega⟩ + mu ⟨y, h.2⟩)
  else if y = 0 then 1 else 0

/-- `R(y) = r(y)ϕ(y) + r(y − 1)(1 − ϕ(y))`, the return rate under the monotone policy `(y)`
(p. 157). -/
noncomputable def plateReturn (lam mu r : Fin k → ℝ) (y : ℕ) : ℝ :=
  extendReward r y * plateShare lam mu y + extendReward r (y - 1) * (1 - plateShare lam mu y)

/-- The right-hand side of (6.10): `max_{0 ≤ y ≤ k} [Wϕ(y) + R(y)]`. -/
noncomputable def plateEnvelope (lam mu r : Fin k → ℝ) (W : ℝ) : ℝ :=
  (range (k + 1)).sup' (by simp) fun y ↦ W * plateShare lam mu y + plateReturn lam mu r y

/-- `W*(x) = (R(x + 1) − R(x))/(ϕ(x) − ϕ(x + 1))`, Eq. (6.11). -/
noncomputable def plateIndex (lam mu r : Fin k → ℝ) (x : Fin k) : ℝ :=
  (plateReturn lam mu r (x.val + 1) - plateReturn lam mu r x.val) /
    (plateShare lam mu x.val - plateShare lam mu (x.val + 1))

/-! #### The vigour model (Example 6.1, p. 158) -/

/-- The **vigour** bandit (p. 158): active moves down with probability `ν(x)` and earns `r(x)`,
passive moves up with probability `ρ(x)` and earns nothing. Rates uniformized to `[0, 1]`; the
model's `ν(1) = ρ(k) = 0` are hypotheses of the theorem. -/
noncomputable def vigourBandit (nu rho r : Fin k → ℝ) (hnu : ∀ x, nu x ∈ Set.Icc (0 : ℝ) 1)
    (hrho : ∀ x, rho x ∈ Set.Icc (0 : ℝ) 1) : RestlessBandit (Fin k) where
  step u := if u then driftKernel nu downState else driftKernel rho upState
  reward x u := if u then r x else 0
  avail _ := univ
  avail_nonempty _ := univ_nonempty
  markov u := by
    cases u
    · simpa using driftKernel_isMarkovKernel rho upState hrho
    · simpa using driftKernel_isMarkovKernel nu downState hnu

/-- The monotone policy of the class `B` (p. 159): active exactly in the states `x ≥ y`. -/
def vigourThreshold (y : ℕ) : Fin k → Bool :=
  fun x ↦ decide (y ≤ x.val)

/-- `ψ(y) = ν(y)/(ν(y) + ρ(y − 1))` (p. 159) for thresholds `0 < y < k`; `ψ(0) = 0` and
`ψ(k) = 1` (the conventions `ν(1) = 0`, `ρ(0) > 0`, `ν(k+1) > 0`, `ρ(k) = 0`). -/
noncomputable def vigourShare (nu rho : Fin k → ℝ) (y : ℕ) : ℝ :=
  if h : 0 < y ∧ y < k then
    nu ⟨y, h.2⟩ / (nu ⟨y, h.2⟩ + rho ⟨y - 1, by omega⟩)
  else if y = 0 then 0 else 1

/-- `Wψ(y) + r(y)(1 − ψ(y))`, the average reward of the monotone policy with threshold `y`. -/
noncomputable def vigourValue (nu rho r : Fin k → ℝ) (W : ℝ) (y : ℕ) : ℝ :=
  W * vigourShare nu rho y + extendReward r y * (1 - vigourShare nu rho y)

/-- `W**(x) = (r(x)(1 − ψ(x)) − r(x + 1)(1 − ψ(x + 1)))/(ψ(x + 1) − ψ(x))` (Theorem 6.5). -/
noncomputable def vigourIndex (nu rho r : Fin k → ℝ) (x : Fin k) : ℝ :=
  (extendReward r x.val * (1 - vigourShare nu rho x.val) -
      extendReward r (x.val + 1) * (1 - vigourShare nu rho (x.val + 1))) /
    (vigourShare nu rho (x.val + 1) - vigourShare nu rho x.val)

end Monotone

end AllocationIndices


