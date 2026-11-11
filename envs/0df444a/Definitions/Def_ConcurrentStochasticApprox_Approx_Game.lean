-- Prove2me | Definitions.Def_ConcurrentStochasticApprox_Approx_Game
-- name    : ConcurrentStochasticApprox_Approx_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:43:20.78857+00:00
-- url     : https://prove2.me/theorems/32fdbd9c-1ebd-4329-943f-e4318ed7556b
-- title:
--   §2 — concurrent stochastic games, plays, strategies, objectives, values, MDPs and interval bounds
-- statement:
--   A **concurrent stochastic game** $G=(S,A,B,\delta)$ has a nonempty finite state set $S=\{0,\dots,n-1\}$, nonempty finite action sets $A$ and $B$ of Players 1 and 2, and a transition function $\delta:S\times A\times B\to\Delta(S)$. A reward function is $r:S\times A\times B\to\mathbb R$; the paper's rewards take values in $[0,1]$.
--
--   A **play** is a sequence $\omega=\langle s_0,a_0,b_0,s_1,a_1,b_1,\dots\rangle$. A (behavioural) **strategy** of Player 1 maps every finite history $\langle s_0,a_0,b_0,\dots,s_k\rangle$ to a distribution $\sigma(h)\in\Delta(A)$; likewise $\tau(h)\in\Delta(B)$ for Player 2. Strategies have arbitrary memory and arbitrary real probabilities. A **stationary** strategy depends only on the current state. Given an initial state $s$ and strategies $\sigma,\tau$, the probability measure $\mathbb P^{\sigma,\tau}_s$ on plays is the trajectory measure of the process in which both players draw their actions independently from $\sigma(h)$ and $\tau(h)$ and the next state is drawn from $\delta(s_t,a_t,b_t)$; $\mathbb E^{\sigma,\tau}_s$ is its expectation.
--
--   The objectives are
--   $$\mathrm{Reach}(T)(\omega)=\mathbf 1[\exists t\ge0:\ s_t\in T],\qquad \mathrm{Disc}(r,\lambda)(\omega)=(1-\lambda)\sum_{t\ge0}\lambda^t r(s_t,a_t,b_t),$$
--   $$\mathrm{LimAvg}(r)(\omega)=\liminf_{k\to\infty}\frac1k\sum_{t=0}^{k-1}r(s_t,a_t,b_t).$$
--   The **value** of an objective $\varphi$ is $\mathrm{val}_\varphi(s)=\sup_{\sigma}\inf_{\tau}\mathbb E^{\sigma,\tau}_s[\varphi]$ (and the upper value is $\inf_\tau\sup_\sigma$). We write $\mathrm{val}_T,\mathrm{val}_\lambda,\mathrm{val}$ for the three objectives. A Player-1 strategy is **$\varepsilon$-optimal** if $\inf_\tau\mathbb E^{\sigma,\tau}_s[\varphi]\ge\mathrm{val}_\varphi(s)-\varepsilon$ at every state; for Player 2, $\sup_\sigma\mathbb E^{\sigma,\tau}_s[\varphi]\le\mathrm{val}_\varphi(s)+\varepsilon$.
--
--   A **player-$p$ MDP** is a game in which the other player has a single action, and a **Markov chain** one in which both players have a single action. The **Bellman operator** of a player-$p$ MDP $P$ with reward $r$ and discount $\lambda$ is
--   $$\Psi_P(\rho)(s)=\operatorname*{op}_{a\in A}\Big((1-\lambda)r(s,a)+\lambda\sum_{s'}\delta(s,a)(s')\rho(s')\Big),$$
--   with op $=\max$ for $p=1$ and $\min$ for $p=2$. Fixing a stationary strategy $\sigma$ of Player 1 gives the player-2 MDP $G_\sigma$ with $\delta_\sigma(s,b)=\sum_a\sigma(s)(a)\delta(s,a,b)$ and $r_\sigma(s,b)=\sum_a\sigma(s)(a)r(s,a,b)$; $G_\tau$ is symmetric. An **interval bound** $(L,U)$ has $L\preceq U$; it is **shrinking** for $P$ if $L\preceq\Psi_P(L)$ and $\Psi_P(U)\preceq U$, and **$\eta$-close** if $U(s)-L(s)\le\eta$ for all $s$.
--
--   The file also defines the **succinct discount factor** $\lambda=1-2^{-2^{B_\lambda}}$; common denominators (all probabilities and rewards are integer multiples of $1/Q$); absorbing states and absorbing Markov chains (from every state an absorbing state is reached with probability one); the chain $C^{\mathrm{abs}}$ of Lemma 6.3 on $S\cup\{\top,\bot\}$; and the game $G_T$ with target states made absorbing and reward $r_T=\mathbf 1_T$ of Lemma 7.1.
--
--   These are the objects of every statement in the mission.
--
--   **Formalization Note** States and actions are `Fin n`, `Fin mA`, `Fin mB` with `n, mA, mB ≥ 1` (structure fields). The measure is `ProbabilityTheory.Kernel.trajMeasure`; it gives probability zero to plays leaving the support of $\delta$. Expectations are Bochner integrals of bounded measurable payoffs, and the suprema/infima range over the nonempty strategy types, so no default value is ever used. In $C^{\mathrm{abs}}$ the original state $s$ is `Fin.castAdd 2 s`, $\top$ is `Fin.natAdd n 0` and $\bot$ is `Fin.natAdd n 1`.
-- source:
--   Ali Asadi, Krishnendu Chatterjee, The Computational Complexity of Concurrent Stochastic Games: Exact Value and Approximation, STOC 2027 submission #285 (October 2026), SHA-256 5cff187cf6b230b3bdfe540f2832f824d1ddb6acb43239fbf469d37c43b0d461, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/285.pdf, §2 (printed pp. 3–5, PDF pp. 5–7), §3.2 (succinct discount, printed p. 6), §5.2 interval bounds (printed p. 15), §6.1 absorbing MCs and Lemma 6.3 (printed pp. 19–20), Lemma 7.1 (printed p. 30)

import Mathlib

/-!
# Concurrent stochastic games, their plays, objectives and values

Asadi–Chatterjee, *The Computational Complexity of Concurrent Stochastic Games: Exact Value and
Approximation*, STOC 2027 submission #285, §2 (printed pp. 3–5, PDF pp. 5–7), §5.2 (printed
p. 14), §6.1 (printed pp. 18–20), §7 (printed p. 30).

Conventions.
* The state set is `Fin n`, the action sets of Players 1 and 2 are `Fin mA` and `Fin mB`;
  all three sets are nonempty (fields `hN`, `hA`, `hB`). The paper's `m` is `max mA mB`.
* A probability distribution on `Fin k` is a real vector with nonnegative entries summing to one.
* A play is a sequence `ω : ℕ → Fin n × Fin mA × Fin mB`; `ω t = (s_t, a_t, b_t)`.
* A behavioural strategy maps the list of past stages `[(s₀,a₀,b₀), …, (s_{k-1},a_{k-1},b_{k-1})]`
  together with the current state `s_k` (i.e. the full history `⟨s₀,a₀,b₀,…,s_k⟩`) to a
  distribution on actions. Strategies are arbitrary (full memory, real probabilities).
* The probability measure on plays is the Ionescu-Tulcea trajectory measure
  (`ProbabilityTheory.Kernel.trajMeasure`) of the step kernels: the next state is drawn from
  `δ(s_t,a_t,b_t)`, then both players draw their actions independently from the strategies applied
  to the history. It gives probability zero to invalid plays.
* A player-1 MDP is a game with `mB = 1`, a player-2 MDP one with `mA = 1`, a Markov chain one with
  `mA = mB = 1` (the paper's convention: "the other player has only one action").
-/

open MeasureTheory ProbabilityTheory Finset

noncomputable section

namespace ConcurrentStochasticApprox.Approx

/-! ### Distributions -/

/-- `μ` is a probability distribution on `Fin k`. -/
def IsDist {k : ℕ} (μ : Fin k → ℝ) : Prop := (∀ i, 0 ≤ μ i) ∧ ∑ i, μ i = 1

/-- The probability distributions `Δ(Fin k)`. -/
abbrev Dist (k : ℕ) := {μ : Fin k → ℝ // IsDist μ}

/-- A distribution as a `PMF`. -/
def Dist.toPMF {k : ℕ} (μ : Dist k) : PMF (Fin k) :=
  PMF.ofFintype (fun i => ENNReal.ofReal (μ.1 i)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => μ.2.1 i), μ.2.2, ENNReal.ofReal_one])

/-- The Dirac distribution `1[i]`. -/
def Dist.dirac {k : ℕ} (i : Fin k) : Dist k :=
  ⟨fun j => if j = i then 1 else 0, fun j => by by_cases h : j = i <;> simp [h], by simp⟩

/-- The mixture `∑ₐ w(a) μₐ` of distributions. -/
def Dist.mix {m k : ℕ} (w : Dist m) (μ : Fin m → Dist k) : Dist k :=
  ⟨fun j => ∑ a, w.1 a * (μ a).1 j,
   fun j => Finset.sum_nonneg (fun a _ => mul_nonneg (w.2.1 a) ((μ a).2.1 j)), by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, (fun a => (μ a).2.2), mul_one]
    exact w.2.2⟩

/-! ### Games -/

/-- A concurrent stochastic game `G = (S, A, B, δ)` with `S = Fin n`, `A = Fin mA`, `B = Fin mB`
(§2, printed p. 3). -/
structure CSG (n mA mB : ℕ) where
  /-- The transition function `δ : S × A × B → Δ(S)`. -/
  δ : Fin n → Fin mA → Fin mB → Dist n
  hA : 0 < mA
  hB : 0 < mB
  hN : 0 < n

/-- A reward function `r : S × A × B → ℝ`. -/
abbrev Reward (n mA mB : ℕ) := Fin n → Fin mA → Fin mB → ℝ

/-- The paper's reward functions take values in `[0, 1]`. -/
def IsReward {n mA mB : ℕ} (r : Reward n mA mB) : Prop := ∀ s a b, 0 ≤ r s a b ∧ r s a b ≤ 1

/-- One stage `(s_t, a_t, b_t)` of a play. -/
abbrev Stage (n mA mB : ℕ) := Fin n × Fin mA × Fin mB

/-- Plays `ω = ⟨s₀,a₀,b₀,s₁,a₁,b₁,…⟩`. -/
abbrev Play (n mA mB : ℕ) := ℕ → Stage n mA mB

/-- Behavioural strategies of Player 1, `σ : H → Δ(A)`. -/
abbrev Strategy₁ (n mA mB : ℕ) := List (Stage n mA mB) → Fin n → Dist mA

/-- Behavioural strategies of Player 2, `τ : H → Δ(B)`. -/
abbrev Strategy₂ (n mA mB : ℕ) := List (Stage n mA mB) → Fin n → Dist mB

/-- Stationary strategies of Player 1, `σ : S → Δ(A)`. -/
abbrev Stationary₁ (n mA : ℕ) := Fin n → Dist mA

/-- Stationary strategies of Player 2, `τ : S → Δ(B)`. -/
abbrev Stationary₂ (n mB : ℕ) := Fin n → Dist mB

/-- A stationary strategy as a behavioural strategy (it ignores the past). -/
def Stationary₁.toStrategy {n mA : ℕ} (σ : Stationary₁ n mA) (mB : ℕ) : Strategy₁ n mA mB :=
  fun _ s => σ s

/-- A stationary strategy as a behavioural strategy (it ignores the past). -/
def Stationary₂.toStrategy {n mB : ℕ} (τ : Stationary₂ n mB) (mA : ℕ) : Strategy₂ n mA mB :=
  fun _ s => τ s

variable {n mA mB : ℕ}

/-- The history of stages `0, …, k` stored in a trajectory prefix. -/
def histOf {k : ℕ} (x : (i : Finset.Iic k) → Stage n mA mB) : List (Stage n mA mB) :=
  List.ofFn (fun i : Fin (k + 1) => x ⟨i.val, Finset.mem_Iic.mpr (Nat.lt_succ_iff.mp i.isLt)⟩)

/-- Initial stage: `s₀ = s`, then `a₀ ∼ σ(⟨s⟩)` and `b₀ ∼ τ(⟨s⟩)` independently. -/
def initPMF (σ : Strategy₁ n mA mB) (τ : Strategy₂ n mA mB) (s : Fin n) : PMF (Stage n mA mB) :=
  (σ [] s).toPMF.bind fun a => (τ [] s).toPMF.map fun b => (s, a, b)

/-- One stage transition: from history `h` ending with the stage `cur = (s,a,b)`, draw
`s' ∼ δ(s,a,b)`, then `a' ∼ σ(h·s')` and `b' ∼ τ(h·s')` independently. -/
def stepPMF (G : CSG n mA mB) (σ : Strategy₁ n mA mB) (τ : Strategy₂ n mA mB)
    (h : List (Stage n mA mB)) (cur : Stage n mA mB) : PMF (Stage n mA mB) :=
  (G.δ cur.1 cur.2.1 cur.2.2).toPMF.bind fun s' =>
    (σ h s').toPMF.bind fun a => (τ h s').toPMF.map fun b => (s', a, b)

/-- The step kernels of the play process. -/
def stepKernel (G : CSG n mA mB) (σ : Strategy₁ n mA mB) (τ : Strategy₂ n mA mB) (k : ℕ) :
    Kernel ((i : Finset.Iic k) → Stage n mA mB) (Stage n mA mB) :=
  Kernel.ofFunOfCountable fun x =>
    (stepPMF G σ τ (histOf x) (x ⟨k, Finset.mem_Iic.mpr le_rfl⟩)).toMeasure

instance (G : CSG n mA mB) (σ : Strategy₁ n mA mB) (τ : Strategy₂ n mA mB) (k : ℕ) :
    IsMarkovKernel (stepKernel G σ τ k) :=
  ⟨fun x => by
    simp only [stepKernel, Kernel.ofFunOfCountable, Kernel.coe_mk]
    infer_instance⟩

/-- The probability measure `P_s^{σ,τ}` on plays induced by the initial state `s` and the
strategies `σ, τ` (§2, "Probability space", printed p. 4). -/
def playMeasure (G : CSG n mA mB) (σ : Strategy₁ n mA mB) (τ : Strategy₂ n mA mB) (s : Fin n) :
    Measure (Play n mA mB) :=
  Kernel.trajMeasure (initPMF σ τ s).toMeasure (stepKernel G σ τ)

/-- The expectation `E_s^{σ,τ}[φ]`. -/
def expect (G : CSG n mA mB) (σ : Strategy₁ n mA mB) (τ : Strategy₂ n mA mB) (s : Fin n)
    (φ : Play n mA mB → ℝ) : ℝ :=
  ∫ ω, φ ω ∂(playMeasure G σ τ s)

/-! ### Objectives -/

/-- `Reach(T)(ω) = 1` if `s_t ∈ T` for some `t ≥ 0`, else `0`. -/
def reachObj (T : Finset (Fin n)) (ω : Play n mA mB) : ℝ := by
  classical exact if ∃ t, (ω t).1 ∈ T then 1 else 0

/-- `Disc(r, λ)(ω) = (1 - λ) ∑_{t ≥ 0} λ^t r(s_t, a_t, b_t)`. -/
def discObj (r : Reward n mA mB) (lam : ℝ) (ω : Play n mA mB) : ℝ :=
  (1 - lam) * ∑' t : ℕ, lam ^ t * r (ω t).1 (ω t).2.1 (ω t).2.2

/-- `LimAvg(r)(ω) = liminf_{k → ∞} (1/k) ∑_{t=0}^{k-1} r(s_t, a_t, b_t)`. -/
def limAvgObj (r : Reward n mA mB) (ω : Play n mA mB) : ℝ :=
  Filter.liminf (fun k : ℕ => (1 / (k : ℝ)) * ∑ t ∈ Finset.range k, r (ω t).1 (ω t).2.1 (ω t).2.2)
    Filter.atTop

/-! ### Values and ε-optimal strategies -/

/-- The value `val_φ(s) = sup_σ inf_τ E_s^{σ,τ}[φ]`. -/
def value (G : CSG n mA mB) (φ : Play n mA mB → ℝ) (s : Fin n) : ℝ :=
  ⨆ σ : Strategy₁ n mA mB, ⨅ τ : Strategy₂ n mA mB, expect G σ τ s φ

/-- The upper value `inf_τ sup_σ E_s^{σ,τ}[φ]`. -/
def upperValue (G : CSG n mA mB) (φ : Play n mA mB → ℝ) (s : Fin n) : ℝ :=
  ⨅ τ : Strategy₂ n mA mB, ⨆ σ : Strategy₁ n mA mB, expect G σ τ s φ

/-- `val_T`, the value of `Reach(T)`. -/
def reachValue (G : CSG n mA mB) (T : Finset (Fin n)) (s : Fin n) : ℝ := value G (reachObj T) s

/-- `val_λ`, the value of `Disc(r, λ)`. -/
def discValue (G : CSG n mA mB) (r : Reward n mA mB) (lam : ℝ) (s : Fin n) : ℝ :=
  value G (discObj r lam) s

/-- `val`, the value of `LimAvg(r)`. -/
def limAvgValue (G : CSG n mA mB) (r : Reward n mA mB) (s : Fin n) : ℝ := value G (limAvgObj r) s

/-- Player 1's strategy `σ` is `ε`-optimal: `inf_τ E_s^{σ,τ}[φ] ≥ val_φ(s) - ε` at every state. -/
def IsEpsOptimal₁ (G : CSG n mA mB) (φ : Play n mA mB → ℝ) (ε : ℝ) (σ : Strategy₁ n mA mB) :
    Prop :=
  ∀ s, value G φ s - ε ≤ ⨅ τ : Strategy₂ n mA mB, expect G σ τ s φ

/-- Player 2's strategy `τ` is `ε`-optimal: `sup_σ E_s^{σ,τ}[φ] ≤ val_φ(s) + ε` at every state. -/
def IsEpsOptimal₂ (G : CSG n mA mB) (φ : Play n mA mB → ℝ) (ε : ℝ) (τ : Strategy₂ n mA mB) :
    Prop :=
  ∀ s, ⨆ σ : Strategy₁ n mA mB, expect G σ τ s φ ≤ value G φ s + ε

/-! ### MDPs, Bellman operators and fixed strategies -/

/-- The Bellman operator of a player-1 MDP `P` (a game with `mB = 1`), op = max (§2, p. 5):
`Ψ_P(ρ)(s) = max_a ((1-λ) r(s,a) + λ ∑_{s'} δ(s,a)(s') ρ(s'))`. -/
def bellman₁ {m : ℕ} (P : CSG n m 1) (r : Reward n m 1) (lam : ℝ) (ρ : Fin n → ℝ) (s : Fin n) : ℝ :=
  Finset.univ.sup' ⟨⟨0, P.hA⟩, Finset.mem_univ _⟩
    (fun a => (1 - lam) * r s a 0 + lam * ∑ s', (P.δ s a 0).1 s' * ρ s')

/-- The Bellman operator of a player-2 MDP `P` (a game with `mA = 1`), op = min. -/
def bellman₂ {m : ℕ} (P : CSG n 1 m) (r : Reward n 1 m) (lam : ℝ) (ρ : Fin n → ℝ) (s : Fin n) : ℝ :=
  Finset.univ.inf' ⟨⟨0, P.hB⟩, Finset.mem_univ _⟩
    (fun b => (1 - lam) * r s 0 b + lam * ∑ s', (P.δ s 0 b).1 s' * ρ s')

/-- The player-2 MDP `G_σ` obtained by fixing a stationary strategy `σ` of Player 1:
`δ_σ(s,b) = ∑_a σ(s)(a) δ(s,a,b)` (§2, printed p. 5). -/
def fixP1 (G : CSG n mA mB) (σ : Stationary₁ n mA) : CSG n 1 mB where
  δ s _ b := Dist.mix (σ s) (fun a => G.δ s a b)
  hA := Nat.one_pos
  hB := G.hB
  hN := G.hN

/-- The reward `r_σ(s,b) = ∑_a σ(s)(a) r(s,a,b)` of `G_σ`. -/
def fixP1Reward (r : Reward n mA mB) (σ : Stationary₁ n mA) : Reward n 1 mB :=
  fun s _ b => ∑ a, (σ s).1 a * r s a b

/-- The player-1 MDP `G_τ` obtained by fixing a stationary strategy `τ` of Player 2. -/
def fixP2 (G : CSG n mA mB) (τ : Stationary₂ n mB) : CSG n mA 1 where
  δ s a _ := Dist.mix (τ s) (fun b => G.δ s a b)
  hA := G.hA
  hB := Nat.one_pos
  hN := G.hN

/-- The reward `r_τ(s,a) = ∑_b τ(s)(b) r(s,a,b)` of `G_τ`. -/
def fixP2Reward (r : Reward n mA mB) (τ : Stationary₂ n mB) : Reward n mA 1 :=
  fun s a _ => ∑ b, (τ s).1 b * r s a b

/-! ### Interval bounds (§5.2, printed p. 15) -/

/-- `(L, U)` is a shrinking interval bound of the player-1 MDP `P`:
`L ⪯ U`, `L ⪯ Ψ_P(L)` and `Ψ_P(U) ⪯ U`. -/
def IsShrinking₁ {m : ℕ} (P : CSG n m 1) (r : Reward n m 1) (lam : ℝ) (L U : Fin n → ℝ) : Prop :=
  L ≤ U ∧ L ≤ bellman₁ P r lam L ∧ bellman₁ P r lam U ≤ U

/-- `(L, U)` is a shrinking interval bound of the player-2 MDP `P`. -/
def IsShrinking₂ {m : ℕ} (P : CSG n 1 m) (r : Reward n 1 m) (lam : ℝ) (L U : Fin n → ℝ) : Prop :=
  L ≤ U ∧ L ≤ bellman₂ P r lam L ∧ bellman₂ P r lam U ≤ U

/-- `(L, U)` is `η`-close: `U(s) - L(s) ≤ η` for every state. -/
def IsClose (η : ℝ) (L U : Fin n → ℝ) : Prop := ∀ s, U s - L s ≤ η

/-! ### Succinct discount factors and common denominators -/

/-- The succinct discount factor `λ = 1 - 2^{-2^{Bλ}}` (§3.2, printed p. 6). -/
def succinct (Blam : ℕ) : ℝ := 1 - (1 / 2 : ℝ) ^ (2 ^ Blam)

/-- All transition probabilities of `G` and all rewards `r` are integer multiples of `1/Q`. -/
def HasCommonDenom (G : CSG n mA mB) (r : Reward n mA mB) (Q : ℕ) : Prop :=
  (∀ s a b s', ∃ z : ℤ, (G.δ s a b).1 s' = (z : ℝ) / Q) ∧ ∀ s a b, ∃ z : ℤ, r s a b = (z : ℝ) / Q

/-! ### Markov chains -/

/-- The unique strategy of a player with one action. -/
def trivial₁ (n mB : ℕ) : Strategy₁ n 1 mB := fun _ _ => Dist.dirac 0

/-- The unique strategy of a player with one action. -/
def trivial₂ (n mA : ℕ) : Strategy₂ n mA 1 := fun _ _ => Dist.dirac 0

/-- A state `t` of a Markov chain is absorbing: `δ(t)(t) = 1`. -/
def IsAbsorbingState (C : CSG n 1 1) (t : Fin n) : Prop := (C.δ t 0 0).1 t = 1

/-- A Markov chain is absorbing if, from every state, it reaches an absorbing state with
probability one (§6.1, printed p. 19). -/
def IsAbsorbingMC (C : CSG n 1 1) : Prop :=
  ∀ s, playMeasure C (trivial₁ n 1) (trivial₂ n 1) s
    {ω | ∃ t, IsAbsorbingState C (ω t).1} = 1

/-- The reward `r : S → ℝ` of a Markov chain as a reward function of the game. -/
def mcReward (r : Fin n → ℝ) : Reward n 1 1 := fun s _ _ => r s

/-- The transition rows of `C^abs` (Lemma 6.3, printed p. 20). States `Fin (n+2)`: the original
states `Fin.castAdd 2 s`, then `⊤ = Fin.natAdd n 0` and `⊥ = Fin.natAdd n 1`. -/
def absRow (C : CSG n 1 1) (r : Fin n → ℝ) (lam : ℝ) (s : Fin n) : Fin (n + 2) → ℝ :=
  Fin.addCases (fun s' : Fin n => lam * (C.δ s 0 0).1 s')
    (fun j : Fin 2 => if j = 0 then (1 - lam) * r s else (1 - lam) * (1 - r s))

/-- The Markov chain `C^abs` of Lemma 6.3: from `s ∈ S` go to `s'` with probability `λ δ(s)(s')`,
to `⊤` with probability `(1-λ) r(s)`, to `⊥` with probability `(1-λ)(1-r(s))`; `⊤` and `⊥` are
absorbing. -/
def absChain (C : CSG n 1 1) (r : Fin n → ℝ) (hr : ∀ s, 0 ≤ r s ∧ r s ≤ 1) (lam : ℝ)
    (hlam : 0 ≤ lam ∧ lam < 1) : CSG (n + 2) 1 1 where
  δ i _ _ := Fin.addCases (motive := fun _ => Dist (n + 2))
    (fun s => ⟨absRow C r lam s, by
      refine ⟨fun i => ?_, ?_⟩
      · refine Fin.addCases (fun s' => ?_) (fun j => ?_) i
        · simp only [absRow, Fin.addCases_left]
          exact mul_nonneg hlam.1 ((C.δ s 0 0).2.1 s')
        · simp only [absRow, Fin.addCases_right]
          split_ifs
          · exact mul_nonneg (by linarith [hlam.2]) (hr s).1
          · exact mul_nonneg (by linarith [hlam.2]) (by linarith [(hr s).2])
      · rw [Fin.sum_univ_add]
        simp only [absRow, Fin.addCases_left, Fin.addCases_right, Fin.sum_univ_two]
        rw [← Finset.mul_sum, (C.δ s 0 0).2.2]
        simp
        ring⟩)
    (fun j => Dist.dirac (Fin.natAdd n j)) i
  hA := Nat.one_pos
  hB := Nat.one_pos
  hN := by omega

/-- The state `⊤` of `C^abs`. -/
def absTop (n : ℕ) : Fin (n + 2) := Fin.natAdd n 0

/-- The state `⊥` of `C^abs`. -/
def absBot (n : ℕ) : Fin (n + 2) := Fin.natAdd n 1

/-! ### Reachability as limit-average (Lemma 7.1, printed p. 30) -/

/-- The game `G_T`: every target state is made absorbing, `δ_T(s,a,b) = 1[s]` for `s ∈ T`. -/
def targetGame (G : CSG n mA mB) (T : Finset (Fin n)) : CSG n mA mB where
  δ s a b := if s ∈ T then Dist.dirac s else G.δ s a b
  hA := G.hA
  hB := G.hB
  hN := G.hN

/-- The reward `r_T(s,a,b) = 1` for `s ∈ T`, `0` otherwise. -/
def targetReward (T : Finset (Fin n)) : Reward n mA mB := fun s _ _ => if s ∈ T then 1 else 0

end ConcurrentStochasticApprox.Approx


