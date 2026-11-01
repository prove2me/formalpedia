-- Prove2me | Definitions.Def_WeakSignalBandit_Experiment
-- name    : WeakSignalBandit_Experiment
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:29:21.568511+00:00
-- url     : https://prove2.me/theorems/eb4e9aa5-abfc-4b48-8de8-fbf4f1f9dcba
-- title:
--   Sequentially randomized Markov experiments on a $K$-armed bandit: states $(Q,S)$, scaled paths $(\bar Q^n,\bar S^n)$, weak signal regime, convergent sampling functions
-- statement:
--   Fix $K$ arms, indexed $k=1,\dots,K$.
--
--   1. **Bandit and experiment (Definitions 1–2).** On a probability space, actions $A_i\in\{1,\dots,K\}$ and rewards $Y_i\in\mathbb R$, $i=1,\dots,n$, are random variables. With the state variables
--   $$Q_{k,i}=\sum_{j=1}^i\mathbf 1(\{A_j=k\}),\qquad S_{k,i}=\sum_{j=1}^i\mathbf 1(\{A_j=k\})\,Y_j,\qquad Q_{k,0}=S_{k,0}=0\quad(2.1),$$
--   a **sequentially randomized Markov experiment** with measurable sampling function $\psi:\mathbb R^K\times\mathbb R^K\to\Delta^K$ (the unit simplex) draws $A_i\mid A_1,Y_1,\dots,A_{i-1},Y_{i-1}\sim\mathrm{Multinomial}(\pi_i)$ with $\pi_i=\psi(Q_{i-1},S_{i-1})$ (2.2)–(2.3), and, conditionally on the chosen action $A_i$, the reward $Y_i$ is drawn from $P_{A_i}$ independently of the history.
--   2. **Scaling (2.10)–(3.2).** $Q^n_{k,i}=Q_{k,i}/n$, $S^n_{k,i}=S_{k,i}/\sqrt n$, and $(\bar Q^n_t,\bar S^n_t)_{t\in[0,1]}$ is their piecewise-linear interpolation on the time scale $i/n$, a random element of $C([0,1],\mathbb R^{2K})$.
--   3. **Weak signal regime (Definition 3).** Reward distributions $\{P^n_k\}$ with means $\mu^n_k=\mathbb E_{P^n_k}[Y]$ and variances $(\sigma^n_k)^2=\mathrm{Var}_{P^n_k}[Y]$ satisfy
--   $$\lim_{n\to\infty}\sqrt n\,\mu^n_k=\mu_k,\qquad\lim_{n\to\infty}(\sigma^n_k)^2=\sigma_k^2.$$
--   Their fourth moments are *uniformly bounded* if $\sup_{n,k}\mathbb E_{P^n_k}[Y^4]<\infty$.
--   4. **Convergent sampling functions (Definition 4).** With $\bar\psi^n(q,s)=\psi^n(nq,\sqrt n\,s)$ (2.11), the sequence $\psi^n$ is convergent with limit $\psi$ if $\bar\psi^n\to\psi$ uniformly on every compact subset of $D=[0,1]^K\times\mathbb R^K$ (2.12).
--
--   This is the model of the paper's first main result (Theorem 1): it covers tempered greedy, Luce's rule and Thompson sampling with exponential-family conjugate priors.
--
--   **Formalization Note** Arm $k$ is `k − 1 : Fin K`; Lean period $i$ is the paper's period $i+1$. The state space $\mathbb R^K\times\mathbb R^K$ is the Euclidean space on `Fin K ⊕ Fin K` (`Sum.inl k` is $q_k$, `Sum.inr k` is $s_k$). Definition 1's phrase "$A_i$ is measurable with respect to the observed history" cannot be literal when $A_i$ is a randomized draw (Definition 2), so the experiment of horizon $n$ is encoded by the two conditional laws above for the periods $1,\dots,n$: $\mathbb P(A_i=k\mid\mathcal F_{i-1})=\psi_k(Q_{i-1},S_{i-1})$ and $\mathbb P(Y_i\in B\mid\mathcal F_{i-1}\vee\sigma(A_i))=P_{A_i}(B)$, which determine the joint law; every $A_i$, $Y_i$ is measurable. The weak-signal parameters $\mu,\sigma$ are arguments (Theorem 1 fixes them). The variance is $\mathbb E[(Y-\mu^n_k)^2]$.
-- source:
--   Kuang, Wager, Weak signal asymptotics for sequentially randomized experiments, arXiv:2101.09855v7, Definition 1 and (2.1) p.7; Definition 2, (2.2)–(2.3) pp.7–8; Definition 3, (2.9)–(2.10) p.10; Definition 4, (2.11)–(2.12) p.10; (3.2) p.12; Theorem 1 (fourth moments) p.12

import Mathlib
import Definitions.Def_WeakSignalBandit_DiffusionLaw
import Definitions.Def_WeakSignalBandit_Interpolation

open MeasureTheory Filter Topology

namespace WeakSignalBandit

/-- The state space `ℝ^K × ℝ^K = ℝ^{2K}` of `z = (q, s)`, with Euclidean norm: coordinate
`Sum.inl k` is `q_k` (the index set `I_Q`), coordinate `Sum.inr k` is `s_k` (the index set `I_S`).
Kuang, Wager, *Weak signal asymptotics for sequentially randomized experiments*,
arXiv:2101.09855v7, (2.3) p.8 and §A.1 p.31 ("Denote by `I_S` and `I_Q` the indices in `Z_t`").

**Formalization Note** Arm `k` of the paper (`k = 1, …, K`) is `k - 1 : Fin K`. -/
abbrev State (K : ℕ) := Sp (Fin K ⊕ Fin K)

/-- The state `(q, s) ∈ ℝ^K × ℝ^K` as a point of `State K`. -/
noncomputable def mkState {K : ℕ} (q s : Fin K → ℝ) : State K :=
  WithLp.toLp 2 (Sum.elim q s)

variable {K : ℕ} {Ω : Type*}

/-- `Q_{k,i} = Σ_{j=1}^{i} 1({A_j = k})`: the number of times arm `k` was chosen in the first `i`
periods. Kuang, Wager, arXiv:2101.09855v7, (2.1) p.7.

**Formalization Note** Periods are indexed from `0`: Lean period `j` is the paper's period `j + 1`,
so `count A i k` sums over the Lean periods `j < i` (the paper's periods `1, …, i`) and
`count A 0 k = 0` is the paper's convention `Q_{k,0} = 0`. -/
noncomputable def count (A : ℕ → Ω → Fin K) (i : ℕ) (k : Fin K) (ω : Ω) : ℝ :=
  ∑ j ∈ Finset.range i, if A j ω = k then 1 else 0

/-- `S_{k,i} = Σ_{j=1}^{i} 1({A_j = k}) Y_j`: the cumulative reward of arm `k` in the first `i`
periods. Kuang, Wager, arXiv:2101.09855v7, (2.1) p.7 (same indexing as `count`). -/
noncomputable def cumReward (A : ℕ → Ω → Fin K) (Y : ℕ → Ω → ℝ) (i : ℕ) (k : Fin K)
    (ω : Ω) : ℝ :=
  ∑ j ∈ Finset.range i, if A j ω = k then Y j ω else 0

/-- The unscaled state `(Q_i, S_i)` after `i` periods. -/
noncomputable def rawState (A : ℕ → Ω → Fin K) (Y : ℕ → Ω → ℝ) (i : ℕ) (ω : Ω) : State K :=
  mkState (fun k => count A i k ω) (fun k => cumReward A Y i k ω)

/-- The scaled state `(Q^n_i, S^n_i)` with `Q^n_{k,i} = Q_{k,i}/n` and `S^n_{k,i} = S_{k,i}/√n`.
Kuang, Wager, arXiv:2101.09855v7, (2.10) p.10. -/
noncomputable def scaledState (n : ℕ) (A : ℕ → Ω → Fin K) (Y : ℕ → Ω → ℝ) (i : ℕ) (ω : Ω) :
    State K :=
  mkState (fun k => count A i k ω / n) (fun k => cumReward A Y i k ω / Real.sqrt n)

/-- The interpolated sample path `t ↦ (Q̄^n_t, S̄^n_t)`, `t ∈ [0,1]`, an element of
`C = C([0,1], ℝ^{2K})`:
`Q̄^n_{k,t} = (1 − tn + ⌊tn⌋) Q^n_{k,⌊tn⌋} + (tn − ⌊tn⌋) Q^n_{k,⌊tn⌋+1}`, and `S̄^n` analogously.
Kuang, Wager, arXiv:2101.09855v7, (3.2) p.12. -/
noncomputable def banditPath (n : ℕ) (A : ℕ → Ω → Fin K) (Y : ℕ → Ω → ℝ) (ω : Ω) :
    Path (Fin K ⊕ Fin K) :=
  interpPath n (fun i => scaledState n A Y i ω)

/-- The observed history `σ(A_1, Y_1, …, A_i, Y_i)` of the first `i` periods (Lean periods
`j < i`). -/
abbrev history [MeasurableSpace Ω] (A : ℕ → Ω → Fin K) (Y : ℕ → Ω → ℝ) (i : ℕ) :
    MeasurableSpace Ω :=
  ⨆ j < i, (MeasurableSpace.comap (A j) inferInstance ⊔ MeasurableSpace.comap (Y j) inferInstance)

/-- A sampling function `ψ : ℝ^K × ℝ^K → Δ^K` of Definition 2: measurable, with values in the unit
simplex `Δ^K = {π ∈ ℝ^K : π_k ≥ 0, Σ_k π_k = 1}`.
Kuang, Wager, arXiv:2101.09855v7, Definition 2, (2.3) p.8. -/
def IsSamplingFunction (ψ : State K → Fin K → ℝ) : Prop :=
  Measurable ψ ∧ ∀ z, ψ z ∈ stdSimplex ℝ (Fin K)

/-- A realization of the `n`-th problem: a stochastic `K`-armed bandit with horizon `n` and reward
distributions `P_1, …, P_K` (Definition 1), run by the sequentially randomized Markov experiment with
sampling function `ψ` (Definition 2). On a probability space `(Ω, ℙ)` the actions `A_i ∈ {1, …, K}`
and rewards `Y_i ∈ ℝ` are random variables, and for every period `i = 1, …, n`:
1. given the history `A_1, Y_1, …, A_{i−1}, Y_{i−1}`, the action `A_i` is a single draw from
   `Multinomial(π_i)` with `π_i = ψ(Q_{i−1}, S_{i−1})`, i.e.
   `ℙ(A_i = k | history) = ψ_k(Q_{i−1}, S_{i−1})` (2.2)–(2.3);
2. conditionally on the chosen action `A_i` (and on the history), the reward `Y_i` has law
   `P_{A_i}`: `ℙ(Y_i ∈ B | history, A_i) = P_{A_i}(B)` for every Borel set `B`.
Kuang, Wager, arXiv:2101.09855v7, Definition 1 p.7, Definition 2 pp.7–8.

**Formalization Note** Lean period `i` is the paper's period `i + 1`; the conditions are imposed
for the Lean periods `i < n` (the paper's `i = 1, …, n`). Definition 1's phrase "`A_i` is
measurable with respect to the observed history" cannot be literal when `A_i` is a randomized draw
(Definition 2), so the two definitions are encoded together by these two conditional laws, which
determine the joint law of `(A_i, Y_i)_{i ≤ n}`. Every `A_i`, `Y_i` (also for `i ≥ n`) is required
to be measurable; values after period `n` never enter the interpolated path on `[0,1]`. -/
def IsSRMExperiment [MeasurableSpace Ω] (n : ℕ) (Pr : Measure Ω) (P : Fin K → Measure ℝ)
    (ψ : State K → Fin K → ℝ) (A : ℕ → Ω → Fin K) (Y : ℕ → Ω → ℝ) : Prop :=
  (∀ i, Measurable (A i)) ∧ (∀ i, Measurable (Y i)) ∧
  (∀ i < n, ∀ k : Fin K,
    condExp (history A Y i) Pr ({ω | A i ω = k}.indicator fun _ => (1 : ℝ)) =ᵐ[Pr]
      fun ω => ψ (rawState A Y i ω) k) ∧
  (∀ i < n, ∀ B : Set ℝ, MeasurableSet B →
    condExp (history A Y i ⊔ MeasurableSpace.comap (A i) inferInstance) Pr
        ((Y i ⁻¹' B).indicator fun _ => (1 : ℝ)) =ᵐ[Pr]
      fun ω => (P (A i ω) B).toReal)

/-- The mean `μ^n_k = E_{P^n_k}[Y]` of a reward distribution. -/
noncomputable def rewardMean (Pk : Measure ℝ) : ℝ := ∫ y, y ∂Pk

/-- The variance `(σ^n_k)² = Var_{P^n_k}[Y] = E_{P^n_k}[(Y − μ^n_k)²]` of a reward distribution. -/
noncomputable def rewardVar (Pk : Measure ℝ) : ℝ := ∫ y, (y - rewardMean Pk) ^ 2 ∂Pk

/-- The sequence of reward distributions `{P^n_k}` resides in the weak signal regime with
parameters `μ, σ`: `lim_{n→∞} √n μ^n_k = μ_k` and `lim_{n→∞} (σ^n_k)² = σ_k²` for every arm `k`.
Kuang, Wager, arXiv:2101.09855v7, Definition 3, (2.9) p.10.

**Formalization Note** The parameters are arguments rather than existentially quantified, because
Theorem 1 fixes them; Definition 3 prints `μ, σ ∈ ℝ^K_+`, while Theorem 1 fixes `μ ∈ ℝ^K` and
`σ ∈ ℝ^K_+`, so the sign conditions are left to the theorems. -/
def IsWeakSignal (P : ℕ → Fin K → Measure ℝ) (μ σ : Fin K → ℝ) : Prop :=
  ∀ k, Tendsto (fun n : ℕ => Real.sqrt n * rewardMean (P n k)) atTop (𝓝 (μ k)) ∧
    Tendsto (fun n : ℕ => rewardVar (P n k)) atTop (𝓝 (σ k ^ 2))

/-- The reward distributions admit fourth moments that are uniformly bounded across `k` and `n`.
Kuang, Wager, arXiv:2101.09855v7, Theorem 1 p.12. -/
def HasBoundedFourthMoments (P : ℕ → Fin K → Measure ℝ) : Prop :=
  ∃ C : ℝ, ∀ n k, Integrable (fun y : ℝ => y ^ 4) (P n k) ∧ ∫ y, y ^ 4 ∂(P n k) ≤ C

/-- The domain `D = [0,1]^K × ℝ^K` of scaled states, on which the limit sampling function lives.
Kuang, Wager, arXiv:2101.09855v7, Definition 4, (2.11) p.10. -/
def domainD : Set (State K) := {z | ∀ k, z (Sum.inl k) ∈ Set.Icc (0 : ℝ) 1}

/-- `(q, s) ↦ (nq, √n s)`. -/
noncomputable def scaleUp (n : ℕ) (z : State K) : State K :=
  mkState (fun k => n * z (Sum.inl k)) (fun k => Real.sqrt n * z (Sum.inr k))

/-- The scale-adapted sampling function `ψ̄^n(q, s) = ψ^n(nq, √n s)`.
Kuang, Wager, arXiv:2101.09855v7, (2.11) p.10. -/
noncomputable def psiBar (n : ℕ) (ψ : State K → Fin K → ℝ) (z : State K) : Fin K → ℝ :=
  ψ (scaleUp n z)

/-- The sequence of sampling functions `ψ^n` is convergent with limit `ψ`: `ψ̄^n → ψ` uniformly
over all compact subsets of `[0,1]^K × ℝ^K`.
Kuang, Wager, arXiv:2101.09855v7, Definition 4, (2.12) p.10.

**Formalization Note** Uniform convergence of `Fin K → ℝ`-valued functions is coordinatewise
uniform convergence. Values of `ψ` outside `D` play no role. -/
def IsConvergentSampling (ψn : ℕ → State K → Fin K → ℝ) (ψ : State K → Fin K → ℝ) : Prop :=
  ∀ C ⊆ (domainD : Set (State K)), IsCompact C →
    TendstoUniformlyOn (fun n => psiBar n (ψn n)) ψ atTop C

end WeakSignalBandit


