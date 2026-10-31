-- Prove2me | Definitions.Def_RiskExpPG_Algorithm
-- name    : RiskExpPG_Algorithm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:26:39.847914+00:00
-- url     : https://prove2.me/theorems/07badcf6-40a7-41ed-80d6-a6801bf16cce
-- title:
--   The trajectory-based algorithm, Eq. (11) and (12): updates, runs, return times, noise, Lyapunov families, and the two regimes
-- statement:
--   The algorithm samples the chain under the policy $\theta_m$ from the $m$-th to the $(m+1)$-th visit to $x^*$, and then updates. Its inputs are step sizes $\gamma_m$, a constant $\eta$, a truncation sequence $M_m$, initial values $\theta_0$ and $\widetilde\Lambda_0$, and an update rule.
--
--   1. **Update rules.** With $F_m=F^{(M_m)}$ and $G_m=G^{(M_m)}$ evaluated on the observed cycle, rule (11) is
--   $$\theta_{m+1}=\theta_m-\gamma_mF_m(\theta_m,\widetilde\Lambda_m),\qquad\widetilde\Lambda_{m+1}=\widetilde\Lambda_m+\eta\gamma_m\big(G_m(\theta_m,\widetilde\Lambda_m)-1\big),$$
--   and rule (12) replaces the two increments by $\Gamma_{\theta_{\mathrm{thresh}}}(\gamma_mF_m)$ and $\Gamma_{\Lambda_{\mathrm{thresh}}}(\eta\gamma_m(G_m-1))$, where $\Gamma_a$ is the element-wise projection to $[-a,a]$.
--   2. **State of the algorithm.** The state after $\Phi_1,\dots,\Phi_n$ holds the number of completed cycles, the current pair $(\theta,\widetilde\Lambda)$, and the states since the last return. A return to $x^*$ closes the cycle and applies the update.
--   3. **Run.** A process $\{\Phi_i\}$ on a probability space is a run if $\Phi_0=x^*$ and each step has the law $P_\theta(\Phi_n,\cdot)$ given the prefix, where $\theta$ is the policy computed from the prefix.
--   4. **Return times and iterates.** $t_m$ is the time of the $m$-th return, with $t_0=0$, and $r_m=(\theta_m,\widetilde\Lambda_m)$ is the state at $t_m$.
--   5. **Drift and noise.** $k_m(r)=(-f_m(r),\eta(g_m(r)-1))$, $K_m$ is its stochastic version on the observed cycle, and $\epsilon_m=\gamma_m(K_m(r_m)-k_m(r_m))$.
--   6. **Lyapunov families.** $\{\psi_m\}$ is a family of Lyapunov functions if $\{\psi_m\}$, $\{\nabla\psi_m\}$ and $\{\nabla^2\psi_m\}$ are uniformly bounded over $\mathbb R^l\times I$ for any $I=[a,b]$ and $\sum_m\sup_{r\in\mathbb R^l\times I}\psi_{m+1}(r)-\psi_m(r)<\infty$. The remainder is $\Delta_m(\psi_m):=\psi_m(r_{m+1})-\psi_m(r_m)-\gamma_m\nabla\psi_m(r_m)\cdot k_m(r_m)$.
--   7. **Regimes.** Either $M_m=M>1$ for all $m$, with target $\Lambda^{(M)}_\theta$, or $\sum_m\gamma_m^{2(1-\beta)}<\infty$ for some $\beta\in(0,\frac12)$ and $M_m=\sup\{N_i:N_i\le1/\gamma_m^\beta\}$ with $\{N_i\}$ as in Assumption 4, with target $\Lambda_\theta$.
--
--   These definitions state Theorem 1 and the steps of its proof in Appendix B.
--
--   **Formalization Note** The chain is adaptive, so the run is stated through the probability of each cylinder set. If a trajectory has fewer than $m$ returns, $t_m$ takes the value $0$ of an empty infimum; Theorem 1 proves that this has probability zero. The noise uses the unprojected $K_m$ for both rules, as Remark 2 intends. The page prints the sum in the definition of a Lyapunov family without absolute values, and so does this definition. Where the set in the supremum for $M_m$ is empty, $M_m$ is any value above $1$.
-- source:
--   Moharrami, Murthy, Roy & Srikant, A Policy Gradient Algorithm for the Risk-Sensitive Exponential Cost MDP, arXiv:2202.04157v2, §6, p.11, Eq. (11), (12); App. B, pp.21, 23–25, Eq. (20), Remark 2

import Mathlib
import Definitions.Def_RiskExpPG_Chain
import Definitions.Def_RiskExpPG_Model

open Filter Topology MeasureTheory
open scoped ENNReal

namespace RiskExpPG

/-- The two update rules of §6 (p.11): Eq. (11), or Eq. (12) with the thresholds `θ_thresh` and
`Λ_thresh`. -/
inductive UpdateRule where
  /-- The update rule Eq. (11). -/
  | plain : UpdateRule
  /-- The update rule Eq. (12), with the fixed constants `θ_thresh` and `Λ_thresh`. -/
  | projected (θthresh Λthresh : ℝ) : UpdateRule

/-- The element-wise projection `Γ_a` of a real number to `[-a, a]` (p.11). -/
noncomputable def clamp (a t : ℝ) : ℝ :=
  max (-a) (min a t)

/-- The element-wise projection `Γ_a` of a vector to `[-a, a]^l` (p.11). -/
noncomputable def clampVec {l : ℕ} (a : ℝ) (v : Param l) : Param l :=
  WithLp.toLp 2 fun i => clamp a (v i)

/-- The inputs of the algorithm of §6 (p.11): step sizes `γ`, the tunable parameter `η`, the
truncation sequence `M`, the deterministic initial values `θ₀` and `Λ̃₀`, and the update rule. -/
structure Config (l : ℕ) where
  /-- The step sizes `γ_m`. -/
  γ : ℕ → ℝ
  /-- The tunable parameter `η`. -/
  η : ℝ
  /-- The truncation sequence `M_m`. -/
  M : ℕ → ℝ
  /-- The initial parameter `θ₀`. -/
  θ₀ : Param l
  /-- The initial estimate `Λ̃₀`. -/
  Λ₀ : ℝ
  /-- Eq. (11) or Eq. (12). -/
  rule : UpdateRule

/-- Assumption 5 on the step sizes, `η > 0`, and positive thresholds in Eq. (12). -/
def Config.IsValid {l : ℕ} (cfg : Config l) : Prop :=
  Assumption5 cfg.γ ∧ 0 < cfg.η ∧
    match cfg.rule with
    | .plain => True
    | .projected θthresh Λthresh => 0 < θthresh ∧ 0 < Λthresh

variable {X : Type*} {l : ℕ}

/-- One update at time-step `t_{k+1}`, from the pair `(θ_k, Λ̃_k)` and the observed excursion `e`:
Eq. (11), or Eq. (12) with the projections. `F_k` and `G_k` are `F^(M_k)` and `G^(M_k)` evaluated on
the excursion. -/
noncomputable def Model.step (m : Model X l) (cfg : Config l) (k : ℕ) (θ : Param l) (Λ : ℝ)
    (e : List X) : Param l × ℝ :=
  let dθ := cfg.γ k • m.F (cfg.M k) θ Λ e
  let dΛ := cfg.η * cfg.γ k * (m.G (cfg.M k) θ Λ e - 1)
  match cfg.rule with
  | .plain => (θ - dθ, Λ + dΛ)
  | .projected θthresh Λthresh => (θ - clampVec θthresh dθ, Λ + clamp Λthresh dΛ)

/-- What the algorithm knows after a finite prefix of the trajectory: the number `index` of
completed cycles, the current pair `(θ_index, Λ̃_index)`, and the states visited since the last
return to `x*`, excluding that return. -/
structure State (X : Type*) (l : ℕ) where
  /-- The number of completed cycles. -/
  index : ℕ
  /-- The current policy parameter. -/
  θ : Param l
  /-- The current estimate of the cost. -/
  Λ : ℝ
  /-- The open cycle: the states after the last return to `x*`. -/
  excursion : List X

/-- The effect of observing the next state `y`: a return to `x*` closes the cycle and applies
`Model.step`, and any other state extends the open cycle. -/
noncomputable def Model.advance [DecidableEq X] (m : Model X l) (cfg : Config l) (s : State X l)
    (y : X) : State X l :=
  if y = m.xstar then
    let r := m.step cfg s.index s.θ s.Λ s.excursion
    ⟨s.index + 1, r.1, r.2, []⟩
  else
    ⟨s.index, s.θ, s.Λ, s.excursion ++ [y]⟩

/-- The state of the algorithm after observing `Φ₁ = x 1, …, Φₙ = x n`, from `(θ₀, Λ̃₀)` with no
completed cycle. The starting state `Φ₀ = x*` is not an observation (`t₀ = 0`). The policy in force
for the transition from time `n` to time `n + 1` is the field `θ` of this state, so that the chain
follows `θ_k` on `{t_k, …, t_{k+1} - 1}`. -/
noncomputable def Model.stateAt [DecidableEq X] (m : Model X l) (cfg : Config l) (x : ℕ → X)
    (n : ℕ) : State X l :=
  ((List.range n).map fun i => x (i + 1)).foldl (m.advance cfg) ⟨0, cfg.θ₀, cfg.Λ₀, []⟩

/-- `IsRun m cfg μ Φ`: the process `Φ` on `(Ω, μ)` is a run of the algorithm of §6 (p.11). It is
started at `x*` and, for every `n` and every trajectory `x`,
`μ(Φ₀ = x₀, …, Φₙ₊₁ = xₙ₊₁) = P_θ(xₙ, xₙ₊₁) μ(Φ₀ = x₀, …, Φₙ = xₙ)`, where `θ` is the policy the
algorithm has computed from `x₀, …, xₙ`.

**Formalization Note** The chain is adaptive: it is not the Markov chain of a single `θ`. The
statement is the one-step conditional law, written without a conditional expectation. `Φ₀ = x*`
is how the page sets `t₀ = 0` with `t_m` the visits to `x*`. -/
structure IsRun [Fintype X] [DecidableEq X] (m : Model X l) (cfg : Config l) {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (Φ : ℕ → Ω → X) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure μ
  measurableSet_preimage : ∀ n y, MeasurableSet (Φ n ⁻¹' {y})
  start : μ {ω | Φ 0 ω = m.xstar} = 1
  markov : ∀ (n : ℕ) (x : ℕ → X),
    μ {ω | ∀ i ≤ n + 1, Φ i ω = x i} =
      ENNReal.ofReal (m.P (m.stateAt cfg x n).θ (x n) (x (n + 1))) *
        μ {ω | ∀ i ≤ n, Φ i ω = x i}

/-- The time-step `t_k` of the `k`-th return to `x*` along the trajectory `x`, with `t₀ = 0`: the
first `n` at which `k` cycles are complete.

**Formalization Note** If the trajectory returns fewer than `k` times the set is empty and `sInf`
gives `0`. This does not matter: the trajectory returns infinitely often almost surely, and that
is a conclusion of Theorem 1. -/
noncomputable def Model.returnAt [DecidableEq X] (m : Model X l) (cfg : Config l) (x : ℕ → X)
    (k : ℕ) : ℕ :=
  sInf {n | (m.stateAt cfg x n).index = k}

/-- The parameter `θ_k` along the trajectory `x`: the state of the algorithm at time `t_k`. -/
noncomputable def Model.thetaAt [DecidableEq X] (m : Model X l) (cfg : Config l) (x : ℕ → X)
    (k : ℕ) : Param l :=
  (m.stateAt cfg x (m.returnAt cfg x k)).θ

/-- The estimate `Λ̃_k` along the trajectory `x`: the state of the algorithm at time `t_k`. -/
noncomputable def Model.lamAt [DecidableEq X] (m : Model X l) (cfg : Config l) (x : ℕ → X)
    (k : ℕ) : ℝ :=
  (m.stateAt cfg x (m.returnAt cfg x k)).Λ

/-- The iterate `r_k = (θ_k, Λ̃_k)` (p.23). -/
noncomputable def Model.iterate [DecidableEq X] (m : Model X l) (cfg : Config l) (x : ℕ → X)
    (k : ℕ) : Param l × ℝ :=
  (m.thetaAt cfg x k, m.lamAt cfg x k)

/-- The `k`-th observed excursion: the states `Φ_{t_k + 1}, …, Φ_{t_{k+1} - 1}` of the trajectory
`x`, strictly between the returns `t_k` and `t_{k+1}`. -/
noncomputable def Model.cycleAt [DecidableEq X] (m : Model X l) (cfg : Config l) (x : ℕ → X)
    (k : ℕ) : List X :=
  (List.range (m.returnAt cfg x (k + 1) - m.returnAt cfg x k - 1)).map fun i =>
    x (m.returnAt cfg x k + 1 + i)

/-- The mean drift `k_k(r) = (-f_k(r), η(g_k(r) - 1))` (p.23), with `f_k = f^(M_k)` and
`g_k = g^(M_k)`. -/
noncomputable def Model.drift (m : Model X l) (cfg : Config l) (k : ℕ) (r : Param l × ℝ) :
    Param l × ℝ :=
  (-m.fTrunc (cfg.M k) r.1 r.2, cfg.η * (m.gTruncReal (cfg.M k) r - 1))

/-- The stochastic version `K_k(r) = (-F_k(r), η(G_k(r) - 1))` of `k_k(r)` (p.24), on the excursion
`e`. -/
noncomputable def Model.stochDrift (m : Model X l) (cfg : Config l) (k : ℕ) (r : Param l × ℝ)
    (e : List X) : Param l × ℝ :=
  (-m.F (cfg.M k) r.1 r.2 e, cfg.η * (m.G (cfg.M k) r.1 r.2 e - 1))

/-- The stochastic noise `ε_k = γ_k (K_k(r_k) - k_k(r_k))` (pp.23–24) along the trajectory `x`.

**Formalization Note** It is defined from the unprojected `K_k` for both update rules, as Remark 2
(p.25) intends. -/
noncomputable def Model.noise [DecidableEq X] (m : Model X l) (cfg : Config l) (x : ℕ → X)
    (k : ℕ) : Param l × ℝ :=
  cfg.γ k • (m.stochDrift cfg k (m.iterate cfg x k) (m.cycleAt cfg x k) -
    m.drift cfg k (m.iterate cfg x k))

/-- The remainder `Δ_k(ψ_k) := ψ_k(r_{k+1}) - ψ_k(r_k) - γ_k ∇ψ_k(r_k) · k_k(r_k)` of Eq. (20) (p.25)
along the trajectory `x`. -/
noncomputable def Model.remainder [DecidableEq X] (m : Model X l) (cfg : Config l)
    (ψ : ℕ → Param l × ℝ → ℝ) (x : ℕ → X) (k : ℕ) : ℝ :=
  ψ k (m.iterate cfg x (k + 1)) - ψ k (m.iterate cfg x k) -
    cfg.γ k * fderiv ℝ (ψ k) (m.iterate cfg x k) (m.drift cfg k (m.iterate cfg x k))

/-- A **family of Lyapunov functions** (p.25): `{ψ_k}`, `{∇ψ_k}` and `{∇²ψ_k}` are uniformly bounded
over `ℝ^l × I` for any interval `I = [a, b]`, and moreover
`Σ_{k=0}^∞ sup_{r ∈ ℝ^l × I} ψ_{k+1}(r) - ψ_k(r) < ∞`.

**Formalization Note** The functions are taken twice differentiable, which is what `∇ψ_k` and
`∇²ψ_k` presuppose. The page prints the sum without absolute values, and so does this definition.
The printed sum is written through a majorant `d` with bounded partial sums. -/
def IsLyapunovFamily (ψ : ℕ → Param l × ℝ → ℝ) : Prop :=
  (∀ k, Differentiable ℝ (ψ k)) ∧ (∀ k, Differentiable ℝ (fderiv ℝ (ψ k))) ∧
    ∀ a b : ℝ,
      (∃ B : ℝ, ∀ k r, r.2 ∈ Set.Icc a b →
        |ψ k r| ≤ B ∧ ‖fderiv ℝ (ψ k) r‖ ≤ B ∧ ‖fderiv ℝ (fderiv ℝ (ψ k)) r‖ ≤ B) ∧
      ∃ (d : ℕ → ℝ) (B : ℝ), (∀ n, ∑ k ∈ Finset.range n, d k ≤ B) ∧
        ∀ k r, r.2 ∈ Set.Icc a b → ψ (k + 1) r - ψ k r ≤ d k

/-- The setting of Theorem 1(i) (p.11): `M_k = M` for all `k`, with `M > 1`. -/
def Config.FixedTruncation (cfg : Config l) (M : ℝ) : Prop :=
  1 < M ∧ ∀ k, cfg.M k = M

/-- The set `{N_i : N_i ≤ 1/γ_k^β}` of Theorem 1(ii) (p.11). -/
def Config.truncCandidates (cfg : Config l) (β : ℝ) (N : ℕ → ℝ) (k : ℕ) : Set ℝ :=
  {r | ∃ i, r = N i ∧ r ≤ 1 / cfg.γ k ^ β}

/-- The setting of Theorem 1(ii) (p.11): `Σ_k γ_k^{2(1-β)} < ∞` for some `β ∈ (0, 0.5)`, `N` satisfies
Assumption 4, and `M_k = sup{N_i : N_i ≤ 1/γ_k^β}`.

**Formalization Note** The set can be empty for finitely many `k`, where the page does not define
`M_k`. There `M_k` is any value above `1`, which covers every way of filling that case. -/
def Config.GrowingTruncation (m : Model X l) (cfg : Config l) (β : ℝ) (N : ℕ → ℝ) : Prop :=
  0 < β ∧ β < 1 / 2 ∧ Summable (fun k => cfg.γ k ^ (2 * (1 - β))) ∧ m.Assumption4 N ∧
    (∀ k, 1 < cfg.M k) ∧
    ∀ k, (cfg.truncCandidates β N k).Nonempty → cfg.M k = sSup (cfg.truncCandidates β N k)

/-- The two regimes of App. B (p.21), with their target function: `Λ^(M)_θ` when the truncation is
fixed at `M`, and `Λ_θ` when it grows as in Theorem 1(ii). "We focus on Theorem 1(ii) as the proof
of Theorem 1(i) follows by the exact same argument, replacing `Λ_θ` with `Λ^(M)_θ`." -/
def Config.Regime [Fintype X] (m : Model X l) (cfg : Config l) (target : Param l → ℝ) : Prop :=
  (∃ M, cfg.FixedTruncation M ∧ target = m.truncCost M) ∨
    ∃ β N, cfg.GrowingTruncation m β N ∧ target = m.riskCost

end RiskExpPG


