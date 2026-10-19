-- Prove2me | Definitions.Def_SeqSocialLearning_Adequate_Model
-- name    : SeqSocialLearning_Adequate_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:13:29.81688+00:00
-- url     : https://prove2.me/theorems/8bd12207-221d-4e10-a406-31b79ebf8a4e
-- title:
--   §2, pp. 3–4 — sequential social learning game: utility class U, mixed strategy profiles, play measure Pσ, PBE, asymptotic and adequate learning
-- statement:
--   A **social learning model** $(\Omega, \mu, A, S, F)$ has a state space $\Omega$, a prior $\mu \in \Delta(\Omega)$, an action space $A$, a signal space $S$ and a Markov kernel $F : \Omega \to \Delta(S)$.
--
--   1. **Utility class.** $U$ is the set of bounded, jointly measurable $u : A \times \Omega \to \mathbb R$ such that $a \mapsto u(a, \omega)$ is continuous for every $\omega$. The maximal payoff is $O(\omega) = \max_{a \in A} u(a, \omega)$.
--   2. **Strategies.** A state $\omega \sim \mu$ is drawn once. Agents act in sequence. Agent $t$ observes the actions $h_t$ of its predecessors and a private signal $s_t \sim F_\omega$, drawn conditionally i.i.d. given $\omega$. A (mixed) strategy of agent $t$ is a Markov kernel $\sigma_t : A^{t} \times S \to \Delta(A)$ (in the paper's numbering, agent $t$ sees $A^{t-1}$).
--   3. **Play measure.** $P_\sigma$ is the joint law of the state, the signals and the actions induced by $\mu$, $F$ and the profile $\sigma = (\sigma_t)_t$. It is constructed by the Ionescu-Tulcea theorem.
--   4. **Perfect Bayesian equilibrium.** $\sigma$ is a PBE if each $\sigma_t$ maximizes agent $t$'s expected utility $E_\sigma[u(a_t, \omega)]$ given the strategies of all other agents:
--   $$
--   E_{\sigma_{-t}, \tau}[u(a_t,\omega)] \le E_\sigma[u(a_t,\omega)] \quad \text{for every } t \text{ and every strategy } \tau \text{ of agent } t.
--   $$
--   5. **Learning.** Asymptotic learning holds for $u$ if, for every PBE $\sigma$, the realized payoff $y_t = u(a_t, \omega)$ converges $P_\sigma$-almost surely to $O(\omega)$. Adequate learning holds if asymptotic learning holds for every $u \in U$.
--
--   These are the objects of Theorem 1, the paper's main result.
--
--   **Formalization Note** Agents are indexed from $0$: Lean's agent $t$ is the paper's agent $t+1$ and sees the history `Fin t → A`; limits as $t\to\infty$ are unaffected. A trajectory is a sequence of triples $(\omega, s_t, a_t)$; the state is copied into every coordinate and read from coordinate $0$. Equilibrium optimality is ex ante, against every measurable mixed deviation, which is the definition on p. 4. The model's topological and measurability assumptions (separable complete metric $\Omega$, compact metric $A$ with two or more actions, standard Borel $S$, the standing assumptions on $F$) are hypotheses of each theorem.
-- source:
--   Arieli & Mueller-Frank, A General Analysis of Sequential Social Learning, SSRN 2466903 (version of February 21, 2019), pp. 3–4, §2 The Model

import Mathlib

namespace SeqSocialLearning.Adequate

open MeasureTheory ProbabilityTheory Filter Topology Finset

variable {Ω A S : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace S]

/-- The utility class `U` (§2, p. 3): bounded, jointly measurable utilities `u : A × Ω → ℝ`
that are continuous in the action for every fixed state. -/
def InU [TopologicalSpace A] (u : A → Ω → ℝ) : Prop :=
  Measurable (Function.uncurry u) ∧ (∃ M : ℝ, ∀ a ω, |u a ω| ≤ M) ∧
    ∀ ω, Continuous fun a => u a ω

/-- The maximal payoff `O(ω) = max_{a ∈ A} u(a, ω)` (§2, p. 4). -/
noncomputable def maxPayoff (u : A → Ω → ℝ) (ω : Ω) : ℝ :=
  ⨆ a, u a ω

variable (A S) in
/-- A (mixed) strategy profile (§2, p. 4). Agents are indexed from `0`: agent `t` (the paper's
agent `t + 1`) observes the history `Fin t → A` of its predecessors' actions and its private
signal, and draws an action from the probability measure `σ t (h, s)`. -/
structure Profile where
  /-- the strategy of agent `t` -/
  σ : (t : ℕ) → Kernel ((Fin t → A) × S) A
  /-- each strategy assigns a probability measure on actions -/
  markov : ∀ t, IsMarkovKernel (σ t)

instance (p : Profile A S) (t : ℕ) : IsMarkovKernel (p.σ t) := p.markov t

/-- The profile in which agent `t` deviates to the strategy `τ` and everybody else keeps `p`. -/
noncomputable def Profile.replace (p : Profile A S) (t : ℕ)
    (τ : Kernel ((Fin t → A) × S) A) [IsMarkovKernel τ] : Profile A S where
  σ := Function.update p.σ t τ
  markov := by
    intro n
    by_cases h : n = t
    · subst h
      rw [Function.update_self]
      infer_instance
    · rw [Function.update_of_ne h]
      infer_instance

/-- From the trajectory up to time `n`, read the state (stored in coordinate `0`) and the
history of actions `a₀, …, aₙ`. -/
def stateHist (n : ℕ) (x : (i : Iic n) → Ω × S × A) : Ω × (Fin (n + 1) → A) :=
  ((x ⟨0, Finset.mem_Iic.2 (Nat.zero_le n)⟩).1,
    fun i => (x ⟨i.1, Finset.mem_Iic.2 (Nat.lt_succ_iff.1 i.2)⟩).2.2)

lemma measurable_stateHist (n : ℕ) : Measurable (stateHist (Ω := Ω) (S := S) (A := A) n) := by
  unfold stateHist
  refine Measurable.prodMk ?_ ?_
  · exact measurable_fst.comp (measurable_pi_apply _)
  · exact measurable_pi_lambda _ fun i =>
      (measurable_snd.comp measurable_snd).comp (measurable_pi_apply _)

/-- Agent `n + 1`'s step: the state is copied, a fresh signal `s ~ F ω` is drawn, and the
action is drawn from `σ (n+1) ((a₀, …, aₙ), s)`. -/
noncomputable def stepKernel (F : Kernel Ω S) [IsMarkovKernel F] (p : Profile A S) (n : ℕ) :
    Kernel ((i : Iic n) → Ω × S × A) (Ω × S × A) :=
  (Kernel.deterministic (Prod.fst : Ω × (Fin (n + 1) → A) → Ω) measurable_fst ×ₖ
    ((F.comap (Prod.fst : Ω × (Fin (n + 1) → A) → Ω) measurable_fst) ⊗ₖ
      ((p.σ (n + 1)).comap
        (fun q : (Ω × (Fin (n + 1) → A)) × S => (q.1.2, q.2))
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))).comap
    (stateHist n) (measurable_stateHist n)

instance (F : Kernel Ω S) [IsMarkovKernel F] (p : Profile A S) (n : ℕ) :
    IsMarkovKernel (stepKernel F p n) := by
  unfold stepKernel
  infer_instance

/-- Time `0`: the state `ω ~ µ`, agent `0`'s signal `s₀ ~ F ω`, and its action
`a₀ ~ σ 0 (∅, s₀)`. -/
noncomputable def initMeasure (μ : Measure Ω) (F : Kernel Ω S) [IsMarkovKernel F]
    (p : Profile A S) : Measure (Ω × S × A) :=
  μ ⊗ₘ (F ⊗ₖ ((p.σ 0).comap (fun q : Ω × S => ((Fin.elim0 : Fin 0 → A), q.2))
    (measurable_const.prodMk measurable_snd)))

/-- The play measure `Pσ` (§2, p. 4): the joint law of the state, the signals and the actions,
built by the Ionescu-Tulcea theorem. Coordinate `t` of a trajectory is `(ω, s_t, a_t)`; the state
is stored (identically) in every coordinate and read from coordinate `0`. -/
noncomputable def playMeasure (μ : Measure Ω) (F : Kernel Ω S) [IsMarkovKernel F]
    (p : Profile A S) : Measure (ℕ → Ω × S × A) :=
  Kernel.trajMeasure (X := fun _ => Ω × S × A) (initMeasure μ F p) (stepKernel F p)

instance (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Kernel Ω S) [IsMarkovKernel F]
    (p : Profile A S) : IsProbabilityMeasure (initMeasure μ F p) := by
  unfold initMeasure
  infer_instance

instance (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Kernel Ω S) [IsMarkovKernel F]
    (p : Profile A S) : IsProbabilityMeasure (playMeasure μ F p) := by
  unfold playMeasure
  infer_instance

/-- The realized state `ω`. -/
def state (x : ℕ → Ω × S × A) : Ω := (x 0).1

/-- The private signal `s_t` of agent `t`. -/
def signal (x : ℕ → Ω × S × A) (t : ℕ) : S := (x t).2.1

/-- The realized action `a_t` of agent `t`. -/
def action (x : ℕ → Ω × S × A) (t : ℕ) : A := (x t).2.2

/-- The history `h_t = (a₀, …, a_{t-1})` observed by agent `t`. -/
def history (x : ℕ → Ω × S × A) (t : ℕ) : Fin t → A := fun i => action x i

/-- The infinite history `h_∞ = (a₀, a₁, …)`. -/
def fullHistory (x : ℕ → Ω × S × A) : ℕ → A := fun i => action x i

/-- Perfect Bayesian equilibrium as defined on p. 4: each strategy `σ_t` maximizes the
(ex-ante) expected utility `E_σ[u(a_t, ω)]` of agent `t` given the strategies of all other agents,
i.e. no agent gains by a unilateral change of its own (mixed) strategy. -/
def IsPBE (μ : Measure Ω) (F : Kernel Ω S) [IsMarkovKernel F] (u : A → Ω → ℝ)
    (p : Profile A S) : Prop :=
  ∀ (t : ℕ) (τ : Kernel ((Fin t → A) × S) A) [IsMarkovKernel τ],
    ∫ x, u (action x t) (state x) ∂(playMeasure μ F (p.replace t τ)) ≤
      ∫ x, u (action x t) (state x) ∂(playMeasure μ F p)

/-- Asymptotic learning holds for `u` (§2, p. 4): in every perfect Bayesian equilibrium the
realized payoff `y_t = u(a_t, ω)` converges `Pσ`-almost surely to the maximal payoff `O(ω)`. -/
def AsymptoticLearning (μ : Measure Ω) (F : Kernel Ω S) [IsMarkovKernel F]
    (u : A → Ω → ℝ) : Prop :=
  ∀ p : Profile A S, IsPBE μ F u p →
    ∀ᵐ x ∂(playMeasure μ F p),
      Tendsto (fun t => u (action x t) (state x)) atTop (𝓝 (maxPayoff u (state x)))

/-- Adequate learning holds (§2, p. 4): asymptotic learning holds for every utility `u ∈ U`. -/
def AdequateLearning [TopologicalSpace A] (μ : Measure Ω) (F : Kernel Ω S) [IsMarkovKernel F] :
    Prop :=
  ∀ u : A → Ω → ℝ, InU u → AsymptoticLearning (S := S) μ F u

end SeqSocialLearning.Adequate


