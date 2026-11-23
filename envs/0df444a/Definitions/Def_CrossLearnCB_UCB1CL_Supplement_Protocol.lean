-- Prove2me | Definitions.Def_CrossLearnCB_UCB1CL_Supplement_Protocol
-- name    : CrossLearnCB_UCB1CL_Supplement_Protocol
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T04:48:17.433247+00:00
-- url     : https://prove2.me/theorems/a44f93c8-1af3-4698-b524-587479c118ff
-- title:
--   §2.2–2.3 and App. A, pp. 9–11, 39–42 — adversarial-reward protocol with cross-learning feedback, policies, run law, ex ante/ex post regret, π_Stoc and π_Adv instances
-- statement:
--   The contextual bandit problem with cross-learning, with stochastic contexts, used by Theorems 2, 3, 7 and 8.
--
--   There are $K$ arms, $C$ contexts and $T$ rounds. In each round $t$ a context $c_t$ is drawn independently from a distribution $D$ on $[C]$, the learner pulls an arm $I_t$ and earns $r_{I_t,t}(c_t) \in [0,1]$. Each arm $i$ has a known **cross-learning graph** $G_i$ on $[C]$ with all self-loops; pulling $i$ in context $c$ also reveals $r_{i,t}(c')$ for every $c' \in O_i(c)$, the out-neighbours of $c$.
--
--   1. **Algorithms.** A (possibly randomized) algorithm knows $T$ and the graphs, and at round $t$ chooses a probability vector over arms from the record of the previous rounds (their contexts, pulled arms and revealed rewards) and the current context.
--   2. **Run law.** For an oblivious reward table $r = (r_{i,t}(c))$ fixed before the game, the probability of a trajectory $(c_t, I_t)_{t}$ is $\prod_t D(c_t)\, p_t(I_t)$, where $p_t$ is the algorithm's vector at round $t$; expectations are finite sums over trajectories.
--   3. **Ex ante regret** (Theorems 2–3). The benchmark plays $\pi(c) \in \arg\max_i \sum_t r_{i,t}(c)$; its expected reward is $\sum_c D(c) \max_i \sum_t r_{i,t}(c)$, and
--   $$\mathbb E[\mathrm{Reg}_{\mathrm{Ante}}(A)] = \sum_{c} D(c)\max_i \sum_{t} r_{i,t}(c) - \mathbb E\Big[\sum_t r_{I_t,t}(c_t)\Big].$$
--   4. **Ex post regret** (Theorem 7). The benchmark is best in hindsight for the realized contexts, $\pi_{\mathrm{Post}}(c) \in \arg\max_i \sum_t r_{i,t}(c)\,\mathbb 1(c_t = c)$:
--   $$\mathbb E[\mathrm{Reg}_{\mathrm{Post}}(A)] = \mathbb E\Big[\sum_c \max_i \sum_{t:\,c_t = c} r_{i,t}(c) - \sum_t r_{I_t,t}(c_t)\Big].$$
--   The instance of Theorem 7 has $K = 2$, uniform $D$, and for every round and context an independent fair coin deciding whether arm 1 pays $1$ and arm 2 pays $0$ or the reverse.
--   5. **Stochastic instances** (Theorem 8). A context distribution $D$ and laws $F_i(c)$ on $[0,1]$ with means $\mu_i(c)$; round vectors are independent and each $r_{i,t}(c)$ has law $F_i(c)$, with arbitrary correlation across arms and contexts within a round (p. 9, footnote 3). The regret against $\pi_{\mathrm{Stoc}}(c) \in \arg\max_i \mu_i(c)$ is $T\sum_c D(c)\max_i \mu_i(c) - \mathbb E[\sum_t r_{I_t,t}(c_t)]$.
--   6. **Adversarial instances** (Theorem 8). A context distribution $D$ and a law of reward tables in $[0,1]$, independent of the contexts and of the algorithm (a fixed table is a point mass). The regret against $\pi_{\mathrm{Adv}}(c) \in \arg\max_i \sum_t r_{i,t}(c)$ for the realized table is the expected ex ante regret, averaged over the table.
--
--   **Formalization Note** Rounds are 0-based (`t : Fin T` is the paper's round $t+1$), arms are `Fin K` (arm `0` is the paper's arm 1), contexts `Fin C`. A policy is a function of the round, the record and the current context returning a weight per arm; `IsValid` says these are probability vectors and `IsMeasurable` that they depend measurably on the record (needed to integrate over random tables). The revealed rewards of a round are stored as a vector over contexts that is $0$ off $O_{I_t}(c_t)$; the learner knows the graphs, so nothing is lost. Benchmarks are written as maxima (`Finset.sup'`), so the choice among tied arg-maxima does not matter. `IsDistribution D` says $D \ge 0$ and $\sum_c D(c) = 1$.
--
--   The round-vector law may vary with time while its coordinate marginals remain $F_i(c)$. `IsCoordinateIndependent` selects the product coupling at each round; Lemma 6 and Theorems 5–6 explicitly require their hard witnesses to satisfy this property.
-- source:
--   Balseiro et al., Contextual Bandits with Cross-Learning, arXiv:1809.09582v3, pp. 9–11, §2.2–2.3 (benchmarks p. 10, CL graphs p. 11); p. 39, App. A (Reg_Ante, Reg_Post); p. 40, proof of Theorem 7 (instance); pp. 41–42, App. A.1 (π_Stoc, π_Adv)

import Mathlib
import Definitions.Def_CrossLearnCB_UCB1CL_Model

namespace CrossLearnCB.UCB1CL.Supplement

open MeasureTheory

/-! ### The contextual bandit protocol with cross-learning (§2.2–2.3, pp. 9–11)

Arms are `Fin K`, contexts `Fin C`, rounds are the 0-based `t : Fin T` (the paper's round
`t + 1`). `G i c c'` is the edge `c → c'` of the cross-learning graph `G_i` (the encoding of the
published `CrossLearnCB.UCB1CL.Model`): pulling arm `i` in context `c` reveals `r_{i,t}(c')`.
An oblivious reward table is `r : Fin T → Fin K → Fin C → ℝ`, `r t i c = r_{i,t}(c)`. -/

/-- What the learner records about one past round: the context, the pulled arm, and the
revealed rewards of that arm, as a vector over contexts whose entry is `0` at every context
whose reward was not revealed (the learner knows the graphs, so it knows which entries are
revealed). -/
abbrev Obs (K C : ℕ) := Fin C × Fin K × (Fin C → ℝ)

/-- A (possibly randomized) algorithm, in behavioural form: at round `t`, from the record of
rounds `0, …, t-1` and the current context, a weight for each arm (its probability of being
pulled). It is chosen knowing `T` and the graphs. -/
def Policy (K C : ℕ) : Type := (t : ℕ) → (Fin t → Obs K C) → Fin C → Fin K → ℝ

/-- The weights of a policy are probability vectors. -/
def Policy.IsValid {K C : ℕ} (A : Policy K C) : Prop :=
  (∀ t h c i, 0 ≤ A t h c i) ∧ ∀ t h c, ∑ i, A t h c i = 1

/-- The arm probabilities are measurable functions of the record (needed for expectations over
a random reward table). -/
def Policy.IsMeasurable {K C : ℕ} (A : Policy K C) : Prop :=
  ∀ t c i, Measurable (fun h : Fin t → Obs K C => A t h c i)

/-- A probability vector on contexts (the context distribution `D`). -/
def IsDistribution {C : ℕ} (D : Fin C → ℝ) : Prop :=
  (∀ c, 0 ≤ D c) ∧ ∑ c, D c = 1

open Classical in
/-- The rewards revealed by pulling arm `i` in context `c` at round `t`: `r_{i,t}(c')` for every
`c' ∈ O_i(c)` (edge `c → c'`), and `0` elsewhere. -/
noncomputable def feedback {K C T : ℕ} (G : Fin K → Fin C → Fin C → Prop)
    (r : Fin T → Fin K → Fin C → ℝ) (t : Fin T) (c : Fin C) (i : Fin K) : Fin C → ℝ :=
  fun c' => if G i c c' then r t i c' else 0

/-- A trajectory `τ` lists the context `(τ t).1` and the pulled arm `(τ t).2` of every round.
`hist G r τ t` is the learner's record of rounds `0, …, t-1` along it. -/
noncomputable def hist {K C T : ℕ} (G : Fin K → Fin C → Fin C → Prop)
    (r : Fin T → Fin K → Fin C → ℝ) (τ : Fin T → Fin C × Fin K) (t : Fin T) :
    Fin t → Obs K C :=
  fun s =>
    let u : Fin T := Fin.castLE t.2.le s
    ((τ u).1, (τ u).2, feedback G r u (τ u).1 (τ u).2)

/-- The probability of a trajectory when contexts are i.i.d. `D` and the policy `A` plays
against the oblivious table `r`: `∏_t D(c_t) · A_t(history, c_t)(I_t)`. -/
noncomputable def trajProb {K C T : ℕ} (G : Fin K → Fin C → Fin C → Prop) (D : Fin C → ℝ)
    (A : Policy K C) (r : Fin T → Fin K → Fin C → ℝ) (τ : Fin T → Fin C × Fin K) : ℝ :=
  ∏ t : Fin T, D (τ t).1 * A t (hist G r τ t) (τ t).1 (τ t).2

/-- Expectation of a function of the trajectory over contexts and the algorithm's randomness,
for a fixed table `r`. -/
noncomputable def expect {K C T : ℕ} (G : Fin K → Fin C → Fin C → Prop) (D : Fin C → ℝ)
    (A : Policy K C) (r : Fin T → Fin K → Fin C → ℝ) (X : (Fin T → Fin C × Fin K) → ℝ) : ℝ :=
  ∑ τ, trajProb G D A r τ * X τ

/-- Expected total reward of the algorithm, `E[Σ_t r_{I_t,t}(c_t)]`, for a fixed table. -/
noncomputable def algReward {K C T : ℕ} (G : Fin K → Fin C → Fin C → Prop) (D : Fin C → ℝ)
    (A : Policy K C) (r : Fin T → Fin K → Fin C → ℝ) : ℝ :=
  expect G D A r (fun τ => ∑ t, r t (τ t).2 (τ t).1)

/-- The ex ante benchmark (§2.2, p. 10; Appendix A, p. 39): the expected reward
`E[Σ_t r_{π(c_t),t}(c_t)] = Σ_c Pr[c] Σ_t r_{π(c),t}(c)` of `π(c) ∈ argmax_i Σ_t r_{i,t}(c)`,
written as `Σ_c D(c) · max_i Σ_t r_{i,t}(c)` so that ties do not matter. -/
noncomputable def exAnteBenchmark {K C T : ℕ} [NeZero K] (D : Fin C → ℝ)
    (r : Fin T → Fin K → Fin C → ℝ) : ℝ :=
  ∑ c, D c * Finset.univ.sup' Finset.univ_nonempty (fun i => ∑ t, r t i c)

/-- Expected ex ante regret `E[Reg_Ante(A)]` against the oblivious table `r`. -/
noncomputable def exAnteRegret {K C T : ℕ} [NeZero K] (G : Fin K → Fin C → Fin C → Prop)
    (D : Fin C → ℝ) (A : Policy K C) (r : Fin T → Fin K → Fin C → ℝ) : ℝ :=
  exAnteBenchmark D r - algReward G D A r

open Classical in
/-- Expected ex post regret `E[Reg_Post(A)]` (Appendix A, p. 39) against the table `r`: the
benchmark `π_Post(c) ∈ argmax_i Σ_t r_{i,t}(c) I(c_t = c)` is best in hindsight for the realized
contexts, with value `Σ_c max_i Σ_{t : c_t = c} r_{i,t}(c)`. -/
noncomputable def exPostRegret {K C T : ℕ} [NeZero K] (G : Fin K → Fin C → Fin C → Prop)
    (D : Fin C → ℝ) (A : Policy K C) (r : Fin T → Fin K → Fin C → ℝ) : ℝ :=
  expect G D A r (fun τ =>
    (∑ c, Finset.univ.sup' Finset.univ_nonempty
        (fun i => ∑ t ∈ Finset.univ.filter (fun t => (τ t).1 = c), r t i c))
      - ∑ t, r t (τ t).2 (τ t).1)

/-! ### The instance of the proof of Theorem 7 (p. 40) -/

/-- The uniform distribution on `C` contexts. -/
noncomputable def uniformDist (C : ℕ) : Fin C → ℝ := fun _ => 1 / (C : ℝ)

/-- The two-arm reward table of a coin pattern `b`: in round `t` and context `c`, arm `0`
(the paper's arm 1) pays `1` and arm `1` pays `0` if `b t c`, and the other way round
otherwise. -/
noncomputable def coinTable {C T : ℕ} (b : Fin T → Fin C → Bool) : Fin T → Fin 2 → Fin C → ℝ :=
  fun t i c => if (b t c = true ↔ i = 0) then 1 else 0

/-- Expected ex post regret on the instance of the proof of Theorem 7: uniform contexts, and
each `(t, c)` independently a fair coin choosing which arm pays `1` (the average over all
coin patterns). -/
noncomputable def coinExPostRegret (T C : ℕ) (G : Fin 2 → Fin C → Fin C → Prop)
    (A : Policy 2 C) : ℝ :=
  (Fintype.card (Fin T → Fin C → Bool) : ℝ)⁻¹ *
    ∑ b : Fin T → Fin C → Bool, exPostRegret G (uniformDist C) A (coinTable b)

/-! ### Stochastic and randomized adversarial instances (Appendix A.1, pp. 41–42) -/

/-- An instance with stochastic rewards and contexts: a context distribution `D` and, for
every arm and context, a law `F_i(c)` on `[0, 1]`. Round vectors are independent;
within a round the coordinates may be correlated (p. 9, footnote 3), with any coupling
of the fixed marginals at each time. -/
structure StochInstance (K C : ℕ) where
  D : Fin C → ℝ
  F : Fin K → Fin C → Measure ℝ
  D_dist : IsDistribution D
  F_prob : ∀ i c, IsProbabilityMeasure (F i c)
  F_supp : ∀ i c, F i c (Set.Icc (0 : ℝ) 1)ᶜ = 0
  roundLaw : ℕ → Measure (Fin K → Fin C → ℝ)
  round_prob : ∀ t, IsProbabilityMeasure (roundLaw t)
  round_marginal : ∀ t i c, Measure.map (fun x => x i c) (roundLaw t) = F i c

/-- Independent coordinates, the source's default stochastic model (p. 9).
The lower bounds retain witnesses in this class; the transfer also covers footnote 3. -/
def StochInstance.IsCoordinateIndependent {K C : ℕ} (S : StochInstance K C) : Prop :=
  ∀ t, S.roundLaw t =
    Measure.pi (fun i : Fin K => Measure.pi (fun c : Fin C => S.F i c))

/-- The law of the reward table: independent round vectors with time-independent coordinate
marginals `F_i(c)`, allowing the within-round correlations of p. 9, footnote 3. -/
noncomputable def StochInstance.tableLaw {K C : ℕ} (S : StochInstance K C) (T : ℕ) :
    Measure (Fin T → Fin K → Fin C → ℝ) :=
  Measure.pi fun t : Fin T => S.roundLaw t

/-- The mean `μ_i(c)` of `F_i(c)`. -/
noncomputable def StochInstance.mean {K C : ℕ} (S : StochInstance K C) (i : Fin K)
    (c : Fin C) : ℝ :=
  ∫ x, x ∂(S.F i c)

/-- Expected regret with stochastic rewards and contexts against `π_Stoc(c) ∈ argmax_i μ_i(c)`:
`E[Σ_t (r_{π_Stoc(c_t),t}(c_t) − r_{I_t,t}(c_t))] = T Σ_c D(c) max_i μ_i(c) − E[Σ_t r_{I_t,t}(c_t)]`,
the expectation over rewards, contexts and the algorithm's randomness. -/
noncomputable def stochRegret {K C : ℕ} [NeZero K] (T : ℕ) (G : Fin K → Fin C → Fin C → Prop)
    (S : StochInstance K C) (A : Policy K C) : ℝ :=
  (T : ℝ) * ∑ c, S.D c * Finset.univ.sup' Finset.univ_nonempty (fun i => S.mean i c)
    - ∫ r, algReward G S.D A r ∂(S.tableLaw T)

/-- An instance with adversarial rewards and stochastic contexts: a context distribution `D`
and a (possibly randomized) reward table with values in `[0, 1]`, drawn independently of the
contexts and of the algorithm (a deterministic table is a Dirac law). -/
structure AdvInstance (K C T : ℕ) where
  D : Fin C → ℝ
  law : Measure (Fin T → Fin K → Fin C → ℝ)
  D_dist : IsDistribution D
  law_prob : IsProbabilityMeasure law
  law_supp : ∀ᵐ r ∂law, ∀ t i c, r t i c ∈ Set.Icc (0 : ℝ) 1

/-- Expected regret with adversarial rewards and stochastic contexts against
`π_Adv(c) ∈ argmax_i Σ_t r_{i,t}(c)` for the realized table, the expectation over contexts,
the table and the algorithm's randomness. -/
noncomputable def advRegret {K C T : ℕ} [NeZero K] (G : Fin K → Fin C → Fin C → Prop)
    (V : AdvInstance K C T) (A : Policy K C) : ℝ :=
  ∫ r, exAnteRegret G V.D A r ∂V.law

end CrossLearnCB.UCB1CL.Supplement


