-- Prove2me | Definitions.Def_StochKnapSL_CapacityGap_Model
-- name    : StochKnapSL_CapacityGap_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:19:38.691208+00:00
-- url     : https://prove2.me/theorems/6a90a948-4eca-46ed-9a62-4e805aae35d5
-- title:
--   §1, §3.1, §3.3, p. 20 — capacity pooling with Type-I service: allocation runs, adaptive and anticipative randomized policies, Γ(Q), Q^Anti_I, Q^Adap_I, Q_II
-- statement:
--   This file sets up the capacity pooling problem of Lyu, Chou, Teo, Zheng and Zhong, in which a planner allocates a single pool of $Q \ge 0$ units of capacity among $N$ customers $i = 1, \dots, N$ with random demands $\tilde d = (\tilde d_1, \dots, \tilde d_N)$ on a probability space $(\Omega, \mathcal F, \mathbf P)$.
--
--   1. **Allocation run.** Customers are served one at a time. When a customer is chosen, she is **fully served** if her demand does not exceed the remaining capacity, and that demand is deducted. Otherwise she receives what is left and is not fully served, and the run stops. The run also stops when the planner chooses nobody.
--   2. **Adaptive policy** ($\Pi^{\mathrm{Adap}}$). The next customer is a function of the customers chosen so far and of their realized demands, and of nothing else. Every decision event is measurable.
--   3. **Anticipative policy** ($\Pi^{\mathrm{Anti}}$). A priority order $\sigma$ is fixed before the demands are realized, and customers are chosen in that order. Each anticipative policy is in particular an adaptive one.
--   4. **Randomized policies** are finite mixtures $\pi = \sum_k w_k A_k$ of deterministic policies, with weights $w_k \ge 0$ and $\sum_k w_k = 1$, chosen independently of the demands. The **Type-I service level** of customer $i$ is
--   $$ \mathbf P^\pi_Q(i \text{ fully served}) = \sum_k w_k\, \mathbf P\big(i \text{ fully served by } A_k \text{ with capacity } Q\big). $$
--   5. **Optimal Type-I capacities.** Given targets $\alpha \in [0,1]^N$, a capacity $Q \ge 0$ is feasible for a class if some randomized policy of that class has $\mathbf P^\pi_Q(i \text{ fully served}) \ge \alpha_i$ for every $i$. Then $Q^{\mathrm{Adap}}_I$ and $Q^{\mathrm{Anti}}_I$ are the infima of the feasible capacities, i.e. the optimal values of problem (CPP-A) over the two classes.
--   6. **Type-II side.** $\Gamma(Q)$ is the set of $\alpha$ with
--   $$ \sum_{i\in U} \alpha_i\, \mathbf E[\tilde d_i] \le \mathbf E\Big[\min\Big(Q, \sum_{i\in U} \tilde d_i\Big)\Big] \quad \text{for all } U \subseteq \{1,\dots,N\}, $$
--   and $Q_{II}$ is the least $Q \ge 0$ with $\alpha \in \Gamma(Q)$, the optimal value of (CPP-B).
--   7. **Greedy fill.** For a priority order $\sigma$ the greedy solution of the fractional knapsack (CPP-F) gives customer $i$ the amount $x^*_i = \min\{\tilde d_i, \max(0, Q - \sum_{j \text{ ahead of } i} \tilde d_j)\}$.
--   8. **Standing assumptions** (§3.3). The demands are measurable, independent and positive, almost surely bounded by a constant $\Delta > 0$, and $0 \le \alpha_i \le 1$.
--
--   These objects are the vocabulary of Theorems 3–5 of the paper, which compare the capacity anticipative policies need with what adaptive policies need.
--
--   **Formalization Note.** The paper defines service levels as long-run frequencies over sampled scenarios (p. 11). Here they are probabilities, and randomization is written as a finite mixture. A run has at most $N$ steps, ties go to service (demand equal to the remaining capacity is served), and an anticipative policy also stops at the first customer it cannot fully serve (p. 37). $Q_{II}$ is defined through the subset form $\Gamma(Q)$, which p. 17 shows to be equivalent to the Type-II problem (CPP-B). The greedy fill is stated for a priority order $\sigma$, which is the paper's $x^*(\theta', \tilde d, Q)$ for any $\theta'$ whose decreasing order, ties broken by index (footnote 4, p. 16), is $\sigma$. All optimal capacities are real infima. They are not assumed to be attained.
-- source:
--   Lyu, Chou, Teo, Zheng & Zhong, Stochastic Knapsack Revisited: The Service Level Perspective, SSRN working paper 3674463 (version of 2021-05-29), pp. 2–3, 11, 15–17, 19–20, 24, 37; §1, §3.1, §3.3 (CPP-A), (CPP-F), (CPP-B), §4 Γ(Q), Appendix A.3

import Mathlib

namespace StochKnapSL.CapacityGap

open MeasureTheory ProbabilityTheory

/-- State of an allocation run (Lyu et al., §1 pp. 2–3, §3.1 p. 11, p. 37): the customers chosen so far
(in order), the customers fully served so far (in order), the remaining capacity, and whether the run
has stopped. -/
structure RunState (N : ℕ) where
  chosen : List (Fin N)
  full : List (Fin N)
  rem : ℝ
  stopped : Bool

/-- One step of an allocation run, given the planner's choice `c` and the demand vector `x`.
A stopped run is unchanged; choosing nobody or an already chosen customer stops the run. A chosen
customer whose demand does not exceed the remaining capacity is fully served and her demand is
deducted; otherwise she receives the remaining capacity, is not fully served, and the run stops
(p. 19 "served only if her demand requirement does not exceed the remaining capacity"; p. 24; p. 37). -/
noncomputable def step {N : ℕ} (c : Option (Fin N)) (x : Fin N → ℝ) (s : RunState N) : RunState N :=
  if s.stopped then s else
    match c with
    | none => { s with stopped := true }
    | some c =>
      if c ∈ s.chosen then { s with stopped := true }
      else if x c ≤ s.rem then
        { chosen := s.chosen ++ [c], full := s.full ++ [c], rem := s.rem - x c, stopped := false }
      else
        { chosen := s.chosen ++ [c], full := s.full, rem := 0, stopped := true }

/-- A deterministic **adaptive policy** (§1, p. 2, item (2)): the next customer to serve is chosen as a
function of the list of customers already chosen and of the demand vector, but may depend only on the
realized demands of the customers already chosen (`nonanticipative`). Each decision event is
measurable. `none` means "serve nobody further". -/
structure AdaptivePolicy (N : ℕ) where
  next : List (Fin N) → (Fin N → ℝ) → Option (Fin N)
  nonanticipative : ∀ (l : List (Fin N)) (x x' : Fin N → ℝ),
    (∀ j ∈ l, x j = x' j) → next l x = next l x'
  measurable_next : ∀ (l : List (Fin N)) (c : Option (Fin N)),
    MeasurableSet {x : Fin N → ℝ | next l x = c}

/-- The run of policy `P` with capacity `Q` on demand vector `x`: `N` steps from the initial state
(nobody chosen, remaining capacity `Q`). -/
noncomputable def run {N : ℕ} (P : AdaptivePolicy N) (Q : ℝ) (x : Fin N → ℝ) : RunState N :=
  (fun s => step (P.next s.chosen x) x s)^[N] ⟨[], [], Q, false⟩

/-- Customer `i` is fully served by policy `P` with capacity `Q` on demand vector `x`
(the event `y^A_i = 1` of p. 11). -/
def fullyServed {N : ℕ} (P : AdaptivePolicy N) (Q : ℝ) (x : Fin N → ℝ) (i : Fin N) : Prop :=
  i ∈ (run P Q x).full

/-- Customer `i` is reached (chosen) by the run: she is fully served, or she is the one customer
turned away when capacity ran out (p. 37). -/
def reached {N : ℕ} (P : AdaptivePolicy N) (Q : ℝ) (x : Fin N → ℝ) (i : Fin N) : Prop :=
  i ∈ (run P Q x).chosen

noncomputable instance {N : ℕ} (P : AdaptivePolicy N) (Q : ℝ) (x : Fin N → ℝ) (i : Fin N) :
    Decidable (fullyServed P Q x i) :=
  inferInstanceAs (Decidable (i ∈ (run P Q x).full))

noncomputable instance {N : ℕ} (P : AdaptivePolicy N) (Q : ℝ) (x : Fin N → ℝ) (i : Fin N) :
    Decidable (reached P Q x i) :=
  inferInstanceAs (Decidable (i ∈ (run P Q x).chosen))

/-- A deterministic **anticipative policy** (§1, pp. 2–3, item (3)) is a priority order fixed before
the demands are realized; `σ k` is the customer in position `k`. It is run as the adaptive policy
that always chooses the first customer in the order not yet chosen, ignoring the demands. -/
def priority {N : ℕ} (σ : Equiv.Perm (Fin N)) : AdaptivePolicy N where
  next l _ := (List.ofFn σ).find? (fun c => decide (c ∉ l))
  nonanticipative := fun _ _ _ _ => rfl
  measurable_next := fun _ _ => MeasurableSet.const _

/-- A **randomized policy**: a finite mixture, with probability weights `w`, of deterministic
policies `pol k`; the randomization is independent of the demands. -/
structure Mixture (P : Type*) where
  m : ℕ
  w : Fin m → ℝ
  pol : Fin m → P
  w_nonneg : ∀ k, 0 ≤ w k
  w_sum : ∑ k, w k = 1

/-- Push a mixture forward along a map of policies (same weights). -/
def Mixture.map {P P' : Type*} (f : P → P') (π : Mixture P) : Mixture P' where
  m := π.m
  w := π.w
  pol := fun k => f (π.pol k)
  w_nonneg := π.w_nonneg
  w_sum := π.w_sum

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Type-I service level of customer `i` under the randomized adaptive policy `π` with capacity `Q`:
the probability that she is fully served. -/
noncomputable def serviceProb (μ : Measure Ω) {N : ℕ} (d : Fin N → Ω → ℝ)
    (π : Mixture (AdaptivePolicy N)) (Q : ℝ) (i : Fin N) : ℝ :=
  ∑ k, π.w k * μ.real {ω | fullyServed (π.pol k) Q (fun j => d j ω) i}

/-- Capacity `Q ≥ 0` is feasible for (CPP-A) within the class of (randomized) adaptive policies:
some policy fully serves every customer `i` with probability at least `α i`. -/
def AdapFeasible (μ : Measure Ω) {N : ℕ} (d : Fin N → Ω → ℝ) (α : Fin N → ℝ) (Q : ℝ) : Prop :=
  0 ≤ Q ∧ ∃ π : Mixture (AdaptivePolicy N), ∀ i, α i ≤ serviceProb μ d π Q i

/-- Capacity `Q ≥ 0` is feasible for (CPP-A) within the class of (randomized) anticipative policies. -/
def AntiFeasible (μ : Measure Ω) {N : ℕ} (d : Fin N → Ω → ℝ) (α : Fin N → ℝ) (Q : ℝ) : Prop :=
  0 ≤ Q ∧ ∃ π : Mixture (Equiv.Perm (Fin N)), ∀ i, α i ≤ serviceProb μ d (π.map priority) Q i

/-- `Q^Adap_I`: the optimal Type-I capacity under adaptive policies (p. 16). -/
noncomputable def QAdap (μ : Measure Ω) {N : ℕ} (d : Fin N → Ω → ℝ) (α : Fin N → ℝ) : ℝ :=
  sInf {Q | AdapFeasible μ d α Q}

/-- `Q^Anti_I`: the optimal Type-I capacity under anticipative policies (p. 16). -/
noncomputable def QAnti (μ : Measure Ω) {N : ℕ} (d : Fin N → Ω → ℝ) (α : Fin N → ℝ) : ℝ :=
  sInf {Q | AntiFeasible μ d α Q}

/-- `α ∈ Γ(Q)` (p. 20): for every subset `U` of customers,
`∑_{i∈U} α_i E[d_i] ≤ E[min(Q, ∑_{i∈U} d_i)]`. -/
def InGamma (μ : Measure Ω) {N : ℕ} (d : Fin N → Ω → ℝ) (α : Fin N → ℝ) (Q : ℝ) : Prop :=
  ∀ U : Finset (Fin N), ∑ i ∈ U, α i * ∫ ω, d i ω ∂μ ≤ ∫ ω, min Q (∑ i ∈ U, d i ω) ∂μ

/-- `Q_II`: the optimal Type-II capacity, as the solution of (CPP-B) in its subset form (p. 17):
the least `Q ≥ 0` with `α ∈ Γ(Q)`. -/
noncomputable def QII (μ : Measure Ω) {N : ℕ} (d : Fin N → Ω → ℝ) (α : Fin N → ℝ) : ℝ :=
  sInf {Q | 0 ≤ Q ∧ InGamma μ d α Q}

/-- The customers ahead of `i` in the order `σ`. -/
def ahead {N : ℕ} (σ : Equiv.Perm (Fin N)) (i : Fin N) : Finset (Fin N) :=
  Finset.univ.filter (fun j => σ.symm j < σ.symm i)

/-- The greedy solution `x*(θ', x, Q)` of the fractional knapsack (CPP-F) (p. 16) for the priority
order `σ` (customers in decreasing order of `θ'`, ties by index): customer `i` receives her demand,
capped by the capacity left after everyone ahead of her has been filled. -/
noncomputable def fill {N : ℕ} (σ : Equiv.Perm (Fin N)) (Q : ℝ) (x : Fin N → ℝ) (i : Fin N) : ℝ :=
  min (x i) (max 0 (Q - ∑ j ∈ ahead σ i, x j))

/-- The standing assumptions of §3.3 (p. 15) and §1 (p. 3): measurable, independent, positive
demands, almost surely bounded by a constant `Δ > 0`, and service targets in `[0, 1]`. -/
structure Standing (μ : Measure Ω) {N : ℕ} (d : Fin N → Ω → ℝ) (Δ : ℝ) (α : Fin N → ℝ) : Prop where
  meas : ∀ i, Measurable (d i)
  indep : iIndepFun d μ
  pos : ∀ i, ∀ᵐ ω ∂μ, 0 < d i ω
  bdd : ∀ i, ∀ᵐ ω ∂μ, d i ω ≤ Δ
  Δ_pos : 0 < Δ
  α_mem : ∀ i, 0 ≤ α i ∧ α i ≤ 1

end StochKnapSL.CapacityGap


