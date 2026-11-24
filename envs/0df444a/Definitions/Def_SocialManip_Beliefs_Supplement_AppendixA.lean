-- Prove2me | Definitions.Def_SocialManip_Beliefs_Supplement_AppendixA
-- name    : SocialManip_Beliefs_Supplement_AppendixA
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T04:12:29.551533+00:00
-- url     : https://prove2.me/theorems/d8254694-395f-4d53-91fb-edd65cb20833
-- title:
--   Appendix A, pp. 33–35 — Poisson news at heterogeneous rates, Bayesian posteriors over the state and the principal's type, Assumption 2, equilibrium with Bayesian agents
-- statement:
--   The Appendix A model uses independent organic Poisson streams with rates $\lambda_i>\underline\lambda>0$, independent principal streams with targeted intensities $0\le\lambda_i^*\le\overline\lambda$, and independent organic marks with the law (1). Zero intensity sends no messages and targeting still incurs cost. Received count histories feed the source's personal Bayesian formula. DeGroots exchange social reports at intervals $\Delta>0$ and, for $k\Delta<t\le(k+1)\Delta$, hold
--   $$\pi_{i,t}=\theta_i\mathrm{BU}_i(h_{i,t})+\sum_j\alpha_{ij}\pi_{j,k\Delta}.$$
--   Each Bayesian has her own joint prior over organic rates, with full-support coordinate marginals on $(\underline\lambda,\infty)$. No common rate prior, independence of rates or joint-full-support premise is imposed. Assumption 2(a)–(e) retains the printed rate, signal, positive-experience and connectivity conditions; genericity is quantified separately in the free normalized social rows.
--
--   The general reporting interface is distinct from the paper's Poisson data. A local history contains own received counts and the entire continuously observed path of every neighbour's state report. It includes off-grid and contemporaneous reports from both agent types. A local report rule maps only that history to a probability. State reports are public; principal-type posteriors are private. The implementation receives only received-count paths, without hidden state, true rates, principal type, organic/principal labels or future news. Its finite prefixes are measurable functions of the corresponding raw prefixes and are unique solutions of the local report equations. Bayesian state and type reports are proper posterior versions: they are information-measurable, integrable, and satisfy the conditional-expectation integral identities for every measurable information event under the agent's subjective experiment. There is no default-zero conditional expectation or ambient-intersection shortcut.
--
--   The equilibrium predicate requires this honest continuous reporting as part of the witness, permits information-dependent Bayesian choices at indifference and every DeGroot tie probability, and checks all admissible principal deviations while holding reporting and terminal strategies fixed. These objects are used by the counterexamples to Lemmas 1–2 and Theorem 8. Theorem 7, the existence target on this model, is not stated in this mission (HARD.md): the source does not determine the contemporaneous Bayesian report process in networks with Bayesian-to-Bayesian links.
--
--   **Formalization Note** The source's $t+dt$ notation is given a conservative operational reading: a valid mechanism's reports must be the *unique* solution of the local report equations on every received-count input, with measurable raw-prefix maps. This is stricter than any causal reading of p. 33, so every equilibrium witnessing a counterexample here is also an equilibrium under any such reading. In the witnesses used (no Bayesian, or one Bayesian observing only a DeGroot) the report equations are acyclic within each exchange interval and the source's process is fully determined, so the stricter requirement excludes nothing relevant. Zero is included in the principal's intensity domain; no one-arrival-per-$\Delta$ restriction is used.
--
--   **Pending source obligation** The continuous observation spaces and posterior identities are implemented, but the all-input algebraic uniqueness condition in AOperational is provisional. The source does not specify an event order proving it or identifying it with the intended causal learning process. It may exclude a legitimate causal realization merely because other noncausal algebraic fixed points exist. This bundle is not certified as a completed source model; HARD.md and DRAFT_PENDING.md isolate the remaining issue.
-- source:
--   Mostagir, Ozdaglar & Siderius, When Is Society Susceptible to Manipulation?, SSRN preprint 3474643 (version of 2020-06-08; Manag. Sci. 2022, doi:10.1287/mnsc.2021.4265), Appendix A, pp. 33–35 (modified model, Bayesian update, Assumption 2, equilibrium with Bayesian agents, properties (*)); footnotes 31–35

import Mathlib
import Definitions.Def_SocialManip_Beliefs_Setting
import Definitions.Def_SocialManip_Beliefs_Supplement_Network
import Definitions.Def_SocialManip_Beliefs_Supplement_Game

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SocialManip.Beliefs.Supplement

open SocialManip.Beliefs

/-- The data of the Appendix A model (pp. 33–35): Bayesian set `B`, DeGroot weights `θ`, `α`,
signal qualities `p`, prior `q = P(y = S)`, prior `μ₀ = P(ω = T)` of the truthful type, the true
organic rates `lam i = λ_i`, the lower bound `lamLow = λ̲` on organic rates, the principal's
capacity `lamUp = λ̄`, the DeGroot exchange interval `Δ`, the cost `ε`, the payoff asymmetry `b`,
the neighbourhoods `N i ⊆ {1, …, n}` and each Bayesian's own joint rate prior `ν i`. -/
structure AModel (n : ℕ) where
  B : Finset (Fin n)
  θ : Fin n → ℝ
  α : Matrix (Fin n) (Fin n) ℝ
  p : Fin n → ℝ
  q : ℝ
  μ0 : ℝ
  lam : Fin n → ℝ
  lamLow : ℝ
  lamUp : ℝ
  Δ : ℝ
  ε : ℝ
  b : ℝ
  N : Fin n → Finset (Fin n)
  ν : Fin n → Measure (Fin n → ℝ)

namespace AModel

variable {n : ℕ}

/-- The standing constraints of Appendix A: `p_i ∈ [1/2, 1)`, DeGroot weights nonnegative with
`θ_i + ∑_j α_ij = 1`, `q, μ₀ ∈ (0,1)`, `λ_i > λ̲ > 0`, `λ̄ > 0`, `Δ > 0`, `ε > 0`, `b ∈ (-1,1)`, and a
Bayesian-specific rate priors `ν i`, whose every coordinate marginal has full support on
`(λ̲, ∞)` (footnote 34). No independence, common prior or joint full support is imposed. The observation
neighbourhood of a DeGroot agent consists exactly of her positive weights (§2, p. 7). -/
def Standing (M : AModel n) : Prop :=
  (∀ i, 1 / 2 ≤ M.p i ∧ M.p i < 1) ∧ (∀ i ∉ M.B, 0 ≤ M.θ i) ∧
    (∀ i ∉ M.B, ∀ j, 0 ≤ M.α i j) ∧ (∀ i ∉ M.B, M.θ i + ∑ j, M.α i j = 1) ∧
    0 < M.q ∧ M.q < 1 ∧ 0 < M.μ0 ∧ M.μ0 < 1 ∧ 0 < M.lamLow ∧ (∀ i, M.lamLow < M.lam i) ∧
    0 < M.lamUp ∧ 0 < M.Δ ∧ 0 < M.ε ∧ -1 < M.b ∧ M.b < 1 ∧
    (∀ i ∈ M.B, IsProbabilityMeasure (M.ν i) ∧
      M.ν i (Set.univ.pi fun _ => Set.Ioi M.lamLow)ᶜ = 0 ∧
      ∀ j, ∀ U : Set ℝ, IsOpen U → (U ∩ Set.Ioi M.lamLow).Nonempty →
        0 < M.ν i {r | r j ∈ U}) ∧
    ∀ i ∉ M.B, ∀ j, j ∈ M.N i ↔ 0 < M.α i j

/-- `λ_max = max_i λ_i`. -/
noncomputable def lamMax (M : AModel n) : ℝ := ⨆ i, M.lam i

/-- A path from `i` to `j` in the observation network along links `u → v` with `v ∈ N(u)`. -/
def Linked (M : AModel n) (i j : Fin n) : Prop := Relation.TransGen (fun u v => v ∈ M.N u) i j

/-- Assumption 2 (a)–(e), p. 34: (a) `λ_max < λ̲ + λ̄/2`; (b) `p_i < (λ̄ + λ_max)/(2λ_max)` for all
`i`; (c) some `p_i > (λ̄ + λ̲)/(2λ̲ + λ̄)`; (d) some `p_i > 1/2`, and DeGroots have `θ_i > 0` iff
`p_i > 1/2`; (e) the network is strongly connected. Part (f), genericity, is a quantifier in
each statement. -/
def Assumption2 (M : AModel n) : Prop :=
  M.lamMax < M.lamLow + M.lamUp / 2 ∧
    (∀ i, M.p i < (M.lamUp + M.lamMax) / (2 * M.lamMax)) ∧
    (∃ i, (M.lamUp + M.lamLow) / (2 * M.lamLow + M.lamUp) < M.p i) ∧
    ((∃ i, 1 / 2 < M.p i) ∧ ∀ i ∉ M.B, (0 < M.θ i ↔ 1 / 2 < M.p i)) ∧
    ∀ i j, i ≠ j → M.Linked i j

end AModel

/-- A network influence strategy of Appendix A: the influence state `ŷ`, the targeting `x`, and the
principal's intensities `λ*_i`. -/
abbrev AAction (n : ℕ) := State × (Fin n → Bool) × (Fin n → ℝ)

/-- Admissible actions: every targeted agent gets an intensity `0 ≤ λ*_i ≤ λ̄`.
The zero-rate boundary sends no messages but still pays the targeting cost. -/
def AAction.Admissible {n : ℕ} (M : AModel n) (a : AAction n) : Prop :=
  ∀ i, a.2.1 i = true → 0 ≤ a.2.2 i ∧ a.2.2 i ≤ M.lamUp

/-- The committed action of the truthful type: `x = 0`. -/
def truthfulAction (n : ℕ) : AAction n := (State.S, fun _ => false, fun _ => 1)

/-- A principal strategy of Appendix A: in each state, a lottery over network influence strategies. -/
abbrev APrincipalStrategy (n : ℕ) := State → Measure (AAction n)

/-- The exogenous randomness: unit-rate exponential inter-arrival times of the organic news and of
the principal's news of every agent, and uniform marks of the organic signals. -/
abbrev Base (n : ℕ) := (Fin n × ℕ → ℝ) × (Fin n × ℕ → ℝ) × (Fin n × ℕ → unitInterval)

/-- The law of the exogenous randomness: all coordinates independent. -/
noncomputable def baseMeasure (n : ℕ) : Measure (Base n) :=
  (Measure.infinitePi fun _ : Fin n × ℕ => expMeasure 1).prod
    ((Measure.infinitePi fun _ : Fin n × ℕ => expMeasure 1).prod
      (Measure.infinitePi fun _ : Fin n × ℕ => (volume : Measure unitInterval)))

/-- Parameters drawn by nature and the principal: the state `y`, whether the principal is the
truthful type, his action, and the organic rates. -/
abbrev Params (n : ℕ) := State × Bool × AAction n × (Fin n → ℝ)

/-- A full outcome: parameters and exogenous randomness. -/
abbrev Full (n : ℕ) := Params n × Base n

/-- The `k`-th organic arrival time of agent `i` (rate `λ_i`, scaled unit exponentials). -/
noncomputable def orgArrival {n : ℕ} (z : Full n) (i : Fin n) (k : ℕ) : ℝ :=
  (∑ l ∈ Finset.range (k + 1), z.2.1 (i, l)) / z.1.2.2.2 i

/-- The `k`-th arrival time of the principal's news at agent `i` (rate `λ*_i`). -/
noncomputable def prinArrival {n : ℕ} (z : Full n) (i : Fin n) (k : ℕ) : ℝ :=
  (∑ l ∈ Finset.range (k + 1), z.2.2.1 (i, l)) / z.1.2.2.1.2.2 i

/-- The `k`-th organic signal of agent `i`, distributed as in (1) given `y`. -/
noncomputable def orgSignal {n : ℕ} (M : AModel n) (z : Full n) (i : Fin n) (k : ℕ) : State :=
  if ((z.2.2.2 (i, k) : unitInterval) : ℝ) < organicProbS (M.p i) z.1.1 then State.S else State.R

open Classical in
/-- `z^s_{i,t}`: the number of signals equal to `s` agent `i` has received by time `t`, organic ones
and, if `x_i = 1` and `ŷ = s`, the principal's. A zero principal intensity contributes zero arrivals explicitly. -/
noncomputable def countA {n : ℕ} (M : AModel n) (z : Full n) (i : Fin n) (t : ℝ) (s : State) : ℕ :=
  {k : ℕ | orgArrival z i k ≤ t ∧ orgSignal M z i k = s}.ncard +
    (if z.1.2.2.1.2.1 i = true ∧ 0 < z.1.2.2.1.2.2 i ∧ z.1.2.2.1.1 = s then {k : ℕ | prinArrival z i k ≤ t}.ncard else 0)

/-! ### Continuous local reporting, independently of the Poisson experiment

A raw input contains *received* counts, not the hidden decomposition into organic and principal
news. A report policy takes exactly its own history and the continuously observed reports of its
neighbours. The realization certificate below requires a unique causal solution for these local
policies; a self-confirming posterior fixed point alone is not an implementation. -/

abbrev RawPath (n : ℕ) := ℝ → Fin n → ℕ × ℕ
abbrev ReportPath (n : ℕ) := ℝ → Fin n → ℝ
abbrev RawPrefix (n : ℕ) (t : ℝ) := Set.Icc (0 : ℝ) t → Fin n → ℕ × ℕ
abbrev ReportPrefix (n : ℕ) (t : ℝ) := Set.Icc (0 : ℝ) t → Fin n → ℝ
abbrev LocalHistory (n : ℕ) (t : ℝ) :=
  (Set.Icc (0 : ℝ) t → ℕ × ℕ) × ReportPrefix n t

open Classical in
/-- The entire local observation, including off-grid and contemporaneous neighbour reports.
The zero entries mask agents outside the observation neighbourhood. -/
noncomputable def localHistory {n : ℕ} (N : Fin n → Finset (Fin n)) (h : RawPath n)
    (H : ReportPath n) (t : ℝ) (i : Fin n) : LocalHistory n t :=
  (fun s => h s i, fun s j => if j ∈ N i then H s j else 0)

/-- A deterministic local reporting mechanism. `stateRule` and `typeRule` are functions of
observable histories, not of hidden outcomes. The state rule is publicly reported; the type rule
is private. `realize` implements the public reports from received-news paths. All causal,
measurability and Bayesian requirements are predicates below, not assumptions baked into data. -/
structure AReporting (n : ℕ) where
  stateRule : (t : ℝ) → Fin n → LocalHistory n t → unitInterval
  typeRule : (t : ℝ) → Fin n → LocalHistory n t → unitInterval
  realize : RawPath n → ReportPath n

/-- Received counts of both marks at every physical time. No hidden state, rate, principal type
or organic/principal label is made available to the reporting mechanism. -/
noncomputable def receivedPath {n : ℕ} (M : AModel n) (z : Full n) : RawPath n :=
  fun t i => (countA M z i t State.S, countA M z i t State.R)

/-- The source BU formula applied to the two received counts of a raw path. -/
noncomputable def rawBU {n : ℕ} (M : AModel n) (h : RawPath n) (i : Fin n) (t : ℝ) : ℝ :=
  1 - BUS (M.p i) M.q (h t i).1 (h t i).2

/-- The local report equations on a finite prefix. At zero everyone starts with the prior;
DeGroots use the last *strictly preceding* exchange, including at `t = kΔ`; Bayesians apply
their local state-report rule to the entire observed prefix, as on pp. 33–34. -/
def ReportsSolve {n : ℕ} (M : AModel n) (R : AReporting n) (h : RawPath n)
    (H : ReportPath n) (T : ℝ) : Prop :=
  ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i,
    H t i = if t = 0 then priorOf M.q State.R
      else if i ∈ M.B then (R.stateRule t i (localHistory M.N h H t i) : ℝ)
      else M.θ i * rawBU M h i t +
        ∑ j, M.α i j * H (((⌈t / M.Δ⌉₊ - 1 : ℕ) : ℝ) * M.Δ) j

/-- Operational causal implementation on `[0,T]`. Prefixes have unique solutions to the local
report equations for every received-news input. A measurable prefix map uses *only* the raw
prefix through that horizon. Thus hidden parameters, future news and arbitrary self-confirming
solutions cannot be used to create reports. This spells out the causal reading of `t+dt` on
p. 33 and of “determines ... terminal beliefs” on p. 35 conservatively: it is stricter than any
causal reading, so an equilibrium using such a mechanism is an equilibrium under every such reading. -/
def AOperational {n : ℕ} (M : AModel n) (T : ℝ) (R : AReporting n) : Prop :=
  (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i, Measurable (R.stateRule t i) ∧ Measurable (R.typeRule t i)) ∧
  (∀ h, ReportsSolve M R h (R.realize h) T) ∧
  (∀ h H, ReportsSolve M R h H T →
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i, H t i = R.realize h t i) ∧
  ∀ t ∈ Set.Icc (0 : ℝ) T,
    ∃ f : RawPrefix n t → ReportPrefix n t, Measurable f ∧
      ∀ h (s : Set.Icc (0 : ℝ) t) i, R.realize h s i = f (fun u j => h u j) s i

/-- The full continuous local observation in the actual experiment. -/
noncomputable def obsWith {n : ℕ} (M : AModel n) (R : AReporting n) (t : ℝ) (i : Fin n)
    (z : Full n) : LocalHistory n t :=
  localHistory M.N (receivedPath M z) (R.realize (receivedPath M z)) t i

/-- The observation σ-algebra itself. It is not intersected with the ambient σ-algebra to
conceal a non-measurable observation map; explicit measurability is required below. -/
noncomputable def infoSigma {n : ℕ} (M : AModel n) (R : AReporting n) (t : ℝ)
    (i : Fin n) : MeasurableSpace (Full n) :=
  MeasurableSpace.comap (obsWith M R t i) inferInstance

/-- The realized public belief path, for Bayesians and DeGroots alike. -/
noncomputable def beliefA {n : ℕ} (M : AModel n) (R : AReporting n) (t : ℝ) (i : Fin n)
    (z : Full n) : ℝ := R.realize (receivedPath M z) t i

/-- The private type posterior is a local-history function; it is not added to neighbours'
observations. -/
noncomputable def typePosterior {n : ℕ} (M : AModel n) (R : AReporting n) (t : ℝ)
    (i : Fin n) (z : Full n) : ℝ := R.typeRule t i (obsWith M R t i z)

/-- The indicator of the event `y = R`. -/
noncomputable def indR {n : ℕ} (z : Full n) : ℝ := if z.1.1 = State.R then 1 else 0

/-- The indicator of the event that the principal is the truthful type. -/
noncomputable def indT {n : ℕ} (z : Full n) : ℝ := if z.1.2.1 = true then 1 else 0

/-- Bayesian `i`'s subjective law of the outcome given the principal's strategy `σP`:
`y` with `P(y = S) = q`, the type with `P(T) = μ₀`, the truthful type's action `x = 0` and the
strategic type's lottery `σP y`, the rates from `ν i`, and the exogenous randomness. -/
noncomputable def subjLaw {n : ℕ} (M : AModel n) (σP : APrincipalStrategy n) (i : Fin n) :
    Measure (Full n) :=
  (∑ y : State, ∑ τ : Bool, ENNReal.ofReal (priorOf M.q y * (if τ then M.μ0 else 1 - M.μ0)) •
      (Measure.dirac y).prod ((Measure.dirac τ).prod
        ((if τ then Measure.dirac (truthfulAction n) else σP y).prod (M.ν i)))).prod (baseMeasure n)

/-- The true law of the outcome when the state is `y`, the type is `τ` (`true` = truthful), the
principal plays `a`, and the organic rates are the true `λ_i`. -/
noncomputable def trueLaw {n : ℕ} (M : AModel n) (y : State) (τ : Bool) (a : AAction n) :
    Measure (Full n) :=
  (Measure.dirac (y, τ, a, M.lam)).prod (baseMeasure n)

/-- A posterior version stated by its defining integral identities. Both integrability and
observation measurability are explicit; no totalized conditional expectation can silently supply
zero. Off-path local-history decisions are supplied by the reporting policy. -/
def IsHistoryPosterior {n : ℕ} (M : AModel n) (R : AReporting n) (Q : Measure (Full n))
    (t : ℝ) (i : Fin n) (f X : Full n → ℝ) : Prop :=
  Measurable (obsWith M R t i) ∧ Measurable[infoSigma M R t i] f ∧
    Integrable f Q ∧ Integrable X Q ∧
    ∀ U : Set (Full n), MeasurableSet[infoSigma M R t i] U →
      ∫ z in U, f z ∂Q = ∫ z in U, X z ∂Q

/-- Honest continuous Bayesian reporting from the experiment. These conditions identify the
state and type posteriors at every time up to `T`, under each Bayesian's own subjective law.
They are required of every equilibrium witness, not supplied learning assumptions. -/
def AValidReporting {n : ℕ} (M : AModel n) (T : ℝ) (σP : APrincipalStrategy n)
    (R : AReporting n) : Prop :=
  AOperational M T R ∧ ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i ∈ M.B,
    IsHistoryPosterior M R (subjLaw M σP i) t i (beliefA M R t i) indR ∧
    IsHistoryPosterior M R (subjLaw M σP i) t i (typePosterior M R t i) indT

/-- DeGroots act as functions of their terminal belief. A Bayesian's decision rule is a
function of her information on outcomes; equilibrium imposes information measurability. This
permits history- and type-posterior-dependent randomization at indifference. -/
structure AAgentStrategy (n : ℕ) where
  degroot : DeGrootStrategy n
  bayes : Fin n → Full n → ℝ

/-- Terminal probability of action R under the appropriate decision rule. -/
noncomputable def actionProbA {n : ℕ} (M : AModel n) (T : ℝ) (R : AReporting n)
    (σA : AAgentStrategy n) (i : Fin n) (z : Full n) : ℝ :=
  if i ∈ M.B then σA.bayes i z else σA.degroot i (beliefA M R T i z)

/-- The strategic principal's expected payoff from action `a` in state `y` at horizon `T`. -/
noncomputable def principalPayoffA {n : ℕ} (M : AModel n) (T : ℝ) (R : AReporting n)
    (σA : AAgentStrategy n) (y : State) (a : AAction n) : ℝ :=
  ∫ z, ∑ i, actionProbA M T R σA i z ∂(trueLaw M y false a) -
    M.ε * ((Finset.univ.filter fun i => a.2.1 i = true).card : ℝ)

/-- The equilibrium of Appendix A at horizon `T` (p. 34): every agent's strategy is a best
response to her terminal belief (for a Bayesian, her posterior given `σP`), and in each state the
principal's lottery is a probability measure on admissible actions, almost every one of which
maximizes his payoff among admissible actions. -/
def AIsEquilibrium {n : ℕ} (M : AModel n) (T : ℝ) (σP : APrincipalStrategy n)
    (R : AReporting n) (σA : AAgentStrategy n) : Prop :=
  AValidReporting M T σP R ∧ IsDeGrootBestResponse
    (⟨M.B, M.θ, M.α, M.p, M.q, 1, 1, M.ε, M.b⟩ : Model n) σA.degroot ∧
  (∀ i ∈ M.B,
    Measurable[infoSigma M R T i] (σA.bayes i) ∧
    ∀ z, (0 ≤ σA.bayes i z ∧ σA.bayes i z ≤ 1) ∧
      ((1 - M.b) / 2 < beliefA M R T i z → σA.bayes i z = 1) ∧
      (beliefA M R T i z < (1 - M.b) / 2 → σA.bayes i z = 0)) ∧
  ∀ y, IsProbabilityMeasure (σP y) ∧ σP y {a | ¬ a.Admissible M} = 0 ∧
    ∀ᵐ a ∂(σP y), ∀ a' : AAction n, a'.Admissible M →
      principalPayoffA M T R σA y a' ≤ principalPayoffA M T R σA y a

/-- The probability that Bayesian `i` is manipulated at horizon `T` given `y`, the strategic
principal's action `a` and the exogenous randomness `ω`: wrong action under `a`, right action under
the truthful `x = 0` with the same exogenous randomness and private tie lottery. -/
noncomputable def bayesManipProb {n : ℕ} (M : AModel n) (T : ℝ) (R : AReporting n)
    (σA : AAgentStrategy n) (y : State) (a : AAction n) (ω : Base n) (i : Fin n) : ℝ :=
  let rS := actionProbA M T R σA i ((y, false, a, M.lam), ω)
  let rT := actionProbA M T R σA i ((y, true, truthfulAction n, M.lam), ω)
  if y = State.R then max 0 (rT - rS) else max 0 (rS - rT)

/-- The probability that some Bayesian agent is manipulated in the equilibrium `(σP, σA)` at
horizon `T` (private lotteries independent across agents and shared across counterfactual worlds). -/
noncomputable def someBayesManipulated {n : ℕ} (M : AModel n) (T : ℝ) (σP : APrincipalStrategy n)
    (R : AReporting n) (σA : AAgentStrategy n) : ℝ :=
  ∑ y : State, priorOf M.q y * ∫ a, ∫ ω,
    (1 - ∏ i ∈ M.B, (1 - bayesManipProb M T R σA y a ω i)) ∂(baseMeasure n) ∂(σP y)

/-- The agent `j` can be reached from Bayesian `i` through DeGroots: `j ∈ N(i)`, or
`i → v₁ → ⋯ → v_k → j` with every `v` DeGroot and every link `u → w` with `w ∈ N(u)`. -/
def DeGrootReach {n : ℕ} (M : AModel n) (i j : Fin n) : Prop :=
  j ∈ M.N i ∨ ∃ v ∈ M.N i, v ∉ M.B ∧
    Relation.TransGen (fun u w => u ∉ M.B ∧ w ∈ M.N u) v j

/-- The DeGroot weights of the free coordinates (the DeGroot rows of `A`); `θ` is then determined
by the row sums. -/
def degrootRows {n : ℕ} (B : Finset (Fin n)) (α : Matrix (Fin n) (Fin n) ℝ) :
    {i : Fin n // i ∉ B} → Fin n → ℝ :=
  fun i j => α i.1 j

end SocialManip.Beliefs.Supplement


