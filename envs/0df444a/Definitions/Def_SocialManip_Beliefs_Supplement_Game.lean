-- Prove2me | Definitions.Def_SocialManip_Beliefs_Supplement_Game
-- name    : SocialManip_Beliefs_Supplement_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T04:11:06.295863+00:00
-- url     : https://prove2.me/theorems/92b838ee-0622-4c79-8b5d-c0fca5f2407f
-- title:
--   §2–§4 — the signal experiment, the horizon-T game of Table 1, equilibrium (Def. 1), manipulation (Def. 2), essential uniqueness (Def. 3), impervious networks
-- statement:
--   The physical-time terminal game of §§2–4 uses one organic Poisson clock of rate $\lambda$ shared by all agents, independent marks over agents and arrivals with quality $p_i$, and one independent principal Poisson clock of rate $\lambda^*$ shared by all targeted agents. Received counts, not a deterministic message index, determine personal experience. The principal chooses a message and a binary target vector after observing the state. His payoff is the expected number of R actions minus the targeting cost. DeGroots best-respond to terminal beliefs, with arbitrary indifference mixing; Bayesians know the truth. At social exchanges,
--   $$\pi_{i,k+1}=\theta_i\mathrm{BU}_i(h_{i,k+1})+\sum_j\alpha_{ij}\pi_{j,k}.$$
--   Between exchanges the current personal experience is combined with the preceding social report, as in Appendix A with $\Delta=1$. Strategies and equilibria allow every nonnegative real physical horizon, including zero. Manipulation compares strategic and truthful worlds using the same organic arrivals and marks, with private tie lotteries shared across the counterfactual worlds and independent across agents. Its count law is defined both conditional on y and mixed over the prior. Imperviousness uses the ex ante law and all large horizons/equilibria; count growth uses the conditional S law. Essential uniqueness compares independent runs conditional on the same realized state. This conditioning is a correction supported by the fixed-state argument on p. 46, not a claim about independently redrawing y. Poisson explosion paths receive ncard's total value but are null under positive-rate clocks. The sample law is explicitly a probability measure.
-- source:
--   Mostagir, Ozdaglar & Siderius, When Is Society Susceptible to Manipulation?, SSRN preprint 3474643 (version of 2020-06-08; Manag. Sci. 2022, doi:10.1287/mnsc.2021.4265), §2 pp. 4–8 (display (1), Table 1); Definition 1 p. 8; Definitions 2–3 p. 9; imperviousness p. 15; initial belief in the proof of Lemma 2, p. 44

import Mathlib
import Definitions.Def_SocialManip_Beliefs_Setting
import Definitions.Def_SocialManip_Beliefs_Supplement_Network

open MeasureTheory
open scoped ENNReal NNReal

namespace SocialManip.Beliefs.Supplement

open SocialManip.Beliefs

/-! ### The signal experiment (§2, p. 5) -/

/-- `r` clamped into `[0, 1]`, as a probability. On the paper's parameter domain the clamp is the
identity. -/
noncomputable def clampProb (r : ℝ) : unitInterval := Set.projIcc 0 1 zero_le_one r

/-- One common organic clock, one independent common principal clock, and independent organic
marks for every agent/event (§2, p. 5). Clock coordinates are unit exponential waiting times. -/
abbrev Sample (n : ℕ) := (Fin n × ℕ → State) × (ℕ → ℝ) × (ℕ → ℝ)

instance : IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) :=
  ProbabilityTheory.isProbabilityMeasure_expMeasure one_pos

/-- The exact continuous-time experiment. The organic arrival clock is shared, as stipulated
on p. 5; its marks are independent over both agents and arrival indices. The principal's clock
is shared by all targeted agents and independent of the organic stream. -/
noncomputable def sampleMeasure {n : ℕ} (M : Model n) (y : State) : Measure (Sample n) :=
  (Measure.infinitePi fun k : Fin n × ℕ =>
      ProbabilityTheory.bernoulliMeasure State.S State.R
        (clampProb (organicProbS (M.p k.1) y))).prod
    ((Measure.infinitePi fun _ : ℕ => ProbabilityTheory.expMeasure 1).prod
      (Measure.infinitePi fun _ : ℕ => ProbabilityTheory.expMeasure 1))

instance {n : ℕ} (M : Model n) (y : State) : IsProbabilityMeasure (sampleMeasure M y) := by
  unfold sampleMeasure
  infer_instance

/-- The time of arrival `k`, starting at zero, for waiting times `e` and rate `r > 0`.
This is just the exponential-arrival construction, not an abstract substitute for its law. -/
noncomputable def arrivalTime (e : ℕ → ℝ) (r : ℝ) (k : ℕ) : ℝ :=
  (∑ l ∈ Finset.range (k + 1), e l) / r

open Classical in
/-- Counts of actually received messages through physical time `t`. There is no fixed number
of messages per interval. Infinite-arrival paths receive `ncard`'s totalization; they form a
null set under the positive-rate exponential clocks at every finite time. -/
noncomputable def countAt {n : ℕ} (M : Model n) (yhat : State) (x : Fin n → Bool)
    (ω : Sample n) (i : Fin n) (t : ℝ) (s : State) : ℕ :=
  {k : ℕ | arrivalTime ω.2.1 M.lam k ≤ t ∧ ω.1 (i, k) = s}.ncard +
    (if x i = true ∧ yhat = s then
      {k : ℕ | arrivalTime ω.2.2 M.lamStar k ≤ t}.ncard else 0)

/-- The prior belief in `y'`. -/
noncomputable def priorOf (q : ℝ) (y' : State) : ℝ := if y' = State.S then q else 1 - q

/-- Personal posterior from the physical-time counts (p. 6). -/
noncomputable def personalR {n : ℕ} (M : Model n) (yhat : State) (x : Fin n → Bool)
    (ω : Sample n) (i : Fin n) (t : ℝ) : ℝ :=
  1 - BUS (M.p i) M.q (countAt M yhat x ω i t State.S) (countAt M yhat x ω i t State.R)

/-- Social exchange at integer times, using all messages received by that physical time.
Bayesians hold the true state from time zero; the initial DeGroot belief is the common prior. -/
noncomputable def gridBeliefR {n : ℕ} (M : Model n) (y yhat : State) (x : Fin n → Bool)
    (ω : Sample n) : ℕ → Fin n → ℝ
  | 0 => fun i => if i ∈ M.B then truth y State.R else priorOf M.q State.R
  | k + 1 => fun i => if i ∈ M.B then truth y State.R
      else M.θ i * personalR M yhat x ω i (k + 1 : ℕ) +
        ∑ j, M.α i j * gridBeliefR M y yhat x ω k j

/-- Terminal belief at an arbitrary finite physical time. Between exchanges personal news is
current and the social term is from the preceding exchange, as made explicit in Appendix A,
p. 33 with Δ = 1. At integer times this is exactly the main-text recursion on p. 7. -/
noncomputable def beliefR {n : ℕ} (M : Model n) (y yhat : State) (x : Fin n → Bool) (ω : Sample n)
    (T : ℝ) (i : Fin n) : ℝ :=
  if i ∈ M.B then truth y State.R
  else if T ≤ 0 then priorOf M.q State.R
  else M.θ i * personalR M yhat x ω i T +
    ∑ j, M.α i j * gridBeliefR M y yhat x ω (⌈T⌉₊ - 1) j

/-! ### Strategies, payoffs and equilibrium (Table 1, Definition 1, pp. 7–9) -/

/-- A DeGroot strategy profile: `σD i π ∈ [0,1]` is the probability that agent `i` takes action `R`
at terminal belief `π = π_{i,T}(R)`. -/
abbrev DeGrootStrategy (n : ℕ) := Fin n → ℝ → ℝ

/-- A strategy of the strategic principal: after observing `y`, a lottery over network influence
strategies `(ŷ, x)` (the truthful type always plays `x = 0`). -/
abbrev PrincipalStrategy (n : ℕ) := State → PMF (State × (Fin n → Bool))

/-- Every DeGroot agent best-responds to her terminal belief under Table 1: action `R` is strictly
better iff `π(R) > (1-b)/2`, so `σD i π = 1` above, `0` below, any probability at equality. -/
def IsDeGrootBestResponse {n : ℕ} (M : Model n) (σD : DeGrootStrategy n) : Prop :=
  ∀ i ∉ M.B, ∀ π : ℝ, (0 ≤ σD i π ∧ σD i π ≤ 1) ∧
    ((1 - M.b) / 2 < π → σD i π = 1) ∧ (π < (1 - M.b) / 2 → σD i π = 0)

open Classical in
/-- The strategic principal's expected payoff from `(ŷ, x)` in state `y` at horizon `T`, given the
DeGroot strategies: the expected number of agents taking action `R` (Bayesians know `y` and take
action `y`) minus the cost `ε ∑_i 1{x_i = 1}` (p. 8). -/
noncomputable def principalPayoff {n : ℕ} (M : Model n) (T : ℝ) (σD : DeGrootStrategy n)
    (y yhat : State) (x : Fin n → Bool) : ℝ :=
  (M.B.card : ℝ) * (if y = State.R then 1 else 0) +
    ∑ i ∈ Finset.univ.filter (· ∉ M.B),
      ∫ ω, σD i (beliefR M y yhat x ω T i) ∂(sampleMeasure M y) -
    M.ε * ((Finset.univ.filter fun i => x i = true).card : ℝ)

/-- Definition 1, p. 8: `(σP, σD)` is an equilibrium of the horizon-`T` game if every DeGroot agent
best-responds to her terminal belief and, in each state `y`, every influence strategy in the
support of `σP y` maximizes the principal's expected payoff. -/
def IsEquilibrium {n : ℕ} (M : Model n) (T : ℝ) (σP : PrincipalStrategy n)
    (σD : DeGrootStrategy n) : Prop :=
  IsDeGrootBestResponse M σD ∧
    ∀ y a, σP y a ≠ 0 → ∀ a' : State × (Fin n → Bool),
      principalPayoff M T σD y a'.1 a'.2 ≤ principalPayoff M T σD y a.1 a.2

/-! ### Manipulation (Definition 2, p. 9) -/

/-- The probability that agent `i` is manipulated, given the state `y`, the strategic principal's
realized `(ŷ, x)` and the sample `ω`: her action is wrong under `(ŷ, x)` and right under the
truthful principal's `x = 0` with the same organic news (each agent uses the same private uniform lottery in the two counterfactual worlds;
lotteries are independent across agents). Bayesian agents always act correctly. -/
noncomputable def manipProb {n : ℕ} (M : Model n) (T : ℝ) (σD : DeGrootStrategy n) (y yhat : State)
    (x : Fin n → Bool) (ω : Sample n) (i : Fin n) : ℝ :=
  if i ∈ M.B then 0 else
    let rS := σD i (beliefR M y yhat x ω T i)
    let rT := σD i (beliefR M y yhat (fun _ => false) ω T i)
    if y = State.R then max 0 (rT - rS) else max 0 (rS - rT)

/-- The probability that exactly `j` of independent events with probabilities `r i` occur. -/
noncomputable def countLaw {n : ℕ} (r : Fin n → ℝ) (j : ℕ) : ℝ :=
  ∑ A ∈ Finset.univ.filter fun A : Finset (Fin n) => A.card = j,
    (∏ i ∈ A, r i) * ∏ i ∈ Aᶜ, (1 - r i)

/-- The manipulated-count distribution conditional on a fixed realized state `y`.
The strategic and truthful counterfactual worlds use the same organic arrivals and marks. -/
noncomputable def manipLawGiven {n : ℕ} (M : Model n) (T : ℝ) (σP : PrincipalStrategy n)
    (σD : DeGrootStrategy n) (y : State) (j : ℕ) : ℝ :=
  ∑ a : State × (Fin n → Bool), (σP y a).toReal *
    ∫ ω, countLaw (manipProb M T σD y a.1 a.2 ω) j ∂(sampleMeasure M y)

/-- The ex ante count law, mixing the two realized states with their prior probabilities. -/
noncomputable def manipLaw {n : ℕ} (M : Model n) (T : ℝ) (σP : PrincipalStrategy n)
    (σD : DeGrootStrategy n) (j : ℕ) : ℝ :=
  ∑ y : State, priorOf M.q y * manipLawGiven M T σP σD y j

/-- Definition 3, p. 9: the equilibria are essentially unique if for every `κ > 0` there is `T*`
such that for every `T > T*` and every two (not necessarily distinct) equilibria of the horizon-`T`
game, independent draws `k⁽¹⁾, k⁽²⁾` conditional on the same realized state `y` of their manipulated counts agree with probability `≥ 1 - κ`. -/
def EssentiallyUnique {n : ℕ} (M : Model n) : Prop :=
  ∀ κ : ℝ, 0 < κ → ∃ Tstar : ℝ, ∀ T, Tstar < T → ∀ σP₁ σD₁ σP₂ σD₂,
    IsEquilibrium M T σP₁ σD₁ → IsEquilibrium M T σP₂ σD₂ → ∀ y : State,
      1 - κ ≤ ∑ j ∈ Finset.range (n + 1),
        manipLawGiven M T σP₁ σD₁ y j * manipLawGiven M T σP₂ σD₂ y j

/-- At least `K` agents are manipulated conditional on state S in equilibrium (as `T → ∞`): for every `κ > 0`, for all
large horizons, every equilibrium manipulates at least `K` agents with probability `≥ 1 - κ`. -/
def ManipulatesAtLeast {n : ℕ} (M : Model n) (K : ℕ) : Prop :=
  ∀ κ : ℝ, 0 < κ → ∃ Tstar : ℝ, ∀ T, Tstar < T → ∀ σP σD, IsEquilibrium M T σP σD →
    1 - κ ≤ ∑ j ∈ Finset.Icc K n, manipLawGiven M T σP σD State.S j

/-- §4, p. 15: society is impervious to manipulation if no agent is manipulated in equilibrium:
for every `κ > 0`, for all large horizons, in every equilibrium no agent is manipulated with
probability `≥ 1 - κ`. It is susceptible otherwise (`¬ Impervious`). -/
def Impervious {n : ℕ} (M : Model n) : Prop :=
  ∀ κ : ℝ, 0 < κ → ∃ Tstar : ℝ, ∀ T, Tstar < T → ∀ σP σD, IsEquilibrium M T σP σD →
    1 - κ ≤ manipLaw M T σP σD 0

end SocialManip.Beliefs.Supplement


