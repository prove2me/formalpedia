-- Prove2me | Definitions.Def_IntroBandits_Agents
-- name    : IntroBandits_Agents
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-24T02:33:31.836989+00:00
-- url     : https://prove2.me/theorems/5e7f9e14-4c73-4a20-9807-6ef4f539ad04
-- title:
--   Incentivized exploration: prior and posterior means, Bayesian incentive-compatibility (11.1), GREEDY (11.2), the posterior gap and (11.12), single-round HiddenExploration, and the law of RepeatedHE
-- statement:
--   The setting of Chapter 11, incentivized exploration, on top of the Bayesian-bandit layer of Chapter 3 (`RewardFamily`, `instanceOf`, `jointMeasure`, `posterior`, `bayesianRegret`), with the chapter's simplifications: the prior $P$ has a finite support $F$, realized rewards take finitely many values, and signal universes are finite.
--
--   **Means.** $\mu^0_a = \mathbb{E}[\mu_a] = \sum_{\mu \in F} P(\mu)\,\mu_a$ (`priorMean`); $\mathbb{E}[\mu_a \mid H_t = H] = \sum_{\mu \in F} P_H(\mu)\,\mu_a$ (`postMean`) with $P_H$ the Bayes posterior of Chapter 3.
--
--   **Bayesian incentive-compatibility (Definition 11.4).** For a joint law $Q$ of $(\mu, \text{record})$ of a $T$-round run in which every agent complies, and $\mathrm{rec}_t$ the arm recommended in round $t$ of the record: `IsBIC F Q rec` holds if for every round $t$ and every two distinct arms $a, a'$ with $\Pr[\mathrm{rec}_t = a] > 0$,
--   $$\sum_{\mu \in F} (\mu_a - \mu_{a'})\, Q(\{\mu\} \times \{\mathrm{rec}_t = a\}) \ge 0, \quad\text{i.e.}\quad \mathbb{E}[\mu_a - \mu_{a'} \mid \mathrm{rec}_t = a] \ge 0 .$$
--   The event $E_{t-1}$ of (11.1), that all previous agents complied, is built into $Q$: it is the law of the compliant run. `IsBICPolicy P F fam π T` is the case of a bandit policy $\pi$, whose compliant run has the law `jointMeasure P F fam π T` of Chapter 3 (Remark 11.2). `IsStrictlyBIC` (two arms) adds the tie convention of Theorem 11.19: arm 2 is recommended only if $\mathbb{E}[\mu_2 - \mu_1 \mid \mathrm{rec}_t = 2] > 0$.
--
--   **GREEDY (11.2).** `IsGreedy P F fam π`: for every feasible history $H$, the arm played is almost surely a maximizer of $\mathbb{E}[\mu_a \mid H_t = H]$; ties are broken arbitrarily.
--
--   **The posterior gap of arm 1's samples.** For a tuple $s$ of $n$ samples of arm 1, `gapNumerator P F fam s` $= \sum_{\mu \in F} P(\mu) \prod_i D_{\mu_1}(\{s_i\})\,(\mu_2 - \mu_1) = \mathbb{E}[(\mu_2 - \mu_1)\mathbf 1\{S_{1,n} = s\}]$, so $G_{1,n} = \mathbb{E}[\mu_2 - \mu_1 \mid S_{1,n}]$ (11.11) is positive at $s$ iff the numerator is. Property (11.12), `PriorAllowsExploration`, is $\exists n, s:\ \text{numerator} > 0$, i.e. $\Pr[G_{1,n} > 0] > 0$ for some $n$. `initialGapPlus P F fam N₀` $= \sum_{s \in \mathrm{values}^{N_0}} \max(0, \text{numerator}(s)) = \mathbb{E}[G \cdot \mathbf 1\{G > 0\}]$ for $G = G_{1,N_0}$, the posterior gap given the $N_0$ initial samples of arm 1 (the $G = G_{N_0+1}$ of Theorem 11.15).
--
--   **One round with an abstract signal (§11.3).** $\Omega$ a finite type, $Q$ a joint law of $(\mu, \mathrm{sig})$: `sigProb` $= \Pr[\mathrm{sig} = S]$; `sigPostMean` $= \mathbb{E}[\mu_a \mid \mathrm{sig} = S]$ (junk $0$ off the support); `sigGapNum` $= \mathbb{E}[(\mu_2 - \mu_1)\mathbf 1\{\mathrm{sig} = S\}]$; `sigGapPlus` $= \sum_S \max(0, \cdot) = \mathbb{E}[G \cdot \mathbf 1\{G > 0\}]$ for the posterior gap $G = \mathbb{E}[\mu_2 - \mu_1 \mid \mathrm{sig}]$; `exploitArm` $= \min \arg\max_a \mathbb{E}[\mu_a \mid \mathrm{sig} = S]$ (arm 1 unless arm 2 is strictly better); `hiddenExploration ε trg Q F S a` $= \varepsilon\, \mathrm{trg}(S)(a) + (1 - \varepsilon)\mathbf 1\{a = \text{exploitArm}(S)\}$, the probability that Algorithm 11.1 recommends $a$ on $S$ for a randomized target $\mathrm{trg}$; `IsSingleRoundBIC Q F rule` is (11.5) for a rule $\mathrm{rule}(S)(a) = \Pr[\mathrm{rec} = a \mid \mathrm{sig} = S]$: $\Pr[\mathrm{rec} = a] > 0 \Rightarrow \sum_{\mu, S} Q(\mu, S)(\mu_a - \mu_{a'})\,\mathrm{rule}(S)(a) \ge 0$.
--
--   **RepeatedHE (Algorithm 11.2).** A round of the record is $((\text{explore?}, a_t), r_t)$; `recHE`, `isExplore` read it. The exploration data $S_t$ of (11.10) is the sub-record of exploration rounds: `explLikelihood fam μ h` $= \prod_{s\ \text{expl}} D_{\mu(a_s)}(\{r_s\})$, `explPostMean` the Bayes posterior mean $\mathbb{E}[\mu_a \mid S_t]$ from it, `explGap` $= G_t$, `exploitArmHE` $= \min\arg\max_a \mathbb{E}[\mu_a \mid S_t]$. `algRounds N₀ h` are the exploration rounds after the $N_0$ initial ones (the calls to ALG) and `algHistory` their (arm, reward) pairs in order, the history ALG is fed. `roundProb` is the probability of round $t$ given $\mu$: in an initial round ($t < N_0$) the round is an exploration round and the arm is arm 1; afterwards the round is an exploration round with probability $\varepsilon$ and the arm is drawn by ALG from its history, else the arm is the exploitation branch's; then $r_t \sim D_{\mu(a_t)}$. `recordProb` is the product over rounds, `heRecords fam T` the finite set of records with rewards in $\mathrm{values}$, and
--   $$\texttt{repeatedHELaw}\ P\,F\,\mathrm{fam}\,A\,N_0\,\varepsilon\,T = \sum_{\mu \in F}\sum_{h \in \mathrm{heRecords}} P(\mu)\Pr[\text{record} = h \mid \mu]\;\delta_{(\mu, h)}$$
--   is the joint law of $(\mu, \text{record})$ of the compliant run; `heExpect` is the expectation of a function of the record under it.
--
--   **Formalization notes.** (1) Arms are indexed by `Fin 2`: the book's arm 1 is index `0` and arm 2 is index `1`; the Preliminaries' $\mu^0_1 \ge \mu^0_2$ is a hypothesis of the theorems. (2) Rounds are `Fin T`, so the book's round $t$ is index $t - 1$ and the signal $S_t$ before it is the record of the first $t-1$ rounds. (3) The law of RepeatedHE is an explicit finitely supported measure rather than a kernel composition, because ALG is fed a history of variable length (its own calls); it is the law of the run exactly as Algorithm 11.2 specifies it.
-- source:
--   Slivkins, Introduction to Multi-Armed Bandits, arXiv:1904.07272 (FnT ML 12, 2019), Chapter 11 pp. 145-152: the protocol (p. 145), Definition 11.4 (p. 146), the Preliminaries (p. 146), GREEDY (11.2) (p. 147), Algorithm 11.1 and (11.5) (p. 149), Algorithm 11.2 with S_t (11.10) (p. 151), G_{1,n} (11.11) and Property (11.12) (p. 152)

import Mathlib.Probability.Independence.Basic
import Definitions.Def_IntroBandits_Bayesian

/-!
Slivkins, *Introduction to Multi-Armed Bandits* (arXiv:1904.07272), Chapter 11 (pp. 144-153):
bandits and agents, incentivized exploration.

Problem protocol (p. 145): `K` arms, `T` rounds, a common prior `P` on the mean reward vector
`μ ∈ [0,1]^K`, reward distributions `(D_x)` with `E[D_x] = x`. In each round the principal
recommends an arm `rec_t`; agent `t` sees only the recommendation (and the algorithm, the prior
and the round), chooses an arm `a_t`, and its reward `r_t ~ D_{μ(a_t)}` is observed by the
principal. The chapter's simplifications are built in, as in Chapter 3: the prior has a finite
support `F`, realized rewards take finitely many values, and the signal universes are finite.
All Bayesian objects are those of `Def_IntroBandits_Bayesian`: `RewardFamily`, `instanceOf`,
`jointMeasure` (the joint law of `(μ, H_t)` when the agents comply and the recommendations are
the arms of a `BanditPolicy`), `posterior`, `bayesianRegret`.

* `priorMean P F a = μ⁰_a = E[μ_a]`; `postMean P F fam H a = E[μ_a | H_t = H]`, the posterior
  mean given a history.
* `IsBIC F Q rec` — Definition 11.4, Bayesian incentive-compatibility, for a joint law `Q` of
  `(μ, record)` and the recommendation `rec record t` of each round: whenever
  `Pr[rec_t = a] > 0`, `E[μ_a − μ_{a'} | rec_t = a] ≥ 0` for every other arm `a'`. The law `Q`
  is the law of a run in which every agent complies, so the event `E_{t-1}` of (11.1) is the
  sure event; `IsBICPolicy P F fam π T` is the case of a bandit policy (Remark 11.2).
  `IsStrictlyBIC` adds the tie convention of Theorem 11.19: arm 2 is recommended only when its
  conditional advantage is strictly positive.
* `IsGreedy P F fam π` — Algorithm GREEDY, Eq. (11.2): the arm played is a maximizer of the
  posterior mean given the full history, ties broken arbitrarily.
* `gapNumerator P F fam n s = E[(μ₂ − μ₁) 𝟙{S_{1,n} = s}]` for a tuple `s` of `n` samples of arm 1,
  so that the posterior gap `G_{1,n}` of (11.11) is positive at `s` iff the numerator is;
  `PriorAllowsExploration P F fam` is Property (11.12); `initialGapPlus P F fam N₀ =
  E[G · 𝟙{G > 0}]` for `G = G_{1,N₀}`, the quantity of Theorem 11.15.
* The single-round setting of §11.3, for an abstract signal in a finite type `Ω` with joint law
  `Q` of `(μ, sig)`: `sigProb`, `sigPostMean = E[μ_a | sig = S]`, `sigGapNum = E[(μ₂ − μ₁) 𝟙{sig = S}]`,
  `sigGapPlus Q F = E[G · 𝟙{G > 0}]` with `G = E[μ₂ − μ₁ | sig]`; `exploitArm` — the
  exploitation branch `min argmax_a E[μ_a | sig = S]`; `hiddenExploration ε trg Q F S a` — the
  probability that Algorithm 11.1 recommends `a` on the signal `S`, for a randomized target
  `trg`; `IsSingleRoundBIC Q F rule` — the single-round BIC property (11.5) of a recommendation
  rule that depends on the signal only.
* RepeatedHE (Algorithm 11.2): `HERound = ((explore?, arm), reward)`, `HERecord T`; `recHE`,
  `isExplore`; `explLikelihood`, `explPostMean`, `explGap` — the posterior given the
  exploration rounds `S_t` of (11.10); `exploitArmHE` — the exploitation branch; `algRounds`,
  `algHistory` — the rounds and the history seen by the bandit algorithm `ALG`;
  `roundProb`, `recordProb` — the probability of a record given `μ`; `heRecords fam T` — the
  finite set of records with rewards in `fam.values`; `repeatedHELaw P F fam A N₀ ε T` — the
  joint law of `(μ, record)` when the agents comply; `heExpect` — expectations under it.
-/

open MeasureTheory ProbabilityTheory BanditAlgorithm Finset

noncomputable section

namespace IntroBandits

variable {K : ℕ}

/-- The prior mean reward `μ⁰_a = E[μ_a]` of arm `a`, for a prior supported on `F`. -/
def priorMean (P : Measure (Fin K → ℝ)) (F : Finset (Fin K → ℝ)) (a : Fin K) : ℝ :=
  ∑ μ ∈ F, (P {μ}).toReal * μ a

/-- The posterior mean reward `E[μ_a | H_t = H]` given the history `H`, computed from the
Bayesian posterior `P_H` of Chapter 3. -/
def postMean (P : Measure (Fin K → ℝ)) (F : Finset (Fin K → ℝ)) (fam : RewardFamily)
    {t : ℕ} (H : BanditHistory K t) (a : Fin K) : ℝ :=
  ∑ μ ∈ F, (posterior P F fam H {μ}).toReal * μ a

/-- Definition 11.4 (Bayesian incentive-compatibility) for a joint law `Q` of the mean vector
`μ` (supported on `F`) and the record of a `T`-round run in which every agent complies, with
`rec r t` the arm recommended in round `t` of the record `r`: for every round `t` and every two
distinct arms `a, a'` with `Pr[rec_t = a] > 0`,
`E[(μ_a − μ_{a'}) 𝟙{rec_t = a}] ≥ 0`, i.e. `E[μ_a − μ_{a'} | rec_t = a] ≥ 0`. Conditioning on the
compliance of the previous agents (the event `E_{t-1}` of (11.1)) is built into `Q`. -/
def IsBIC (F : Finset (Fin K → ℝ)) {R : Type} [MeasurableSpace R] {T : ℕ}
    (Q : Measure ((Fin K → ℝ) × R)) (rec : R → Fin T → Fin K) : Prop :=
  ∀ (t : Fin T) (a a' : Fin K), a ≠ a' → Q (Set.univ ×ˢ {r | rec r t = a}) ≠ 0 →
    0 ≤ ∑ μ ∈ F, (μ a - μ a') * (Q ({μ} ×ˢ {r | rec r t = a})).toReal

/-- A bandit policy `π` is BIC (Remark 11.2: with compliance the protocol is a Bayesian bandit,
and `rec_t = a_t`): `IsBIC` for the joint law of `(μ, H_T)` of Chapter 3. -/
def IsBICPolicy (P : Measure (Fin K → ℝ)) (F : Finset (Fin K → ℝ)) (fam : RewardFamily)
    (π : BanditPolicy K) (T : ℕ) : Prop :=
  IsBIC F (jointMeasure P F fam π T) (fun h t ↦ (h t).1)

/-- The tie convention of Theorem 11.19 for two arms: BIC, and arm 2 (index `1`) is recommended
only when its conditional advantage over arm 1 is strictly positive, i.e. ties in (11.1) are
resolved in favor of arm 1. -/
def IsStrictlyBIC (F : Finset (Fin 2 → ℝ)) {R : Type} [MeasurableSpace R] {T : ℕ}
    (Q : Measure ((Fin 2 → ℝ) × R)) (rec : R → Fin T → Fin 2) : Prop :=
  IsBIC F Q rec ∧ ∀ t : Fin T, Q (Set.univ ×ˢ {r | rec r t = 1}) ≠ 0 →
    0 < ∑ μ ∈ F, (μ 1 - μ 0) * (Q ({μ} ×ˢ {r | rec r t = 1})).toReal

/-- Algorithm GREEDY, Eq. (11.2): in every round, given a feasible history `H`, the arm played
is (almost surely) a maximizer of the posterior mean `E[μ_a | H_t = H]`; ties are broken
arbitrarily. -/
def IsGreedy (P : Measure (Fin K → ℝ)) (F : Finset (Fin K → ℝ)) (fam : RewardFamily)
    (π : BanditPolicy K) : Prop :=
  ∀ t (H : BanditHistory K t), IsFeasible P F fam H →
    (π.select t) H {a | ∀ b, postMean P F fam H b ≤ postMean P F fam H a} = 1

/-- `E[(μ₂ − μ₁) 𝟙{S_{1,n} = s}]` for a tuple `s` of `n` samples of arm 1: the prior weight
times the likelihood `∏_i D_{μ₁}({s_i})` of the samples, weighted by `μ₂ − μ₁`. The posterior
gap `G_{1,n} = E[μ₂ − μ₁ | S_{1,n}]` of (11.11) at `s` is this divided by `Pr[S_{1,n} = s]`, so
`G_{1,n} > 0` at `s` iff the numerator is positive. -/
def gapNumerator (P : Measure (Fin 2 → ℝ)) (F : Finset (Fin 2 → ℝ)) (fam : RewardFamily)
    {n : ℕ} (s : Fin n → ℝ) : ℝ :=
  ∑ μ ∈ F, (P {μ} * ∏ i, fam.D (μ 0) {s i}).toReal * (μ 1 - μ 0)

/-- Property (11.12): `Pr[G_{1,n} > 0] > 0` for some `n`, i.e. arm 2 can appear better after
seeing sufficiently many samples of arm 1. -/
def PriorAllowsExploration (P : Measure (Fin 2 → ℝ)) (F : Finset (Fin 2 → ℝ))
    (fam : RewardFamily) : Prop :=
  ∃ (n : ℕ) (s : Fin n → ℝ), 0 < gapNumerator P F fam s

/-- `E[G · 𝟙{G > 0}]` for the posterior gap `G = G_{1,N₀} = E[μ₂ − μ₁ | S_{1,N₀}]` given `N₀`
samples of arm 1 (the quantity of Theorem 11.15, where `G = G_{N₀+1}`): the sum over the sample
tuples `s` of `max(0, E[(μ₂ − μ₁) 𝟙{S_{1,N₀} = s}])`. -/
def initialGapPlus (P : Measure (Fin 2 → ℝ)) (F : Finset (Fin 2 → ℝ)) (fam : RewardFamily)
    (N₀ : ℕ) : ℝ :=
  ∑ s ∈ Fintype.piFinset (fun _ : Fin N₀ ↦ fam.values), max 0 (gapNumerator P F fam s)

/-! ### A single round: hidden exploration with an abstract signal (§11.3) -/

section Signal

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MeasurableSpace Ω]

/-- `Pr[sig = S]` under the joint law `Q` of `(μ, sig)`. -/
def sigProb (Q : Measure ((Fin 2 → ℝ) × Ω)) (S : Ω) : ENNReal :=
  Q (Set.univ ×ˢ {S})

/-- The posterior mean `E[μ_a | sig = S]` (junk `0` when `Pr[sig = S] = 0`). -/
def sigPostMean (Q : Measure ((Fin 2 → ℝ) × Ω)) (F : Finset (Fin 2 → ℝ)) (S : Ω) (a : Fin 2) :
    ℝ :=
  (∑ μ ∈ F, (Q {(μ, S)}).toReal * μ a) / (sigProb Q S).toReal

/-- `E[(μ₂ − μ₁) 𝟙{sig = S}] = Pr[sig = S] · G(S)` for the posterior gap `G = E[μ₂ − μ₁ | sig]`. -/
def sigGapNum (Q : Measure ((Fin 2 → ℝ) × Ω)) (F : Finset (Fin 2 → ℝ)) (S : Ω) : ℝ :=
  ∑ μ ∈ F, (Q {(μ, S)}).toReal * (μ 1 - μ 0)

/-- `E[G · 𝟙{G > 0}]` for the posterior gap `G = E[μ₂ − μ₁ | sig]`. -/
def sigGapPlus (Q : Measure ((Fin 2 → ℝ) × Ω)) (F : Finset (Fin 2 → ℝ)) : ℝ :=
  ∑ S, max 0 (sigGapNum Q F S)

/-- The exploitation branch of Algorithm 11.1: `min argmax_{a ∈ {1,2}} E[μ_a | sig = S]`, i.e.
arm 1 (index `0`) unless arm 2 has strictly larger posterior mean. -/
def exploitArm (Q : Measure ((Fin 2 → ℝ) × Ω)) (F : Finset (Fin 2 → ℝ)) (S : Ω) : Fin 2 :=
  if sigPostMean Q F S 1 ≤ sigPostMean Q F S 0 then 0 else 1

/-- Algorithm 11.1, HiddenExploration with signal `sig`: the probability of recommending `a` on
the signal `S`. With probability `ε` the exploration branch recommends the target `trg S`, a
(possibly randomized) function of the signal, given as a distribution over the two arms; with
probability `1 − ε` the exploitation branch recommends `exploitArm S`. -/
def hiddenExploration (ε : ℝ) (trg : Ω → Fin 2 → ℝ) (Q : Measure ((Fin 2 → ℝ) × Ω))
    (F : Finset (Fin 2 → ℝ)) (S : Ω) (a : Fin 2) : ℝ :=
  ε * trg S a + (1 - ε) * (if a = exploitArm Q F S then 1 else 0)

/-- The single-round BIC property (11.5) of a recommendation rule `rule S a = Pr[rec = a | sig = S]`
that depends on the signal only (and on independent randomness): for any two distinct arms,
`Pr[rec = a] > 0` implies `E[(μ_a − μ_{a'}) 𝟙{rec = a}] ≥ 0`, i.e. `E[μ_a − μ_{a'} | rec = a] ≥ 0`. -/
def IsSingleRoundBIC (Q : Measure ((Fin 2 → ℝ) × Ω)) (F : Finset (Fin 2 → ℝ))
    (rule : Ω → Fin 2 → ℝ) : Prop :=
  ∀ a a' : Fin 2, a ≠ a' → 0 < ∑ S, (sigProb Q S).toReal * rule S a →
    0 ≤ ∑ μ ∈ F, ∑ S, (Q {(μ, S)}).toReal * (μ a - μ a') * rule S a

end Signal

/-! ### RepeatedHE (Algorithm 11.2) -/

/-- One round of a run of RepeatedHE: whether the round was an exploration round (the initial
rounds and the rounds in which `ALG` is called), the arm recommended (and, with compliance,
played), and the reward. -/
abbrev HERound := (Bool × Fin 2) × ℝ

/-- The record of `T` rounds of RepeatedHE. -/
abbrev HERecord (T : ℕ) := Fin T → HERound

/-- The arm recommended in round `t`. -/
def recHE {T : ℕ} (h : HERecord T) (t : Fin T) : Fin 2 :=
  (h t).1.2

/-- Whether round `t` was an exploration round. -/
def isExplore {T : ℕ} (h : HERecord T) (t : Fin T) : Bool :=
  (h t).1.1

/-- The first `t` rounds of a record. -/
def hePrefix {T : ℕ} (h : HERecord T) {t : ℕ} (ht : t ≤ T) : HERecord t :=
  fun s ↦ h (Fin.castLE ht s)

/-- The likelihood `Pr[S_t | μ]` of the exploration data (10.10): the product over the
exploration rounds of `D_{μ(a_s)}({r_s})`. -/
def explLikelihood (fam : RewardFamily) (μ : Fin 2 → ℝ) {t : ℕ} (h : HERecord t) : ENNReal :=
  ∏ s : Fin t with isExplore h s = true, fam.D (μ (recHE h s)) {(h s).2}

/-- The posterior mean `E[μ_a | S_t]` given the exploration rounds `S_t` of (11.10), by Bayes'
rule from the prior and the likelihood of the exploration data (junk `0` when the data has
probability zero). -/
def explPostMean (P : Measure (Fin 2 → ℝ)) (F : Finset (Fin 2 → ℝ)) (fam : RewardFamily)
    {t : ℕ} (h : HERecord t) (a : Fin 2) : ℝ :=
  (∑ μ ∈ F, (P {μ} * explLikelihood fam μ h).toReal * μ a) /
    (∑ μ ∈ F, (P {μ} * explLikelihood fam μ h).toReal)

/-- The posterior gap `G_t = E[μ₂ − μ₁ | S_t]` given the exploration rounds. -/
def explGap (P : Measure (Fin 2 → ℝ)) (F : Finset (Fin 2 → ℝ)) (fam : RewardFamily)
    {t : ℕ} (h : HERecord t) : ℝ :=
  explPostMean P F fam h 1 - explPostMean P F fam h 0

/-- The exploitation branch of Algorithm 11.2: `min argmax_{a ∈ {1,2}} E[μ_a | S_t]`. -/
def exploitArmHE (P : Measure (Fin 2 → ℝ)) (F : Finset (Fin 2 → ℝ)) (fam : RewardFamily)
    {t : ℕ} (h : HERecord t) : Fin 2 :=
  if explPostMean P F fam h 1 ≤ explPostMean P F fam h 0 then 0 else 1

/-- The rounds in which `ALG` was called: the exploration rounds after the `N₀` initial rounds. -/
def algRounds (N₀ : ℕ) {t : ℕ} (h : HERecord t) : Finset (Fin t) :=
  univ.filter fun s ↦ isExplore h s = true ∧ N₀ ≤ s.val

/-- The history seen by `ALG`: the (arm, reward) pairs of the rounds in which it was called, in
order. -/
def algHistory (N₀ : ℕ) {t : ℕ} (h : HERecord t) : BanditHistory 2 (algRounds N₀ h).card :=
  fun i ↦ (recHE h ((algRounds N₀ h).orderEmbOfFin rfl i), (h ((algRounds N₀ h).orderEmbOfFin rfl i)).2)

/-- The probability of round `t` of the record `h` given the mean vector `μ`, for RepeatedHE
with bandit algorithm `A`, `N₀` initial rounds and exploration probability `ε`: in an initial
round the arm is 1 and the round is an exploration round; afterwards the round is an exploration
round with probability `ε`, in which case the arm is drawn by `ALG` from its own history, and
otherwise the arm is the exploitation branch's; the reward is then drawn from `D_{μ(a_t)}`. -/
def roundProb (P : Measure (Fin 2 → ℝ)) (F : Finset (Fin 2 → ℝ)) (fam : RewardFamily)
    (A : BanditPolicy 2) (N₀ : ℕ) (ε : ℝ) (μ : Fin 2 → ℝ) {T : ℕ} (h : HERecord T) (t : Fin T) :
    ENNReal :=
  let hp := hePrefix h t.isLt.le
  let branch : ENNReal :=
    if t.val < N₀ then (if isExplore h t then 1 else 0)
    else (if isExplore h t then ENNReal.ofReal ε else ENNReal.ofReal (1 - ε))
  let arm : ENNReal :=
    if t.val < N₀ then (if recHE h t = 0 then 1 else 0)
    else if isExplore h t then (A.select _ (algHistory N₀ hp)) {recHE h t}
    else (if recHE h t = exploitArmHE P F fam hp then 1 else 0)
  branch * arm * fam.D (μ (recHE h t)) {(h t).2}

/-- The probability `Pr[record = h | μ]` of a whole record. -/
def recordProb (P : Measure (Fin 2 → ℝ)) (F : Finset (Fin 2 → ℝ)) (fam : RewardFamily)
    (A : BanditPolicy 2) (N₀ : ℕ) (ε : ℝ) (μ : Fin 2 → ℝ) {T : ℕ} (h : HERecord T) : ENNReal :=
  ∏ t, roundProb P F fam A N₀ ε μ h t

/-- The finite set of records whose rewards lie in `fam.values`; every other record has
probability zero. -/
def heRecords (fam : RewardFamily) (T : ℕ) : Finset (HERecord T) :=
  Fintype.piFinset fun _ : Fin T ↦ (univ : Finset (Bool × Fin 2)) ×ˢ fam.values

/-- The joint law of the mean vector `μ ~ P` (supported on `F`) and the `T`-round record of
RepeatedHE when every agent complies: a finitely supported measure, `μ` and the record `h`
carrying the weight `P({μ}) · Pr[record = h | μ]`. -/
def repeatedHELaw (P : Measure (Fin 2 → ℝ)) (F : Finset (Fin 2 → ℝ)) (fam : RewardFamily)
    (A : BanditPolicy 2) (N₀ : ℕ) (ε : ℝ) (T : ℕ) : Measure ((Fin 2 → ℝ) × HERecord T) :=
  ∑ μ ∈ F, ∑ h ∈ heRecords fam T,
    (P {μ} * recordProb P F fam A N₀ ε μ h) • Measure.dirac (μ, h)

/-- The expectation `E[f(record)]` of a function of the `T`-round record under the joint law of
RepeatedHE. -/
def heExpect (P : Measure (Fin 2 → ℝ)) (F : Finset (Fin 2 → ℝ)) (fam : RewardFamily)
    (A : BanditPolicy 2) (N₀ : ℕ) (ε : ℝ) (T : ℕ) (f : HERecord T → ℝ) : ℝ :=
  ∑ μ ∈ F, ∑ h ∈ heRecords fam T, (P {μ} * recordProb P F fam A N₀ ε μ h).toReal * f h

end IntroBandits

end


