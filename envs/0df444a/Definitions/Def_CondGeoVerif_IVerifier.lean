-- Prove2me | Definitions.Def_CondGeoVerif_IVerifier
-- name    : CondGeoVerif_IVerifier
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:25:29.207377+00:00
-- url     : https://prove2.me/theorems/9908f96a-8631-441b-8bd1-57ff66b5bf0a
-- title:
--   Interactive improper verifiers, prover strategies, soundness, completeness at a known law
-- statement:
--   An **interactive verifier** in dimension $d$ draws a private sample of $m_V$ labeled observations and coins from an arbitrary probability space, and runs $R$ rounds with a prover: in round $i$ it sends a query (in an arbitrary measurable space), computed from its sample, its coins and the answers so far, and receives an answer (in an arbitrary measurable space). At the end it accepts or rejects and, on acceptance, outputs an arbitrary measurable predictor $\mathbb R^d\to\{-1,1\}$, not necessarily in the class. A **prover strategy** answers each round as a function of the queries so far.
--
--   1. **Arbitrary-label Gaussian soundness** against $\mathcal H$: for every law with Gaussian feature marginal and every measurable prover strategy, the probability that the run outputs some $h$ with $R_P(h)>\mathrm{OPT}_P(\mathcal H)+\varepsilon$ is at most $\delta$.
--   2. **Completeness at a known law $Q$**: some honest prover, using any number of its own observations from $Q$, its own coins, and a strategy measurable in all of these, makes the run output some $h$ with $R_Q(h)\le\mathrm{OPT}_Q(\mathcal H)+\varepsilon$ with probability at least $1-\delta$.
--
--   This is the verifier model of the lower bounds: interaction, communication and computation are unrestricted, and outputs may be improper.
--
--   **Formalization Note** Queries, the acceptance bit and the output predictor are measurable in all their arguments (the predictor jointly in sample, coins, answers and feature), so every probability is defined. The number of rounds is a fixed worst-case bound. Soundness is required against measurable deterministic strategies; a measurable randomized strategy, such as the simulated honest prover in the proof of Theorem B.1, is a mixture of them. A one-message verifier with measurable decision is the case of one round with a trivial query.
-- source:
--   T. Y. Chen, The Conditional Geometry of Statistical Verification, manuscript (October 2026, STOC 2027 submission, sha256 07a66d18…), §2, p.3 (PDF p.6); Theorem B.1, p.24 (PDF p.27); §B.5, p.27 (PDF p.30)

import Mathlib
import Definitions.Def_CondGeoVerif_risk

set_option autoImplicit false

namespace CondGeoVerif

open MeasureTheory

/-- An **interactive, possibly improper verifier** in ambient dimension `d` (Chen, *The
Conditional Geometry of Statistical Verification*, manuscript, October 2026, sha256 07a66d18…,
§2, p.3: "All lower bounds permit arbitrary interaction and improper outputs"; Theorem B.1, p.24:
"Interaction, computation, communication, and the malicious prover's knowledge are unrestricted").

The verifier draws a private sample of `m` labeled observations and coins from an arbitrary
probability space. It runs `R` rounds: in round `i` it sends the query
`query i (sample) (coins) (answers so far)` in an arbitrary measurable space `Qs` and receives an
answer in an arbitrary measurable space `As`. At the end it accepts or rejects
(`accept (sample) (coins) (all answers)`) and, on acceptance, outputs the predictor
`pred (sample) (coins) (all answers) : ℝᵈ → {−1, 1}`, which need not belong to the class.

**Formalization Note** `m` is the worst-case private sample count `m_V`; every observation
counts (a bounded stopping rule is padded with unused samples, p.28). Queries, the acceptance bit
and the predictor are measurable in all their arguments; in particular the output predictor is
jointly measurable in (sample, coins, answers, feature), so it is a measurable Boolean predictor
for each run ("Outputs may be arbitrary measurable Boolean predictors", p.24). A one-message
verifier with measurable decision is the case `R = 1`, `Qs = Unit`, `As = Msg`. -/
structure IVerifier (d : ℕ) where
  /-- The private sample count `m_V`. -/
  m : ℕ
  /-- The verifier's coin space. -/
  Ω : Type
  [mΩ : MeasurableSpace Ω]
  /-- The law of the verifier's coins. -/
  coins : ProbabilityMeasure Ω
  /-- The number of rounds. -/
  R : ℕ
  /-- The query space. -/
  Qs : Type
  [mQ : MeasurableSpace Qs]
  /-- The answer space. -/
  As : Type
  [mA : MeasurableSpace As]
  /-- The query of round `i`, from the sample, the coins and the first `i` answers. -/
  query : (i : Fin R) → (Fin m → Vec d × Bool) → Ω → (Fin i → As) → Qs
  /-- The acceptance bit. -/
  accept : (Fin m → Vec d × Bool) → Ω → (Fin R → As) → Bool
  /-- The output predictor (used on acceptance). -/
  pred : (Fin m → Vec d × Bool) → Ω → (Fin R → As) → Vec d → Bool
  query_meas : ∀ i : Fin R,
    Measurable (fun p : ((Fin m → Vec d × Bool) × Ω) × (Fin i → As) => query i p.1.1 p.1.2 p.2)
  accept_meas :
    Measurable (fun p : ((Fin m → Vec d × Bool) × Ω) × (Fin R → As) => accept p.1.1 p.1.2 p.2)
  pred_meas :
    Measurable (fun p : (((Fin m → Vec d × Bool) × Ω) × (Fin R → As)) × Vec d =>
      pred p.1.1.1 p.1.1.2 p.1.2 p.2)

attribute [instance] IVerifier.mΩ IVerifier.mQ IVerifier.mA

/-- A **prover strategy** against an interactive verifier: the answer of round `i` as a function of
the queries of rounds `0, …, i` (deterministic and history dependent). Randomized strategies are
mixtures of these. -/
def Strategy {d : ℕ} (V : IVerifier d) : Type :=
  (i : Fin V.R) → (Fin ((i : ℕ) + 1) → V.Qs) → V.As

/-- A strategy is **measurable** if every round's answer map is measurable in the query history. -/
def Strategy.IsMeasurable {d : ℕ} {V : IVerifier d} (σ : Strategy V) : Prop :=
  ∀ i : Fin V.R, Measurable (σ i)

/-- The answers of the first `n` rounds of the run of `V` against `σ`, on sample `s` and coins `ω`,
by recursion on the rounds. -/
def answersUpTo {d : ℕ} (V : IVerifier d) (σ : Strategy V) (s : Fin V.m → Vec d × Bool) (ω : V.Ω) :
    (n : ℕ) → n ≤ V.R → (Fin n → V.As)
  | 0, _ => Fin.elim0
  | n + 1, h =>
    let prev := answersUpTo V σ s ω n (Nat.le_of_succ_le h)
    Fin.snoc (α := fun _ => V.As) prev
      (σ ⟨n, h⟩ (fun j => V.query ⟨j, lt_of_le_of_lt (Nat.le_of_lt_succ j.2) h⟩ s ω
        (fun l => prev ⟨l, lt_of_lt_of_le l.2 (Nat.le_of_lt_succ j.2)⟩)))

/-- The outcome of a complete run: the output predictor on acceptance, `none` on rejection. -/
def outcome {d : ℕ} (V : IVerifier d) (σ : Strategy V) (s : Fin V.m → Vec d × Bool) (ω : V.Ω) :
    Option (Vec d → Bool) :=
  if V.accept s ω (answersUpTo V σ s ω V.R le_rfl) then
    some (V.pred s ω (answersUpTo V σ s ω V.R le_rfl))
  else none

/-- **Arbitrary-label Gaussian soundness** of an interactive verifier against a class `H` (Chen,
Oct. 2026, Definition 2.1, p.3; Theorem B.1, p.24: "for every prover, the probability of
outputting a predictor of risk greater than inf_{h∈H_{f,d}} R(h) + ε is at most 1/3; rejection is
allowed"): for every law with feature marginal `N(0, I_d)` and every measurable prover strategy,
the probability that the run outputs some `h` with `R_P(h) > OPT_P(H) + ε` is at most `δ`.

**Formalization Note** Soundness is required against measurable deterministic strategies; a
measurable randomized strategy (in particular the simulated honest prover of the proof of
Theorem B.1) is a mixture of them. All maps are measurable, so the bad event is measurable. -/
def ISound {d : ℕ} (V : IVerifier d) (H : Set (Vec d → Bool)) (ε δ : ℝ) : Prop :=
  ∀ P : ProbabilityMeasure (Vec d × Bool), GaussMarginal (P : Measure (Vec d × Bool)) →
    ∀ σ : Strategy V, σ.IsMeasurable →
      ((sampleLaw P V.m).prod (V.coins : Measure V.Ω))
          {sω | ∃ h, outcome V σ sω.1 sω.2 = some h ∧
            risk (P : Measure (Vec d × Bool)) h > opt (P : Measure (Vec d × Bool)) H + ε}
        ≤ ENNReal.ofReal δ

/-- **Completeness at a single known law `Q`** (Chen, Oct. 2026, Theorem B.1, p.24: "complete with
probability at least 2/3 at the single known null Q"; "An honest prover may use any number of
samples independent of the verifier's samples"): there is an honest prover, drawing any number
`m_P` of its own observations from `Q` and coins from any probability space, and answering through
a strategy that is jointly measurable in (its sample, its coins, the query history), under which the
run outputs a correct predictor, i.e. some `h` with `R_Q(h) ≤ OPT_Q(H) + ε`, with probability at
least `1 − δ`. The prover's and the verifier's samples are independent. -/
def ICompleteAt {d : ℕ} (V : IVerifier d) (Q : ProbabilityMeasure (Vec d × Bool))
    (H : Set (Vec d → Bool)) (ε δ : ℝ) : Prop :=
  ∃ (mP : ℕ) (Ωp : Type) (_ : MeasurableSpace Ωp) (μp : ProbabilityMeasure Ωp)
    (hon : (Fin mP → Vec d × Bool) → Ωp → Strategy V),
    (∀ i : Fin V.R,
      Measurable (fun p : ((Fin mP → Vec d × Bool) × Ωp) × (Fin ((i : ℕ) + 1) → V.Qs) =>
        hon p.1.1 p.1.2 i p.2)) ∧
    ENNReal.ofReal (1 - δ) ≤
      (((sampleLaw Q mP).prod (μp : Measure Ωp)).prod ((sampleLaw Q V.m).prod (V.coins : Measure V.Ω)))
        {x | ∃ h, outcome V (hon x.1.1 x.1.2) x.2.1 x.2.2 = some h ∧
          risk (Q : Measure (Vec d × Bool)) h ≤ opt (Q : Measure (Vec d × Bool)) H + ε}

end CondGeoVerif


