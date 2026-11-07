-- Prove2me | Definitions.Def_DynOracleConn_RandAlg
-- name    : DynOracleConn_RandAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:50:32.124425+00:00
-- url     : https://prove2.me/theorems/313eb96b-b82a-4041-81db-fcb0a1f725e5
-- title:
--   Randomized dynamic algorithms and expected amortized cost
-- statement:
--   A **randomized dynamic algorithm** is a probability space $(\Omega,\mu)$ together with a deterministic algorithm $A_\omega$ for each outcome $\omega$, all with the same state set $S$. Reading independent uniform random words is the special case where $\Omega$ is the space of random tapes, and the tape is not charged as memory.
--
--   It has **measurable runs** when, for each update sequence, every set of transcripts has a measurable preimage under $\omega\mapsto$ (the transcript of $A_\omega$ on $\sigma$).
--
--   It has **expected amortized cost at most $T$** when, for every valid forest sequence $\sigma$,
--
--   $$\mathbb E_\omega[\mathrm{cost}(A_\omega,\sigma)]\le|\sigma|\,T.$$
--
--   This is the paper's "E[cost(σ)] ≤ |σ|T for every fixed update sequence σ", restricted to the sequences its lower bound uses.
--
--   **Formalization Note** The expectation is a lower Lebesgue integral in $[0,\infty]$, and for $T<0$ the right side is $0$. Measurability is needed for the probability of correctness to be meaningful on a general $\Omega$.
-- source:
--   Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, Connectivity in a New Bounded-Space Dynamic Model, STOC 2027 submission (manuscript sha256 e9b19480…), §1.1, p.4 and §1.2, p.7

import Mathlib
import Definitions.Def_DynOracleConn_DetAlg

namespace DynOracleConn

/-!
# Randomized dynamic oracle algorithms and expected amortized cost

Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, *Connectivity in a New Bounded-Space
Dynamic Model*, STOC 2027 submission (manuscript sha256 e9b19480…), §1.1, p.4: "An expected
amortized bound requires E[cost(σ)] ≤ |σ|T for every fixed update sequence σ." … "A randomized
algorithm may additionally read independent, uniformly random words." p.7: "Probabilities and
expectations are over the algorithm's randomness."

**Formalization Note.**
1. A randomized algorithm is a probability space `(Ω, μ)` together with a deterministic algorithm
   `alg ω` for every outcome `ω`, all with the same state type `S`. Reading independent uniform
   random words is the special case where `Ω` is the space of random tapes; the tape is not
   charged as memory.
2. `MeasurableRuns A O`: for every update sequence, the run's transcript (probes, replies,
   answers) is a measurable function of `ω` for the discrete σ-algebra on transcripts, i.e. every
   preimage is measurable. Without it, the probability of "all answers correct" is not defined for
   general `Ω`.
3. `ExpAmortized A O T`: for every valid update sequence that keeps the graph a forest, the
   expected total number of probes is at most `|σ| · T`. The expectation is a lower Lebesgue
   integral in `[0, ∞]`; for `T < 0` the right side is `0`.
-/

open MeasureTheory

/-- A randomized dynamic algorithm: a probability space of deterministic algorithms with a common
state type `S`. -/
structure RandAlg (n : ℕ) (Q Ans S : Type) : Type 1 where
  /-- The randomness (e.g. the random tape). -/
  Ω : Type
  [measΩ : MeasurableSpace Ω]
  /-- Its law. -/
  μ : Measure Ω
  [isProb : IsProbabilityMeasure μ]
  /-- The deterministic algorithm run on outcome `ω`. -/
  alg : Ω → DetAlg n Q Ans S

attribute [instance] RandAlg.measΩ RandAlg.isProb

variable {n : ℕ} {Q Ans S : Type}

/-- The transcript of the run on every fixed update sequence is a measurable function of the
randomness: every set of transcripts has a measurable preimage. -/
def MeasurableRuns (A : RandAlg n Q Ans S) (O : SimpleGraph (Fin n) → Q → Ans) : Prop :=
  ∀ (σ : List (PunctSketch.Update n)) (P : Set (List (List (Q × Ans) × Bool))),
    MeasurableSet ((fun ω => (A.alg ω).transcript O σ) ⁻¹' P)

/-- Expected amortized cost at most `T` per update: on every valid update sequence `σ` under which
the graph stays a forest, the expected total number of probes is at most `|σ| · T`. -/
def ExpAmortized (A : RandAlg n Q Ans S) (O : SimpleGraph (Fin n) → Q → Ans) (T : ℝ) : Prop :=
  ∀ σ : List (PunctSketch.Update n), PunctSketch.IsValidStream σ → ForestThroughout σ →
    ∫⁻ ω, ((A.alg ω).totalCost O σ : ENNReal) ∂A.μ ≤ ENNReal.ofReal (σ.length * T)

end DynOracleConn


