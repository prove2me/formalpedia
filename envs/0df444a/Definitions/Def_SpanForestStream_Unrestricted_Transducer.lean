-- Prove2me | Definitions.Def_SpanForestStream_Unrestricted_Transducer
-- name    : SpanForestStream_Unrestricted_Transducer
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T02:31:39.606201+00:00
-- url     : https://prove2.me/theorems/95f52fec-c446-4a6c-903a-a451397c34d7
-- title:
--   Event-driven private-randomness streaming transducers, worst-case and expected peak space, retained-linear state
-- statement:
--   A randomized one-pass algorithm on $[v]$ (App. A) is an **event-driven private-randomness transducer**. Its **complete state** is a binary string, charged by its length. It consists of a **setup law** for the initial state (setup data and stored randomness included), one **update kernel** for each update symbol giving the law of the next complete state from the current one, where the outcome *none* means the update never finishes, and a **report kernel** giving the law of the answer (a set of edge names, or *none* for failure or a malformed answer) from the final complete state with fresh coins. Transitions are arbitrary. The future law depends only on the complete state and the next symbol, so there is no free clock, reusable random tape or input-position register. The parameters (such as $\delta$) are fixed when the algorithm is chosen.
--
--   The **run** on a stream $w$ is the law of the list of complete states $s_0,s_1,\dots$ at the event boundaries, together with whether every update finished. The **failure probability** on a fixed stream $w$ is the probability that the report is not a spanning forest of $G(w)$; nonresponse, failure and malformed output count as errors. The **peak** of a run is $\max_i|s_i|$.
--
--   - **Worst-case peak space**: the supremum of the peak over legal streams and over runs of positive probability.
--   - **Worst-input expected peak space**: $\sup_w\mathbb E[\text{peak}]$ over legal streams, with the expectation over the private randomness and no conditioning on success.
--
--   Space is measured as peak plus one.
--
--   **Retained-linear state** (§6.1, over $\mathbb F_2$). There are a graph-independent setup law on data $\rho$, a dimension $s$, $\mathbb F_2$-linear maps $M_\rho:\mathbb F_2^{\binom v2}\to\mathbb F_2^{s}$ and an injective encoding $\mathrm{enc}$ such that on every legal stream the whole run, with one $\rho$ for the entire stream, is $\mathrm{enc}(\rho,M_\rho x)$ at every event boundary, where $x$ is the current adjacency vector, and every update finishes.
--
--   **Formalization Note** Space is read at event boundaries. Lower bounds over this class are at least as strong as the paper's, since transitions are arbitrary. The effectiveness remark of §6.1 (columns computable from the stored description) is not encoded.
-- source:
--   Chao, Cen, Ma, Wang, Space-Optimal Algorithms for Spanning Forests in Dynamic Streams at Every Confidence Level, arXiv:2611.04365 (PDF sha256 00f5bb17…69c92), p. 45 (PDF 48), Appendix A; p. 7 (PDF 10), §1.5; p. 43 (PDF 46), §6.1

import Mathlib
import Definitions.Def_SpanForestStream_Unrestricted_Stream

open scoped ENNReal

namespace SpanForestStream.Unrestricted

noncomputable section

/-!
# Event-driven private-randomness transducers and their peak space

Chao, Cen, Ma, Wang, arXiv:2611.04365: App. A, p. 45; §1.5, p. 7; §6.1, p. 43.

An algorithm for vertex count `v` (its parameters, such as the confidence `δ`, are fixed when it
is chosen) has bit-string complete states. Its future law depends only on its complete state and
the next input symbol: a setup law for the initial state, one Markov kernel per update symbol, and
a report kernel reading the final complete state with fresh coins. Transitions are arbitrary. An
update may fail to finish (`none`), which counts as an error at the report. There is no clock,
reusable random tape or input-position register beyond what the state stores, and all of the state
is charged.
-/

/-- A complete state: a binary string, charged by its length. -/
abbrev BitState := List Bool

/-- A randomized one-pass streaming algorithm on `[v]` with one report. -/
structure Transducer (v : ℕ) where
  /-- The law of the complete state after setup (setup data and stored randomness included). -/
  setup : PMF BitState
  /-- The law of the next complete state given the current one and the update; `none` means the
  update never finishes (nonresponse). -/
  update : BitState → Update v → PMF (Option BitState)
  /-- The answer law at the report; `none` is failure or a malformed answer. -/
  report : BitState → PMF (Option (Finset (EdgeName v)))

/-- The law of a run from state `s` on the updates `w`: the list of complete states at the
event boundaries `s, s₁, …` reached, and whether every update finished. -/
def Transducer.runFrom {v : ℕ} (A : Transducer v) :
    BitState → List (Update v) → PMF (List BitState × Bool)
  | s, [] => PMF.pure ([s], true)
  | s, u :: w => (A.update s u).bind fun o =>
      match o with
      | none => PMF.pure ([s], false)
      | some s' => (A.runFrom s' w).map fun r => (s :: r.1, r.2)

/-- The run law on the stream `w`: setup, then the updates of `w` in order, with fresh coins at
every step. -/
def Transducer.run {v : ℕ} (A : Transducer v) (w : List (Update v)) :
    PMF (List BitState × Bool) :=
  A.setup.bind fun s => A.runFrom s w

/-- The peak of a run: the largest bit length of a complete state at an event boundary. -/
def runPeak (r : List BitState × Bool) : ℕ :=
  (r.1.map List.length).foldr max 0

/-- The answer law on the stream `w` with one report at its end. -/
def Transducer.answer {v : ℕ} (A : Transducer v) (w : List (Update v)) :
    PMF (Option (Finset (EdgeName v))) :=
  (A.run w).bind fun r => if r.2 then A.report (r.1.getLastD []) else PMF.pure none

/-- Failure probability on the fixed stream `w`: the answer is not a spanning forest of the
current graph (failure, malformed output and nonresponse all count as errors). -/
def Transducer.errorProb {v : ℕ} (A : Transducer v) (w : List (Update v)) : ℝ≥0∞ :=
  (A.answer w).toOuterMeasure
    {o | ¬ ∃ F, o = some F ∧ IsSpanningForest (currentGraph w) F}

/-- Worst-case peak space: the supremum, over legal streams and over runs of positive
probability, of the peak. -/
def Transducer.hardPeak {v : ℕ} (A : Transducer v) : ℝ≥0∞ :=
  ⨆ (w : List (Update v)) (_ : IsLegal w) (r : List BitState × Bool) (_ : r ∈ (A.run w).support),
    (runPeak r : ℝ≥0∞)

/-- Worst-input expected peak space: the supremum, over legal streams, of the expected peak over
the private randomness, without conditioning on success. -/
def Transducer.expPeak {v : ℕ} (A : Transducer v) : ℝ≥0∞ :=
  ⨆ (w : List (Update v)) (_ : IsLegal w), ∑' r, A.run w r * (runPeak r : ℝ≥0∞)

/-- The retained state is a binary linear sketch conditional on the setup (§6.1): there are a
graph-independent setup law on data `ρ`, a dimension `s`, `F₂`-linear maps
`M_ρ : F₂^(v choose 2) → F₂^s` and an injective encoding `enc` such that on every legal stream the
whole run, one `ρ` for the entire stream, is `enc(ρ, M_ρ x)` at every event boundary, where `x` is
the current adjacency vector, and every update finishes. -/
def Transducer.IsRetainedLinear {v : ℕ} (A : Transducer v) : Prop :=
  ∃ (R : Type) (μ : PMF R) (s : ℕ)
    (M : R → (EdgeName v → ZMod 2) →ₗ[ZMod 2] (Fin s → ZMod 2))
    (enc : R × (Fin s → ZMod 2) → BitState),
    Function.Injective enc ∧
      ∀ w : List (Update v), IsLegal w →
        A.run w = μ.map fun ρ => (w.inits.map fun p => enc (ρ, M ρ (adjVector p)), true)

end

end SpanForestStream.Unrestricted


