-- Prove2me | Definitions.Def_DeepQOperator_Supplement_AdaptiveAlg
-- name    : DeepQOperator_Supplement_AdaptiveAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:38:58.068255+00:00
-- url     : https://prove2.me/theorems/896939e9-02cb-47c1-88a5-9d81aeafccd0
-- title:
--   Exact-real adaptive affine-query algorithms, bounded-error oracles and per-family worst-input regrets
-- statement:
--   A **randomized adaptive affine-query algorithm** over a parameter $\theta\in\mathbb{R}^\iota$ draws a private seed $\omega$ from a probability space $(\Omega,\mu)$, independent of $\theta$. At each stage it looks at the public transcript $h$ (the affine maps it has queried so far and the values it observed), and either stops or asks one affine functional $\theta\mapsto\alpha^{\mathsf T}\theta+\alpha_0$, where $(\alpha,\alpha_0)$ is a function of $(\omega,h)$. It observes $q_{\omega,h}(\text{reply})$, where the observation map $q$ is the identity in the exact model and an arbitrary quantizer otherwise. At the end it outputs a decision in $\{+,-\}$ from $(\omega,h)$. With a hard budget of $N$ queries the algorithm is run for at most $N$ steps. A deterministic algorithm has a one-point seed space.
--
--   For an input set $S$ and a loss $\ell$, the **worst-input expected regret** of such an algorithm is
--   $$
--   \sup_{\theta\in S}\ \mathbb{E}_{\omega}\,\ell\big(A(\theta;\omega),\theta\big).
--   $$
--   In the **bounded-error model** of §L.3, each query $q$ asked at public transcript $h$ is answered by $q(\theta)+E(h,q)$, where the error rule $E$ satisfies $|E|\le\tau$. The rule is chosen together with $\theta$ before the seed, sees the public preceding transcript and the current query, and cannot see the seed. The noisy worst-case regret takes the supremum over $\theta\in S$ and over all such rules.
--
--   The module also defines the analogous worst-input regret of a scalar-reply protocol on an arbitrary input set and loss. It defines what it means for a fixed design, an adaptive algorithm, or a protocol to be **raw** for a dictionary $D$ (every query lies in $D$), protocols whose every field is a single bit, protocols with at most $k$ fields, and at-most-two-stage adaptive algorithms.
--
--   These objects state the adaptive, quantized and bounded-error results (Theorems 3, 4, 5, 9, 11–15, 21, 24) for each Bellman family of the paper.
--
--   **Formalization Note** The transcript records the queried maps as well as the observed values. The maps are themselves functions of the seed and earlier values, so recording them gives the algorithm nothing new, but it lets an error rule read the public transcript. Measurability is joint in (seed, history) on every history length, and for the observation map also in the reply. Regrets are $\mathbb{R}_{\ge0}\cup\{\infty\}$-valued suprema of lower Lebesgue integrals and need not be attained.
-- source:
--   Qi, Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions, STOC 2027 submission (manuscript sha256 9f8f3285…), Definition 1, p.3 (PDF p.6); §5 eq. (20), p.8 (PDF p.11); §L.3, p.45 (PDF p.48); Appendix A, p.13 (PDF p.16)

import Mathlib
import Definitions.Def_DeepQOperator_Family
import Definitions.Def_DeepQOperator_ExactDesign
import Definitions.Def_DeepQOperator_ReplyProtocol

open MeasureTheory

namespace DeepQOperator.Supplement

/-!
# Exact-real adaptive query algorithms, bounded-error oracles, and per-family regrets

Q. Qi, *Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions*,
STOC 2027 submission (manuscript sha256 9f8f3285…), Definition 1 p.3 (PDF p.6), §5 eq. (20) p.8
(PDF p.11), §L.3 p.45 (PDF p.48), Appendix Q p.64 (PDF p.67), Appendix A p.13 (PDF p.16).

An adaptive algorithm chooses each affine scalar query `θ ↦ αᵀθ + α₀` from the earlier replies and
its private seed `ω`, may stop early, and finally decides from the seed and the replies. With a
quantizer it observes only a (measurable) function of each reply. In the bounded-error model of
§L.3 each queried scalar is returned with an additive error `e`, `|e| ≤ τ`, chosen by an error rule
from the public preceding transcript and the current query.

**Formalization Note.**
* A history is the public transcript: the list of queried affine maps and observed replies. The
  queried maps are themselves determined by the seed and the earlier replies, so giving them to the
  algorithm adds nothing; they are recorded so that an error rule can read the public transcript.
* `runWith A ans ω k h` runs at most `k` further queries from `h`, the oracle `ans` answering the
  query `q` at public transcript `h` by `ans h q`. The algorithms with a hard budget of `N` queries on
  every input and every random path are exactly the runs with fuel `N`: a run with fuel `N` never
  asks more than `N` queries, and an algorithm that never asks more than `N` queries on the inputs
  behaves identically when run with fuel `N`. So `decision A N θ ω` (exact oracle) is the final action
  of an algorithm with hard budget `N`.
* `quant` is the observation map applied to every exact reply; `IsExact` (identity) is the
  exact-information model. The alphabet of a quantizer is a subset of `ℝ`, which loses nothing: every
  standard Borel alphabet embeds measurably into `ℝ`.
* Deterministic algorithms are the case `Ω = Unit` with the Dirac measure.
* `IsMeasurable`: on every history length `k`, every component is jointly measurable in the seed and
  the history (`Ω × (Fin k → AffQuery ι × ℝ)`), the quantizer also in the reply (§5).
* `algRegret`, `noisyRegret`, `replyRegret` are worst-input expected regrets
  `sup_θ E_ω ℓ(A(θ; ω), θ)`, as `ℝ≥0∞`-valued suprema of lower Lebesgue integrals; the supremum need
  not be attained. The noisy regret also takes the supremum over error rules bounded by `τ`, chosen
  with `θ` before the seed and blind to it.
* `IsRawDesign`, `IsRawProtocol`, `AdaptiveAlg.IsRaw`: every query (row, field) lies in the given
  raw dictionary of the family.
-/

/-- A public transcript: the queried affine maps and the observed replies, in order. -/
abbrev Transcript (ι : Type) : Type := List (AffQuery ι × ℝ)

/-- A randomized adaptive algorithm with affine scalar queries over coordinates `ι` and seeds `Ω`. -/
structure AdaptiveAlg (ι : Type) (Ω : Type*) where
  /-- whether a further query is made at this history (`false` = stop) -/
  ask : Ω → Transcript ι → Bool
  /-- the affine map `(α, α₀)` queried at this history -/
  query : Ω → Transcript ι → AffQuery ι
  /-- the observation map applied to the reply (the identity in the exact model) -/
  quant : Ω → Transcript ι → ℝ → ℝ
  /-- the final decision (`true` is `+`) from the seed and the public transcript -/
  decide : Ω → Transcript ι → Bool

namespace AdaptiveAlg

variable {ι : Type} [Fintype ι] {Ω : Type*}

/-- Run at most `k` further queries from `h`, the oracle answering query `q` at transcript `h` by
`ans h q`; the observed value `quant (ans h q)` is appended with the query. -/
def runWith (A : AdaptiveAlg ι Ω) (ans : Transcript ι → AffQuery ι → ℝ) (ω : Ω) :
    ℕ → Transcript ι → Transcript ι
  | 0, h => h
  | k + 1, h =>
      if A.ask ω h then
        A.runWith ans ω k (h ++ [(A.query ω h, A.quant ω h (ans h (A.query ω h)))])
      else h

/-- The final action under the oracle `ans` with hard budget (fuel) `N`. -/
def decisionWith (A : AdaptiveAlg ι Ω) (ans : Transcript ι → AffQuery ι → ℝ) (N : ℕ) (ω : Ω) :
    Bool :=
  A.decide ω (A.runWith ans ω N [])

/-- The final action on input `θ` with exact replies and hard budget `N`. -/
def decision (A : AdaptiveAlg ι Ω) (N : ℕ) (θ : ι → ℝ) (ω : Ω) : Bool :=
  A.decisionWith (fun _ q => affEval q θ) N ω

/-- Exact information: the algorithm observes the replies themselves. -/
def IsExact (A : AdaptiveAlg ι Ω) : Prop := ∀ ω h x, A.quant ω h x = x

/-- Raw algorithm for the dictionary `D`: every asked query is a listed raw site. -/
def IsRaw (A : AdaptiveAlg ι Ω) (D : Set (AffQuery ι)) : Prop :=
  ∀ ω h, A.ask ω h = true → A.query ω h ∈ D

/-- At most two stages: a stage-one list fixed by the seed (positions `< k ω`), then a stage-two
list fixed by the first `k ω` entries of the transcript. -/
def IsAtMostTwoStage (A : AdaptiveAlg ι Ω) : Prop :=
  ∃ k : Ω → ℕ, ∀ ω (h h' : Transcript ι), h.length = h'.length →
    (h.length < k ω ∨ h.take (k ω) = h'.take (k ω)) →
      A.ask ω h = A.ask ω h' ∧ A.query ω h = A.query ω h' ∧ A.quant ω h = A.quant ω h'

/-- Joint measurability in the seed and the history on every history length. -/
def IsMeasurable [MeasurableSpace Ω] (A : AdaptiveAlg ι Ω) : Prop :=
  ∀ k : ℕ,
    Measurable (fun p : Ω × (Fin k → AffQuery ι × ℝ) => A.ask p.1 (List.ofFn p.2)) ∧
    Measurable (fun p : Ω × (Fin k → AffQuery ι × ℝ) => A.query p.1 (List.ofFn p.2)) ∧
    Measurable (fun p : (Ω × (Fin k → AffQuery ι × ℝ)) × ℝ =>
      A.quant p.1.1 (List.ofFn p.1.2) p.2) ∧
    Measurable (fun p : Ω × (Fin k → AffQuery ι × ℝ) => A.decide p.1 (List.ofFn p.2))

end AdaptiveAlg

/-- Worst-input expected regret `sup_{θ ∈ S} E_ω ℓ(A(θ; ω), θ)` of an adaptive algorithm with exact
oracle and hard budget `N`. -/
noncomputable def algRegret {ι : Type} [Fintype ι] {Ω : Type*} [MeasurableSpace Ω]
    (S : Set (ι → ℝ)) (ℓ : Bool → (ι → ℝ) → ℝ) (μ : Measure Ω) (A : AdaptiveAlg ι Ω) (N : ℕ) :
    ENNReal :=
  ⨆ θ ∈ S, ∫⁻ ω, ENNReal.ofReal (ℓ (A.decision N θ ω) θ) ∂μ

/-- A causal error rule bounded by `τ`: the error added to the reply of the current query `q`
depends only on the public preceding transcript `h` and on `q`. -/
def IsErrorRule {ι : Type} (τ : ℝ) (E : Transcript ι → AffQuery ι → ℝ) : Prop :=
  ∀ h q, |E h q| ≤ τ

/-- Worst-case expected regret under bounded errors: the supremum over inputs `θ ∈ S` and over
error rules bounded by `τ` (chosen with `θ`, before and independently of the seed) of the expected
loss, each query `q` being answered by `αᵀθ + α₀ + E(h, q)`. -/
noncomputable def noisyRegret {ι : Type} [Fintype ι] {Ω : Type*} [MeasurableSpace Ω]
    (S : Set (ι → ℝ)) (ℓ : Bool → (ι → ℝ) → ℝ) (μ : Measure Ω) (A : AdaptiveAlg ι Ω) (N : ℕ)
    (τ : ℝ) : ENNReal :=
  ⨆ θ ∈ S, ⨆ (E : Transcript ι → AffQuery ι → ℝ) (_ : IsErrorRule τ E),
    ∫⁻ ω, ENNReal.ofReal (ℓ (A.decisionWith (fun h q => affEval q θ + E h q) N ω) θ) ∂μ

/-- A fixed exact design whose every row is a raw site of the dictionary `D`. -/
def IsRawDesign {ι : Type} {Ω : Type*} {N : ℕ} (D : Set (AffQuery ι)) (X : ExactDesign ι Ω N) :
    Prop :=
  ∀ ω k, (X.C ω k, X.b ω k) ∈ D

/-- A scalar-reply protocol whose every requested field is a raw site of the dictionary `D`. -/
def IsRawProtocol {ι : Type} {Ω : Type*} (D : Set (AffQuery ι)) (P : ReplyProtocol ι Ω) : Prop :=
  ∀ ω h, P.ask ω h = true → (P.coef ω h, P.const ω h) ∈ D

/-- Every requested field of the protocol is a single bit. -/
def UsesOneBitReplies {ι : Type} {Ω : Type*} (P : ReplyProtocol ι Ω) : Prop :=
  ∀ ω h, P.ask ω h = true → P.len ω h = 1

/-- On every input of `S` and every seed, the protocol requests at most `k` fields. -/
def AtMostFields {ι : Type} [Fintype ι] {Ω : Type*} (P : ReplyProtocol ι Ω) (S : Set (ι → ℝ))
    (k : ℕ) : Prop :=
  ∀ θ ∈ S, ∀ ω j, (P.runFrom θ ω j []).length ≤ k

/-- Worst-input expected regret `sup_{θ ∈ S} E_ω ℓ(P(θ; ω), θ)` of a scalar-reply protocol with
fuel `B`. -/
noncomputable def replyRegret {ι : Type} [Fintype ι] {Ω : Type*} [MeasurableSpace Ω]
    (S : Set (ι → ℝ)) (ℓ : Bool → (ι → ℝ) → ℝ) (μ : Measure Ω) (P : ReplyProtocol ι Ω) (B : ℕ) :
    ENNReal :=
  ⨆ θ ∈ S, ∫⁻ ω, ENNReal.ofReal (ℓ (P.decision B θ ω) θ) ∂μ

end DeepQOperator.Supplement


