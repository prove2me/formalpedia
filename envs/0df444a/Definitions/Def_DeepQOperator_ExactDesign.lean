-- Prove2me | Definitions.Def_DeepQOperator_ExactDesign
-- name    : DeepQOperator_ExactDesign
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:00:02.256464+00:00
-- url     : https://prove2.me/theorems/601d2d42-6592-475d-b9b7-cb69f28ee81c
-- title:
--   Randomized fixed designs of exact affine measurements
-- statement:
--   A **randomized fixed design of $N$ arbitrary-affine measurements** selects, from a private seed $\omega$ and before any reply, a matrix $C(\omega)\in\mathbb R^{N\times\iota}$ and an offset $b(\omega)\in\mathbb R^N$; it observes the exact real vector $C(\omega)\theta+b(\omega)$ and decides from that vector and the seed. Its worst expected regret on an input set $P$ for a loss $\ell$ is
--   $$\sup_{\theta\in P}\ \mathbb E_\omega\,\ell\big(A(\theta;\omega),\theta\big),\tag{20}$$
--   and the design is measurable when $C$ and $b$ are measurable in the seed and the decoder is jointly measurable.
--
--   These designs are the benchmark that finite-reply protocols are reduced to in the lower bounds of Theorem 2.
--
--   **Formalization Note** "At most $N$ measurements" is encoded by exactly $N$ rows with zero rows allowed. Decisions are Booleans; the regret is a supremum of lower Lebesgue integrals.
-- source:
--   Qi, Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions, STOC 2027 submission (manuscript sha256 9f8f3285…), Definition 1 p.3, §5 eq. (20) p.8 (PDF pp.6, 11)

import Mathlib

open MeasureTheory

namespace DeepQOperator

/-!
# Randomized fixed designs of exact affine measurements

Q. Qi, *Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions*,
STOC 2027 submission (manuscript sha256 9f8f3285…), Definition 1 p.3 (PDF p.6), §5 eq. (20) p.8
(PDF p.11).

A randomized fixed design of `N` arbitrary-affine measurements selects, from a private seed `ω`,
the matrix `C(ω)` and offset `b(ω)` of its measurements before any reply, observes the exact real
vector `C(ω)θ + b(ω)`, and decides from that vector and the seed. Its worst expected regret is
`sup_{θ ∈ P} E_ω ℓ(A(θ; ω), θ)` (20).

**Formalization Note.** "At most `N` measurements" is encoded by exactly `N` rows, zero rows
allowed (a zero row is a constant and carries no information). Decisions are `Bool`. The regret is
an `ℝ≥0∞`-valued lower Lebesgue integral and a supremum, with the loss `ℓ` a parameter of
`designRegret`. `IsMeasurable` is the joint measurability of §5.
-/

/-- A randomized fixed design of `N` exact affine measurements on parameters `ι → ℝ`. -/
structure ExactDesign (ι : Type) (Ω : Type*) (N : ℕ) where
  /-- the measurement matrix `C(ω)` -/
  C : Ω → Fin N → ι → ℝ
  /-- the measurement offsets `b(ω)` -/
  b : Ω → Fin N → ℝ
  /-- the decoder: seed and exact replies to a decision -/
  dec : Ω → (Fin N → ℝ) → Bool

namespace ExactDesign

variable {ι : Type} [Fintype ι] {Ω : Type*} {N : ℕ}

/-- The exact replies `C(ω)θ + b(ω)`. -/
def obs (D : ExactDesign ι Ω N) (θ : ι → ℝ) (ω : Ω) : Fin N → ℝ :=
  fun k => ∑ i, D.C ω k i * θ i + D.b ω k

/-- The decision on input `θ` and seed `ω`. -/
def decision (D : ExactDesign ι Ω N) (θ : ι → ℝ) (ω : Ω) : Bool := D.dec ω (D.obs θ ω)

/-- Measurability of the design in the seed and joint measurability of the decoder. -/
def IsMeasurable [MeasurableSpace Ω] (D : ExactDesign ι Ω N) : Prop :=
  (∀ k i, Measurable fun ω => D.C ω k i) ∧ (∀ k, Measurable fun ω => D.b ω k) ∧
    Measurable (fun p : Ω × (Fin N → ℝ) => D.dec p.1 p.2)

end ExactDesign

/-- Worst expected regret `sup_{θ ∈ S} E_ω ℓ(D(θ; ω), θ)` of a randomized fixed design. -/
noncomputable def designRegret {ι : Type} [Fintype ι] {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (S : Set (ι → ℝ)) (ℓ : Bool → (ι → ℝ) → ℝ) (μ : Measure Ω) (D : ExactDesign ι Ω N) : ENNReal :=
  ⨆ θ ∈ S, ∫⁻ ω, ENNReal.ofReal (ℓ (D.decision θ ω) θ) ∂μ

end DeepQOperator


