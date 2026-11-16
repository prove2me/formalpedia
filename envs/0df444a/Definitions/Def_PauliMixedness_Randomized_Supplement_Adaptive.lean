-- Prove2me | Definitions.Def_PauliMixedness_Randomized_Supplement_Adaptive
-- name    : PauliMixedness_Randomized_Supplement_Adaptive
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T16:53:47.281203+00:00
-- url     : https://prove2.me/theorems/33fd975c-8465-41a6-8fd0-99dc94ea299e
-- title:
--   Randomized adaptive single-copy mixedness protocols
-- statement:
--   Fix an arbitrary measurable seed space $\Omega$ and a probability law $\mu$, independent of the unknown state. At each classical history $h$, the protocol selects a finite POVM $M(r,h)$ measurably in the seed $r$. Its outcome count may vary with the seed and history; padded effect entries and the count are measurable. The final acceptance kernel $a(r,h)\in[0,1]$ is measurable and depends only on this classical information. Starting with history $h$ and $k$ remaining copies, define
--
--   $$F_0(\rho,r,h)=a(r,h),\qquad F_{k+1}(\rho,r,h)=\sum_{x=0}^{m(r,h)-1}\operatorname{Re}\operatorname{Tr}(M_x(r,h)\rho)F_k(\rho,r,hx).$$
--
--   The acceptance probability is $p_\rho=\int F_n(\rho,r,\varnothing)\,d\mu(r)$. Lean computes this with a nonnegative integral followed by conversion to real; for density matrices the integrand is measurable and belongs to $[0,1]$, so the integral is finite. `Uses` requires every selected measurement before the copy budget is exhausted to belong to the allowed class. Success means $p_{\rho_{\rm mm}}\ge2/3$ and $1-p_\rho\ge2/3$ for every density matrix with unhalved trace distance at least $\varepsilon$ from $\rho_{\rm mm}$.
--
--   The finite branching recursion gives the physical outcome law without a state oracle or an assumed correctness guarantee. Arbitrary probability spaces for shared and private classical randomness are allowed; only classical history passes between copies.
-- source:
--   Abhilash Dharmavarapu, Jayadev Acharya, Nengkun Yu, Yuhan Liu, STOC 2027 submission #231 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/231.pdf, §1.1 p.2; §5 and Eq. (3) p.18

import Definitions.Def_PauliMixedness_Randomized_Supplement_Measurements

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace PauliMixedness.Randomized.Supplement

/-- §§1.1,5: an arbitrary measurable seed, a finite POVM at each classical
history, and an outcome-only randomized decision. No state is an input to the rule.
Outcome cardinalities may depend on both seed and history. -/
structure AdaptiveProtocol (N : ℕ) (Ω : Type) [MeasurableSpace Ω] where
  measurement : Ω → List ℕ → FinitePOVM N
  accept : Ω → List ℕ → Set.Icc (0 : ℝ) 1
  measurable_count : ∀ h, Measurable (fun r => (measurement r h).outcomes)
  measurable_effect : ∀ h x i j,
    Measurable (fun r => paddedEffect (measurement r h) x i j)
  measurable_accept : ∀ h, Measurable (fun r => (accept r h : ℝ))

/-- Finite branching Born expectation for the remaining copies. The recursion
uses only one fresh copy at each node and appends only its classical outcome. -/
def conditionalAccept {N : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (A : AdaptiveProtocol N Ω) (ρ : Operator N) (r : Ω) : ℕ → List ℕ → ℝ
  | 0, h => (A.accept r h : ℝ)
  | k+1, h => ∑ x : Fin (A.measurement r h).outcomes,
      QAlgorithms.effectProb ((A.measurement r h).effect x) ρ *
        conditionalAccept A ρ r k (h ++ [x.val])

/-- Seed-averaged acceptance. For states, conditionalAccept is measurable and
lies in [0,1] by the finite Born recursion, so this lintegral is finite.
Using a nonnegative integral avoids the Bochner non-integrability default. -/
def adaptiveAcceptProbability {N : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (A : AdaptiveProtocol N Ω) (μ : Measure Ω) (n : ℕ) (ρ : Operator N) : ℝ :=
  (∫⁻ r, ENNReal.ofReal (conditionalAccept A ρ r n []) ∂μ).toReal

/-- Every measurement chosen on any seed/history belongs to the allowed class. -/
def Uses {N : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (A : AdaptiveProtocol N Ω) (n : ℕ) (M : Set (FinitePOVM N)) : Prop :=
  ∀ r h, h.length < n → A.measurement r h ∈ M

/-- Eq. (3), p.18: both worst-case testing errors are at most 1/3,
with the same protocol and seed law for all input density matrices. -/
def AdaptiveSucceeds {N : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (A : AdaptiveProtocol N Ω) (μ : Measure Ω) (n : ℕ) (ε : ℝ) : Prop :=
  (2 / 3 : ℝ) ≤ adaptiveAcceptProbability A μ n (maximallyMixed N) ∧
    ∀ ρ : Operator N, QAlgorithms.IsDensityMatrix ρ →
      ε ≤ QAlgorithms.traceNorm (ρ - maximallyMixed N) →
        (2 / 3 : ℝ) ≤ 1 - adaptiveAcceptProbability A μ n ρ

end PauliMixedness.Randomized.Supplement


