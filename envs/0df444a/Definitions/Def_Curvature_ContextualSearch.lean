-- Prove2me | Definitions.Def_Curvature_ContextualSearch
-- name    : Curvature_ContextualSearch
-- status  : Definition
-- author  : @ssakaue
-- created : 2026-11-24T07:21:58.57472+00:00
-- url     : https://prove2.me/theorems/7b740818-a7fd-45f3-b4e2-4453dd5a2c01
-- title:
--   Contextual search with noisy comparisons: prediction rule, noise condition and independent flips
-- statement:
--   This file defines the two probabilistic models of Corollary 7 and the prediction rule obtained from Algorithm 5. Contexts and the target lie in the unit ball $\mathbb B_2^d$, and the response to a context $\phi$ is $\langle\phi,u\rangle$ for the target $u$. After seeing the context $\phi_t$, the learner predicts $\widehat y_t$, and the comparison bit $Y_t\in\{-1,1\}$ reports the sign of $\widehat y_t-\langle\phi_t,u\rangle$, possibly with an error.
--
--   For the upper bound, the prediction rule runs Algorithm 5 on $\mathbb B_2^d$ with $G=1$, base learners using the fixed initialization of the Euclidean ball in standard coordinates, and the inputs $Y_s\phi_s$ of the earlier rounds $s<t$; it predicts $\widehat y_t\coloneqq\langle\phi_t,w_t\rangle$ and uses neither the target nor the noise level. The noise condition with parameter $\kappa$ requires a filtration $(\mathcal F_t)$ such that $\phi_t$ and $\widehat y_t$ are $\mathcal F_t$-measurable, $Y_t$ is $\mathcal F_{t+1}$-measurable with values in $\{-1,1\}$, and some $\mathcal F_t$-measurable sign $\sigma_t\in\{-1,1\}$ satisfies $\sigma_t(\widehat y_t-\langle\phi_t,u\rangle)=|\widehat y_t-\langle\phi_t,u\rangle|$, with either sign allowed at a tie, and $\Pr(Y_t=\sigma_t\mid\mathcal F_t)\ge(1+\kappa)/2$ almost surely.
--
--   For the lower bound, a learner predicts a value in $[-1,1]$ from a private seed, the earlier bits and the contexts up to the current round, and for each fixed history of bits and contexts its prediction is a measurable function of the seed. In the independent-flip model, the correct bit is $+1$ exactly when the prediction is at least the response. The learner observes its opposite with probability $(1-\kappa)/2$ and the correct bit otherwise. The flip decisions are independent across rounds and independent of the learner's seed, with the same probability for every target. The expected error of a learner on a finite context sequence is the expected cumulative absolute error $\sum_t|\widehat y_t-\langle\phi_t,u\rangle|$ over the seed and the flips. The coordinate schedule presents each standard basis vector $e_1,\ldots,e_d$ in turn for $\max\{1,\lfloor1/(16\kappa^2)\rfloor\}$ consecutive rounds. These definitions follow Section 5.1 and Appendix F.2.
-- source:
--   arXiv:2611.27572v1, Corollary 7, Section 5.1, p. 14; Appendix F, pp. 63–65. https://arxiv.org/html/2611.27572v1#Thmtheorem7

import Definitions.Def_Curvature_AdaptivePredictor
import Definitions.Def_Curvature_MinimaxGame
import Definitions.Def_Curvature_WidthAndSignGame
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.OfFn
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Probability.Process.Filtration
import Mathlib.Tactic

section
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace Curvature.ContextualSearch

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω}

/-- The indicator of receiving the correct comparison bit. -/
def correctComparison (bit sign : Ω → ℝ) (ω : Ω) : ℝ :=
  if bit ω = sign ω then 1 else 0


end Curvature.ContextualSearch

end
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature.ContextualSearch

abbrev History := List Bool
abbrev Strategy := History → ℝ


/-- Conditional mean of the two continuations. A true bit represents +1. -/
def branch (k : ℝ) (truth : Bool) (f t : ℝ) : ℝ :=
  let s := if truth then k else -k
  ((1 - s) * f + (1 + s) * t) / 2

def truthBit (x y : ℝ) : Bool := decide (y ≤ x)


end Curvature.ContextualSearch

end
end

section
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace Curvature.ContextualSearch


variable {Ω : Type*} [MeasurableSpace Ω]

/-- Independent initial seed with a measurable query at each possible bit history. -/
structure Learner (Ω : Type*) [MeasurableSpace Ω] where
  query : Ω → Strategy
  measurable : ∀ h, Measurable fun w => query w h
  bounded : ∀ w h, |query w h| ≤ 1


end Curvature.ContextualSearch

end
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature.ContextualSearch

/-- Independent correctness indicators. The distribution of the tape does not depend on
    the learner, target, history, or seed. -/
def flipExpectation (k : ℝ) : (n : ℕ) → ((Fin n → Bool) → ℝ) → ℝ
  | 0, f => f Fin.elim0
  | n+1, f =>
    branch k true (flipExpectation k n (fun b => f (Fin.cons false b)))
      (flipExpectation k n (fun b => f (Fin.cons true b)))


def observedBit (x y : ℝ) (correct : Bool) : Bool :=
  if correct then truthBit x y else !(truthBit x y)

/-- Absolute prediction error along a fixed target sequence and a fixed correctness tape. -/
def realizedError (p : Strategy) : (ys : List ℝ) → (Fin ys.length → Bool) → History → ℝ
  | [], _, _ => 0
  | y::ys, b, h => |p h - y| +
    realizedError p ys (Fin.tail b) (observedBit (p h) y (b 0) :: h)


end Curvature.ContextualSearch

end
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature

def searchUnitBall (d : ℕ) : Set (Vec d) := {x | norm₂ x ≤ 1}

private theorem searchUnitBall_eq (d : ℕ) : searchUnitBall d = canonicalUnitBall d 2 := by
  ext x
  change Real.sqrt (dotProduct x x) ≤ 1 ↔ ∑ i, |x i|^(2:ℝ) ≤ 1
  rw [Real.sqrt_le_left (by norm_num)]
  simp [dotProduct,pow_two]

theorem searchUnitBall_compact (d : ℕ) : IsCompact (searchUnitBall d) := by
  rw [searchUnitBall_eq]
  exact canonicalUnitBall_compact (by norm_num)

theorem searchUnitBall_convex (d : ℕ) : Convex ℝ (searchUnitBall d) := by
  rw [searchUnitBall_eq]
  exact canonicalUnitBall_convex (by norm_num)

theorem searchUnitBall_nonempty (d : ℕ) : (searchUnitBall d).Nonempty :=
  ⟨0, by simp [searchUnitBall,norm₂]⟩


/-- The fixed-matrix initialization in the standard Euclidean coordinates. -/
def searchUnitBall_initialization {d : ℕ} (hd : 0 < d) :
    DomainInitialization (searchUnitBall d) := by
  let : NeZero d := ⟨hd.ne'⟩
  refine .fixed (N:=d) (a:=fun _ => 1) (q:=2) 0 1 (fun _ => zero_lt_one)
    (by norm_num) (by norm_num) ?_ ?_ (.ball 1 rfl)
  · simp
  · rw [searchUnitBall_eq]
    norm_num [fixedUnitCoeffs, canonicalUnitBall]

end Curvature

end
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature

variable {d : ℕ}


def searchContext (i : Fin d) : Vec d := Pi.single i 1


/-- Number of consecutive presentations of each coordinate. -/
def searchBlockLength (κ : ℝ) : ℕ := max 1 ⌊1 / (16 * κ^2)⌋₊


end Curvature

end
end

section
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace Curvature.ContextualSearch

variable {d : ℕ}

/-- A prediction may depend on the private seed, all past bits and all contexts through this round.
The bit history has its newest entry first, while the contexts are indexed in chronological order. -/
structure ContextLearner (d : ℕ) (Ω : Type*) [MeasurableSpace Ω] where
  query : (h : History) → (Fin (h.length+1) → Vec d) → Ω → ℝ
  measurable : ∀ h ctx, Measurable (query h ctx)
  bounded : ∀ h ctx ω, |query h ctx ω| ≤ 1

variable {Ω : Type*} [MeasurableSpace Ω]

def ContextLearner.onSchedule (L : ContextLearner d Ω) (ctx : List (Vec d)) : Learner Ω where
  query := fun ω h => L.query h (fun i => ctx.getD i.val 0) ω
  measurable := fun h => L.measurable h _
  bounded := fun ω h => L.bounded h _ ω

/-- Average over the learner's private seed and the independent comparison flips. -/
def expectedError (μ : Measure Ω) (L : ContextLearner d Ω) (κ : ℝ)
    (ctx : List (Vec d)) (u : Vec d) : ℝ :=
  let ys := ctx.map (fun x => dotProduct x u)
  ∫ ω, flipExpectation κ ys.length
    (fun b => realizedError ((L.onSchedule ctx).query ω) ys b []) ∂μ

def coordinateSchedule (d n : ℕ) : List (Vec d) :=
  (List.finRange d).flatMap (fun i => List.replicate n (searchContext i))


end Curvature.ContextualSearch

end
end

section
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace Curvature.ContextualSearch

variable {d : ℕ}

/-- Linear loss input formed after receiving the comparison bit. -/
def feedback (φ : ℕ → searchUnitBall d) (Y : ℕ → ℝ) (t : ℕ) : Vec d :=
  Y t • (φ t).val

/-- Apply the adaptive unit-ball algorithm to past comparison inputs and predict with the
current context. The algorithm does not use the target or the noise bias. -/
def predictedResponse (I : DomainInitialization (searchUnitBall d)) {W : ℝ}
    (P : AdaptiveWeightRule (adaptiveWidthScale 1 W))
    (φ : ℕ → searchUnitBall d) (Y : ℕ → ℝ) (t : ℕ) : ℝ :=
  let B := I.adaptiveBase (searchUnitBall_nonempty d) (searchUnitBall_compact d)
    (searchUnitBall_convex d)
  dotProduct (φ t).val (B.adaptivePlay (searchUnitBall_convex d) P 1 (feedback φ Y) t).val


variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The filtration at index t describes information available just before the tth comparison.
The next sigma algebra contains the received bit. The correct sign may be chosen using
the information available before the bit, and either choice is valid at a tie. -/
structure ComparisonNoise (μ : Measure Ω) (κ : ℝ) (u : searchUnitBall d)
    (φ : ℕ → Ω → searchUnitBall d) (Y predict : ℕ → Ω → ℝ) where
  beforeBit : Filtration ℕ mΩ
  context_measurable : ∀ t, @Measurable Ω (searchUnitBall d) (beforeBit t) _ (φ t)
  prediction_measurable : ∀ t, @Measurable Ω ℝ (beforeBit t) _ (predict t)
  bit_measurable : ∀ t, @Measurable Ω ℝ (beforeBit (t+1)) _ (Y t)
  bit_values : ∀ t ω, Y t ω = -1 ∨ Y t ω = 1
  sign : ℕ → Ω → ℝ
  sign_measurable : ∀ t, @Measurable Ω ℝ (beforeBit t) _ (sign t)
  sign_values : ∀ t ω, sign t ω = -1 ∨ sign t ω = 1
  sign_correct : ∀ t ω,
    let error := predict t ω - dotProduct (φ t ω).val u.val
    sign t ω * error = |error|
  bias : ∀ t, ∀ᵐ ω ∂μ, (1 + κ)/2 ≤ μ[correctComparison (Y t) (sign t) | beforeBit t] ω


end Curvature.ContextualSearch

end
end


