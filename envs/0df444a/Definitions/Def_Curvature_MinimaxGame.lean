-- Prove2me | Definitions.Def_Curvature_MinimaxGame
-- name    : Curvature_MinimaxGame
-- status  : Definition
-- author  : @ssakaue
-- created : 2026-11-24T07:18:34.513491+00:00
-- url     : https://prove2.me/theorems/59bd2032-9d48-4a3d-b476-e652631a16c4
-- title:
--   The minimax game with a comparator-loss budget and its standard domains
-- statement:
--   This file defines the game behind Theorem 21 and the domains for which the theorem is stated. Let $\mathcal K$ be a nonempty compact subset of a real inner product space $E$. For a horizon $T\ge1$ and losses $f_1,\ldots,f_T\colon E\to\mathbb R$ that are continuous on $\mathcal K$, the best loss is $\inf_{u\in\mathcal K}\sum_tf_t(u)$, the regret of predictions $w_1,\ldots,w_T$ is $\sum_tf_t(w_t)$ minus the best loss, and the minimum of the shifted comparator loss is
--
--   $$
--   \Delta_T^\star\coloneqq\inf_{u\in\mathcal K}\sum_{t=1}^Tf_t(u)-\sum_{t=1}^T\inf_{w\in\mathcal K}f_t(w).
--   $$
--
--   A full-information learner chooses $w_t\in\mathcal K$ from a private seed and the loss functions $f_1,\ldots,f_{t-1}$, and for each fixed history of losses its prediction is a measurable function of the seed. Its predictions do not depend on the horizon. Such a learner has a hard sequence at level $R$ for $(G,b)$ if there are $T\ge1$ and losses $f_1,\ldots,f_T$, each convex and $G$-Lipschitz on $E$, with $\Delta_T^\star\le b$, for which the regret is integrable in the seed and its expectation is at least $R$.
--
--   For the minimax value on $E=\mathbb R^d$, a strategy is a full-information learner together with a probability law for its seed. An environment consists of a horizon $T\ge1$, a probability law for its own seed, and a causal policy that chooses $f_t$ from the past predictions, the past losses, the current prediction $w_t$ and its seed. Every loss must be convex and $G$-Lipschitz on $\mathbb R^d$, and $\Delta_T^\star\le b$ must hold for every pair of seeds. The realized regret, as a function of the two seeds, must be almost everywhere strongly measurable for the product of the two seed laws, and the payoff is its expectation under this product law. The minimax value $R_\infty^\star(\mathcal K,G,b)$ is the infimum over strategies of the supremum over environments of the payoff, taken in the extended reals. Since the value is defined for each budget $b$, the strategy may depend on $b$.
--
--   The file also defines the one-subgradient upper-bound property with constant $c$. It requires a single deterministic rule that computes $w_t\in\mathcal K$ from the earlier feedback vectors $g_1,\ldots,g_{t-1}$ and is common to every horizon and every budget. Suppose that $f_1,\ldots,f_T$ are convex and $G$-Lipschitz on $E$, and that each $g_s$ satisfies $\lVert g_s\rVert\le G$ and $f_s(w_s)-f_s(v)\le\langle g_s,w_s-v\rangle$ for all $v\in\mathcal K$. Then the regret of the rule must be at most $c\bigl(G\,\omega_{\psi_1}(\mathcal K)+\sqrt{G\,\omega_{\psi_1}(\mathcal K)\,b}\bigr)$ for every $b\ge\Delta_T^\star$, where $\omega_{\psi_1}(\mathcal K)$ is the maximal subexponential mean width. In ambient dimension $d\ge1$, the standard domains in Corollary 12 are the unit $\ell_p$ balls $\{x:\sum_i|x_i|^p\le1\}$ with $1\le p<\infty$, the unit $\ell_\infty$ ball, the closed Euclidean balls of radius $R>0$ centered at the origin, the ellipsoids and boxes of dimension $1\le r\le d$ with arbitrary center and orthonormal axes, and the probability simplex for $d\ge2$. The file also defines finite histories over a finite alphabet, which index the sparse loss sequences of the lower-bound construction.
-- source:
--   arXiv:2611.27572v1, Theorem 21 and Appendix E, pp. 58–62; Corollary 12, p. 30. https://arxiv.org/html/2611.27572v1#Thmtheorem21

import Definitions.Def_Curvature_AdaptivePredictor
import Definitions.Def_Curvature_DomainGeometry
import Definitions.Def_Curvature_FixedAxes
import Definitions.Def_Curvature_WidthAndSignGame
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.EReal.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

section
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Curvature.Sparse

def Hist (m : ℕ) : ℕ → Type
  | 0 => Unit
  | t+1 => Hist m t × Fin m

instance histFinite (m : ℕ) : (t : ℕ) → Fintype (Hist m t)
  | 0 => inferInstanceAs (Fintype Unit)
  | t+1 => let := histFinite m t; inferInstanceAs (Fintype (Hist m t × Fin m))

instance histNonempty (m : ℕ) [NeZero m] : (t : ℕ) → Nonempty (Hist m t)
  | 0 => ⟨()⟩
  | t+1 => let := histNonempty m t; inferInstanceAs (Nonempty (Hist m t × Fin m))


variable {m : ℕ}


end Curvature.Sparse

end
end

section
set_option autoImplicit false
noncomputable section
open scoped BigOperators NNReal
open MeasureTheory

namespace Curvature

/-- The learner sees every past loss function and uses the same seed throughout a play. -/
structure FullInfoLearner (E Ω : Type*) [MeasurableSpace E] [MeasurableSpace Ω] (K : Set E) where
  predict : (t : ℕ) → (Fin t → E → ℝ) → Ω → E
  mem : ∀ t h ω, predict t h ω ∈ K
  measurable : ∀ t h, Measurable (predict t h)

namespace FullInfoLearner

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] {K : Set E} {T : ℕ}

def pastLosses (f : Fin T → E → ℝ) (t : Fin T) : Fin t.val → E → ℝ :=
  fun k => f ⟨k.val, lt_trans k.isLt t.isLt⟩

def bestLoss (K : Set E) (f : Fin T → E → ℝ) : ℝ := sInf ((fun x => ∑ t, f t x) '' K)

def comparatorBudget (K : Set E) (f : Fin T → E → ℝ) : ℝ :=
  bestLoss K f - ∑ t, sInf (f t '' K)

def regret (L : FullInfoLearner E Ω K) (f : Fin T → E → ℝ) (ω : Ω) : ℝ :=
  (∑ t, f t (L.predict t.val (pastLosses f t) ω)) - bestLoss K f

/-- One deterministic sequence, fixed before the learner's random seed is drawn. -/
def HasHardSequence (L : FullInfoLearner E Ω K) (μ : Measure Ω) (G : ℝ≥0) (b R : ℝ) : Prop :=
  ∃ T : ℕ, 0 < T ∧ ∃ f : Fin T → E → ℝ,
    (∀ t, ConvexOn ℝ Set.univ (f t) ∧ LipschitzWith G (f t)) ∧
    comparatorBudget K f ≤ b ∧ Integrable (L.regret f) μ ∧ R ≤ ∫ ω, L.regret f ω ∂μ


end FullInfoLearner

open Coordinate


end Curvature

end
end

section
set_option autoImplicit false
noncomputable section
open scoped BigOperators NNReal
open MeasureTheory
namespace Curvature.Sparse

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

variable {d : ℕ}


variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] {K : Set E}


end Curvature.Sparse

end
end

section
set_option autoImplicit false
noncomputable section
open scoped BigOperators NNReal InnerProductSpace
open MeasureTheory
namespace Curvature.Sparse

variable {d : ℕ}

def simplex (d : ℕ) : Set (Space d) := {x | x.ofLp ∈ stdSimplex ℝ (Fin d)}

def lpBall (d : ℕ) (p : ℝ) : Set (Space d) := {x | ∑ i, |x i|^p ≤ 1}


end Curvature.Sparse

end
end

section
set_option autoImplicit false
noncomputable section
open scoped BigOperators NNReal
open MeasureTheory

namespace Curvature
open Coordinate

/-- Corollary 12 uses standard coordinates for the unit norm balls and probability simplex.
Its boxes and ellipsoids allow arbitrary centers and orthonormal axes in the ambient space. -/
inductive CanonicalDomain (d : ℕ) : Set (Sparse.Space d) → Prop
  | unitLp (hd : 0 < d) (p : ℝ) (hp : 1 ≤ p) : CanonicalDomain d (Sparse.lpBall d p)
  | unitLinf (hd : 0 < d) : CanonicalDomain d {x | ∀ i, |x i| ≤ 1}
  | euclidean (hd : 0 < d) (R : ℝ) (hR : 0 < R) :
      CanonicalDomain d (Metric.closedBall 0 R)
  | ellipsoid {r : ℕ} (hr : 0 < r) (hrd : r ≤ d) (c : Sparse.Space d)
      (U : Axes r →ₗᵢ[ℝ] Sparse.Space d) (a : Fin r → ℝ) (ha : ∀ i, 0 < a i) :
      CanonicalDomain d (Coordinate.ellipsoid c U a)
  | box {r : ℕ} (hr : 0 < r) (hrd : r ≤ d) (c : Sparse.Space d)
      (U : Axes r →ₗᵢ[ℝ] Sparse.Space d) (a : Fin r → ℝ) (ha : ∀ i, 0 < a i) :
      CanonicalDomain d (Coordinate.box c U a)
  | simplex (hd : 2 ≤ d) : CanonicalDomain d (Sparse.simplex d)


end Curvature

end
end

section
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Curvature

variable {d r : ℕ}

theorem canonicalUnitBall_compact {p : ℝ} (hp : 0 < p) : IsCompact (canonicalUnitBall r p) := by
  apply (isCompact_Icc (a := fun _ : Fin r => (-1:ℝ)) (b := fun _ => 1)).of_isClosed_subset
  · apply isClosed_le _ continuous_const
    exact continuous_finsetSum _ fun i _ => (Real.continuous_rpow_const hp.le).comp (continuous_apply i).abs
  · intro v hv
    exact ⟨fun i => (abs_le.mp (canonicalUnitBall_coord hp v hv i)).1,
      fun i => (abs_le.mp (canonicalUnitBall_coord hp v hv i)).2⟩

theorem canonicalUnitBall_convex {p : ℝ} (hp : 1 ≤ p) : Convex ℝ (canonicalUnitBall r p) := by
  intro x hx y hy a b ha hb hab
  have hi (i : Fin r) : |a*x i+b*y i|^p ≤ a*|x i|^p+b*|y i|^p := by
    have h := abs_add_le (a*x i) (b*y i)
    rw [abs_mul,abs_mul,abs_of_nonneg ha,abs_of_nonneg hb] at h
    exact (Real.rpow_le_rpow (abs_nonneg _) h (by linarith)).trans
      ((convexOn_rpow hp).2 (abs_nonneg (x i)) (abs_nonneg (y i)) ha hb hab)
  change (∑ i, |a*x i+b*y i|^p) ≤ 1
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
  rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum] at h
  have hx' : ∑ i, |x i|^p ≤ 1 := hx
  have hy' : ∑ i, |y i|^p ≤ 1 := hy
  linarith only [h,mul_le_mul_of_nonneg_left hx' ha,mul_le_mul_of_nonneg_left hy' hb,hab]


end Curvature

end
end

section
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace NNReal
open MeasureTheory
namespace Curvature

variable {d : ℕ} {K : Set (Vec d)}

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "e" => ContinuousLinearEquiv.symm (EuclideanSpace.equiv (Fin d) ℝ)


namespace AdaptiveBase

variable (B : AdaptiveBase K) (hcv : Convex ℝ K) {M : ℝ}
  (P : AdaptiveWeightRule M) (G : ℝ≥0)


end AdaptiveBase


/-- The history available to a learner that observes one subgradient per round. -/
def pastGradients {T : ℕ} (g : Fin T → E) (t : Fin T) : Fin t.val → E :=
  fun j => g ⟨j.val, j.isLt.trans t.isLt⟩


/-- A single strategy with past subgradients as its only feedback, valid for every budget. -/
def OneSubgradientUpper (S : Set E) (G : ℝ≥0) (c : ℝ) : Prop :=
  ∃ play : (t : ℕ) → (Fin t → E) → S,
    ∀ {T : ℕ}, 0 < T → ∀ (f : Fin T → E → ℝ),
      (∀ t, ConvexOn ℝ Set.univ (f t) ∧ LipschitzWith G (f t)) →
      ∀ (g : Fin T → E), (∀ t, ‖g t‖ ≤ G) →
        let w := fun t : Fin T => (play t.val (pastGradients g t)).val
        (∀ t, ∀ u ∈ S, f t (w t) - f t u ≤ ⟪g t,w t-u⟫_ℝ) →
        ∀ b : ℝ, FullInfoLearner.comparatorBudget S f ≤ b →
          (∑ t, f t (w t)) - FullInfoLearner.bestLoss S f ≤
            c * ((G:ℝ)*subexponentialWidth S + Real.sqrt ((G:ℝ)*subexponentialWidth S*b))


end Curvature

end
end

section
set_option autoImplicit false
noncomputable section
open scoped BigOperators NNReal
open MeasureTheory
namespace Curvature
universe u v

variable {d : ℕ}


/-- The private seed is drawn once and used in every round. -/
structure MinimaxStrategy (K : Set (Sparse.Space d)) where
  Seed : Type u
  [measurable : MeasurableSpace Seed]
  law : Measure Seed
  [probability : IsProbabilityMeasure law]
  learner : FullInfoLearner (Sparse.Space d) Seed K

attribute [instance] MinimaxStrategy.measurable MinimaxStrategy.probability

/-- The environment observes past predictions, past losses and the current prediction. -/
def CausalLossPolicy (X Ξ : Type*) :=
  (t : ℕ) → (Fin t → X) → (Fin t → X → ℝ) → X → Ξ → X → ℝ

namespace CausalLossPolicy
variable {Ξ Ω : Type*} [MeasurableSpace Ω] {K : Set (Sparse.Space d)}
    (P : CausalLossPolicy (Sparse.Space d) Ξ) (L : FullInfoLearner (Sparse.Space d) Ω K)

def play (P : CausalLossPolicy (Sparse.Space d) Ξ) (L : FullInfoLearner (Sparse.Space d) Ω K) (ω : Ω) (ξ : Ξ) : (t : ℕ) → Fin t → (Sparse.Space d) → ℝ :=
  Nat.rec (motive := fun t => Fin t → (Sparse.Space d) → ℝ) Fin.elim0 (fun t f =>
    let w := L.predict t f ω
    let past := fun j : Fin t => L.predict j.val (FullInfoLearner.pastLosses f j) ω
    Fin.snoc f (P t past f w ξ))


end CausalLossPolicy

/-- Learner and environment use independent seeds with product law. The budget
holds for every seed pair. -/
structure MinimaxEnvironment {K : Set (Sparse.Space d)} (S : MinimaxStrategy.{u} K) (G : ℝ≥0) (b : ℝ) where
  T : ℕ
  horizon_pos : 0 < T
  Seed : Type v
  [measurable : MeasurableSpace Seed]
  law : Measure Seed
  [probability : IsProbabilityMeasure law]
  policy : CausalLossPolicy (Sparse.Space d) Seed
  losses : ∀ ω ξ t, let f := policy.play S.learner ω ξ T t
                    ConvexOn ℝ Set.univ f ∧ LipschitzWith G f
  budget : ∀ ω ξ, FullInfoLearner.comparatorBudget K (policy.play S.learner ω ξ T) ≤ b
  measurablePayoff : AEStronglyMeasurable (fun z : S.Seed × Seed => S.learner.regret (policy.play S.learner z.1 z.2 T) z.1)
    (S.law.prod law)

attribute [instance] MinimaxEnvironment.measurable MinimaxEnvironment.probability


def MinimaxEnvironment.payoff {K : Set (Sparse.Space d)} {S : MinimaxStrategy K} {G : ℝ≥0} {b : ℝ}
    (A : MinimaxEnvironment S G b) : ℝ :=
  ∫ z : S.Seed × A.Seed, S.learner.regret (A.policy.play S.learner z.1 z.2 A.T) z.1 ∂S.law.prod A.law

/-- The learner may use the budget when choosing the strategy. Its predictions
are common to every finite horizon. -/
def minimaxValue (K : Set (Sparse.Space d)) (G : ℝ≥0) (b : ℝ) : EReal :=
  ⨅ S : MinimaxStrategy.{u} K, ⨆ A : MinimaxEnvironment.{u,v} S G b, (A.payoff : EReal)


end Curvature

end
end


