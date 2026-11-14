-- Prove2me | Definitions.Def_CBCCompactChasingModel
-- name    : CBCCompactChasingModel
-- status  : Definition
-- author  : @nhc
-- created : 2026-11-13T13:34:53.474934+00:00
-- url     : https://prove2.me/theorems/b5e1d001-bb6e-40b1-bc60-5bd9310b8721
-- title:
--   Compact convex-body chasing: algorithms, movement and competitiveness
-- statement:
--   Let $E$ be a real normed vector space. A request is a nonempty compact convex subset of $E$. A deterministic algorithm chooses a feasible point from the current request as a function of that request and the finite request history. For a start point $x_0$ and a finite trajectory $x_1,\ldots,x_T$, movement is
--
--   $$\sum_{t=1}^T\|x_t-x_{t-1}\|.$$
--
--   A randomized algorithm consists of a probability space of seeds and a deterministic algorithm for each seed, with measurable decisions. Expected movement is the extended nonnegative Lebesgue integral. A factor $R$ is competitive when every request sequence and every feasible comparator trajectory $y_0=x_0,y_1,\ldots,y_T$ satisfy
--
--   $$\mathbb E[\operatorname{cost}(A)]\le \operatorname{ofReal}\!\left(R\sum_{t=1}^T\|y_t-y_{t-1}\|\right).$$
--
--   Here $\operatorname{ofReal}$ converts a real number to an extended nonnegative real number. The definition permits arbitrary real $R$; in nonzero spaces a competitive factor is necessarily at least one.
--
--   This is the compact-request auxiliary model used in the lower-bound construction. The file also provides finite convex-hull requests and the structural measurability lemma for the cost. **Formalization Note.** The model compares against every feasible path, without dividing by an offline optimum. It is connected to the mission's closed-convex-request model by a separate proof.
-- source:
--   Nicolas Christianson, A Linear Lower Bound for Convex Body Chasing in Every Norm, STOC 2027 submission #674, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/674.pdf, Section 1, p. 2 (chasing model), and Section 4, p. 16 (compact lifted requests); compact-request auxiliary interface from the accompanying local formalization.

import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.List.Chain
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Gluing
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Lipschitz

set_option autoImplicit false

/- Component source: ConvexBodyChasing.Model -/
section BundledModule000
/-!
# The convex body chasing model

Requests are nonempty compact convex sets; lower dimensional requests are allowed.
An online algorithm sees precisely the finite request history and the current request.
The competitive guarantee compares its movement against every feasible offline path.
This avoids conventions about division by a zero offline optimum.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped ENNReal

namespace ConvexBodyChasing

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An admissible request in the manuscript's model. -/
structure Body where
  carrier : Set E
  nonempty : carrier.Nonempty
  compact : IsCompact carrier
  convex : Convex ℝ carrier

instance : SetLike (Body E) E where
  coe K := K.carrier
  coe_injective K L h := by cases K; cases L; congr

/-- A deterministic online algorithm, with no access to future requests or the horizon. -/
abbrev OnlineAlgorithm := (history : List (Body E)) → (K : Body E) → K

variable {E}

/-- Movement of a finite path, including its first move from the specified initial point. -/
def movement (start : E) : List E → ℝ
  | [] => 0
  | x :: xs => ‖x - start‖ + movement x xs

/-- Offline feasibility; the two lists must have the same length. -/
def Serves : List (Body E) → List E → Prop :=
  List.Forall₂ fun K x => x ∈ K

/-- Run an online algorithm, accumulating only the requests already revealed. -/
def trajectory (A : OnlineAlgorithm E) (history : List (Body E)) : List (Body E) → List E
  | [] => []
  | K :: Ks => (A history K).val :: trajectory A (history ++ [K]) Ks

def cost (A : OnlineAlgorithm E) (start : E) (requests : List (Body E)) : ℝ :=
  movement start (trajectory A [] requests)

/-- The manuscript uses a purely multiplicative competitive guarantee. -/
def Competitive (A : OnlineAlgorithm E) (start : E) (R : ℝ) : Prop :=
  ∀ (requests : List (Body E)) (path : List E), Serves requests path →
    cost A start requests ≤ R * movement start path

omit [NormedSpace ℝ E] in
theorem movement_nonneg (start : E) (path : List E) : 0 ≤ movement start path := by
  induction path generalizing start with
  | nil => exact le_refl 0
  | cons x xs ih => exact add_nonneg (norm_nonneg _) (ih x)

theorem trajectory_serves (A : OnlineAlgorithm E) (history requests : List (Body E)) :
    Serves requests (trajectory A history requests) := by
  induction requests generalizing history with
  | nil => exact .nil
  | cons K Ks ih => exact .cons (A history K).property (ih _)

/-- The actual mathlib finite dimensional ℓ_p space, rather than a surrogate norm. -/
abbrev Space (d : ℕ) (p : ℝ≥0∞) := PiLp p (fun _ : Fin d => ℝ)

end ConvexBodyChasing

end
end BundledModule000

/- Component source: ConvexBodyChasing.Statement -/
section BundledModule001
/-!
# Auditable target statement

`LinearLowerBound` states the manuscript's main result without importing its
construction. `Main.lean` proves it as `ConvexBodyChasing.linear_lower_bound`.

Randomness is an independent seed sampled once from an arbitrary probability
space. Each seed determines a feasible online algorithm. Only measurability of
each decision is required. Expected movement is an extended nonnegative integral,
so the definition does not silently replace infinite expected costs by zero.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped ENNReal
open MeasureTheory

namespace ConvexBodyChasing

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]

structure RandomizedOnlineAlgorithm where
  Seed : Type
  measurableSpace : MeasurableSpace Seed
  law : Measure Seed
  probability : IsProbabilityMeasure law
  algorithm : Seed → OnlineAlgorithm E
  measurable_decision : ∀ history K, Measurable (fun ω => (algorithm ω history K).val)

attribute [instance] RandomizedOnlineAlgorithm.measurableSpace
attribute [instance] RandomizedOnlineAlgorithm.probability

variable {E}

def expectedCost (A : RandomizedOnlineAlgorithm E) (start : E) (requests : List (Body E)) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (cost (A.algorithm ω) start requests) ∂A.law

def RandomizedCompetitive (A : RandomizedOnlineAlgorithm E) (start : E) (R : ℝ) : Prop :=
  ∀ (requests : List (Body E)) (path : List E), Serves requests path →
    expectedCost A start requests ≤ ENNReal.ofReal (R * movement start path)



end ConvexBodyChasing

end
end BundledModule001

/- Component source: ConvexBodyChasing.MappedOffline -/
section BundledModule048
/-! # The mapped offline comparator in the actual ℓ_p space -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped ENNReal
namespace ConvexBodyChasing









/-- A finite discrete request gives an admissible compact convex body. -/
def Body.ofFinset {V E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : V → E) (S : Finset V) (hS : S.Nonempty) : Body E where
  carrier := convexHull ℝ (f '' (S : Set V))
  nonempty := (hS.to_set.image f).mono (subset_convexHull ℝ _)
  compact := (S.finite_toSet.image f).isCompact_convexHull ℝ
  convex := convex_convexHull ℝ _





end ConvexBodyChasing

end
end BundledModule048

/- Component source: ConvexBodyChasing.RandomizedTree -/
section BundledModule053
/-! # Averaging the finite oblivious tree over an arbitrary random seed

All expectations use the extended nonnegative integral, including when a
randomized algorithm has infinite expected movement.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace ConvexBodyChasing
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem RandomizedOnlineAlgorithm.measurable_movement (A : RandomizedOnlineAlgorithm E)
    (history requests : List (Body E)) (start : A.Seed → E) (hstart : Measurable start) :
    Measurable (fun ω => movement (start ω) (trajectory (A.algorithm ω) history requests)) := by
  induction requests generalizing history start with
  | nil => exact measurable_const
  | cons K Ks ih =>
    exact ((A.measurable_decision history K).sub hstart).norm.add
      (ih (history ++ [K]) (fun ω => (A.algorithm ω history K).val) (A.measurable_decision history K))

theorem RandomizedOnlineAlgorithm.measurable_cost (A : RandomizedOnlineAlgorithm E)
    (start : E) (requests : List (Body E)) :
    Measurable (fun ω => cost (A.algorithm ω) start requests) := by
  exact A.measurable_movement [] requests (fun _ => start) measurable_const

namespace FiniteGame
variable {V : Type*}

















end FiniteGame

end ConvexBodyChasing

end
end BundledModule053


