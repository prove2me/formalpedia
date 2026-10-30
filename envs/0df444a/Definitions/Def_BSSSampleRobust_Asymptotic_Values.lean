-- Prove2me | Definitions.Def_BSSSampleRobust_Asymptotic_Values
-- name    : BSSSampleRobust_Asymptotic_Values
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T22:27:53.573978+00:00
-- url     : https://prove2.me/theorems/cb47b7b1-b0d0-49d0-825c-c0aeced5c558
-- title:
--   Sample-robust values, growth restriction and limiting endpoints
-- statement:
--   For a model, law, radius sequence and data sequence, the sample-robust value is the infimum over policies feasible on the union of sample balls of the average of their separate worst-case total costs. The restricted value adds, at every stage, the bound of the supremum of the decision norm by the supremum of $L(1+\|z\|)$ on that union. Assumption 3 means equality of these infima for one deterministic $L\ge0$, almost surely simultaneously at all positive sample sizes. The lower endpoint optimizes jointly over policies and retained subsets $Z\subseteq\Xi$ with indicator expectation at least $1-\rho$, imposing pointwise feasibility on $Z$ and truncating the cost there; its limit is the supremum over $0<\rho<1$. The envelope is the infimum over positive radii of completed expectations of local cost suprema. The upper endpoint first minimizes that envelope over policies feasible on the $\Xi$-relative expanded support, then takes the infimum over positive support radii. Distance to support is a nonnegative extended infimum. Every value is computed, rather than assumed as an unconstrained parameter.
-- source:
--   Bertsimas, Shtern and Sturt (2023), A Data-Driven Approach to Multistage Stochastic Linear Optimization, Management Science, https://doi.org/10.1287/mnsc.2022.4352; published basis, supplied manuscript/e-companion artifact; problem (2), PDF/printed 7–8; Assumption 3, PDF/printed 10; limiting values, PDF/printed 11

import Mathlib
import Definitions.Def_BSSSampleRobust_Asymptotic_Model
import Definitions.Def_BSSSampleRobust_Asymptotic_Sampling

open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

open scoped ENNReal Classical

namespace BSSSampleRobust.Asymptotic

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {D : Layout}

def sampleCost (M : LinearModel p D) (S : Sampling p (Coord D))
    (ω : ℕ → Path p D) (ε : ℕ → ℝ) (N : ℕ) (x : Policy p D) : EReal :=
  average (fun j : Fin N => supremum (sampleBall S ω ε N j.val) (totalCost M x))

def sampleValue (M : LinearModel p D) (S : Sampling p (Coord D))
    (ω : ℕ → Path p D) (ε : ℕ → ℝ) (N : ℕ) : EReal :=
  ⨅ (x : Policy p D) (_ : feasibleOn M x (sampleUnion S ω ε N)),
    sampleCost M S ω ε N x

def growthRestriction (S : Sampling p (Coord D)) (ω : ℕ → Path p D)
    (ε : ℕ → ℝ) (N : ℕ) (L : ℝ) (x : Policy p D) : Prop :=
  ∀ t : Fin D.T,
    supremum (sampleUnion S ω ε N) (fun z => ‖x.act t (historyOf t z)‖) ≤
      supremum (sampleUnion S ω ε N) (fun z => L * (1 + ‖z‖))

def restrictedValue (M : LinearModel p D) (S : Sampling p (Coord D))
    (ω : ℕ → Path p D) (ε : ℕ → ℝ) (N : ℕ) (L : ℝ) : EReal :=
  ⨅ (x : Policy p D) (_ : feasibleOn M x (sampleUnion S ω ε N))
    (_ : growthRestriction S ω ε N L x), sampleCost M S ω ε N x

/-- Assumption 3: one deterministic L, equality of infima for all positive sizes a.s. -/
def valuePreservingGrowth (M : LinearModel p D) (S : Sampling p (Coord D))
    (ε : ℕ → ℝ) : Prop :=
  ∃ L : ℝ, 0 ≤ L ∧ ∀ᵐ ω ∂sampleLaw S, ∀ N : ℕ, 1 ≤ N →
    sampleValue M S ω ε N = restrictedValue M S ω ε N L

def chanceValue (M : LinearModel p D) (S : Sampling p (Coord D)) (ρ : ℝ) : EReal :=
  ⨅ (x : Policy p D) (Z : Set (Path p D)) (_ : Z ⊆ S.known)
    (_ : feasibleOn M x Z)
    (_ : ((1 - ρ : ℝ) : EReal) ≤ expectation S.law (truncated Z (fun _ => 1))),
    expectation S.law (truncated Z (totalCost M x))

def lowerValue (M : LinearModel p D) (S : Sampling p (Coord D)) : EReal :=
  ⨆ (ρ : ℝ) (_ : 0 < ρ ∧ ρ < 1), chanceValue M S ρ

def envelope (S : Sampling p (Coord D)) (f : Path p D → ℝ) : EReal :=
  ⨅ (r : ℝ) (_ : 0 < r), expectation S.law
    (fun z => supremum {y | y ∈ S.known ∧ ‖y - z‖ ≤ r} f)

/-- Distance to support is an extended nonnegative infimum, avoiding empty-set defaults. -/
def expandedSupport (S : Sampling p (Coord D)) (ρ : ℝ) : Set (Path p D) :=
  {z | z ∈ S.known ∧
    (⨅ y ∈ S.law.support, (ENNReal.ofReal ‖z - y‖)) ≤ ENNReal.ofReal ρ}

def upperAt (M : LinearModel p D) (S : Sampling p (Coord D)) (ρ : ℝ) : EReal :=
  ⨅ (x : Policy p D) (_ : feasibleOn M x (expandedSupport S ρ)),
    envelope S (totalCost M x)

def upperValue (M : LinearModel p D) (S : Sampling p (Coord D)) : EReal :=
  ⨅ (ρ : ℝ) (_ : 0 < ρ), upperAt M S ρ

end BSSSampleRobust.Asymptotic


