-- Prove2me | Definitions.Def_PGDMap20261031_PGD
-- name    : PGDMap20261031_PGD
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-31T13:00:49.6853+00:00
-- url     : https://prove2.me/theorems/f8882b33-6da0-4b7a-9910-08614657a4b5
-- title:
--   Finite-dimensional PGD, fixed penalties, and exact residual performance
-- statement:
--   A penalty is represented by an effective domain $D\subseteq\mathbb R^d$ and a finite real value on $D$. Admissibility requires a nonempty domain, a closed restricted epigraph and convexity on the domain. A separate predicate excludes singleton domains where required. Strong convexity is the full two-point inequality and the best modulus is computed as the real supremum of the nonnegative admissible moduli.
--
--   A smooth term is globally convex and differentiable, with a specified gradient whose Lipschitz constant is at most $L$. A PGD trajectory satisfies the proximal minimization inequality at every update and stays in $D$ through its horizon. The residual performance set retains only positive objective decreases. The exact-curve target uses a least-upper-bound relation; other predicates name the uniform upper bound, scalar quadratic matching, flat-segment approximation and fixed-penalty sharpness obligations.
--
--   Values outside $D$ are auxiliary data and are not used by feasible trajectories. Every analytic proposition in this module is a definition of a target, not a claimed proof or an axiom.
-- source:
--   Three author manuscripts dated 2026-10-30: Exact Residual Curves for Proximal Gradient Descent with a Fixed Penalty; Optimal Constant Stepsizes for the Exact PGD Residual Curve; Jointly Optimal Bregman Geometry and Stepsize for Positive Entropy Mixtures. Definitions preceding Theorem 1 in each manuscript.

import Definitions.Def_PGDMap20261031_Curves
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Function

set_option autoImplicit false
noncomputable section
open scoped RealInnerProductSpace

namespace PGDMap20261031

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

structure Penalty (d : ℕ) where
  domain : Set (Space d)
  value : Space d → ℝ

def IsPenalty {d : ℕ} (r : Penalty d) : Prop :=
  r.domain.Nonempty ∧
  IsClosed {z : Space d × ℝ | z.1 ∈ r.domain ∧ r.value z.1 ≤ z.2} ∧
  ConvexOn ℝ r.domain r.value

def NonSingleton {d : ℕ} (r : Penalty d) : Prop :=
  ∃ x ∈ r.domain, ∃ y ∈ r.domain, x ≠ y

def StrongPenalty {d : ℕ} (r : Penalty d) (μ : ℝ) : Prop :=
  ∀ x ∈ r.domain, ∀ y ∈ r.domain, ∀ t ∈ Set.Icc (0 : ℝ) 1,
    r.value (t • x + (1 - t) • y) ≤
      t * r.value x + (1 - t) * r.value y -
        μ / 2 * t * (1 - t) * ‖x - y‖ ^ 2

def bestModulus {d : ℕ} (r : Penalty d) : ℝ :=
  sSup {μ : ℝ | 0 ≤ μ ∧ StrongPenalty r μ}

def SmoothConvex {d : ℕ} (f : Space d → ℝ) (g : Space d → Space d)
    (L : ℝ) : Prop :=
  ConvexOn ℝ Set.univ f ∧
  (∀ x, HasGradientAt f (g x) x) ∧
  (∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖)

def totalValue {d : ℕ} (r : Penalty d) (f : Space d → ℝ) (x : Space d) : ℝ :=
  f x + r.value x

def IsPGDTrajectory {d : ℕ} (r : Penalty d) (g : Space d → Space d)
    (γ : ℝ) (N : ℕ) (x : ℕ → Space d) : Prop :=
  (∀ i ≤ N, x i ∈ r.domain) ∧
  ∀ i < N, ∀ y ∈ r.domain,
    r.value (x (i + 1)) + ‖x (i + 1) - (x i - γ • g (x i))‖ ^ 2 / (2 * γ) ≤
      r.value y + ‖y - (x i - γ • g (x i))‖ ^ 2 / (2 * γ)

def decrease {d : ℕ} (r : Penalty d) (f : Space d → ℝ)
    (x : ℕ → Space d) (N : ℕ) : ℝ :=
  totalValue r f (x 0) - totalValue r f (x N)

def residualSquared {d : ℕ} (γ : ℝ) (x : ℕ → Space d) (N : ℕ) : ℝ :=
  ‖x (N - 1) - x N‖ ^ 2 / γ ^ 2

def ratioSet {d : ℕ} (r : Penalty d) (L h : ℝ) (N : ℕ) : Set ℝ :=
  {v | ∃ (f : Space d → ℝ) (g : Space d → Space d) (x : ℕ → Space d),
    SmoothConvex f g L ∧ IsPGDTrajectory r g (h / L) N x ∧
    0 < decrease r f x N ∧
    v = residualSquared (h / L) x N / (L * decrease r f x N)}

def quadraticPenalty (d : ℕ) (μ : ℝ) : Penalty d :=
  ⟨Set.univ, fun x => μ / 2 * ‖x‖ ^ 2⟩

def BestModulusClaim : Prop :=
  ∀ d (r : Penalty d), IsPenalty r → NonSingleton r →
    0 ≤ bestModulus r ∧ StrongPenalty r (bestModulus r)

def PrefixCertificateClaim : Prop :=
  ∀ d (r : Penalty d) (q h : ℝ) (k : ℕ)
    (f : Space d → ℝ) (g : Space d → Space d) (x : ℕ → Space d),
    IsPenalty r → 0 ≤ q → StrongPenalty r q → validStep h → 1 ≤ k →
    SmoothConvex f g 1 → IsPGDTrajectory r g h (k + 1) x →
    prefixCoefficient k h q * ‖x k - x (k + 1)‖ ^ 2 ≤ decrease r f x k

def UniformUpperClaim : Prop :=
  ∀ d (r : Penalty d) (L μ h : ℝ) (N : ℕ)
    (f : Space d → ℝ) (g : Space d → Space d) (x : ℕ → Space d),
    IsPenalty r → 0 < L → 0 ≤ μ → StrongPenalty r μ → validStep h →
    1 ≤ N → SmoothConvex f g L → IsPGDTrajectory r g (h / L) N x →
    residualSquared (h / L) x N ≤ L * curve N h (μ / L) * decrease r f x N

def QuadraticAttainmentClaim : Prop :=
  ∀ (L μ h : ℝ) (N : ℕ), 0 < L → 0 ≤ μ → validStep h → 1 ≤ N →
    curve N h (μ / L) ∈ ratioSet (quadraticPenalty 1 μ) L h N

def Supports {d : ℕ} (r : Penalty d) (c s : Space d) : Prop :=
  c ∈ r.domain ∧ ∀ y ∈ r.domain,
    r.value c + inner ℝ s (y - c) ≤ r.value y

def FlatSegmentsClaim : Prop :=
  ∀ d (r : Penalty d), IsPenalty r → NonSingleton r → bestModulus r = 0 →
    ∀ M > (0 : ℝ), ∀ ε > (0 : ℝ),
      ∃ (c s v : Space d) (δ : ℝ), Supports r c s ∧ 0 < δ ∧ ‖v‖ = 1 ∧
        ∀ t ∈ Set.Icc (-M) M,
          c + (δ * t) • v ∈ r.domain ∧
          0 ≤ (r.value (c + (δ * t) • v) - r.value c -
            δ * t * inner ℝ s v) / δ ^ 2 ∧
          (r.value (c + (δ * t) • v) - r.value c -
            δ * t * inner ℝ s v) / δ ^ 2 ≤ ε

def FixedPenaltySharpnessClaim : Prop :=
  ∀ d (r : Penalty d) (L h : ℝ) (N : ℕ),
    IsPenalty r → NonSingleton r → 0 < L → validStep h → 1 ≤ N →
    ∀ ε > (0 : ℝ), ∃ v ∈ ratioSet r L h N,
      curve N h (bestModulus r / L) - ε < v

def ExactCurveClaim : Prop :=
  ∀ d (r : Penalty d) (L h : ℝ) (N : ℕ),
    IsPenalty r → NonSingleton r → 0 < L → validStep h → 1 ≤ N →
    IsLUB (ratioSet r L h N) (curve N h (bestModulus r / L))

def FullCurveTheorem : Prop :=
  ExactCurveClaim ∧ UniformUpperClaim ∧ QuadraticAttainmentClaim

end PGDMap20261031


