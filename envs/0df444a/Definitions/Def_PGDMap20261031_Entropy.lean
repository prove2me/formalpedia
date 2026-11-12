-- Prove2me | Definitions.Def_PGDMap20261031_Entropy
-- name    : PGDMap20261031_Entropy
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-31T13:01:22.457868+00:00
-- url     : https://prove2.me/theorems/e2840017-6794-4116-8444-7f9414aaf559
-- title:
--   Positive entropy mixtures, power Bregman updates, and joint optimality
-- statement:
--   A nonempty finite mixture has positive weights, scales in $(0,1)$ and positive entropy-regularization strength. The target is the explicit one-dimensional objective $F_\ell(t)=\sum_jw_jH(\sqrt{a_j}t)+\lambda H(t)+\ell t$ on $(-1,1)$. Its gradient is the actual real derivative. The normalized power curvature is $k_c(t)=\frac12[(1+t)^{-c}+(1-t)^{-c}]$, with $c\in[0,2]$; its derivative generator is the interval integral from zero. A fixed positive inverse step $p$ defines the implicit entropy update.
--
--   The error ratio is computed from these explicit curvatures. Its real supremum and the realized finite-horizon performance sets define the exact-analysis targets. Other predicates express global joint optimality, explicit location bounds, necessary and sufficient three-point alternation, common finite-horizon optimality and the sharper single-profile conclusions.
--
--   These are definitions and target predicates only. Finiteness of the error supremum is an explicit analytic obligation. The evaluation criterion is worst-case gradient contraction over the linear term and initial point; computational costs and other geometry families are outside this target.
-- source:
--   Three author manuscripts dated 2026-10-30: Exact Residual Curves for Proximal Gradient Descent with a Fixed Penalty; Optimal Constant Stepsizes for the Exact PGD Residual Curve; Jointly Optimal Bregman Geometry and Stepsize for Positive Entropy Mixtures. Definitions preceding Theorem 1 in each manuscript.

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Order.Bounds.Basic

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MeasureTheory

namespace PGDMap20261031

def entropy (t : ℝ) : ℝ :=
  ((1 + t) * Real.log (1 + t) + (1 - t) * Real.log (1 - t)) / 2

def artanh (t : ℝ) : ℝ := (Real.log (1 + t) - Real.log (1 - t)) / 2

structure EntropyMixture where
  m : ℕ
  m_pos : 0 < m
  a : Fin m → ℝ
  weight : Fin m → ℝ
  lambda : ℝ
  a_pos : ∀ j, 0 < a j
  a_lt_one : ∀ j, a j < 1
  weight_pos : ∀ j, 0 < weight j
  lambda_pos : 0 < lambda

def mixtureValue (M : EntropyMixture) (t : ℝ) : ℝ :=
  ∑ j, M.weight j * entropy (Real.sqrt (M.a j) * t)

def mixtureSlope (M : EntropyMixture) (t : ℝ) : ℝ :=
  ∑ j, M.weight j * Real.sqrt (M.a j) * artanh (Real.sqrt (M.a j) * t)

def entropyObjective (M : EntropyMixture) (ell t : ℝ) : ℝ :=
  mixtureValue M t + M.lambda * entropy t + ell * t

def objectiveGradient (M : EntropyMixture) (ell t : ℝ) : ℝ :=
  deriv (entropyObjective M ell) t

def powerCurvature (c t : ℝ) : ℝ :=
  (Real.rpow (1 + t) (-c) + Real.rpow (1 - t) (-c)) / 2

def geometrySlope (c t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, powerCurvature c s

def mixtureCurvature (M : EntropyMixture) (t : ℝ) : ℝ :=
  ∑ j, M.weight j * M.a j / (1 - M.a j * t ^ 2)

def entropyCurvature (M : EntropyMixture) (t : ℝ) : ℝ :=
  M.lambda / (1 - t ^ 2)

def curvatureError (M : EntropyMixture) (c p t : ℝ) : ℝ :=
  (p * powerCurvature c t - mixtureCurvature M t) /
    (p * powerCurvature c t + entropyCurvature M t)

def errorValues (M : EntropyMixture) (c p : ℝ) : Set ℝ :=
  {v | ∃ t ∈ Set.Ico (0 : ℝ) 1, v = |curvatureError M c p t|}

def contraction (M : EntropyMixture) (c p : ℝ) : ℝ := sSup (errorValues M c p)

def validGeometry (z : ℝ × ℝ) : Prop := 0 ≤ z.1 ∧ z.1 ≤ 2 ∧ 0 < z.2

def entropyTrajectory (M : EntropyMixture) (c p ell : ℝ) (N : ℕ)
    (x : ℕ → ℝ) : Prop :=
  (∀ i ≤ N, x i ∈ Set.Ioo (-1 : ℝ) 1) ∧
  ∀ i < N,
    p * geometrySlope c (x (i + 1)) + M.lambda * artanh (x (i + 1)) =
      p * geometrySlope c (x i) - mixtureSlope M (x i) - ell

def entropyPerformanceSet (M : EntropyMixture) (c p : ℝ) (N : ℕ) : Set ℝ :=
  {v | ∃ (ell : ℝ) (x : ℕ → ℝ), entropyTrajectory M c p ell N x ∧
    objectiveGradient M ell (x 0) ≠ 0 ∧
    v = |objectiveGradient M ell (x N)| ^ 2 / |objectiveGradient M ell (x 0)| ^ 2}

def omega (M : EntropyMixture) (c p : ℝ) (N : ℕ) : ℝ :=
  sSup (entropyPerformanceSet M c p N)

def curvatureAtZero (M : EntropyMixture) : ℝ := ∑ j, M.weight j * M.a j

def curvatureAtBoundary (M : EntropyMixture) : ℝ :=
  ∑ j, M.weight j * M.a j / (1 - M.a j)

def maxScale (M : EntropyMixture) : ℝ := sSup (Set.range M.a)

def threshold (a : ℝ) : ℝ := (Real.sqrt (1 + 8 * a) - 1) / 2

def entropyBaseline (M : EntropyMixture) : ℝ :=
  curvatureAtZero M / (curvatureAtZero M + 2 * M.lambda)

def IsGeometryOptimum (M : EntropyMixture) (z : ℝ × ℝ) : Prop :=
  validGeometry z ∧ ∀ u, validGeometry u →
    contraction M z.1 z.2 ≤ contraction M u.1 u.2

def LocationBounds (M : EntropyMixture) (z : ℝ × ℝ) : Prop :=
  0 < z.1 ∧ z.1 < threshold (maxScale M) ∧ threshold (maxScale M) < 1 ∧
  curvatureAtZero M / 2 < z.2 ∧ z.2 < curvatureAtBoundary M ∧
  0 < contraction M z.1 z.2 ∧ contraction M z.1 z.2 < entropyBaseline M ∧
  entropyBaseline M < 1

def UniformErrorBound (M : EntropyMixture) (c p r : ℝ) : Prop :=
  ∀ t ∈ Set.Ico (0 : ℝ) 1, |curvatureError M c p t| ≤ r

def Alternates (M : EntropyMixture) (c p r : ℝ) : Prop :=
  ∃ t₁ t₂ t₃ σ : ℝ,
    0 ≤ t₁ ∧ t₁ < t₂ ∧ t₂ < t₃ ∧ t₃ < 1 ∧
    (σ = 1 ∨ σ = -1) ∧
    curvatureError M c p t₁ = σ * r ∧
    curvatureError M c p t₂ = -σ * r ∧
    curvatureError M c p t₃ = σ * r

def PositiveAlternatesFromZero (M : EntropyMixture) (c p r : ℝ) : Prop :=
  ∃ t₂ t₃ : ℝ, 0 < t₂ ∧ t₂ < t₃ ∧ t₃ < 1 ∧
    curvatureError M c p 0 = r ∧
    curvatureError M c p t₂ = -r ∧ curvatureError M c p t₃ = r

def ExactEntropyPerformanceClaim : Prop :=
  ∀ M c p N, validGeometry (c, p) → 1 ≤ N →
    IsLUB (entropyPerformanceSet M c p N) ((contraction M c p) ^ (2 * N))

def ErrorProfileLUBClaim : Prop :=
  ∀ M c p, validGeometry (c, p) → IsLUB (errorValues M c p) (contraction M c p)

def LocatedExistenceClaim : Prop :=
  ∀ M, ∃ z, IsGeometryOptimum M z ∧ LocationBounds M z

def NecessaryAlternationClaim : Prop :=
  ∀ M z, IsGeometryOptimum M z →
    UniformErrorBound M z.1 z.2 (contraction M z.1 z.2) ∧
    Alternates M z.1 z.2 (contraction M z.1 z.2)

def AlternationCertificateClaim : Prop :=
  ∀ M c p r, validGeometry (c, p) → 0 < r →
    UniformErrorBound M c p r → Alternates M c p r →
    IsGeometryOptimum M (c, p) ∧ contraction M c p = r ∧
      ∀ z, IsGeometryOptimum M z → z = (c, p)

def UniqueLocatedOptimumClaim : Prop :=
  ∀ M, (∃! z, IsGeometryOptimum M z) ∧
    ∀ z, IsGeometryOptimum M z → LocationBounds M z

def CommonFiniteHorizonClaim : Prop :=
  ∀ M N, 1 ≤ N → ∀ z, IsGeometryOptimum M z →
    (∀ u, validGeometry u → omega M z.1 z.2 N ≤ omega M u.1 u.2 N) ∧
    ∀ u, validGeometry u → omega M u.1 u.2 N = omega M z.1 z.2 N → u = z

def SingleProfileClaim : Prop :=
  ∀ M a, 0 < a → a < 1 →
    (∀ t ∈ Set.Ioo (-1 : ℝ) 1, mixtureValue M t = entropy (Real.sqrt a * t)) →
    ∀ z, IsGeometryOptimum M z →
      a < z.2 ∧ z.2 < a / (1 - a) ∧
      PositiveAlternatesFromZero M z.1 z.2 (contraction M z.1 z.2)

def PowerSingleCrossingClaim : Prop :=
  ∀ c₁ c₂, 0 ≤ c₁ → c₁ < c₂ → c₂ ≤ 2 →
    StrictMonoOn (fun t : ℝ => powerCurvature c₂ t / powerCurvature c₁ t)
      (Set.Ico (0 : ℝ) 1)

def EntropyDerivativeClaim : Prop :=
  ∀ M ell t, t ∈ Set.Ioo (-1 : ℝ) 1 →
    objectiveGradient M ell t = mixtureSlope M t + M.lambda * artanh t + ell

def thresholdProfile (a c u : ℝ) : ℝ :=
  (1 - a * u) * powerCurvature c (Real.sqrt u)

def PowerThresholdClaim : Prop :=
  ∀ a c, 0 < a → a < 1 → 0 < c → c < 1 →
    (threshold a ≤ c → StrictMonoOn (thresholdProfile a c) (Set.Ico (0 : ℝ) 1)) ∧
    (c < threshold a → ∃ u ∈ Set.Ioo (0 : ℝ) 1,
      StrictAntiOn (thresholdProfile a c) (Set.Icc 0 u) ∧
      StrictMonoOn (thresholdProfile a c) (Set.Ico u 1))

def fixedGeometryValues (M : EntropyMixture) (c : ℝ) : Set ℝ :=
  {r | ∃ p > (0 : ℝ), r = contraction M c p}

def PureGeometryStrictClaim : Prop :=
  ∀ M z, IsGeometryOptimum M z →
    contraction M z.1 z.2 < sInf (fixedGeometryValues M 0) ∧
    contraction M z.1 z.2 < sInf (fixedGeometryValues M 1)

def FullMapTheorem : Prop :=
  ExactEntropyPerformanceClaim ∧ UniqueLocatedOptimumClaim ∧
  NecessaryAlternationClaim ∧ AlternationCertificateClaim ∧
  CommonFiniteHorizonClaim ∧ SingleProfileClaim ∧ PureGeometryStrictClaim

end PGDMap20261031


