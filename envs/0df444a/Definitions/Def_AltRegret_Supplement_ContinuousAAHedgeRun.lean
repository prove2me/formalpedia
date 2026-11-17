-- Prove2me | Definitions.Def_AltRegret_Supplement_ContinuousAAHedgeRun
-- name    : AltRegret_Supplement_ContinuousAAHedgeRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T00:08:18.016858+00:00
-- url     : https://prove2.me/theorems/5f034171-f2ba-40c4-beac-7a17b7d484ff
-- title:
--   Continuous alternating regret and continuous AA-Hedge (Algorithm 2)
-- statement:
--   Let $X\subseteq\mathbb R^d$ be a nonempty compact convex set and let $f_0\equiv0$. For continuous convex losses $f_t:X\to[-1,1]$, define
--   $$
--   \operatorname{Reg}_{\mathrm{Alt}}^T(u)=\sum_{t=1}^T\bigl(f_{t-1}(x_t)+f_t(x_t)-f_{t-1}(u)-f_t(u)\bigr).
--   $$
--   The continuous AA-Hedge run records the centering maximizer $\theta_t$, the normalized exponential-weight probability $P_t$, its correction $Q_t(du)=(1-(f_{t-1}(u)-\theta_t)/2)P_t(du)$, and the barycentric play $x_t=\int_Xu\,Q_t(du)$. It also defines the distributional regret, variance, the potential $\Phi_t$ of equation (6), and normalized uniform volume on an affine-hull coordinate model.
--
--   These definitions are the common interface for Theorems 7, 8, and 11.
--
--   **Formalization Note** Kullback--Leibler divergence is supplied by Mathlib at theorem use sites. The potential uses a real supremum; the hypotheses of Theorem 11 make its defining objective bounded above with an attained maximum.
-- source:
--   Tao, Zheng, Optimal Alternating Regret for Online Learning and Games, arXiv:2608.24731, §3, Algorithm 2 and Theorem 7, pp.9-10; equation (6), p.19

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace AltRegret.Supplement

abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The continuous loss of round `s`, with the paper's convention `f₀ ≡ 0`. -/
def continuousLossAt {d : ℕ} (f : ℕ → Point d → ℝ) (s : ℕ) : Point d → ℝ :=
  if s = 0 then 0 else f s

/-- The effective comparator loss accumulated through round `T`. -/
def comparatorEffectiveLoss {d : ℕ} (f : ℕ → Point d → ℝ) (T : ℕ) (u : Point d) : ℝ :=
  Finset.sum (Finset.Icc 1 T) (fun t =>
    continuousLossAt f (t - 1) u + continuousLossAt f t u)

/-- Continuous alternating regret against a fixed comparator, equation (3). -/
def continuousAltRegret {d : ℕ} (f : ℕ → Point d → ℝ) (x : ℕ → Point d)
    (T : ℕ) (u : Point d) : ℝ :=
  Finset.sum (Finset.Icc 1 T) (fun t =>
      continuousLossAt f (t - 1) (x t) + continuousLossAt f t (x t)) -
    comparatorEffectiveLoss f T u

/-- Alternating regret against a comparator drawn from `ρ`. -/
noncomputable def distributionalAltRegret {d : ℕ} (f : ℕ → Point d → ℝ)
    (x : ℕ → Point d) (T : ℕ) (ρ : Measure (Point d)) : ℝ :=
  ∫ u, continuousAltRegret f x T u ∂ρ

/-- The variance of a real function under a measure. -/
noncomputable def varianceUnder {α : Type*} [MeasurableSpace α]
    (ρ : Measure α) (g : α → ℝ) : ℝ :=
  ∫ u, (g u - ∫ v, g v ∂ρ) ^ 2 ∂ρ

/-- `log⁺ z = max 0 (log z)`. -/
noncomputable def logPlus (z : ℝ) : ℝ := max 0 (Real.log z)

/-- Exponentially tilt and normalize a reference measure. -/
noncomputable def normalizedExpMeasure {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (h : α → ℝ) : Measure α :=
  let ν := μ.withDensity (fun u => ENNReal.ofReal (Real.exp (h u)))
  (ν Set.univ)⁻¹ • ν

/-- The log-integral objective whose unique maximizer is `θ_t` in Algorithm 2. -/
noncomputable def continuousThetaObjective {d : ℕ} (μ : Measure (Point d))
    (f : ℕ → Point d → ℝ) (η β : ℝ) (t : ℕ) (θ : ℝ) : ℝ :=
  Real.log (∫ u, Real.exp
    (-η * comparatorEffectiveLoss f (t - 1) u -
      β * (continuousLossAt f (t - 1) u - θ) ^ 2) ∂μ)

/-- A run of continuous AA-Hedge (Algorithm 2), with its literal measure-valued updates. -/
structure ContinuousAAHedgeRun {d : ℕ} (X : Set (Point d)) (μ : Measure (Point d))
    (f : ℕ → Point d → ℝ) (η β : ℝ) where
  theta : ℕ → ℝ
  P : ℕ → Measure (Point d)
  Q : ℕ → Measure (Point d)
  play : ℕ → Point d
  theta_max : ∀ t, 1 ≤ t → ∀ a : ℝ,
    continuousThetaObjective μ f η β t a ≤ continuousThetaObjective μ f η β t (theta t)
  P_eq : ∀ t, 1 ≤ t → P t = normalizedExpMeasure μ (fun u =>
    -η * comparatorEffectiveLoss f (t - 1) u -
      β * (continuousLossAt f (t - 1) u - theta t) ^ 2)
  Q_eq : ∀ t, 1 ≤ t → Q t = (P t).withDensity (fun u =>
    ENNReal.ofReal (1 - (continuousLossAt f (t - 1) u - theta t) / 2))
  probability_P : ∀ t, 1 ≤ t → IsProbabilityMeasure (P t)
  probability_Q : ∀ t, 1 ≤ t → IsProbabilityMeasure (Q t)
  play_eq : ∀ t, 1 ≤ t → play t = ∫ u, u ∂(Q t)
  play_mem : ∀ t, 1 ≤ t → play t ∈ X

/-- The continuous potential (6), using a real supremum; under Theorem 11's hypotheses the
objective has an attained finite maximum. -/
noncomputable def continuousPotential {d : ℕ} (μ : Measure (Point d))
    (f : ℕ → Point d → ℝ) (x : ℕ → Point d)
    (η β : ℝ) (t : ℕ) : ℝ :=
  sSup (Set.range fun θ : ℝ => Real.log (∫ u, Real.exp
    (η * continuousAltRegret f x (t - 1) u -
      β * (continuousLossAt f (t - 1) u - θ) ^ 2) ∂μ))

/-- The probability measure obtained by normalizing Euclidean volume on `X`. In Theorem 8,
coordinates are chosen in the affine hull, so the ambient dimension is the affine dimension. -/
def IsUniformProbability {d : ℕ} (X : Set (Point d)) (μ : Measure (Point d)) : Prop :=
  IsProbabilityMeasure μ ∧ μ = (volume X)⁻¹ • volume.restrict X

/-- The standing OCO assumptions of §3: continuous convex losses taking values in `[-1,1]`. -/
def IsOCOSequence {d : ℕ} (X : Set (Point d)) (f : ℕ → Point d → ℝ) : Prop :=
  ∀ t, 1 ≤ t → ContinuousOn (f t) X ∧ ConvexOn ℝ X (f t) ∧
    ∀ u ∈ X, f t u ∈ Set.Icc (-1 : ℝ) 1

end AltRegret.Supplement


