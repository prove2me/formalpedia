-- Prove2me | Definitions.Def_MinimaxAltRegret_Main_Continuous
-- name    : MinimaxAltRegret_Main_Continuous
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:54:52.770126+00:00
-- url     : https://prove2.me/theorems/b342bfa7-e51a-4401-842a-a29af7cc7108
-- title:
--   Convex bodies, continuous corrected densities, and exact means
-- statement:
--   Let X be a compact convex subset of R^d with nonempty interior. Its intrinsic dimension is d. Upper losses are arbitrary convex functions X to [-1,1], while the lower construction additionally produces continuous functions X to [0,1]. Define q(x)=exp(eta R(x))/integral_X exp(eta R), m=integral_X q f, a=f-m, and H=integral_X q a^2. Then
--
--   $$p(x)=q(x)\left[1-4\eta a(x)-2\eta^2(a(x)^2-H)\right],\qquad x_t=\int_X x p_t(x)\,dx.$$
--
--   The scores and terminal conventions are the continuous counterparts of Algorithm 1. The mean is a vector Bochner integral. The normalized potential is F(R)=eta^(-1)log(integral_X exp(eta R)/vol(X)), and U=F-2 eta Var_q(f). A density means an integrable nonnegative function of total mass one. The upper-bound predicate records all three quantitative bounds, including the entire delta-family in (20).
--
--   These definitions retain the source's full bounded convex loss class. Integration uses almost-everywhere representatives under restricted Lebesgue measure; arbitrary original boundary values remain in pointwise comparator regret. No integrability, feasibility, or performance theorem is a field of the domain or loss class.
-- source:
--   Mengxiao Zhang, STOC 2027 submission #57 (October 2026), printed p. 10 / PDF p. 11, Section 4.2; Algorithm 2, Eq. (15), printed p. 11 / PDF p. 12; Eqs. (16), (17), (20); SHA-256 6db5a23e9e92d250b4dea7995bf34c9930d39a95df90f5d3fdc715ca26044f31

import Mathlib
import Definitions.Def_MinimaxAltRegret_Main_Protocol

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace MinimaxAltRegret.Main

abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Full intrinsic dimension in the stated coordinates; no lower-dimensional ambient body. -/
def convexBody {d : ℕ} (X : Set (Point d)) : Prop :=
  IsCompact X ∧ Convex ℝ X ∧ (interior X).Nonempty

/-- The original pointwise functions, including all boundary values. No continuity is imposed. -/
def convexLosses {d : ℕ} (X : Set (Point d)) (T : ℕ) (f : ℕ → Point d → ℝ) : Prop :=
  ∀ t < T, ConvexOn ℝ X (f t) ∧ ∀ x ∈ X, f t x ∈ Set.Icc (-1 : ℝ) 1

/-- The lower-bound witnesses have the additional continuity and [0,1] conclusions. -/
def continuousLosses01 {d : ℕ} (X : Set (Point d)) (T : ℕ)
    (f : ℕ → Point d → ℝ) : Prop :=
  ∀ t < T, ContinuousOn (f t) X ∧ ConvexOn ℝ X (f t) ∧
    ∀ x ∈ X, f t x ∈ Set.Icc (0 : ℝ) 1

/-- Integration uses a.e. representatives under restricted Lebesgue measure. Bounded convex
losses are continuous in the interior; arbitrary boundary values are retained for regret. -/
def bodyMeasure {d : ℕ} (X : Set (Point d)) : Measure (Point d) := volume.restrict X

def continuousEW {d : ℕ} (X : Set (Point d)) (η : ℝ) (R : Point d → ℝ)
    (x : Point d) : ℝ :=
  Real.exp (η * R x) / ∫ y, Real.exp (η * R y) ∂bodyMeasure X

def continuousMean {d : ℕ} (X : Set (Point d)) (q f : Point d → ℝ) : ℝ :=
  ∫ x, q x * f x ∂bodyMeasure X

def continuousVariance {d : ℕ} (X : Set (Point d)) (q f : Point d → ℝ) : ℝ :=
  continuousMean X q (fun x => (f x - continuousMean X q f)^2)

def continuousF {d : ℕ} (X : Set (Point d)) (η : ℝ) (R : Point d → ℝ) : ℝ :=
  Real.log ((∫ x, Real.exp (η*R x) ∂bodyMeasure X) / (volume X).toReal) / η

def continuousU {d : ℕ} (X : Set (Point d)) (η : ℝ) (R f : Point d → ℝ) : ℝ :=
  continuousF X η R - 2*η*continuousVariance X (continuousEW X η R) f

def continuousGamma {d : ℕ} (X : Set (Point d)) (η : ℝ) (R f : Point d → ℝ)
    (x : Point d) : ℝ :=
  let q := continuousEW X η R
  let a := f x - continuousMean X q f
  1 - 4*η*a - 2*η^2*(a^2 - continuousVariance X q f)

def continuousCorrection {d : ℕ} (X : Set (Point d)) (η : ℝ) (R f : Point d → ℝ)
    (x : Point d) : ℝ :=
  continuousEW X η R x * continuousGamma X η R f x

def continuousPadded {d : ℕ} (T : ℕ) (f : ℕ → Point d → ℝ) (t : ℕ) : Point d → ℝ :=
  if t < T then f t else 0

def continuousPrevious {d : ℕ} (T : ℕ) (f : ℕ → Point d → ℝ) : ℕ → Point d → ℝ
  | 0 => 0
  | t+1 => continuousPadded T f t

def continuousScore {d : ℕ} (T : ℕ) (f : ℕ → Point d → ℝ) (t : ℕ) (x : Point d) : ℝ :=
  - ∑ s ∈ Finset.range t, (continuousPrevious T f s x + continuousPadded T f s x)

/-- Algorithm 2's corrected density p_(t+1), including p_(T+1). -/
def continuousDensity {d : ℕ} (X : Set (Point d)) (T : ℕ)
    (f : ℕ → Point d → ℝ) (t : ℕ) : Point d → ℝ :=
  continuousCorrection X (1/10) (continuousScore T f t) (continuousPrevious T f t)

/-- Option I: exact vector-valued mean, not an approximate integration oracle. -/
def continuousAlgorithmI {d : ℕ} (X : Set (Point d)) (T : ℕ)
    (f : ℕ → Point d → ℝ) (t : ℕ) : Point d :=
  ∫ x, continuousDensity X T f t x • x ∂bodyMeasure X

/-- A probability density is integrable, nonnegative pointwise and has unit mass. -/
def bodyDensity {d : ℕ} (X : Set (Point d)) (p : Point d → ℝ) : Prop :=
  Integrable p (bodyMeasure X) ∧ (∀ x ∈ X, 0 ≤ p x) ∧ ∫ x, p x ∂bodyMeasure X = 1

/-- Quantitative content of (20), boundedness, and the uniform proof-derived constant 14. -/
def continuousUpperBounds (d T : ℕ) (B : ℝ) : Prop :=
  B ≤ 4*(T : ℝ) ∧ B ≤ 14*(d : ℝ)*Real.log (1+(T : ℝ)/(d : ℝ)) ∧
  ∀ δ : ℝ, 0 < δ → δ < 1 → B ≤ 4*(T : ℝ)*δ + 10*(d : ℝ)*Real.log (1/δ)

end MinimaxAltRegret.Main


