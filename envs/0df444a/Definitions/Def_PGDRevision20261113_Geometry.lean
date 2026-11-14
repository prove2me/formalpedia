-- Prove2me | Definitions.Def_PGDRevision20261113_Geometry
-- name    : PGDRevision20261113_Geometry
-- status  : Definition
-- author  : @Somehow
-- created : 2026-11-13T06:21:25.525199+00:00
-- url     : https://prove2.me/theorems/f26bd57d-d045-48d4-bbde-9e2a357b5162
-- title:
--   Prescribed geometry families, active features and optimality certificates
-- statement:
--   This module specifies the interval power family and the real-line penalty-curvature family, including bounded nonnegative nonzero loss curvature, positive penalty strength, symmetry or the required continuous differentiability, and the real-line growth conditions.
--   It defines the actual curvature error, global performance norm, active feature sets, boundary tests, three-feature and same-feature contacts. Relative-gradient performance uses actual primitives of the prescribed curvatures and actual implicit trajectories. The classification predicates are proof targets, not axioms.
-- source:
--   Author manuscript: Exact Residual Bounds and Optimal Geometry Selection for Proximal Gradient Methods, revised reading edition, 13 November 2026, Sections 5-6, Theorem 5.1 and Corollary 6.3, pages 12-17.

import Definitions.Def_PGDRevision20261113_Profile
import Mathlib.Data.EReal.Basic

set_option autoImplicit false
noncomputable section
open scoped ENNReal

namespace PGDRevision20261113

inductive GeometryFamily where
  | interval (beta : ℝ)
  | realLine

structure GeometryData where
  family : GeometryFamily
  A : ℝ → ℝ
  b : ℝ → ℝ
  lambda : ℝ

def powerCurvature (c t : ℝ) : ℝ :=
  (Real.rpow (1 + t) (-c) + Real.rpow (1 - t) (-c)) / 2

def geometryDomain (G : GeometryData) : Set ℝ :=
  match G.family with
  | .interval _ => Set.Ioo (-1 : ℝ) 1
  | .realLine => Set.univ

def geometryKernel (G : GeometryData) (c t : ℝ) : ℝ :=
  match G.family with
  | .interval _ => powerCurvature c t
  | .realLine => Real.rpow (G.b t) c

def matchedExponent (G : GeometryData) : ℝ :=
  match G.family with
  | .interval beta => beta
  | .realLine => 1

def geometryFeature (G : GeometryData) (t : ℝ) : ℝ :=
  match G.family with
  | .interval _ => |t|
  | .realLine => Real.log (G.b t)

def boundaryFeature (G : GeometryData) : EReal :=
  match G.family with
  | .interval _ => 1
  | .realLine => ⊤

def EvenLoss (G : GeometryData) : Prop :=
  ∀ t ∈ geometryDomain G, G.A (-t) = G.A t

def AdmissibleGeometry (G : GeometryData) : Prop :=
  0 < G.lambda ∧
  (∀ t ∈ geometryDomain G, 0 ≤ G.A t) ∧
  BddAbove (G.A '' geometryDomain G) ∧
  (∃ t ∈ geometryDomain G, 0 < G.A t) ∧
  match G.family with
  | .interval beta =>
      1 ≤ beta ∧
      (∀ t ∈ geometryDomain G, G.b t = powerCurvature beta t) ∧
      ContinuousOn G.A (Set.Icc (-1 : ℝ) 1) ∧
      (EvenLoss G ∨ ContDiffOn ℝ 1 G.A (geometryDomain G))
  | .realLine =>
      ContDiff ℝ 1 G.A ∧ ContDiff ℝ 1 G.b ∧ G.b 0 = 1 ∧
      (∀ x : ℝ, x ≠ 0 → 1 < G.b x) ∧
      (∀ x : ℝ, x < 0 → deriv G.b x < 0) ∧
      (∀ x : ℝ, 0 < x → 0 < deriv G.b x) ∧
      ∀ M : ℝ, ∃ R > (0 : ℝ), ∀ x : ℝ, R ≤ |x| → M ≤ G.b x

def geometryProfile (G : GeometryData) (c : ℝ) : ScalarProfile :=
  ⟨geometryDomain G, doublePrimitive G.A,
    doublePrimitive (fun t => G.lambda * G.b t),
    doublePrimitive (geometryKernel G c)⟩

def geometryError (G : GeometryData) (c p t : ℝ) : ℝ :=
  (p * geometryKernel G c t - G.A t) /
    (p * geometryKernel G c t + G.lambda * G.b t)

def geometryRho (G : GeometryData) (c p : ℝ) : ℝ≥0∞ :=
  ⨆ t ∈ geometryDomain G, ENNReal.ofReal |geometryError G c p t|

def geometryOmega (G : GeometryData) (z : ℝ × ℝ) (N : ℕ) : ℝ≥0∞ :=
  profileOmega (geometryProfile G z.1) z.2 N

def FeasiblePair (z : ℝ × ℝ) : Prop := 0 ≤ z.1 ∧ 0 < z.2

def GeometryOptimum (G : GeometryData) (z : ℝ × ℝ) : Prop :=
  FeasiblePair z ∧ ∀ w : ℝ × ℝ, FeasiblePair w →
    geometryRho G z.1 z.2 ≤ geometryRho G w.1 w.2

def RestrictedGeometryOptimum (G : GeometryData) (C : Set ℝ) (z : ℝ × ℝ) : Prop :=
  z.1 ∈ C ∧ 0 < z.2 ∧ ∀ w : ℝ × ℝ, w.1 ∈ C → 0 < w.2 →
    geometryRho G z.1 z.2 ≤ geometryRho G w.1 w.2

def geometryM (G : GeometryData) : ℝ :=
  sSup ((fun t => G.A t / G.b t) '' geometryDomain G)
def geometryAmax (G : GeometryData) : ℝ := sSup (G.A '' geometryDomain G)
def matchedRate (G : GeometryData) : ℝ := geometryM G / (geometryM G + 2 * G.lambda)
def QuadraticOptimum (G : GeometryData) (p : ℝ) : Prop :=
  0 < p ∧ ∀ s : ℝ, 0 < s → geometryRho G 0 p ≤ geometryRho G 0 s

def positiveFeatures (G : GeometryData) (p : ℝ) : Set EReal :=
  {z | ∃ t ∈ geometryDomain G, z = (geometryFeature G t : EReal) ∧
    geometryError G 0 p t = (geometryRho G 0 p).toReal}
def negativeFeatures (G : GeometryData) (p : ℝ) : Set EReal :=
  {z | ∃ t ∈ geometryDomain G, z = (geometryFeature G t : EReal) ∧
    geometryError G 0 p t = -(geometryRho G 0 p).toReal}
def zeroFeatures (G : GeometryData) : Set EReal :=
  {boundaryFeature G} ∪
    {z | ∃ t ∈ geometryDomain G, z = (geometryFeature G t : EReal) ∧ G.A t = 0}
def maximalRatioFeatures (G : GeometryData) : Set EReal :=
  {z | ∃ t ∈ geometryDomain G, z = (geometryFeature G t : EReal) ∧
    G.A t / G.b t = geometryM G}

def QuadraticTest (G : GeometryData) (pQ : ℝ) : Prop :=
  sInf (negativeFeatures G pQ) ≤ sSup (positiveFeatures G pQ)
def MatchedTest (G : GeometryData) : Prop :=
  sInf (zeroFeatures G) ≤ sSup (maximalRatioFeatures G)

def alternatingSign (sigma : ℝ) (i : Fin 3) : ℝ := if i = 1 then -sigma else sigma

def UniformGeometryEnvelope (G : GeometryData) (z : ℝ × ℝ) (r : ℝ) : Prop :=
  ∀ t ∈ geometryDomain G, |geometryError G z.1 z.2 t| ≤ r

def ThreeFeatureContacts (G : GeometryData) (z : ℝ × ℝ) (r : ℝ) : Prop :=
  ∃ (t : Fin 3 → ℝ) (sigma : ℝ),
    (∀ i, t i ∈ geometryDomain G) ∧ (sigma = 1 ∨ sigma = -1) ∧
    geometryFeature G (t 0) < geometryFeature G (t 1) ∧
    geometryFeature G (t 1) < geometryFeature G (t 2) ∧
    ∀ i, geometryError G z.1 z.2 (t i) = alternatingSign sigma i * r

def SameFeatureContacts (G : GeometryData) (z : ℝ × ℝ) (r : ℝ) : Prop :=
  ∃ x ∈ geometryDomain G, ∃ y ∈ geometryDomain G,
    x ≠ y ∧ geometryFeature G x = geometryFeature G y ∧ 0 < geometryFeature G x ∧
    geometryError G z.1 z.2 x = r ∧ geometryError G z.1 z.2 y = -r

def OrderedKernelRatioClaim : Prop :=
  ∀ G : GeometryData, AdmissibleGeometry G →
    ∀ c1 c2 p1 p2 : ℝ, 0 ≤ c1 → c1 < c2 → 0 < p1 → 0 < p2 →
      ∀ x ∈ geometryDomain G, ∀ y ∈ geometryDomain G,
        geometryFeature G x < geometryFeature G y →
        (p2 * geometryKernel G c2 x) / (p1 * geometryKernel G c1 x) <
          (p2 * geometryKernel G c2 y) / (p1 * geometryKernel G c1 y)

def OrderedContactCertificateClaim : Prop :=
  ∀ (G : GeometryData), AdmissibleGeometry G →
    ∀ (z : ℝ × ℝ) (r : ℝ), FeasiblePair z → 0 < r →
      UniformGeometryEnvelope G z r → ThreeFeatureContacts G z r →
      GeometryOptimum G z ∧ geometryRho G z.1 z.2 = ENNReal.ofReal r ∧
      ∀ w, GeometryOptimum G w → w = z

def SameFeatureTangencyClaim : Prop :=
  ∀ (G : GeometryData), AdmissibleGeometry G →
    ∀ (z : ℝ × ℝ) (r : ℝ), FeasiblePair z → 0 < r →
      UniformGeometryEnvelope G z r → SameFeatureContacts G z r →
      GeometryOptimum G z ∧ geometryRho G z.1 z.2 = ENNReal.ofReal r ∧
      ∀ w, GeometryOptimum G w → w = z

def GeometryClassificationClaim : Prop :=
  ∀ G : GeometryData, AdmissibleGeometry G →
    (∃! z : ℝ × ℝ, GeometryOptimum G z) ∧
    (∀ a : ℝ, 0 < a → (∀ t ∈ geometryDomain G, G.A t = a) →
      GeometryOptimum G (0, a) ∧ geometryRho G 0 a = 0) ∧
    ((¬ ∃ a : ℝ, ∀ t ∈ geometryDomain G, G.A t = a) →
      ∃ pQ : ℝ, QuadraticOptimum G pQ ∧
        (∀ p : ℝ, QuadraticOptimum G p → p = pQ) ∧
        ∀ z : ℝ × ℝ, GeometryOptimum G z →
          (z.1 ≤ matchedExponent G ∧ geometryM G / 2 ≤ z.2 ∧ z.2 < geometryAmax G) ∧
          (0 < geometryRho G z.1 z.2 ∧
            geometryRho G z.1 z.2 ≤ ENNReal.ofReal (matchedRate G) ∧ matchedRate G < 1) ∧
          (z.1 = 0 ↔ QuadraticTest G pQ) ∧
          (z.1 = matchedExponent G ↔ MatchedTest G) ∧
          ¬ (QuadraticTest G pQ ∧ MatchedTest G) ∧
          (¬ QuadraticTest G pQ → ¬ MatchedTest G →
            0 < z.1 ∧ z.1 < matchedExponent G ∧
            (ThreeFeatureContacts G z (geometryRho G z.1 z.2).toReal ∨
             SameFeatureContacts G z (geometryRho G z.1 z.2).toReal)) ∧
          (¬ MatchedTest G →
            geometryRho G z.1 z.2 < ENNReal.ofReal (matchedRate G) ∧ geometryM G / 2 < z.2) ∧
          (¬ QuadraticTest G pQ → geometryRho G z.1 z.2 < geometryRho G 0 pQ)) ∧
    (∀ (z : ℝ × ℝ) (r : ℝ), FeasiblePair z → 0 < r →
      UniformGeometryEnvelope G z r →
      (ThreeFeatureContacts G z r ∨ SameFeatureContacts G z r) →
      GeometryOptimum G z ∧ geometryRho G z.1 z.2 = ENNReal.ofReal r ∧
      ∀ w, GeometryOptimum G w → w = z) ∧
    (∀ beta : ℝ, G.family = .interval beta → EvenLoss G →
      ∀ z r, 0 < r → ¬ SameFeatureContacts G z r) ∧
    (∀ z : ℝ × ℝ, GeometryOptimum G z →
      ∀ N : ℕ, 1 ≤ N → ∀ w : ℝ × ℝ, FeasiblePair w →
        geometryOmega G z N ≤ geometryOmega G w N ∧
        (geometryOmega G w N = geometryOmega G z N → w = z)) ∧
    (∀ C : ℝ, matchedExponent G ≤ C → ∀ z : ℝ × ℝ,
      RestrictedGeometryOptimum G (Set.Icc 0 C) z ↔ GeometryOptimum G z)

def CurvatureRelationClaim : Prop :=
  ∀ (G : GeometryData) (a : ℝ → ℝ), AdmissibleGeometry G → G.family = .realLine →
    (∀ x : ℝ, G.A x = a (G.b x)) →
    (∀ c p : ℝ, 0 ≤ c → 0 < p →
      geometryRho G c p =
        ⨆ s ∈ Set.Ici (1 : ℝ),
          ENNReal.ofReal |(p * Real.rpow s c - a s) /
            (p * Real.rpow s c + G.lambda * s)|) ∧
    ∀ H : GeometryData, AdmissibleGeometry H → H.family = .realLine →
      H.lambda = G.lambda → (∀ x : ℝ, H.A x = a (H.b x)) →
      ∀ z : ℝ × ℝ, GeometryOptimum G z ↔ GeometryOptimum H z

end PGDRevision20261113


