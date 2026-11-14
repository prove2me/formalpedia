-- Prove2me | Definitions.Def_PGDRevision20261113_Contacts
-- name    : PGDRevision20261113_Contacts
-- status  : Definition
-- author  : @Somehow
-- created : 2026-11-13T06:21:43.332193+00:00
-- url     : https://prove2.me/theorems/20a1bfae-60b9-4b1c-abf3-859858d05c7f
-- title:
--   Approximate contacts, score gaps and parameter enclosures
-- statement:
--   This module specifies a positive curvature family on a compact parameter interval. The score is the actual parameter derivative of the logarithmic kernel, factors through an ordered state feature, and is jointly continuous.
--   It defines approximate signed contacts, certified full-domain norms, logarithmic error bands, minimum score gaps, both orientation-dependent geometry radii and the scale enclosure. Its final target combines the general localization bounds with uniqueness in the admissible geometry specialization.
-- source:
--   Author manuscript: Exact Residual Bounds and Optimal Geometry Selection for Proximal Gradient Methods, revised reading edition, 13 November 2026, Section 7, Theorem 7.1, page 18.

import Definitions.Def_PGDRevision20261113_Geometry

set_option autoImplicit false
noncomputable section
open scoped ENNReal

namespace PGDRevision20261113

structure ContactFamily where
  domain : Set ℝ
  A : ℝ → ℝ
  B : ℝ → ℝ
  kernel : ℝ → ℝ → ℝ
  feature : ℝ → ℝ

def score (D : ContactFamily) (c t : ℝ) : ℝ :=
  deriv (fun s => Real.log (D.kernel s t)) c

def AdmissibleContactFamily (D : ContactFamily) (C : Set ℝ) : Prop :=
  C.Nonempty ∧ IsCompact C ∧ Set.OrdConnected C ∧
  (∀ t ∈ D.domain, 0 ≤ D.A t ∧ 0 < D.B t) ∧
  (∀ c ∈ C, ∀ t ∈ D.domain,
    0 < D.kernel c t ∧ DifferentiableAt ℝ (fun s => Real.log (D.kernel s t)) c) ∧
  ContinuousOn (fun z : ℝ × ℝ => score D z.1 z.2) (C ×ˢ D.domain) ∧
  (∀ c ∈ C, ∀ s ∈ D.domain, ∀ t ∈ D.domain,
    D.feature s = D.feature t → score D c s = score D c t) ∧
  ∀ c ∈ C, ∀ s ∈ D.domain, ∀ t ∈ D.domain,
    D.feature s < D.feature t → score D c s < score D c t

def contactError (D : ContactFamily) (c p t : ℝ) : ℝ :=
  (p * D.kernel c t - D.A t) / (p * D.kernel c t + D.B t)

def contactRho (D : ContactFamily) (c p : ℝ) : ℝ≥0∞ :=
  ⨆ t ∈ D.domain, ENNReal.ofReal |contactError D c p t|

def ApproximateContacts (D : ContactFamily) (C : Set ℝ) (candidate : ℝ × ℝ)
    (L U sigma : ℝ) (t : Fin 3 → ℝ) : Prop :=
  candidate.1 ∈ C ∧ 0 < candidate.2 ∧ 0 < L ∧ L ≤ U ∧ U < 1 ∧
  (sigma = 1 ∨ sigma = -1) ∧ (∀ i, t i ∈ D.domain) ∧
  D.feature (t 0) < D.feature (t 1) ∧ D.feature (t 1) < D.feature (t 2) ∧
  (∀ i, L ≤ alternatingSign sigma i * contactError D candidate.1 candidate.2 (t i)) ∧
  contactRho D candidate.1 candidate.2 ≤ ENNReal.ofReal U ∧
  ∀ i, alternatingSign sigma i = -1 → U * D.B (t i) < D.A (t i)

def contactBeta (D : ContactFamily) (L U sigma : ℝ) (t : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  if alternatingSign sigma i = 1 then
    Real.log (upperBand (D.A (t i)) (D.B (t i)) U) -
      Real.log (upperBand (D.A (t i)) (D.B (t i)) L)
  else
    Real.log (lowerBand (D.A (t i)) (D.B (t i)) L) -
      Real.log (lowerBand (D.A (t i)) (D.B (t i)) U)

def scoreGap (D : ContactFamily) (C : Set ℝ) (s t : ℝ) : ℝ :=
  sInf ((fun c => score D c t - score D c s) '' C)

def contactScoreBound (D : ContactFamily) (C : Set ℝ) (t : Fin 3 → ℝ) : ℝ :=
  sSup {v | ∃ c ∈ C, ∃ i : Fin 3, v = |score D c (t i)|}

def lowerRadius (D : ContactFamily) (C : Set ℝ) (L U sigma : ℝ) (t : Fin 3 → ℝ) : ℝ :=
  if sigma = 1 then
    (contactBeta D L U sigma t 0 + contactBeta D L U sigma t 1) /
      scoreGap D C (t 0) (t 1)
  else
    (contactBeta D L U sigma t 1 + contactBeta D L U sigma t 2) /
      scoreGap D C (t 1) (t 2)

def upperRadius (D : ContactFamily) (C : Set ℝ) (L U sigma : ℝ) (t : Fin 3 → ℝ) : ℝ :=
  if sigma = 1 then
    (contactBeta D L U sigma t 1 + contactBeta D L U sigma t 2) /
      scoreGap D C (t 1) (t 2)
  else
    (contactBeta D L U sigma t 0 + contactBeta D L U sigma t 1) /
      scoreGap D C (t 0) (t 1)

def logScaleRadius (D : ContactFamily) (C : Set ℝ)
    (L U sigma : ℝ) (t : Fin 3 → ℝ) : ℝ :=
  sSup (Set.range (contactBeta D L U sigma t)) +
    contactScoreBound D C t *
      max (lowerRadius D C L U sigma t) (upperRadius D C L U sigma t)

def ContactOptimum (D : ContactFamily) (C : Set ℝ) (z : ℝ × ℝ) : Prop :=
  z.1 ∈ C ∧ 0 < z.2 ∧ ∀ w : ℝ × ℝ, w.1 ∈ C → 0 < w.2 →
    contactRho D z.1 z.2 ≤ contactRho D w.1 w.2

def ApproximateLocalizationBoundsClaim : Prop :=
  ∀ (D : ContactFamily) (C : Set ℝ), AdmissibleContactFamily D C →
    ∀ (candidate : ℝ × ℝ) (L U sigma : ℝ) (t : Fin 3 → ℝ),
      ApproximateContacts D C candidate L U sigma t →
      (0 < scoreGap D C (t 0) (t 1) ∧ 0 < scoreGap D C (t 1) (t 2)) ∧
      (∀ z : ℝ × ℝ, z.1 ∈ C → 0 < z.2 → contactRho D z.1 z.2 ≤ ENNReal.ofReal U →
        candidate.1 - lowerRadius D C L U sigma t ≤ z.1 ∧
        z.1 ≤ candidate.1 + upperRadius D C L U sigma t ∧
        |Real.log (z.2 / candidate.2)| ≤ logScaleRadius D C L U sigma t) ∧
      ∃ z : ℝ × ℝ, ContactOptimum D C z ∧
        ENNReal.ofReal L ≤ contactRho D z.1 z.2 ∧
        contactRho D z.1 z.2 ≤ ENNReal.ofReal U

def LocalizationGeometryUniquenessClaim : Prop :=
  ∀ (G : GeometryData) (C : Set ℝ), AdmissibleGeometry G →
    IsCompact C → Set.OrdConnected C → C ⊆ Set.Ici (0 : ℝ) →
    (∃ z : ℝ × ℝ, GeometryOptimum G z ∧ z.1 ∈ C) →
    ∃! z : ℝ × ℝ, RestrictedGeometryOptimum G C z

def ApproximateContactLocalizationClaim : Prop :=
  ApproximateLocalizationBoundsClaim ∧ LocalizationGeometryUniquenessClaim

end PGDRevision20261113


