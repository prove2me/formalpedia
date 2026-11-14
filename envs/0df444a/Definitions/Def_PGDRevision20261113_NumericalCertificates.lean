-- Prove2me | Definitions.Def_PGDRevision20261113_NumericalCertificates
-- name    : PGDRevision20261113_NumericalCertificates
-- status  : Definition
-- author  : @Somehow
-- created : 2026-11-13T08:00:19.556327+00:00
-- url     : https://prove2.me/theorems/be9419de-2db9-4159-9f25-232eebddbeb1
-- title:
--   Exact rational data and global numerical-certificate target propositions
-- statement:
--   This module defines the entropy and polynomial candidates, exact rational contacts and boxes, global error targets, and stable localization constants. Each continuum norm uses a supremum over the whole prescribed state domain:
--   $$\rho(c,p)=\sup_t|E_{c,p}(t)|.$$
--   It also defines the robust-localization, rational-scale conversion, and linear-shrinkage propositions from Section 7. The definitions record certificate obligations; they do not assert that external numerical computations constitute Lean proofs.
-- source:
--   Author manuscript, Exact Residual Bounds and Optimal Geometry Selection for Proximal Gradient Methods, revised reading edition, 13 November 2026; Sections 4--8 and Appendix B, with exact source references on each associated theorem.

import Definitions.Def_PGDRevision20261113_Examples
import Definitions.Def_PGDRevision20261113_MeasureExtension

set_option autoImplicit false
noncomputable section
open scoped ENNReal

namespace PGDRevision20261113

def entropyNumericalGeometry : GeometryData :=
  intervalExample (fun t => (9 / 16) / (1 - (9 / 16) * t ^ 2)) (1 / 2)
def entropyNumericalFamily : ContactFamily :=
  ⟨geometryDomain entropyNumericalGeometry, entropyNumericalGeometry.A,
    (fun t => (1 / 2) * powerCurvature 1 t), powerCurvature, abs⟩
def entropyNumericalCandidate : ℝ × ℝ :=
  (4021153597 / 10000000000, 1496311423 / 2500000000)
def entropyNumericalContacts (i : Fin 3) : ℝ :=
  if i = 0 then 0 else if i = 1 then 7774713329 / 10000000000 else 4934266229 / 5000000000
def entropyNumericalLower : ℝ := 3279359 / 100000000
def entropyNumericalUpper : ℝ := 2562 / 78125

def EntropyNumericalEnclosureClaim : Prop :=
  ApproximateContacts entropyNumericalFamily (Set.Icc 0 2) entropyNumericalCandidate
    entropyNumericalLower entropyNumericalUpper 1 entropyNumericalContacts ∧
  (∃! z, GeometryOptimum entropyNumericalGeometry z) ∧
  (∀ z, GeometryOptimum entropyNumericalGeometry z →
    z.1 ∈ Set.Icc (125661 / 312500) (1005289 / 2500000) ∧
    z.2 ∈ Set.Icc (149631 / 250000) (1496313 / 2500000) ∧
    ENNReal.ofReal entropyNumericalLower ≤ geometryRho entropyNumericalGeometry z.1 z.2 ∧
    geometryRho entropyNumericalGeometry z.1 z.2 ≤ ENNReal.ofReal entropyNumericalUpper) ∧
  (∀ z : ℝ × ℝ, FeasiblePair z →
    geometryRho entropyNumericalGeometry z.1 z.2 ≤ ENNReal.ofReal entropyNumericalUpper →
    z.1 ∈ Set.Icc (125661 / 312500) (1005289 / 2500000) ∧
    z.2 ∈ Set.Icc (149631 / 250000) (1496313 / 2500000) ∧
    ENNReal.ofReal entropyNumericalLower ≤ geometryRho entropyNumericalGeometry z.1 z.2)

def polynomialNumericalFamily : ContactFamily :=
  ⟨Set.Ioo (-1 : ℝ) 1, (fun t => 1 + t ^ 4), (fun t => 1 / (1 - t ^ 2)),
    (fun c t => 1 + c * t ^ 2), (fun t => t ^ 2)⟩
def polynomialNumericalProfile (c : ℝ) : ScalarProfile :=
  ⟨Set.Ioo (-1 : ℝ) 1, (fun t => t ^ 2 / 2 + t ^ 6 / 30), normalizedEntropy,
    (fun t => t ^ 2 / 2 + c * t ^ 4 / 12)⟩
def polynomialNumericalCandidate : ℝ × ℝ :=
  (17603377874351 / 25000000000000, 47607471887281 / 50000000000000)
def polynomialNumericalSquaredContacts (i : Fin 3) : ℝ :=
  if i = 0 then 0 else if i = 1 then 1207434995079 / 4000000000000
  else 10542972151979 / 12500000000000
def polynomialNumericalContacts (i : Fin 3) : ℝ := Real.sqrt (polynomialNumericalSquaredContacts i)
def polynomialNumericalLower : ℝ := 2451173 / 100000000
def polynomialNumericalUpper : ℝ := 1225587 / 50000000

def PolynomialNumericalEnclosureClaim : Prop :=
  ApproximateContacts polynomialNumericalFamily (Set.Icc 0 2) polynomialNumericalCandidate
    polynomialNumericalLower polynomialNumericalUpper (-1) polynomialNumericalContacts ∧
  (∃! z, ContactOptimum polynomialNumericalFamily (Set.Ici 0) z) ∧
  (∀ z, ContactOptimum polynomialNumericalFamily (Set.Ici 0) z →
    z.1 ∈ Set.Icc (1408269 / 2000000) (3520677 / 5000000) ∧
    z.2 ∈ Set.Icc (9521489 / 10000000) (19043 / 20000) ∧
    ENNReal.ofReal polynomialNumericalLower ≤ contactRho polynomialNumericalFamily z.1 z.2 ∧
    contactRho polynomialNumericalFamily z.1 z.2 ≤ ENNReal.ofReal polynomialNumericalUpper) ∧
  (∀ z : ℝ × ℝ, FeasiblePair z →
    contactRho polynomialNumericalFamily z.1 z.2 ≤ ENNReal.ofReal polynomialNumericalUpper →
    z.1 ≤ 1896437301989138 / 2378943363494569 ∧
    z.1 ∈ Set.Icc (1408269 / 2000000) (3520677 / 5000000) ∧
    z.2 ∈ Set.Icc (9521489 / 10000000) (19043 / 20000) ∧
    ENNReal.ofReal polynomialNumericalLower ≤ contactRho polynomialNumericalFamily z.1 z.2) ∧
  ∀ c p : ℝ, 0 ≤ c → 0 < p →
    AdmissibleProfile (polynomialNumericalProfile c) p ∧
    ∀ N : ℕ, 1 ≤ N → profileOmega (polynomialNumericalProfile c) p N =
      contactRho polynomialNumericalFamily c p ^ (2 * N)

def rationalPolynomialError (p c u : ℝ) : ℝ :=
  ((p * (1 + c * u) - (1 + u ^ 2)) * (1 - u)) /
    (p * (1 + c * u) * (1 - u) + 1)

def PolynomialGlobalEnvelopeClaim : Prop :=
  let c := polynomialNumericalCandidate.1
  let p := polynomialNumericalCandidate.2
  (∀ u ∈ Set.Icc (0 : ℝ) 1, |rationalPolynomialError p c u| ≤ polynomialNumericalUpper) ∧
  (∀ i : Fin 3, polynomialNumericalLower <
    alternatingSign (-1) i * rationalPolynomialError p c (polynomialNumericalSquaredContacts i))

def EntropyGlobalEnvelopeClaim : Prop :=
  let z := entropyNumericalCandidate
  (∀ t ∈ Set.Icc (0 : ℝ) (9999 / 10000),
    |geometryError entropyNumericalGeometry z.1 z.2 t| ≤ entropyNumericalUpper) ∧
  (∀ t ∈ Set.Ico (9999 / 10000 : ℝ) 1,
    |geometryError entropyNumericalGeometry z.1 z.2 t| < 5465 / 1000000) ∧
  (∀ i : Fin 3, entropyNumericalLower <
    alternatingSign 1 i * geometryError entropyNumericalGeometry z.1 z.2 (entropyNumericalContacts i)) ∧
  (∀ c ∈ Set.Icc (0 : ℝ) 2,
    score entropyNumericalFamily c (entropyNumericalContacts 1) -
      score entropyNumericalFamily c (entropyNumericalContacts 0) ≥
      ((entropyNumericalContacts 1) ^ 2 - (entropyNumericalContacts 0) ^ 2) /
        (2 - (entropyNumericalContacts 0) ^ 2 - (entropyNumericalContacts 1) ^ 2)) ∧
  (∀ c ∈ Set.Icc (0 : ℝ) 2,
    score entropyNumericalFamily c (entropyNumericalContacts 2) -
      score entropyNumericalFamily c (entropyNumericalContacts 1) ≥
      ((entropyNumericalContacts 2) ^ 2 - (entropyNumericalContacts 1) ^ 2) /
        (2 - (entropyNumericalContacts 1) ^ 2 - (entropyNumericalContacts 2) ^ 2)) ∧
  (∀ c ∈ Set.Icc (0 : ℝ) 2, ∀ i : Fin 3,
    |score entropyNumericalFamily c (entropyNumericalContacts i)| ≤ 5)

def suppliedLowerRadius (beta : Fin 3 → ℝ) (d12 d23 sigma : ℝ) : ℝ :=
  if sigma = 1 then (beta 0 + beta 1) / d12 else (beta 1 + beta 2) / d23
def suppliedUpperRadius (beta : Fin 3 → ℝ) (d12 d23 sigma : ℝ) : ℝ :=
  if sigma = 1 then (beta 1 + beta 2) / d23 else (beta 0 + beta 1) / d12
def suppliedScaleRadius (beta : Fin 3 → ℝ) (d12 d23 M sigma : ℝ) : ℝ :=
  sSup (Set.range beta) + M * max (suppliedLowerRadius beta d12 d23 sigma)
    (suppliedUpperRadius beta d12 d23 sigma)

def RobustContactLocalizationClaim : Prop :=
  ∀ (D : ContactFamily) (C : Set ℝ), AdmissibleContactFamily D C →
    ∀ (candidate : ℝ × ℝ) (L U sigma : ℝ) (t : Fin 3 → ℝ),
      ApproximateContacts D C candidate L U sigma t →
      ∀ (beta : Fin 3 → ℝ) (d12 d23 M : ℝ),
        (∀ i, contactBeta D L U sigma t i ≤ beta i) →
        0 < d12 → d12 ≤ scoreGap D C (t 0) (t 1) →
        0 < d23 → d23 ≤ scoreGap D C (t 1) (t 2) →
        contactScoreBound D C t ≤ M →
        ∀ z : ℝ × ℝ, z.1 ∈ C → 0 < z.2 → contactRho D z.1 z.2 ≤ ENNReal.ofReal U →
          candidate.1 - suppliedLowerRadius beta d12 d23 sigma ≤ z.1 ∧
          z.1 ≤ candidate.1 + suppliedUpperRadius beta d12 d23 sigma ∧
          |Real.log (z.2 / candidate.2)| ≤ suppliedScaleRadius beta d12 d23 M sigma

def RationalScaleEnclosureClaim : Prop :=
  ∀ p phat b : ℝ, 0 < p → 0 < phat → 0 ≤ b → b < 1 →
    |Real.log (p / phat)| ≤ b → phat * (1 - b) ≤ p ∧ p ≤ phat / (1 - b)

def LocalizationLinearShrinkageClaim : Prop :=
  ∀ (D : ContactFamily) (C : Set ℝ), AdmissibleContactFamily D C →
    ∀ (t : Fin 3 → ℝ) (sigma rlo rhi : ℝ),
      (∀ i, t i ∈ D.domain) → (sigma = 1 ∨ sigma = -1) →
      D.feature (t 0) < D.feature (t 1) → D.feature (t 1) < D.feature (t 2) →
      0 < rlo → rlo ≤ rhi → rhi < 1 →
      (∀ i, alternatingSign sigma i = -1 → rhi * D.B (t i) < D.A (t i)) →
      ∃ K ≥ (0 : ℝ), ∀ L U : ℝ, rlo ≤ L → L ≤ U → U ≤ rhi →
        (∀ i, 0 ≤ contactBeta D L U sigma t i ∧ contactBeta D L U sigma t i ≤ K * (U - L)) ∧
        0 ≤ lowerRadius D C L U sigma t ∧ lowerRadius D C L U sigma t ≤ K * (U - L) ∧
        0 ≤ upperRadius D C L U sigma t ∧ upperRadius D C L U sigma t ≤ K * (U - L) ∧
        0 ≤ logScaleRadius D C L U sigma t ∧ logScaleRadius D C L U sigma t ≤ K * (U - L)

end PGDRevision20261113


