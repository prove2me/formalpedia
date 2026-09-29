-- Prove2me | Definitions.Def_CK_GeneralCK_CorrectionCertifiedBandClosure
-- name    : CK_GeneralCK_CorrectionCertifiedBandClosure
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:43:08.802778+00:00
-- url     : https://prove2.me/theorems/ecd272b4-8504-4e11-b2fd-f66a9634266f
-- title:
--   Courtade–Kumar proof module `GeneralCK.CorrectionCertifiedBandClosure` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.CorrectionCertifiedBandClosure` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.CorrectionCertifiedBandClosure` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.CorrectionCertifiedBandClosure (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/CorrectionCertifiedBandClosure.lean)

import Definitions.Def_CK_GeneralCK_CorrectionFamilyAssembly

/-!
# Correction closure after the certified C1--C2 band

The accepted C1 and C2 families cover the closed band
`1/50 ≤ u ≤ 1/5`, `1/10 ≤ rho ≤ 1`, with the evaluated point restricted by
`rho < 1`.  This file removes that band from the remaining global correction
obligation.
-/

namespace GeneralCK.Correction

def OutsideCertifiedC1C2Band (u rho : ℝ) : Prop :=
  u < 1 / 50 ∨ 1 / 5 < u ∨ rho < 1 / 10

def ActualRatioFamilyOutsideCertifiedC1C2Band : Prop :=
  ∀ ⦃u rho : ℝ⦄, 0 < u → u < 1 / 2 → 0 < rho → rho < 1 →
    OutsideCertifiedC1C2Band u rho → ActualRatioMinorsPositive u rho

/-- Exact complement of the union of C1 and C2, retaining C1's additional
`3/40 ≤ rho < 1/10` strip for `u ≤ 1/10`. -/
def OutsideCertifiedC1C2Region (u rho : ℝ) : Prop :=
  u < 1 / 50 ∨ 1 / 5 < u ∨
    (u ≤ 1 / 10 ∧ rho < 3 / 40) ∨
    (1 / 10 < u ∧ rho < 1 / 10)

def ActualRatioFamilyOutsideCertifiedC1C2Region : Prop :=
  ∀ ⦃u rho : ℝ⦄, 0 < u → u < 1 / 2 → 0 < rho → rho < 1 →
    OutsideCertifiedC1C2Region u rho → ActualRatioMinorsPositive u rho

/-- The certified central band and its explicit complement cover every open
probability-ratio coordinate used by the global correction theorem. -/
theorem actualRatioFamily_of_c1_c2_and_remaining
    (hband : ActualRatioFamilyOn (1 / 50) (1 / 5) (1 / 10) 1)
    (hremaining : ActualRatioFamilyOutsideCertifiedC1C2Band) :
    ∀ u rho : ℝ, 0 < u → u < 1 / 2 → 0 < rho → rho < 1 →
      ActualRatioMinorsPositive u rho := by
  intro u rho hu huhalf hr hr1
  by_cases hout : OutsideCertifiedC1C2Band u rho
  · exact hremaining hu huhalf hr hr1 hout
  · simp only [OutsideCertifiedC1C2Band, not_or, not_lt] at hout
    exact hband ⟨hout.1, hout.2.1⟩ ⟨hout.2.2, hr1.le⟩ hr1

/-- Exact union version, using the full reach of C1 and C2 rather than only
their largest common rectangular sub-band. -/
theorem actualRatioFamily_of_exact_c1_c2_and_remaining
    (hC1 : ActualRatioFamilyOn (1 / 50) (1 / 10) (3 / 40) 1)
    (hC2 : ActualRatioFamilyOn (1 / 10) (1 / 5) (1 / 10) 1)
    (hremaining : ActualRatioFamilyOutsideCertifiedC1C2Region) :
    ∀ u rho : ℝ, 0 < u → u < 1 / 2 → 0 < rho → rho < 1 →
      ActualRatioMinorsPositive u rho := by
  intro u rho hu huhalf hr hr1
  by_cases hu10 : u ≤ 1 / 10
  · by_cases hu50 : 1 / 50 ≤ u
    · by_cases hrC1 : 3 / 40 ≤ rho
      · exact hC1 ⟨hu50, hu10⟩ ⟨hrC1, hr1.le⟩ hr1
      · apply hremaining hu huhalf hr hr1
        exact Or.inr (Or.inr (Or.inl ⟨hu10, lt_of_not_ge hrC1⟩))
    · apply hremaining hu huhalf hr hr1
      exact Or.inl (lt_of_not_ge hu50)
  · have hu10' : 1 / 10 < u := lt_of_not_ge hu10
    by_cases hu5 : u ≤ 1 / 5
    · by_cases hrC2 : 1 / 10 ≤ rho
      · exact hC2 ⟨hu10'.le, hu5⟩ ⟨hrC2, hr1.le⟩ hr1
      · apply hremaining hu huhalf hr hr1
        exact Or.inr (Or.inr (Or.inr ⟨hu10', lt_of_not_ge hrC2⟩))
    · apply hremaining hu huhalf hr hr1
      exact Or.inr (Or.inl (lt_of_not_ge hu5))

/-- End-to-end CK closure with the already certified C1--C2 band removed from
the correction premise. -/
theorem generalCourtadeKumar_of_c1_c2_band_and_remaining
    (hband : ActualRatioFamilyOn (1 / 50) (1 / 5) (1 / 10) 1)
    (hremaining : ActualRatioFamilyOutsideCertifiedC1C2Band)
    (href : ∀ a b : ℝ, 0 < b → b < a → a < 1 → 0 ≤ Reflection.curvature a b)
    (hpure : ∀ a c e f : ℝ,
      0 ≤ a → a ≤ c → c ≤ 1 / 2 → 0 < e → e ≤ f →
      e ≤ H a → f ≤ H c → 0 ≤ pureGap a c e f)
    (hpsi : ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
      μ.a < μ.b → μ.a + μ.b ≤ 1 →
      1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
      phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
      μ.gap ≤ μ.cost) :
    GeneralCourtadeKumar :=
  generalCourtadeKumar_of_actual_ratio_family_and_canonical_owners href
    (actualRatioFamily_of_c1_c2_and_remaining hband hremaining) hpure hpsi

/-- End-to-end CK closure using every point certified by C1 or C2. -/
theorem generalCourtadeKumar_of_exact_c1_c2_and_remaining
    (hC1 : ActualRatioFamilyOn (1 / 50) (1 / 10) (3 / 40) 1)
    (hC2 : ActualRatioFamilyOn (1 / 10) (1 / 5) (1 / 10) 1)
    (hremaining : ActualRatioFamilyOutsideCertifiedC1C2Region)
    (href : ∀ a b : ℝ, 0 < b → b < a → a < 1 → 0 ≤ Reflection.curvature a b)
    (hpure : ∀ a c e f : ℝ,
      0 ≤ a → a ≤ c → c ≤ 1 / 2 → 0 < e → e ≤ f →
      e ≤ H a → f ≤ H c → 0 ≤ pureGap a c e f)
    (hpsi : ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
      μ.a < μ.b → μ.a + μ.b ≤ 1 →
      1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
      phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
      μ.gap ≤ μ.cost) :
    GeneralCourtadeKumar :=
  generalCourtadeKumar_of_actual_ratio_family_and_canonical_owners href
    (actualRatioFamily_of_exact_c1_c2_and_remaining hC1 hC2 hremaining) hpure hpsi

#print axioms actualRatioFamily_of_c1_c2_and_remaining
#print axioms generalCourtadeKumar_of_c1_c2_band_and_remaining
#print axioms actualRatioFamily_of_exact_c1_c2_and_remaining
#print axioms generalCourtadeKumar_of_exact_c1_c2_and_remaining

end GeneralCK.Correction


