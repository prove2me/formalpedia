-- Prove2me | Definitions.Def_CK_GeneralCK_CorrectionRatioBellmanClosure
-- name    : CK_GeneralCK_CorrectionRatioBellmanClosure
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:33:29.199988+00:00
-- url     : https://prove2.me/theorems/1d103d50-b04c-44e2-968c-2866281f7024
-- title:
--   Courtade–Kumar proof module `GeneralCK.CorrectionRatioBellmanClosure` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.CorrectionRatioBellmanClosure` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.CorrectionRatioBellmanClosure` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.CorrectionRatioBellmanClosure (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/CorrectionRatioBellmanClosure.lean)

import Definitions.Def_CK_GeneralCK_CorrectionRatioGlobalBridge
import Definitions.Def_CK_GeneralCK_CanonicalCKClosure

/-!
# Bellman closure from probability-ratio correction certificates

This removes the coordinate-conversion plumbing between the generated
correction families and the canonical scalar-owner closure.  The correction
premise is stated directly in the `(u, rho)` coordinates checked by those
families and covers the full open probability rectangle.
-/

namespace GeneralCK

/-- General CK from reflection curvature, a full probability-ratio correction
kernel certificate, the canonical pure-gap owner, and the residual active-psi
owner.  No additional domain restriction is introduced. -/
theorem generalCourtadeKumar_of_ratio_kernel_and_canonical_owners
    (href : ∀ a b : ℝ, 0 < b → b < a → a < 1 → 0 ≤ Reflection.curvature a b)
    (hkernel : ∀ u rho : ℝ, 0 < u → u < 1/2 → 0 < rho → rho < 1 →
      0 < Correction.Natural.m11 u (u+rho*(1/2-u)) ∧
      0 ≤ Correction.Natural.kdet u (u+rho*(1/2-u)))
    (hpure : ∀ a c e f : ℝ,
      0 ≤ a → a ≤ c → c ≤ 1 / 2 → 0 < e → e ≤ f →
      e ≤ H a → f ≤ H c → 0 ≤ pureGap a c e f)
    (hpsi : ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
      μ.a < μ.b → μ.a + μ.b ≤ 1 →
      1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
      phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
      μ.gap ≤ μ.cost) :
    GeneralCourtadeKumar := by
  obtain ⟨hleft, hdet⟩ :=
    Correction.orderedTriangle_signs_of_ratio_kernel hkernel
  exact generalCourtadeKumar_of_canonical_scalar_owners
    href hleft hdet hpure hpsi

/-- Variant matching generated correction leaves, which prove both numerical
minors strictly positive. -/
theorem generalCourtadeKumar_of_strict_ratio_kernel_and_canonical_owners
    (href : ∀ a b : ℝ, 0 < b → b < a → a < 1 → 0 ≤ Reflection.curvature a b)
    (hkernel : ∀ u rho : ℝ, 0 < u → u < 1/2 → 0 < rho → rho < 1 →
      0 < Correction.Natural.m11 u (u+rho*(1/2-u)) ∧
      0 < Correction.Natural.kdet u (u+rho*(1/2-u)))
    (hpure : ∀ a c e f : ℝ,
      0 ≤ a → a ≤ c → c ≤ 1 / 2 → 0 < e → e ≤ f →
      e ≤ H a → f ≤ H c → 0 ≤ pureGap a c e f)
    (hpsi : ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
      μ.a < μ.b → μ.a + μ.b ≤ 1 →
      1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
      phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
      μ.gap ≤ μ.cost) :
    GeneralCourtadeKumar := by
  apply generalCourtadeKumar_of_ratio_kernel_and_canonical_owners
    href _ hpure hpsi
  intro u rho hu huhalf hr hr1
  exact ⟨(hkernel u rho hu huhalf hr hr1).1,
    (hkernel u rho hu huhalf hr hr1).2.le⟩

/-- End-to-end interface matching the `actual_minors_positive` conclusion of
the generated correction-family aggregate theorem. -/
theorem generalCourtadeKumar_of_actual_ratio_family_and_canonical_owners
    (href : ∀ a b : ℝ, 0 < b → b < a → a < 1 → 0 ≤ Reflection.curvature a b)
    (hfamily : ∀ u rho : ℝ, 0 < u → u < 1/2 → 0 < rho → rho < 1 →
      0 < Correction.Mleft (H u) (H (u+rho*(1/2-u))) ∧
      0 < Correction.Mdet (H u) (H (u+rho*(1/2-u))))
    (hpure : ∀ a c e f : ℝ,
      0 ≤ a → a ≤ c → c ≤ 1 / 2 → 0 < e → e ≤ f →
      e ≤ H a → f ≤ H c → 0 ≤ pureGap a c e f)
    (hpsi : ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
      μ.a < μ.b → μ.a + μ.b ≤ 1 →
      1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
      phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
      μ.gap ≤ μ.cost) :
    GeneralCourtadeKumar := by
  obtain ⟨hleft, hdet⟩ :=
    Correction.orderedTriangle_signs_of_actual_ratio_family hfamily
  exact generalCourtadeKumar_of_canonical_scalar_owners
    href hleft hdet hpure hpsi

#print axioms generalCourtadeKumar_of_ratio_kernel_and_canonical_owners
#print axioms generalCourtadeKumar_of_strict_ratio_kernel_and_canonical_owners
#print axioms generalCourtadeKumar_of_actual_ratio_family_and_canonical_owners

end GeneralCK


