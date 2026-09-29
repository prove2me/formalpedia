-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapE8OwnerClosure
-- name    : CK_GeneralCK_PureGapE8OwnerClosure
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T07:18:18.470313+00:00
-- url     : https://prove2.me/theorems/48dfe8a2-617e-4373-b7a9-e528845f7047
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapE8OwnerClosure` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapE8OwnerClosure` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapE8OwnerClosure` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapE8OwnerClosure (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapE8OwnerClosure.lean)

import Definitions.Def_CK_GeneralCK_CanonicalCKClosure
import Definitions.Def_CK_GeneralCK_PureGapE8Inverse

-- ===== source module GeneralCK.PureGapE8OwnerClosure =====
section

/-!
# Closing the smooth pure-gap owner with equation (8)

The compact fixed-entropy argument has seven value owners.  Equation (8)
rules out the only smooth-interior case, so this file exposes the exact
remaining ledger containing just the six boundary faces and the small-mean
region.
-/

namespace GeneralCK

/-- The non-smooth owners of the retained canonical pure-gap chamber. -/
structure CanonicalPureGapBoundaryOwners (S : ℝ) : Prop where
  small : ∀ e f p, 0 < e → 0 < f → e ≤ f → p ∈ canonicalMeanSet e f →
    p.1 + p.2 < S → 0 ≤ canonicalPureGap p.1 p.2 e f
  seam : ∀ e f p, 0 < e → 0 < f → e ≤ f → p ∈ retainedMeanSet S e f →
    p.1 + p.2 = S → 0 ≤ canonicalPureGap p.1 p.2 e f
  equal : ∀ e f p, 0 < e → 0 < f → e ≤ f → p ∈ retainedMeanSet S e f →
    p.1 = p.2 → 0 ≤ canonicalPureGap p.1 p.2 e f
  leftHalf : ∀ e f p, 0 < e → 0 < f → e ≤ f → p ∈ retainedMeanSet S e f →
    p.1 = 1 / 2 → 0 ≤ canonicalPureGap p.1 p.2 e f
  rightHalf : ∀ e f p, 0 < e → 0 < f → e ≤ f → p ∈ retainedMeanSet S e f →
    p.2 = 1 / 2 → 0 ≤ canonicalPureGap p.1 p.2 e f
  leftCap : ∀ e f p, 0 < e → 0 < f → e ≤ f → p ∈ retainedMeanSet S e f →
    e = H p.1 → 0 ≤ canonicalPureGap p.1 p.2 e f
  rightCap : ∀ e f p, 0 < e → 0 < f → e ≤ f → p ∈ retainedMeanSet S e f →
    f = H p.2 → 0 ≤ canonicalPureGap p.1 p.2 e f

/-- The remaining boundary ledger after equal means are discharged by the
same correction-Hessian signs already needed by LB-1. -/
structure CanonicalPureGapOuterOwners (S : ℝ) : Prop where
  small : ∀ e f p, 0 < e → 0 < f → e ≤ f → p ∈ canonicalMeanSet e f →
    p.1 + p.2 < S → 0 ≤ canonicalPureGap p.1 p.2 e f
  seam : ∀ e f p, 0 < e → 0 < f → e ≤ f → p ∈ retainedMeanSet S e f →
    p.1 + p.2 = S → 0 ≤ canonicalPureGap p.1 p.2 e f
  leftHalf : ∀ e f p, 0 < e → 0 < f → e ≤ f → p ∈ retainedMeanSet S e f →
    p.1 = 1 / 2 → 0 ≤ canonicalPureGap p.1 p.2 e f
  rightHalf : ∀ e f p, 0 < e → 0 < f → e ≤ f → p ∈ retainedMeanSet S e f →
    p.2 = 1 / 2 → 0 ≤ canonicalPureGap p.1 p.2 e f
  leftCap : ∀ e f p, 0 < e → 0 < f → e ≤ f → p ∈ retainedMeanSet S e f →
    e = H p.1 → 0 ≤ canonicalPureGap p.1 p.2 e f
  rightCap : ∀ e f p, 0 < e → 0 < f → e ≤ f → p ∈ retainedMeanSet S e f →
    f = H p.2 → 0 ≤ canonicalPureGap p.1 p.2 e f

/-- Correction convexity supplies the equal-mean boundary owner. -/
theorem CanonicalPureGapOuterOwners.toBoundaryOwners {S : ℝ}
    (houter : CanonicalPureGapOuterOwners S)
    (hleft : ∀ p ∈ Correction.orderedTriangle,
      0 < Correction.Mleft p.1 p.2)
    (hdet : ∀ p ∈ Correction.orderedTriangle,
      0 ≤ Correction.Mdet p.1 p.2) :
    CanonicalPureGapBoundaryOwners S where
  small := houter.small
  seam := houter.seam
  leftHalf := houter.leftHalf
  rightHalf := houter.rightHalf
  leftCap := houter.leftCap
  rightCap := houter.rightCap
  equal := by
    intro e f p he hf _hef hp heq
    have hm0 : 0 < p.1 := by
      have hne : p.1 ≠ 0 := by
        intro hzero
        have he0 : e ≤ 0 := by
          calc
            e ≤ H p.1 := hp.1.2.2.2.1
            _ = 0 := by rw [hzero, H_zero]
        exact (not_lt_of_ge he0) he
      exact lt_of_le_of_ne hp.1.1 (Ne.symm hne)
    have hm1 : p.1 < 1 :=
      lt_of_le_of_lt (hp.1.2.1.trans hp.1.2.2.1) (by norm_num)
    have heMem : e ∈ Set.Ioc 0 (H p.1) := ⟨he, hp.1.2.2.2.1⟩
    have hfMem : f ∈ Set.Ioc 0 (H p.1) := by
      refine ⟨hf, ?_⟩
      rw [heq]
      exact hp.1.2.2.2.2
    rw [← pureGap_eq_canonicalPureGap hp.1.2.1 hp.1.2.2.1, ← heq]
    exact pureGap_equal_mean_nonneg_of_convex
      (Correction.convexOn_entropyCorrection_square hleft hdet)
      hm0 hm1 heMem hfMem

/-- Strict equation (8) supplies the smooth-interior owner. -/
theorem CanonicalPureGapBoundaryOwners.toOwners {S : ℝ}
    (hboundary : CanonicalPureGapBoundaryOwners S)
    (hE8 : E8StrictOnSlopeRange) : CanonicalPureGapOwners S where
  small := hboundary.small
  seam := hboundary.seam
  equal := hboundary.equal
  leftHalf := hboundary.leftHalf
  rightHalf := hboundary.rightHalf
  leftCap := hboundary.leftCap
  rightCap := hboundary.rightCap
  interior := by
    intro e f p he hf _hef hp hmin
    have hac : p.1 < p.2 := hp.2.2.1
    have hc : p.2 < 1 / 2 := hp.2.2.2.1
    have ha : p.1 < 1 / 2 := hac.trans hc
    have hsum : p.1 + p.2 < 1 := by linarith
    exact False.elim
      ((not_localMin_of_e8SlopeRange hE8 hac hsum ha hc he hf) hmin)

/-- Boundary ownership plus equation (8) proves the positive-entropy pure
gap globally. -/
theorem pureGap_nonneg_of_boundaryOwners_e8 {S : ℝ} (hS : S ≤ 1)
    (hboundary : CanonicalPureGapBoundaryOwners S)
    (hE8 : E8StrictOnSlopeRange)
    {a b e f : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1)
    (hb₀ : 0 ≤ b) (hb₁ : b ≤ 1) (he : 0 < e) (hf : 0 < f)
    (hecap : e ≤ H a) (hfcap : f ≤ H b) : 0 ≤ pureGap a b e f :=
  pureGap_nonneg_of_canonicalPureGapOwners hS (hboundary.toOwners hE8)
    ha₀ ha₁ hb₀ hb₁ he hf hecap hfcap

/-- End-to-end general CK interface with the smooth pure-gap owner replaced
by the manuscript's range-restricted equation-(8) inequality. -/
theorem generalCourtadeKumar_of_boundary_ledger_and_e8 {S : ℝ}
    (hS : S ≤ 1)
    (href : ∀ a b : ℝ, 0 < b → b < a → a < 1 → 0 ≤ Reflection.curvature a b)
    (hleft : ∀ p ∈ Correction.orderedTriangle,
      0 < Correction.Mleft p.1 p.2)
    (hdet : ∀ p ∈ Correction.orderedTriangle,
      0 ≤ Correction.Mdet p.1 p.2)
    (hboundary : CanonicalPureGapBoundaryOwners S)
    (hE8 : E8StrictOnSlopeRange)
    (hpsi : ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
      μ.a < μ.b → μ.a + μ.b ≤ 1 →
      1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
      phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
      μ.gap ≤ μ.cost) :
    GeneralCourtadeKumar :=
  generalCourtadeKumar_of_fixedEntropy_owner_ledger hS href hleft hdet
    (hboundary.toOwners hE8) hpsi

/-- End-to-end interface after eliminating both the smooth-interior and
equal-mean owners. -/
theorem generalCourtadeKumar_of_outer_ledger_and_e8 {S : ℝ}
    (hS : S ≤ 1)
    (href : ∀ a b : ℝ, 0 < b → b < a → a < 1 → 0 ≤ Reflection.curvature a b)
    (hleft : ∀ p ∈ Correction.orderedTriangle,
      0 < Correction.Mleft p.1 p.2)
    (hdet : ∀ p ∈ Correction.orderedTriangle,
      0 ≤ Correction.Mdet p.1 p.2)
    (houter : CanonicalPureGapOuterOwners S)
    (hE8 : E8StrictOnSlopeRange)
    (hpsi : ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
      μ.a < μ.b → μ.a + μ.b ≤ 1 →
      1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
      phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
      μ.gap ≤ μ.cost) :
    GeneralCourtadeKumar :=
  generalCourtadeKumar_of_boundary_ledger_and_e8 hS href hleft hdet
    (houter.toBoundaryOwners hleft hdet) hE8 hpsi

end GeneralCK

end


