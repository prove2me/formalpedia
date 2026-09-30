-- Prove2me | Definitions.Def_CK_GeneralCK_SmallBoundaryPhiLowContactClosure
-- name    : CK_GeneralCK_SmallBoundaryPhiLowContactClosure
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:58:37.692902+00:00
-- url     : https://prove2.me/theorems/69238251-97e7-4bf2-b066-906da7682102
-- title:
--   Courtade–Kumar proof module `GeneralCK.SmallBoundaryPhiLowContactClosure` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.SmallBoundaryPhiLowContactClosure` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.SmallBoundaryPhiLowContactClosure` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.SmallBoundaryPhiLowContactClosure (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/SmallBoundaryPhiLowContactClosure.lean)

import Definitions.Def_CK_GeneralCK_SmallBoundaryPhiTailSource

-- ===== source module GeneralCK.SmallBoundaryPhiLowContactClosure =====
section

namespace GeneralCK.SmallBoundaryPhiSchur

open Set
open SmallMeanPhiCutoff

theorem tailScalarBounds : TailScalarBounds where
  lowerA := by
    intro t ht htu
    obtain ⟨htU,hz,hzU,hb,hbU⟩ := tail_coordinates_box ht htu
    rw [actualA_eq_box ht (by linarith)]
    exact SmallBoundaryPhiTailBox.A_lower ht.le htU hz.le hzU (by linarith) (by linarith)
  upperA := by
    intro t ht htu
    obtain ⟨htU,hz,hzU,hb,hbU⟩ := tail_coordinates_box ht htu
    rw [actualA_eq_box ht (by linarith)]
    exact SmallBoundaryPhiTailBox.A_upper ht.le htU hz.le hzU (by linarith) (by linarith)
  upperK := by
    intro t ht htu
    obtain ⟨htU,hz,hzU,hb,hbU⟩ := tail_coordinates_box ht htu
    rw [actualK_eq_box ht (by linarith)]
    exact SmallBoundaryPhiTailBox.K_upper ht.le htU hz.le hzU (by linarith) (by linarith)
  defect := by
    intro t ht htu
    obtain ⟨htU,hz,hzU,hb,hbU⟩ := tail_coordinates_box ht htu
    have hbnd := SmallBoundaryPhiTailBox.difference_upper ht htU hz.le hzU
      (show 1 ≤ tailB t by linarith) (show tailB t ≤ 1+1/10000 by linarith)
    rw [← actualA_eq_box ht (by linarith), ← actualK_eq_box ht (by linarith)] at hbnd
    have hv := (div_le_iff₀ (by positivity : 0 < 2*t)).mp hbnd
    linarith
  comparison := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioc _ _)
      (f' := fun t => (SmallBoundaryPhiTailBox.normalizedDerivative t (tailZ t) (tailB t)-
        SmallBoundaryPhiTailBox.EL t (tailZ t) (tailB t)/10)/t)
    · intro t ht
      have htU := (tail_coordinates_box ht.1 ht.2).1
      exact (hasDerivAt_comparisonPotential ht.1 (by linarith)).continuousAt.continuousWithinAt
    · intro t ht
      have htm := interior_subset ht
      have htU := (tail_coordinates_box htm.1 htm.2).1
      exact (hasDerivAt_comparisonPotential htm.1 (by linarith)).hasDerivWithinAt
    · intro t ht
      have htm := interior_subset ht
      obtain ⟨htU,hz,hzU,hb,hbU⟩ := tail_coordinates_box htm.1 htm.2
      exact div_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr (SmallBoundaryPhiTailBox.normalizedDerivative_upper htm.1.le htU
          hz.le hzU (by linarith) (by linarith))) htm.1.le

/-- Unconditional closure of the entire singular low-contact tail. -/
theorem lowContactTailOwner : LowContactTailOwner tailDelta :=
  lowContactTailOwner_of_scalarBounds tailScalarBounds

theorem scalarCurvature_of_compactContact (h : CompactContactOwner tailDelta) :
    ScalarCurvatureOwner := scalarCurvature_of_compact_and_tail h lowContactTailOwner

theorem smallBoundaryMidpoint_of_compactContact (h : CompactContactOwner tailDelta) :
    SmallBoundaryPhiMidpointOwner :=
  smallBoundaryMidpoint_of_scalarCurvature (scalarCurvature_of_compactContact h)

theorem belowCutoffHybrid_of_compactContact (h : CompactContactOwner tailDelta) :
    BelowCutoffPhiHybridOwner :=
  belowCutoffHybrid_of_scalarCurvature (scalarCurvature_of_compactContact h)

#print axioms tailScalarBounds
#print axioms lowContactTailOwner
#print axioms scalarCurvature_of_compactContact
#print axioms smallBoundaryMidpoint_of_compactContact
#print axioms belowCutoffHybrid_of_compactContact

end GeneralCK.SmallBoundaryPhiSchur

end


