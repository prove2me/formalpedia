-- Prove2me | Definitions.Def_CK_CKLaneA1_BSFinal
-- name    : CK_CKLaneA1_BSFinal
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T16:01:58.503877+00:00
-- url     : https://prove2.me/theorems/de68b19e-d95c-4698-b30f-35cb55b987e5
-- title:
--   Courtade–Kumar proof module `CKLaneA1.BSFinal` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA1.BSFinal` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA1.BSFinal` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA1.BSFinal (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA1/BSFinal.lean)

import Definitions.Def_CK_CKLaneA1_BSCover
import Definitions.Def_CK_CKLaneA1_Bridge
import Definitions.Def_CK_GeneralCK_CorrectionComplementCharts
import Definitions.Def_CK_CKLaneA1_BSData_C000
import Definitions.Def_CK_CKLaneA1_BSData_C001
import Definitions.Def_CK_CKLaneA1_BSData_C002
import Definitions.Def_CK_CKLaneA1_BSData_C003
import Definitions.Def_CK_CKLaneA1_BSData_C004
import Definitions.Def_CK_CKLaneA1_BSData_C005
import Definitions.Def_CK_CKLaneA1_BSData_C006
import Definitions.Def_CK_CKLaneA1_BSData_C007
import Definitions.Def_CK_CKLaneA1_BSData_C008

/-!
# CKLaneA1.BSFinal — `ChartOwners.bothSmall`, closed

The generated `(w, u/w)` cover (`9` chunk modules, each checked by `decide +kernel` on the
Boolean checker `bsStripFull`) plus the one-time soundness theorem `bs_pointwise_of_cover` give
pointwise positivity of `m11` and of the gap coefficient on `0 < u < w ≤ 1/40`; the bridge below
converts it to the exact `ChartOwners.bothSmall` field type.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace CKLaneA1

open GeneralCK GeneralCK.Correction GeneralCK.Correction.Natural GeneralCK.Correction.HighU

def bsStrips : List BSStrip := BSData.bstrips000 ++ BSData.bstrips001 ++ BSData.bstrips002 ++ BSData.bstrips003 ++ BSData.bstrips004 ++ BSData.bstrips005 ++ BSData.bstrips006 ++ BSData.bstrips007 ++ BSData.bstrips008

theorem bsStrips_all : bsStrips.all (bsStripFull 22 (ln2Iv 22)) = true := by
  simp only [bsStrips, List.all_append, BSData.bstrips000_ok, BSData.bstrips001_ok, BSData.bstrips002_ok, BSData.bstrips003_ok, BSData.bstrips004_ok, BSData.bstrips005_ok, BSData.bstrips006_ok, BSData.bstrips007_ok, BSData.bstrips008_ok, Bool.and_self, Bool.true_and]

theorem bsStrips_chain : bsChainOK 0 bsStrips = true := by decide +kernel

theorem bsStrips_last : decide (SCz ≤ 40 * bsLastW 0 bsStrips) = true := by decide +kernel

theorem bsStrips_ne : decide (bsStrips ≠ []) = true := by decide +kernel

theorem bsCover_ok : bsCoverOK 22 bsStrips = true := by
  unfold bsCoverOK
  rw [bsStrips_chain, bsStrips_last, bsStrips_ne, bsStrips_all]
  all_goals rfl

/-- Pointwise positivity on the both-small triangle `0 < u < w ≤ 1/40`. -/
theorem bothSmall_pointwise : ∀ u w : ℝ, 0 < u → u < w → w ≤ 1/40 →
    0 < actualDetGapCoefficient u w ∧ 0 < m11 u w :=
  bs_pointwise_of_cover bsCover_ok

/-- **`ChartOwners.bothSmall`**, with the exact field type. -/
theorem bothSmall_field : ∀ ⦃u rho : ℝ⦄, 0 < u → u < 1 / 2 → 0 < rho → rho < 1 →
    u + rho * (1 / 2 - u) ≤ 1 / 40 → GeneralCK.Correction.Complement.RatioSigns u rho := by
  intro u rho hu hu2 hr hr1 hw40
  have hgap : 0 < rho * (1 / 2 - u) := mul_pos hr (by linarith)
  have huw : u < u + rho * (1 / 2 - u) := by linarith
  obtain ⟨hcoef, hm⟩ := bothSmall_pointwise u _ hu huw hw40
  exact ratioSigns_of_pos hu hu2 hr hr1 hcoef.le hm

/-- Machine check that `bothSmall_field` has exactly the `ChartOwners.bothSmall` field type. -/
theorem withBothSmall (c : GeneralCK.Correction.Complement.ChartOwners) :
    GeneralCK.Correction.Complement.ChartOwners :=
  { c with bothSmall := bothSmall_field }

#print axioms bsCover_ok
#print axioms bothSmall_pointwise
#print axioms bothSmall_field

end CKLaneA1


