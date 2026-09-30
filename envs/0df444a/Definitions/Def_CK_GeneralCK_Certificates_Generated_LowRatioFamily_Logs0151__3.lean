-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0151__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0151__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T12:22:27.396067+00:00
-- url     : https://prove2.me/theorems/a9c1aeb9-a80f-4b83-b291-11c6faf158c8
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0151 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0152, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0151 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0152, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0153)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0151 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0152, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0153)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0151 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0152, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0153) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0151 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0152, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0153).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0151 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_9664_neg : (38209733 / 62500000) ≤ -Real.log (488281250 / 899867293) ∧
    -Real.log (488281250 / 899867293) ≤ (611355729 / 1000000000) := by
  have h := checkLog_sound (w := (411586043 / 1388148543)) (n := 12)
    (lo := (38209733 / 62500000)) (hi := (611355729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((899867293 / 488281250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(899867293 / 488281250) = 1/(488281250 / 899867293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9664 : Bounds (38209733 / 62500000) (611355729 / 1000000000) (Real.log (899867293 / 488281250)) := by
  have h := reflection_log_9664_neg
  have he : Real.log (899867293 / 488281250) = -Real.log (488281250 / 899867293) := by
    rw [show ((899867293 / 488281250) : ℝ) = ((488281250 / 899867293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9665_neg : (52010781 / 200000000) ≤ -Real.log (1000 / 1297) ∧
    -Real.log (1000 / 1297) ≤ (130026953 / 500000000) := by
  have h := checkLog_sound (w := (297 / 2297)) (n := 12)
    (lo := (52010781 / 200000000)) (hi := (130026953 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1297 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1297 / 1000) = 1/(1000 / 1297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9665 : Bounds (52010781 / 200000000) (130026953 / 500000000) (Real.log (1297 / 1000)) := by
  have h := reflection_log_9665_neg
  have he : Real.log (1297 / 1000) = -Real.log (1000 / 1297) := by
    rw [show ((1297 / 1000) : ℝ) = ((1000 / 1297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9666_neg : (352398387 / 1000000000) ≤ -Real.log (703 / 1000) ∧
    -Real.log (703 / 1000) ≤ (88099597 / 250000000) := by
  have h := checkLog_sound (w := (297 / 1703)) (n := 12)
    (lo := (352398387 / 1000000000)) (hi := (88099597 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 703) = 1/(703 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9666 : Bounds (-88099597 / 250000000) (-352398387 / 1000000000) (Real.log (703 / 1000)) := by
  have h := reflection_log_9666_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9667_neg : (59391 / 200000000) ≤ -Real.log (1000000 / 1000297) ∧
    -Real.log (1000000 / 1000297) ≤ (74239 / 250000000) := by
  have h := checkLog_sound (w := (297 / 2000297)) (n := 12)
    (lo := (59391 / 200000000)) (hi := (74239 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000297 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000297 / 1000000) = 1/(1000000 / 1000297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9667 : Bounds (59391 / 200000000) (74239 / 250000000) (Real.log (1000297 / 1000000)) := by
  have h := reflection_log_9667_neg
  have he : Real.log (1000297 / 1000000) = -Real.log (1000000 / 1000297) := by
    rw [show ((1000297 / 1000000) : ℝ) = ((1000000 / 1000297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9668_neg : (74261 / 250000000) ≤ -Real.log (999703 / 1000000) ∧
    -Real.log (999703 / 1000000) ≤ (59409 / 200000000) := by
  have h := checkLog_sound (w := (297 / 1999703)) (n := 12)
    (lo := (74261 / 250000000)) (hi := (59409 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999703) = 1/(999703 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9668 : Bounds (-59409 / 200000000) (-74261 / 250000000) (Real.log (999703 / 1000000)) := by
  have h := reflection_log_9668_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9669_neg : (70105703 / 500000000) ≤ -Real.log (1000000 / 1150517) ∧
    -Real.log (1000000 / 1150517) ≤ (140211407 / 1000000000) := by
  have h := checkLog_sound (w := (150517 / 2150517)) (n := 12)
    (lo := (70105703 / 500000000)) (hi := (140211407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1150517 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1150517 / 1000000) = 1/(1000000 / 1150517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9669 : Bounds (70105703 / 500000000) (140211407 / 1000000000) (Real.log (1150517 / 1000000)) := by
  have h := reflection_log_9669_neg
  have he : Real.log (1150517 / 1000000) = -Real.log (1000000 / 1150517) := by
    rw [show ((1150517 / 1000000) : ℝ) = ((1000000 / 1150517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9670_neg : (163127349 / 1000000000) ≤ -Real.log (849483 / 1000000) ∧
    -Real.log (849483 / 1000000) ≤ (3262547 / 20000000) := by
  have h := checkLog_sound (w := (150517 / 1849483)) (n := 12)
    (lo := (163127349 / 1000000000)) (hi := (3262547 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 849483) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 849483) = 1/(849483 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9670 : Bounds (-3262547 / 20000000) (-163127349 / 1000000000) (Real.log (849483 / 1000000)) := by
  have h := reflection_log_9670_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9671_neg : (70346841 / 500000000) ≤ -Real.log (31250 / 35971) ∧
    -Real.log (31250 / 35971) ≤ (140693683 / 1000000000) := by
  have h := checkLog_sound (w := (4721 / 67221)) (n := 12)
    (lo := (70346841 / 500000000)) (hi := (140693683 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((35971 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(35971 / 31250) = 1/(31250 / 35971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9671 : Bounds (70346841 / 500000000) (140693683 / 1000000000) (Real.log (35971 / 31250)) := by
  have h := reflection_log_9671_neg
  have he : Real.log (35971 / 31250) = -Real.log (31250 / 35971) := by
    rw [show ((35971 / 31250) : ℝ) = ((31250 / 35971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9672_neg : (163780901 / 1000000000) ≤ -Real.log (26529 / 31250) ∧
    -Real.log (26529 / 31250) ≤ (81890451 / 500000000) := by
  have h := checkLog_sound (w := (4721 / 57779)) (n := 12)
    (lo := (163780901 / 1000000000)) (hi := (81890451 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 26529) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 26529) = 1/(26529 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9672 : Bounds (-81890451 / 500000000) (-163780901 / 1000000000) (Real.log (26529 / 31250)) := by
  have h := reflection_log_9672_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9673_neg : (23087219 / 1000000000) ≤ -Real.log (954274659 / 976562500) ∧
    -Real.log (954274659 / 976562500) ≤ (1154361 / 50000000) := by
  have h := checkLog_sound (w := (22287841 / 1930837159)) (n := 12)
    (lo := (23087219 / 1000000000)) (hi := (1154361 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 954274659) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 954274659) = 1/(954274659 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9673 : Bounds (-1154361 / 50000000) (-23087219 / 1000000000) (Real.log (954274659 / 976562500)) := by
  have h := reflection_log_9673_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9674_neg : (22915943 / 1000000000) ≤ -Real.log (977344632711 / 1000000000000) ∧
    -Real.log (977344632711 / 1000000000000) ≤ (2864493 / 125000000) := by
  have h := checkLog_sound (w := (22655367289 / 1977344632711)) (n := 12)
    (lo := (22915943 / 1000000000)) (hi := (2864493 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 977344632711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 977344632711) = 1/(977344632711 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9674 : Bounds (-2864493 / 125000000) (-22915943 / 1000000000) (Real.log (977344632711 / 1000000000000)) := by
  have h := reflection_log_9674_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9675_neg : (75834689 / 250000000) ≤ -Real.log (500000000000 / 677186594669) ∧
    -Real.log (500000000000 / 677186594669) ≤ (303338757 / 1000000000) := by
  have h := checkLog_sound (w := (177186594669 / 1177186594669)) (n := 12)
    (lo := (75834689 / 250000000)) (hi := (303338757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((677186594669 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(677186594669 / 500000000000) = 1/(500000000000 / 677186594669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9675 : Bounds (75834689 / 250000000) (303338757 / 1000000000) (Real.log (677186594669 / 500000000000)) := by
  have h := reflection_log_9675_neg
  have he : Real.log (677186594669 / 500000000000) = -Real.log (500000000000 / 677186594669) := by
    rw [show ((677186594669 / 500000000000) : ℝ) = ((500000000000 / 677186594669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9676_neg : (38059323 / 125000000) ≤ -Real.log (500000000000 / 677956198877) ∧
    -Real.log (500000000000 / 677956198877) ≤ (60894917 / 200000000) := by
  have h := checkLog_sound (w := (177956198877 / 1177956198877)) (n := 12)
    (lo := (38059323 / 125000000)) (hi := (60894917 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((677956198877 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(677956198877 / 500000000000) = 1/(500000000000 / 677956198877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9676 : Bounds (38059323 / 125000000) (60894917 / 200000000) (Real.log (677956198877 / 500000000000)) := by
  have h := reflection_log_9676_neg
  have he : Real.log (677956198877 / 500000000000) = -Real.log (500000000000 / 677956198877) := by
    rw [show ((677956198877 / 500000000000) : ℝ) = ((500000000000 / 677956198877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9677_neg : (38209733 / 62500000) ≤ -Real.log (500000000000 / 921464108031) ∧
    -Real.log (500000000000 / 921464108031) ≤ (611355729 / 1000000000) := by
  have h := checkLog_sound (w := (421464108031 / 1421464108031)) (n := 12)
    (lo := (38209733 / 62500000)) (hi := (611355729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((921464108031 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(921464108031 / 500000000000) = 1/(500000000000 / 921464108031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9677 : Bounds (38209733 / 62500000) (611355729 / 1000000000) (Real.log (921464108031 / 500000000000)) := by
  have h := reflection_log_9677_neg
  have he : Real.log (921464108031 / 500000000000) = -Real.log (500000000000 / 921464108031) := by
    rw [show ((921464108031 / 500000000000) : ℝ) = ((500000000000 / 921464108031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9678_neg : (153113073 / 250000000) ≤ -Real.log (250000000000 / 461237553343) ∧
    -Real.log (250000000000 / 461237553343) ≤ (612452293 / 1000000000) := by
  have h := checkLog_sound (w := (211237553343 / 711237553343)) (n := 12)
    (lo := (153113073 / 250000000)) (hi := (612452293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((461237553343 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(461237553343 / 250000000000) = 1/(250000000000 / 461237553343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9678 : Bounds (153113073 / 250000000) (612452293 / 1000000000) (Real.log (461237553343 / 250000000000)) := by
  have h := reflection_log_9678_neg
  have he : Real.log (461237553343 / 250000000000) = -Real.log (250000000000 / 461237553343) := by
    rw [show ((461237553343 / 250000000000) : ℝ) = ((250000000000 / 461237553343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9679_neg : (32554917 / 125000000) ≤ -Real.log (400 / 519) ∧
    -Real.log (400 / 519) ≤ (260439337 / 1000000000) := by
  have h := checkLog_sound (w := (119 / 919)) (n := 12)
    (lo := (32554917 / 125000000)) (hi := (260439337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((519 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(519 / 400) = 1/(400 / 519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9679 : Bounds (32554917 / 125000000) (260439337 / 1000000000) (Real.log (519 / 400)) := by
  have h := reflection_log_9679_neg
  have he : Real.log (519 / 400) = -Real.log (400 / 519) := by
    rw [show ((519 / 400) : ℝ) = ((400 / 519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9680_neg : (353109877 / 1000000000) ≤ -Real.log (281 / 400) ∧
    -Real.log (281 / 400) ≤ (176554939 / 500000000) := by
  have h := checkLog_sound (w := (119 / 681)) (n := 12)
    (lo := (353109877 / 1000000000)) (hi := (176554939 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 281) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400 / 281) = 1/(281 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9680 : Bounds (-176554939 / 500000000) (-353109877 / 1000000000) (Real.log (281 / 400)) := by
  have h := reflection_log_9680_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9681_neg : (59491 / 200000000) ≤ -Real.log (400000 / 400119) ∧
    -Real.log (400000 / 400119) ≤ (18591 / 62500000) := by
  have h := checkLog_sound (w := (119 / 800119)) (n := 12)
    (lo := (59491 / 200000000)) (hi := (18591 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400119 / 400000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400119 / 400000) = 1/(400000 / 400119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9681 : Bounds (59491 / 200000000) (18591 / 62500000) (Real.log (400119 / 400000)) := by
  have h := reflection_log_9681_neg
  have he : Real.log (400119 / 400000) = -Real.log (400000 / 400119) := by
    rw [show ((400119 / 400000) : ℝ) = ((400000 / 400119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9682_neg : (37193 / 125000000) ≤ -Real.log (399881 / 400000) ∧
    -Real.log (399881 / 400000) ≤ (59509 / 200000000) := by
  have h := checkLog_sound (w := (119 / 799881)) (n := 12)
    (lo := (37193 / 125000000)) (hi := (59509 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000 / 399881) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000 / 399881) = 1/(399881 / 400000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9682 : Bounds (-59509 / 200000000) (-37193 / 125000000) (Real.log (399881 / 400000)) := by
  have h := reflection_log_9682_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9683_neg : (2194361 / 15625000) ≤ -Real.log (1000000 / 1150779) ∧
    -Real.log (1000000 / 1150779) ≤ (28087821 / 200000000) := by
  have h := checkLog_sound (w := (150779 / 2150779)) (n := 12)
    (lo := (2194361 / 15625000)) (hi := (28087821 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1150779 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1150779 / 1000000) = 1/(1000000 / 1150779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9683 : Bounds (2194361 / 15625000) (28087821 / 200000000) (Real.log (1150779 / 1000000)) := by
  have h := reflection_log_9683_neg
  have he : Real.log (1150779 / 1000000) = -Real.log (1000000 / 1150779) := by
    rw [show ((1150779 / 1000000) : ℝ) = ((1000000 / 1150779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9684_neg : (8171791 / 50000000) ≤ -Real.log (849221 / 1000000) ∧
    -Real.log (849221 / 1000000) ≤ (163435821 / 1000000000) := by
  have h := checkLog_sound (w := (150779 / 1849221)) (n := 12)
    (lo := (8171791 / 50000000)) (hi := (163435821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 849221) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 849221) = 1/(849221 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9684 : Bounds (-163435821 / 1000000000) (-8171791 / 50000000) (Real.log (849221 / 1000000)) := by
  have h := reflection_log_9684_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9685_neg : (70461069 / 500000000) ≤ -Real.log (200000 / 230267) ∧
    -Real.log (200000 / 230267) ≤ (140922139 / 1000000000) := by
  have h := checkLog_sound (w := (30267 / 430267)) (n := 12)
    (lo := (70461069 / 500000000)) (hi := (140922139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((230267 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(230267 / 200000) = 1/(200000 / 230267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9685 : Bounds (70461069 / 500000000) (140922139 / 1000000000) (Real.log (230267 / 200000)) := by
  have h := reflection_log_9685_neg
  have he : Real.log (230267 / 200000) = -Real.log (200000 / 230267) := by
    rw [show ((230267 / 200000) : ℝ) = ((200000 / 230267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9686_neg : (1281959 / 7812500) ≤ -Real.log (169733 / 200000) ∧
    -Real.log (169733 / 200000) ≤ (164090753 / 1000000000) := by
  have h := checkLog_sound (w := (30267 / 369733)) (n := 12)
    (lo := (1281959 / 7812500)) (hi := (164090753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 169733) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 169733) = 1/(169733 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9686 : Bounds (-164090753 / 1000000000) (-1281959 / 7812500) (Real.log (169733 / 200000)) := by
  have h := reflection_log_9686_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9687_neg : (23168613 / 1000000000) ≤ -Real.log (39083908711 / 40000000000) ∧
    -Real.log (39083908711 / 40000000000) ≤ (11584307 / 500000000) := by
  have h := checkLog_sound (w := (916091289 / 79083908711)) (n := 12)
    (lo := (23168613 / 1000000000)) (hi := (11584307 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39083908711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39083908711) = 1/(39083908711 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9687 : Bounds (-11584307 / 500000000) (-23168613 / 1000000000) (Real.log (39083908711 / 40000000000)) := by
  have h := reflection_log_9687_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9688_neg : (4599343 / 200000000) ≤ -Real.log (977265693159 / 1000000000000) ∧
    -Real.log (977265693159 / 1000000000000) ≤ (5749179 / 250000000) := by
  have h := checkLog_sound (w := (22734306841 / 1977265693159)) (n := 12)
    (lo := (4599343 / 200000000)) (hi := (5749179 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 977265693159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 977265693159) = 1/(977265693159 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9688 : Bounds (-5749179 / 250000000) (-4599343 / 200000000) (Real.log (977265693159 / 1000000000000)) := by
  have h := reflection_log_9688_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9689_neg : (75968731 / 250000000) ≤ -Real.log (125000000000 / 169387444493) ∧
    -Real.log (125000000000 / 169387444493) ≤ (12154997 / 40000000) := by
  have h := checkLog_sound (w := (44387444493 / 294387444493)) (n := 12)
    (lo := (75968731 / 250000000)) (hi := (12154997 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169387444493 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169387444493 / 125000000000) = 1/(125000000000 / 169387444493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9689 : Bounds (75968731 / 250000000) (12154997 / 40000000) (Real.log (169387444493 / 125000000000)) := by
  have h := reflection_log_9689_neg
  have he : Real.log (169387444493 / 125000000000) = -Real.log (125000000000 / 169387444493) := by
    rw [show ((169387444493 / 125000000000) : ℝ) = ((125000000000 / 169387444493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9690_neg : (305012891 / 1000000000) ≤ -Real.log (250000000000 / 339160622861) ∧
    -Real.log (250000000000 / 339160622861) ≤ (76253223 / 250000000) := by
  have h := checkLog_sound (w := (89160622861 / 589160622861)) (n := 12)
    (lo := (305012891 / 1000000000)) (hi := (76253223 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((339160622861 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(339160622861 / 250000000000) = 1/(250000000000 / 339160622861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9690 : Bounds (305012891 / 1000000000) (76253223 / 250000000) (Real.log (339160622861 / 250000000000)) := by
  have h := reflection_log_9690_neg
  have he : Real.log (339160622861 / 250000000000) = -Real.log (250000000000 / 339160622861) := by
    rw [show ((339160622861 / 250000000000) : ℝ) = ((250000000000 / 339160622861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9691_neg : (153113073 / 250000000) ≤ -Real.log (100000000000 / 184495021337) ∧
    -Real.log (100000000000 / 184495021337) ≤ (612452293 / 1000000000) := by
  have h := checkLog_sound (w := (84495021337 / 284495021337)) (n := 12)
    (lo := (153113073 / 250000000)) (hi := (612452293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((184495021337 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(184495021337 / 100000000000) = 1/(100000000000 / 184495021337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9691 : Bounds (153113073 / 250000000) (612452293 / 1000000000) (Real.log (184495021337 / 100000000000)) := by
  have h := reflection_log_9691_neg
  have he : Real.log (184495021337 / 100000000000) = -Real.log (100000000000 / 184495021337) := by
    rw [show ((184495021337 / 100000000000) : ℝ) = ((100000000000 / 184495021337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9692_neg : (613549213 / 1000000000) ≤ -Real.log (125000000000 / 230871886121) ∧
    -Real.log (125000000000 / 230871886121) ≤ (306774607 / 500000000) := by
  have h := checkLog_sound (w := (105871886121 / 355871886121)) (n := 12)
    (lo := (613549213 / 1000000000)) (hi := (306774607 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((230871886121 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(230871886121 / 125000000000) = 1/(125000000000 / 230871886121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9692 : Bounds (613549213 / 1000000000) (306774607 / 500000000) (Real.log (230871886121 / 125000000000)) := by
  have h := reflection_log_9692_neg
  have he : Real.log (230871886121 / 125000000000) = -Real.log (125000000000 / 230871886121) := by
    rw [show ((230871886121 / 125000000000) : ℝ) = ((125000000000 / 230871886121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9693_neg : (130412309 / 500000000) ≤ -Real.log (500 / 649) ∧
    -Real.log (500 / 649) ≤ (260824619 / 1000000000) := by
  have h := checkLog_sound (w := (149 / 1149)) (n := 12)
    (lo := (130412309 / 500000000)) (hi := (260824619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((649 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(649 / 500) = 1/(500 / 649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9693 : Bounds (130412309 / 500000000) (260824619 / 1000000000) (Real.log (649 / 500)) := by
  have h := reflection_log_9693_neg
  have he : Real.log (649 / 500) = -Real.log (500 / 649) := by
    rw [show ((649 / 500) : ℝ) = ((500 / 649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9694_neg : (176910937 / 500000000) ≤ -Real.log (351 / 500) ∧
    -Real.log (351 / 500) ≤ (113223 / 320000) := by
  have h := checkLog_sound (w := (149 / 851)) (n := 12)
    (lo := (176910937 / 500000000)) (hi := (113223 / 320000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 351) = 1/(351 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9694 : Bounds (-113223 / 320000) (-176910937 / 500000000) (Real.log (351 / 500)) := by
  have h := reflection_log_9694_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9695_neg : (59591 / 200000000) ≤ -Real.log (500000 / 500149) ∧
    -Real.log (500000 / 500149) ≤ (74489 / 250000000) := by
  have h := checkLog_sound (w := (149 / 1000149)) (n := 12)
    (lo := (59591 / 200000000)) (hi := (74489 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500149 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500149 / 500000) = 1/(500000 / 500149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9695 : Bounds (59591 / 200000000) (74489 / 250000000) (Real.log (500149 / 500000)) := by
  have h := reflection_log_9695_neg
  have he : Real.log (500149 / 500000) = -Real.log (500000 / 500149) := by
    rw [show ((500149 / 500000) : ℝ) = ((500000 / 500149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9696_neg : (74511 / 250000000) ≤ -Real.log (499851 / 500000) ∧
    -Real.log (499851 / 500000) ≤ (59609 / 200000000) := by
  have h := checkLog_sound (w := (149 / 999851)) (n := 12)
    (lo := (74511 / 250000000)) (hi := (59609 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499851) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499851) = 1/(499851 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9696 : Bounds (-59609 / 200000000) (-74511 / 250000000) (Real.log (499851 / 500000)) := by
  have h := reflection_log_9696_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9697_neg : (562667 / 4000000) ≤ -Real.log (1000000 / 1151041) ∧
    -Real.log (1000000 / 1151041) ≤ (140666751 / 1000000000) := by
  have h := checkLog_sound (w := (151041 / 2151041)) (n := 12)
    (lo := (562667 / 4000000)) (hi := (140666751 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1151041 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1151041 / 1000000) = 1/(1000000 / 1151041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9697 : Bounds (562667 / 4000000) (140666751 / 1000000000) (Real.log (1151041 / 1000000)) := by
  have h := reflection_log_9697_neg
  have he : Real.log (1151041 / 1000000) = -Real.log (1000000 / 1151041) := by
    rw [show ((1151041 / 1000000) : ℝ) = ((1000000 / 1151041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9698_neg : (32748877 / 200000000) ≤ -Real.log (848959 / 1000000) ∧
    -Real.log (848959 / 1000000) ≤ (81872193 / 500000000) := by
  have h := checkLog_sound (w := (151041 / 1848959)) (n := 12)
    (lo := (32748877 / 200000000)) (hi := (81872193 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 848959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 848959) = 1/(848959 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9698 : Bounds (-81872193 / 500000000) (-32748877 / 200000000) (Real.log (848959 / 1000000)) := by
  have h := reflection_log_9698_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9699_neg : (70574837 / 500000000) ≤ -Real.log (1000000 / 1151597) ∧
    -Real.log (1000000 / 1151597) ≤ (5645987 / 40000000) := by
  have h := checkLog_sound (w := (151597 / 2151597)) (n := 12)
    (lo := (70574837 / 500000000)) (hi := (5645987 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1151597 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1151597 / 1000000) = 1/(1000000 / 1151597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9699 : Bounds (70574837 / 500000000) (5645987 / 40000000) (Real.log (1151597 / 1000000)) := by
  have h := reflection_log_9699_neg
  have he : Real.log (1151597 / 1000000) = -Real.log (1000000 / 1151597) := by
    rw [show ((1151597 / 1000000) : ℝ) = ((1000000 / 1151597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9700_neg : (1027497 / 6250000) ≤ -Real.log (848403 / 1000000) ∧
    -Real.log (848403 / 1000000) ≤ (164399521 / 1000000000) := by
  have h := checkLog_sound (w := (151597 / 1848403)) (n := 12)
    (lo := (1027497 / 6250000)) (hi := (164399521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 848403) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 848403) = 1/(848403 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9700 : Bounds (-164399521 / 1000000000) (-1027497 / 6250000) (Real.log (848403 / 1000000)) := by
  have h := reflection_log_9700_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9701_neg : (4649969 / 200000000) ≤ -Real.log (977018349591 / 1000000000000) ∧
    -Real.log (977018349591 / 1000000000000) ≤ (11624923 / 500000000) := by
  have h := checkLog_sound (w := (22981650409 / 1977018349591)) (n := 12)
    (lo := (4649969 / 200000000)) (hi := (11624923 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 977018349591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 977018349591) = 1/(977018349591 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9701 : Bounds (-11624923 / 500000000) (-4649969 / 200000000) (Real.log (977018349591 / 1000000000000)) := by
  have h := reflection_log_9701_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9702_neg : (4615527 / 200000000) ≤ -Real.log (977186616319 / 1000000000000) ∧
    -Real.log (977186616319 / 1000000000000) ≤ (5769409 / 250000000) := by
  have h := checkLog_sound (w := (22813383681 / 1977186616319)) (n := 12)
    (lo := (4615527 / 200000000)) (hi := (5769409 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 977186616319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 977186616319) = 1/(977186616319 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9702 : Bounds (-5769409 / 250000000) (-4615527 / 200000000) (Real.log (977186616319 / 1000000000000)) := by
  have h := reflection_log_9702_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9703_neg : (594553 / 1953125) ≤ -Real.log (250000000000 / 338956592721) ∧
    -Real.log (250000000000 / 338956592721) ≤ (304411137 / 1000000000) := by
  have h := checkLog_sound (w := (88956592721 / 588956592721)) (n := 12)
    (lo := (594553 / 1953125)) (hi := (304411137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((338956592721 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(338956592721 / 250000000000) = 1/(250000000000 / 338956592721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9703 : Bounds (594553 / 1953125) (304411137 / 1000000000) (Real.log (338956592721 / 250000000000)) := by
  have h := reflection_log_9703_neg
  have he : Real.log (338956592721 / 250000000000) = -Real.log (250000000000 / 338956592721) := by
    rw [show ((338956592721 / 250000000000) : ℝ) = ((250000000000 / 338956592721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9704_neg : (152774597 / 500000000) ≤ -Real.log (500000000000 / 678685129591) ∧
    -Real.log (500000000000 / 678685129591) ≤ (61109839 / 200000000) := by
  have h := checkLog_sound (w := (178685129591 / 1178685129591)) (n := 12)
    (lo := (152774597 / 500000000)) (hi := (61109839 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((678685129591 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(678685129591 / 500000000000) = 1/(500000000000 / 678685129591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9704 : Bounds (152774597 / 500000000) (61109839 / 200000000) (Real.log (678685129591 / 500000000000)) := by
  have h := reflection_log_9704_neg
  have he : Real.log (678685129591 / 500000000000) = -Real.log (500000000000 / 678685129591) := by
    rw [show ((678685129591 / 500000000000) : ℝ) = ((500000000000 / 678685129591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9705_neg : (613549213 / 1000000000) ≤ -Real.log (500000000000 / 923487544483) ∧
    -Real.log (500000000000 / 923487544483) ≤ (306774607 / 500000000) := by
  have h := checkLog_sound (w := (423487544483 / 1423487544483)) (n := 12)
    (lo := (613549213 / 1000000000)) (hi := (306774607 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((923487544483 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(923487544483 / 500000000000) = 1/(500000000000 / 923487544483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9705 : Bounds (613549213 / 1000000000) (306774607 / 500000000) (Real.log (923487544483 / 500000000000)) := by
  have h := reflection_log_9705_neg
  have he : Real.log (923487544483 / 500000000000) = -Real.log (500000000000 / 923487544483) := by
    rw [show ((923487544483 / 500000000000) : ℝ) = ((500000000000 / 923487544483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9706_neg : (614646493 / 1000000000) ≤ -Real.log (250000000000 / 462250712251) ∧
    -Real.log (250000000000 / 462250712251) ≤ (307323247 / 500000000) := by
  have h := checkLog_sound (w := (212250712251 / 712250712251)) (n := 12)
    (lo := (614646493 / 1000000000)) (hi := (307323247 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((462250712251 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(462250712251 / 250000000000) = 1/(250000000000 / 462250712251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9706 : Bounds (614646493 / 1000000000) (307323247 / 500000000) (Real.log (462250712251 / 250000000000)) := by
  have h := reflection_log_9706_neg
  have he : Real.log (462250712251 / 250000000000) = -Real.log (250000000000 / 462250712251) := by
    rw [show ((462250712251 / 250000000000) : ℝ) = ((250000000000 / 462250712251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9707_neg : (32651219 / 125000000) ≤ -Real.log (2000 / 2597) ∧
    -Real.log (2000 / 2597) ≤ (261209753 / 1000000000) := by
  have h := checkLog_sound (w := (597 / 4597)) (n := 12)
    (lo := (32651219 / 125000000)) (hi := (261209753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2597 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2597 / 2000) = 1/(2000 / 2597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9707 : Bounds (32651219 / 125000000) (261209753 / 1000000000) (Real.log (2597 / 2000)) := by
  have h := reflection_log_9707_neg
  have he : Real.log (2597 / 2000) = -Real.log (2000 / 2597) := by
    rw [show ((2597 / 2000) : ℝ) = ((2000 / 2597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9708_neg : (354534379 / 1000000000) ≤ -Real.log (1403 / 2000) ∧
    -Real.log (1403 / 2000) ≤ (17726719 / 50000000) := by
  have h := checkLog_sound (w := (597 / 3403)) (n := 12)
    (lo := (354534379 / 1000000000)) (hi := (17726719 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1403) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1403) = 1/(1403 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9708 : Bounds (-17726719 / 50000000) (-354534379 / 1000000000) (Real.log (1403 / 2000)) := by
  have h := reflection_log_9708_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9709_neg : (59691 / 200000000) ≤ -Real.log (2000000 / 2000597) ∧
    -Real.log (2000000 / 2000597) ≤ (37307 / 125000000) := by
  have h := checkLog_sound (w := (597 / 4000597)) (n := 12)
    (lo := (59691 / 200000000)) (hi := (37307 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000597 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000597 / 2000000) = 1/(2000000 / 2000597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9709 : Bounds (59691 / 200000000) (37307 / 125000000) (Real.log (2000597 / 2000000)) := by
  have h := reflection_log_9709_neg
  have he : Real.log (2000597 / 2000000) = -Real.log (2000000 / 2000597) := by
    rw [show ((2000597 / 2000000) : ℝ) = ((2000000 / 2000597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9710_neg : (18659 / 62500000) ≤ -Real.log (1999403 / 2000000) ∧
    -Real.log (1999403 / 2000000) ≤ (59709 / 200000000) := by
  have h := checkLog_sound (w := (597 / 3999403)) (n := 12)
    (lo := (18659 / 62500000)) (hi := (59709 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999403) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999403) = 1/(1999403 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9710 : Bounds (-59709 / 200000000) (-18659 / 62500000) (Real.log (1999403 / 2000000)) := by
  have h := reflection_log_9710_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9711_neg : (140895213 / 1000000000) ≤ -Real.log (125000 / 143913) ∧
    -Real.log (125000 / 143913) ≤ (70447607 / 500000000) := by
  have h := checkLog_sound (w := (18913 / 268913)) (n := 12)
    (lo := (140895213 / 1000000000)) (hi := (70447607 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((143913 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(143913 / 125000) = 1/(125000 / 143913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9711 : Bounds (140895213 / 1000000000) (70447607 / 500000000) (Real.log (143913 / 125000)) := by
  have h := reflection_log_9711_neg
  have he : Real.log (143913 / 125000) = -Real.log (125000 / 143913) := by
    rw [show ((143913 / 125000) : ℝ) = ((125000 / 143913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9712_neg : (6562169 / 40000000) ≤ -Real.log (106087 / 125000) ∧
    -Real.log (106087 / 125000) ≤ (82027113 / 500000000) := by
  have h := checkLog_sound (w := (18913 / 231087)) (n := 12)
    (lo := (6562169 / 40000000)) (hi := (82027113 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 106087) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 106087) = 1/(106087 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9712 : Bounds (-82027113 / 500000000) (-6562169 / 40000000) (Real.log (106087 / 125000)) := by
  have h := reflection_log_9712_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9713_neg : (141378027 / 1000000000) ≤ -Real.log (50000 / 57593) ∧
    -Real.log (50000 / 57593) ≤ (35344507 / 250000000) := by
  have h := checkLog_sound (w := (7593 / 107593)) (n := 12)
    (lo := (141378027 / 1000000000)) (hi := (35344507 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((57593 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(57593 / 50000) = 1/(50000 / 57593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9713 : Bounds (141378027 / 1000000000) (35344507 / 250000000) (Real.log (57593 / 50000)) := by
  have h := reflection_log_9713_neg
  have he : Real.log (57593 / 50000) = -Real.log (50000 / 57593) := by
    rw [show ((57593 / 50000) : ℝ) = ((50000 / 57593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9714_neg : (82354781 / 500000000) ≤ -Real.log (42407 / 50000) ∧
    -Real.log (42407 / 50000) ≤ (164709563 / 1000000000) := by
  have h := checkLog_sound (w := (7593 / 92407)) (n := 12)
    (lo := (82354781 / 500000000)) (hi := (164709563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 42407) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 42407) = 1/(42407 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9714 : Bounds (-164709563 / 1000000000) (-82354781 / 500000000) (Real.log (42407 / 50000)) := by
  have h := reflection_log_9714_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9715_neg : (4666307 / 200000000) ≤ -Real.log (2442346351 / 2500000000) ∧
    -Real.log (2442346351 / 2500000000) ≤ (1458221 / 62500000) := by
  have h := checkLog_sound (w := (57653649 / 4942346351)) (n := 12)
    (lo := (4666307 / 200000000)) (hi := (1458221 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2442346351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2442346351) = 1/(2442346351 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9715 : Bounds (-1458221 / 62500000) (-4666307 / 200000000) (Real.log (2442346351 / 2500000000)) := by
  have h := reflection_log_9715_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9716_neg : (5789753 / 250000000) ≤ -Real.log (15267298431 / 15625000000) ∧
    -Real.log (15267298431 / 15625000000) ≤ (23159013 / 1000000000) := by
  have h := checkLog_sound (w := (357701569 / 30892298431)) (n := 12)
    (lo := (5789753 / 250000000)) (hi := (23159013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15267298431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15267298431) = 1/(15267298431 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9716 : Bounds (-23159013 / 1000000000) (-5789753 / 250000000) (Real.log (15267298431 / 15625000000)) := by
  have h := reflection_log_9716_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9717_neg : (152474719 / 500000000) ≤ -Real.log (500000000000 / 678278205623) ∧
    -Real.log (500000000000 / 678278205623) ≤ (304949439 / 1000000000) := by
  have h := checkLog_sound (w := (178278205623 / 1178278205623)) (n := 12)
    (lo := (152474719 / 500000000)) (hi := (304949439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((678278205623 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(678278205623 / 500000000000) = 1/(500000000000 / 678278205623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9717 : Bounds (152474719 / 500000000) (304949439 / 1000000000) (Real.log (678278205623 / 500000000000)) := by
  have h := reflection_log_9717_neg
  have he : Real.log (678278205623 / 500000000000) = -Real.log (500000000000 / 678278205623) := by
    rw [show ((678278205623 / 500000000000) : ℝ) = ((500000000000 / 678278205623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9718_neg : (306087589 / 1000000000) ≤ -Real.log (250000000000 / 339525314217) ∧
    -Real.log (250000000000 / 339525314217) ≤ (30608759 / 100000000) := by
  have h := checkLog_sound (w := (89525314217 / 589525314217)) (n := 12)
    (lo := (306087589 / 1000000000)) (hi := (30608759 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((339525314217 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(339525314217 / 250000000000) = 1/(250000000000 / 339525314217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9718 : Bounds (306087589 / 1000000000) (30608759 / 100000000) (Real.log (339525314217 / 250000000000)) := by
  have h := reflection_log_9718_neg
  have he : Real.log (339525314217 / 250000000000) = -Real.log (250000000000 / 339525314217) := by
    rw [show ((339525314217 / 250000000000) : ℝ) = ((250000000000 / 339525314217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9719_neg : (614646493 / 1000000000) ≤ -Real.log (500000000000 / 924501424501) ∧
    -Real.log (500000000000 / 924501424501) ≤ (307323247 / 500000000) := by
  have h := checkLog_sound (w := (424501424501 / 1424501424501)) (n := 12)
    (lo := (614646493 / 1000000000)) (hi := (307323247 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((924501424501 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(924501424501 / 500000000000) = 1/(500000000000 / 924501424501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9719 : Bounds (614646493 / 1000000000) (307323247 / 500000000) (Real.log (924501424501 / 500000000000)) := by
  have h := reflection_log_9719_neg
  have he : Real.log (924501424501 / 500000000000) = -Real.log (500000000000 / 924501424501) := by
    rw [show ((924501424501 / 500000000000) : ℝ) = ((500000000000 / 924501424501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9720_neg : (615744131 / 1000000000) ≤ -Real.log (250000000000 / 462758374911) ∧
    -Real.log (250000000000 / 462758374911) ≤ (153936033 / 250000000) := by
  have h := checkLog_sound (w := (212758374911 / 712758374911)) (n := 12)
    (lo := (615744131 / 1000000000)) (hi := (153936033 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((462758374911 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(462758374911 / 250000000000) = 1/(250000000000 / 462758374911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9720 : Bounds (615744131 / 1000000000) (153936033 / 250000000) (Real.log (462758374911 / 250000000000)) := by
  have h := reflection_log_9720_neg
  have he : Real.log (462758374911 / 250000000000) = -Real.log (250000000000 / 462758374911) := by
    rw [show ((462758374911 / 250000000000) : ℝ) = ((250000000000 / 462758374911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9721_neg : (261594737 / 1000000000) ≤ -Real.log (1000 / 1299) ∧
    -Real.log (1000 / 1299) ≤ (130797369 / 500000000) := by
  have h := checkLog_sound (w := (299 / 2299)) (n := 12)
    (lo := (261594737 / 1000000000)) (hi := (130797369 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1299 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1299 / 1000) = 1/(1000 / 1299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9721 : Bounds (261594737 / 1000000000) (130797369 / 500000000) (Real.log (1299 / 1000)) := by
  have h := reflection_log_9721_neg
  have he : Real.log (1299 / 1000) = -Real.log (1000 / 1299) := by
    rw [show ((1299 / 1000) : ℝ) = ((1000 / 1299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9722_neg : (355247391 / 1000000000) ≤ -Real.log (701 / 1000) ∧
    -Real.log (701 / 1000) ≤ (11101481 / 31250000) := by
  have h := checkLog_sound (w := (299 / 1701)) (n := 12)
    (lo := (355247391 / 1000000000)) (hi := (11101481 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 701) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 701) = 1/(701 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9722 : Bounds (-11101481 / 31250000) (-355247391 / 1000000000) (Real.log (701 / 1000)) := by
  have h := reflection_log_9722_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9723_neg : (59791 / 200000000) ≤ -Real.log (1000000 / 1000299) ∧
    -Real.log (1000000 / 1000299) ≤ (74739 / 250000000) := by
  have h := checkLog_sound (w := (299 / 2000299)) (n := 12)
    (lo := (59791 / 200000000)) (hi := (74739 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000299 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000299 / 1000000) = 1/(1000000 / 1000299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9723 : Bounds (59791 / 200000000) (74739 / 250000000) (Real.log (1000299 / 1000000)) := by
  have h := reflection_log_9723_neg
  have he : Real.log (1000299 / 1000000) = -Real.log (1000000 / 1000299) := by
    rw [show ((1000299 / 1000000) : ℝ) = ((1000000 / 1000299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9724_neg : (74761 / 250000000) ≤ -Real.log (999701 / 1000000) ∧
    -Real.log (999701 / 1000000) ≤ (59809 / 200000000) := by
  have h := checkLog_sound (w := (299 / 1999701)) (n := 12)
    (lo := (74761 / 250000000)) (hi := (59809 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999701) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999701) = 1/(999701 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9724 : Bounds (-59809 / 200000000) (-74761 / 250000000) (Real.log (999701 / 1000000)) := by
  have h := reflection_log_9724_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9725_neg : (28224551 / 200000000) ≤ -Real.log (500000 / 575783) ∧
    -Real.log (500000 / 575783) ≤ (35280689 / 250000000) := by
  have h := checkLog_sound (w := (75783 / 1075783)) (n := 12)
    (lo := (28224551 / 200000000)) (hi := (35280689 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((575783 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(575783 / 500000) = 1/(500000 / 575783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9725 : Bounds (28224551 / 200000000) (35280689 / 250000000) (Real.log (575783 / 500000)) := by
  have h := reflection_log_9725_neg
  have he : Real.log (575783 / 500000) = -Real.log (500000 / 575783) := by
    rw [show ((575783 / 500000) : ℝ) = ((500000 / 575783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9726_neg : (164362981 / 1000000000) ≤ -Real.log (424217 / 500000) ∧
    -Real.log (424217 / 500000) ≤ (82181491 / 500000000) := by
  have h := checkLog_sound (w := (75783 / 924217)) (n := 12)
    (lo := (164362981 / 1000000000)) (hi := (82181491 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 424217) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 424217) = 1/(424217 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9726 : Bounds (-82181491 / 500000000) (-164362981 / 1000000000) (Real.log (424217 / 500000)) := by
  have h := reflection_log_9726_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9727_neg : (141606327 / 1000000000) ≤ -Real.log (1000000 / 1152123) ∧
    -Real.log (1000000 / 1152123) ≤ (17700791 / 125000000) := by
  have h := checkLog_sound (w := (152123 / 2152123)) (n := 12)
    (lo := (141606327 / 1000000000)) (hi := (17700791 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1152123 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1152123 / 1000000) = 1/(1000000 / 1152123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9727 : Bounds (141606327 / 1000000000) (17700791 / 125000000) (Real.log (1152123 / 1000000)) := by
  have h := reflection_log_9727_neg
  have he : Real.log (1152123 / 1000000) = -Real.log (1000000 / 1152123) := by
    rw [show ((1152123 / 1000000) : ℝ) = ((1000000 / 1152123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0152 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_9728_neg : (1650197 / 10000000) ≤ -Real.log (847877 / 1000000) ∧
    -Real.log (847877 / 1000000) ≤ (165019701 / 1000000000) := by
  have h := checkLog_sound (w := (152123 / 1847877)) (n := 12)
    (lo := (1650197 / 10000000)) (hi := (165019701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 847877) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 847877) = 1/(847877 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9728 : Bounds (-165019701 / 1000000000) (-1650197 / 10000000) (Real.log (847877 / 1000000)) := by
  have h := reflection_log_9728_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9729_neg : (23413373 / 1000000000) ≤ -Real.log (976858592871 / 1000000000000) ∧
    -Real.log (976858592871 / 1000000000000) ≤ (11706687 / 500000000) := by
  have h := checkLog_sound (w := (23141407129 / 1976858592871)) (n := 12)
    (lo := (23413373 / 1000000000)) (hi := (11706687 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 976858592871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 976858592871) = 1/(976858592871 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9729 : Bounds (-11706687 / 500000000) (-23413373 / 1000000000) (Real.log (976858592871 / 1000000000000)) := by
  have h := reflection_log_9729_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9730_neg : (11620113 / 500000000) ≤ -Real.log (244256936911 / 250000000000) ∧
    -Real.log (244256936911 / 250000000000) ≤ (23240227 / 1000000000) := by
  have h := checkLog_sound (w := (5743063089 / 494256936911)) (n := 12)
    (lo := (11620113 / 500000000)) (hi := (23240227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244256936911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244256936911) = 1/(244256936911 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9730 : Bounds (-23240227 / 1000000000) (-11620113 / 500000000) (Real.log (244256936911 / 250000000000)) := by
  have h := reflection_log_9730_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9731_neg : (38185717 / 125000000) ≤ -Real.log (250000000000 / 339321031453) ∧
    -Real.log (250000000000 / 339321031453) ≤ (305485737 / 1000000000) := by
  have h := checkLog_sound (w := (89321031453 / 589321031453)) (n := 12)
    (lo := (38185717 / 125000000)) (hi := (305485737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((339321031453 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(339321031453 / 250000000000) = 1/(250000000000 / 339321031453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9731 : Bounds (38185717 / 125000000) (305485737 / 1000000000) (Real.log (339321031453 / 250000000000)) := by
  have h := reflection_log_9731_neg
  have he : Real.log (339321031453 / 250000000000) = -Real.log (250000000000 / 339321031453) := by
    rw [show ((339321031453 / 250000000000) : ℝ) = ((250000000000 / 339321031453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9732_neg : (76656507 / 250000000) ≤ -Real.log (62500000000 / 84927044253) ∧
    -Real.log (62500000000 / 84927044253) ≤ (306626029 / 1000000000) := by
  have h := checkLog_sound (w := (22427044253 / 147427044253)) (n := 12)
    (lo := (76656507 / 250000000)) (hi := (306626029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((84927044253 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(84927044253 / 62500000000) = 1/(62500000000 / 84927044253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9732 : Bounds (76656507 / 250000000) (306626029 / 1000000000) (Real.log (84927044253 / 62500000000)) := by
  have h := reflection_log_9732_neg
  have he : Real.log (84927044253 / 62500000000) = -Real.log (62500000000 / 84927044253) := by
    rw [show ((84927044253 / 62500000000) : ℝ) = ((62500000000 / 84927044253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9733_neg : (615744131 / 1000000000) ≤ -Real.log (500000000000 / 925516749821) ∧
    -Real.log (500000000000 / 925516749821) ≤ (153936033 / 250000000) := by
  have h := checkLog_sound (w := (425516749821 / 1425516749821)) (n := 12)
    (lo := (615744131 / 1000000000)) (hi := (153936033 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((925516749821 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(925516749821 / 500000000000) = 1/(500000000000 / 925516749821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9733 : Bounds (615744131 / 1000000000) (153936033 / 250000000) (Real.log (925516749821 / 500000000000)) := by
  have h := reflection_log_9733_neg
  have he : Real.log (925516749821 / 500000000000) = -Real.log (500000000000 / 925516749821) := by
    rw [show ((925516749821 / 500000000000) : ℝ) = ((500000000000 / 925516749821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9734_neg : (616842129 / 1000000000) ≤ -Real.log (250000000000 / 463266761769) ∧
    -Real.log (250000000000 / 463266761769) ≤ (61684213 / 100000000) := by
  have h := checkLog_sound (w := (213266761769 / 713266761769)) (n := 12)
    (lo := (616842129 / 1000000000)) (hi := (61684213 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((463266761769 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(463266761769 / 250000000000) = 1/(250000000000 / 463266761769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9734 : Bounds (616842129 / 1000000000) (61684213 / 100000000) (Real.log (463266761769 / 250000000000)) := by
  have h := reflection_log_9734_neg
  have he : Real.log (463266761769 / 250000000000) = -Real.log (250000000000 / 463266761769) := by
    rw [show ((463266761769 / 250000000000) : ℝ) = ((250000000000 / 463266761769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9735_neg : (10479183 / 40000000) ≤ -Real.log (2000 / 2599) ∧
    -Real.log (2000 / 2599) ≤ (32747447 / 125000000) := by
  have h := checkLog_sound (w := (599 / 4599)) (n := 12)
    (lo := (10479183 / 40000000)) (hi := (32747447 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2599 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2599 / 2000) = 1/(2000 / 2599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9735 : Bounds (10479183 / 40000000) (32747447 / 125000000) (Real.log (2599 / 2000)) := by
  have h := reflection_log_9735_neg
  have he : Real.log (2599 / 2000) = -Real.log (2000 / 2599) := by
    rw [show ((2599 / 2000) : ℝ) = ((2000 / 2599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9736_neg : (355960913 / 1000000000) ≤ -Real.log (1401 / 2000) ∧
    -Real.log (1401 / 2000) ≤ (177980457 / 500000000) := by
  have h := checkLog_sound (w := (599 / 3401)) (n := 12)
    (lo := (355960913 / 1000000000)) (hi := (177980457 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1401) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1401) = 1/(1401 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9736 : Bounds (-177980457 / 500000000) (-355960913 / 1000000000) (Real.log (1401 / 2000)) := by
  have h := reflection_log_9736_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9737_neg : (59891 / 200000000) ≤ -Real.log (2000000 / 2000599) ∧
    -Real.log (2000000 / 2000599) ≤ (4679 / 15625000) := by
  have h := checkLog_sound (w := (599 / 4000599)) (n := 12)
    (lo := (59891 / 200000000)) (hi := (4679 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000599 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000599 / 2000000) = 1/(2000000 / 2000599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9737 : Bounds (59891 / 200000000) (4679 / 15625000) (Real.log (2000599 / 2000000)) := by
  have h := reflection_log_9737_neg
  have he : Real.log (2000599 / 2000000) = -Real.log (2000000 / 2000599) := by
    rw [show ((2000599 / 2000000) : ℝ) = ((2000000 / 2000599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9738_neg : (37443 / 125000000) ≤ -Real.log (1999401 / 2000000) ∧
    -Real.log (1999401 / 2000000) ≤ (59909 / 200000000) := by
  have h := checkLog_sound (w := (599 / 3999401)) (n := 12)
    (lo := (37443 / 125000000)) (hi := (59909 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999401) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999401) = 1/(1999401 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9738 : Bounds (-59909 / 200000000) (-37443 / 125000000) (Real.log (1999401 / 2000000)) := by
  have h := reflection_log_9738_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9739_neg : (28270049 / 200000000) ≤ -Real.log (250000 / 287957) ∧
    -Real.log (250000 / 287957) ≤ (70675123 / 500000000) := by
  have h := checkLog_sound (w := (37957 / 537957)) (n := 12)
    (lo := (28270049 / 200000000)) (hi := (70675123 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((287957 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(287957 / 250000) = 1/(250000 / 287957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9739 : Bounds (28270049 / 200000000) (70675123 / 500000000) (Real.log (287957 / 250000)) := by
  have h := reflection_log_9739_neg
  have he : Real.log (287957 / 250000) = -Real.log (250000 / 287957) := by
    rw [show ((287957 / 250000) : ℝ) = ((250000 / 287957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9740_neg : (164671833 / 1000000000) ≤ -Real.log (212043 / 250000) ∧
    -Real.log (212043 / 250000) ≤ (82335917 / 500000000) := by
  have h := checkLog_sound (w := (37957 / 462043)) (n := 12)
    (lo := (164671833 / 1000000000)) (hi := (82335917 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 212043) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 212043) = 1/(212043 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9740 : Bounds (-82335917 / 500000000) (-164671833 / 1000000000) (Real.log (212043 / 250000)) := by
  have h := reflection_log_9740_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9741_neg : (5673383 / 40000000) ≤ -Real.log (500000 / 576193) ∧
    -Real.log (500000 / 576193) ≤ (8864661 / 62500000) := by
  have h := checkLog_sound (w := (76193 / 1076193)) (n := 12)
    (lo := (5673383 / 40000000)) (hi := (8864661 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((576193 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(576193 / 500000) = 1/(500000 / 576193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9741 : Bounds (5673383 / 40000000) (8864661 / 62500000) (Real.log (576193 / 500000)) := by
  have h := reflection_log_9741_neg
  have he : Real.log (576193 / 500000) = -Real.log (500000 / 576193) := by
    rw [show ((576193 / 500000) : ℝ) = ((500000 / 576193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9742_neg : (33065987 / 200000000) ≤ -Real.log (423807 / 500000) ∧
    -Real.log (423807 / 500000) ≤ (10333121 / 62500000) := by
  have h := checkLog_sound (w := (76193 / 923807)) (n := 12)
    (lo := (33065987 / 200000000)) (hi := (10333121 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 423807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 423807) = 1/(423807 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9742 : Bounds (-10333121 / 62500000) (-33065987 / 200000000) (Real.log (423807 / 500000)) := by
  have h := reflection_log_9742_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9743_neg : (23495359 / 1000000000) ≤ -Real.log (244194626751 / 250000000000) ∧
    -Real.log (244194626751 / 250000000000) ≤ (73423 / 3125000) := by
  have h := checkLog_sound (w := (5805373249 / 494194626751)) (n := 12)
    (lo := (23495359 / 1000000000)) (hi := (73423 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244194626751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244194626751) = 1/(244194626751 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9743 : Bounds (-73423 / 3125000) (-23495359 / 1000000000) (Real.log (244194626751 / 250000000000)) := by
  have h := reflection_log_9743_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9744_neg : (23321587 / 1000000000) ≤ -Real.log (61059266151 / 62500000000) ∧
    -Real.log (61059266151 / 62500000000) ≤ (5830397 / 250000000) := by
  have h := checkLog_sound (w := (1440733849 / 123559266151)) (n := 12)
    (lo := (23321587 / 1000000000)) (hi := (5830397 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61059266151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61059266151) = 1/(61059266151 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9744 : Bounds (-5830397 / 250000000) (-23321587 / 1000000000) (Real.log (61059266151 / 62500000000)) := by
  have h := reflection_log_9744_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9745_neg : (306022079 / 1000000000) ≤ -Real.log (25000000000 / 33950307249) ∧
    -Real.log (25000000000 / 33950307249) ≤ (956319 / 3125000) := by
  have h := checkLog_sound (w := (8950307249 / 58950307249)) (n := 12)
    (lo := (306022079 / 1000000000)) (hi := (956319 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33950307249 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(33950307249 / 25000000000) = 1/(25000000000 / 33950307249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9745 : Bounds (306022079 / 1000000000) (956319 / 3125000) (Real.log (33950307249 / 25000000000)) := by
  have h := reflection_log_9745_neg
  have he : Real.log (33950307249 / 25000000000) = -Real.log (25000000000 / 33950307249) := by
    rw [show ((33950307249 / 25000000000) : ℝ) = ((25000000000 / 33950307249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9746_neg : (307164511 / 1000000000) ≤ -Real.log (500000000000 / 679782306569) ∧
    -Real.log (500000000000 / 679782306569) ≤ (9598891 / 31250000) := by
  have h := checkLog_sound (w := (179782306569 / 1179782306569)) (n := 12)
    (lo := (307164511 / 1000000000)) (hi := (9598891 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((679782306569 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(679782306569 / 500000000000) = 1/(500000000000 / 679782306569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9746 : Bounds (307164511 / 1000000000) (9598891 / 31250000) (Real.log (679782306569 / 500000000000)) := by
  have h := reflection_log_9746_neg
  have he : Real.log (679782306569 / 500000000000) = -Real.log (500000000000 / 679782306569) := by
    rw [show ((679782306569 / 500000000000) : ℝ) = ((500000000000 / 679782306569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9747_neg : (616842129 / 1000000000) ≤ -Real.log (500000000000 / 926533523537) ∧
    -Real.log (500000000000 / 926533523537) ≤ (61684213 / 100000000) := by
  have h := checkLog_sound (w := (426533523537 / 1426533523537)) (n := 12)
    (lo := (616842129 / 1000000000)) (hi := (61684213 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((926533523537 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(926533523537 / 500000000000) = 1/(500000000000 / 926533523537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9747 : Bounds (616842129 / 1000000000) (61684213 / 100000000) (Real.log (926533523537 / 500000000000)) := by
  have h := reflection_log_9747_neg
  have he : Real.log (926533523537 / 500000000000) = -Real.log (500000000000 / 926533523537) := by
    rw [show ((926533523537 / 500000000000) : ℝ) = ((500000000000 / 926533523537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9748_neg : (77242561 / 125000000) ≤ -Real.log (500000000000 / 927551748751) ∧
    -Real.log (500000000000 / 927551748751) ≤ (617940489 / 1000000000) := by
  have h := checkLog_sound (w := (427551748751 / 1427551748751)) (n := 12)
    (lo := (77242561 / 125000000)) (hi := (617940489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((927551748751 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(927551748751 / 500000000000) = 1/(500000000000 / 927551748751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9748 : Bounds (77242561 / 125000000) (617940489 / 1000000000) (Real.log (927551748751 / 500000000000)) := by
  have h := reflection_log_9748_neg
  have he : Real.log (927551748751 / 500000000000) = -Real.log (500000000000 / 927551748751) := by
    rw [show ((927551748751 / 500000000000) : ℝ) = ((500000000000 / 927551748751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9749_neg : (32795533 / 125000000) ≤ -Real.log (10 / 13) ∧
    -Real.log (10 / 13) ≤ (52472853 / 200000000) := by
  have h := checkLog_sound (w := (3 / 23)) (n := 12)
    (lo := (32795533 / 125000000)) (hi := (52472853 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13 / 10) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(13 / 10) = 1/(10 / 13) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9749 : Bounds (32795533 / 125000000) (52472853 / 200000000) (Real.log (13 / 10)) := by
  have h := reflection_log_9749_neg
  have he : Real.log (13 / 10) = -Real.log (10 / 13) := by
    rw [show ((13 / 10) : ℝ) = ((10 / 13) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9750_neg : (356674943 / 1000000000) ≤ -Real.log (7 / 10) ∧
    -Real.log (7 / 10) ≤ (2786523 / 7812500) := by
  have h := checkLog_sound (w := (3 / 17)) (n := 12)
    (lo := (356674943 / 1000000000)) (hi := (2786523 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10 / 7) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10 / 7) = 1/(7 / 10) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9750 : Bounds (-2786523 / 7812500) (-356674943 / 1000000000) (Real.log (7 / 10)) := by
  have h := reflection_log_9750_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9751_neg : (59991 / 200000000) ≤ -Real.log (10000 / 10003) ∧
    -Real.log (10000 / 10003) ≤ (74989 / 250000000) := by
  have h := checkLog_sound (w := (3 / 20003)) (n := 12)
    (lo := (59991 / 200000000)) (hi := (74989 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10003 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10003 / 10000) = 1/(10000 / 10003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9751 : Bounds (59991 / 200000000) (74989 / 250000000) (Real.log (10003 / 10000)) := by
  have h := reflection_log_9751_neg
  have he : Real.log (10003 / 10000) = -Real.log (10000 / 10003) := by
    rw [show ((10003 / 10000) : ℝ) = ((10000 / 10003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9752_neg : (60009 / 200000000) ≤ -Real.log (9997 / 10000) ∧
    -Real.log (9997 / 10000) ≤ (150023 / 500000000) := by
  have h := checkLog_sound (w := (3 / 19997)) (n := 12)
    (lo := (60009 / 200000000)) (hi := (150023 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 9997) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 9997) = 1/(9997 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9752 : Bounds (-150023 / 500000000) (-60009 / 200000000) (Real.log (9997 / 10000)) := by
  have h := reflection_log_9752_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9753_neg : (17697319 / 125000000) ≤ -Real.log (1000000 / 1152091) ∧
    -Real.log (1000000 / 1152091) ≤ (141578553 / 1000000000) := by
  have h := checkLog_sound (w := (152091 / 2152091)) (n := 12)
    (lo := (17697319 / 125000000)) (hi := (141578553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1152091 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1152091 / 1000000) = 1/(1000000 / 1152091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9753 : Bounds (17697319 / 125000000) (141578553 / 1000000000) (Real.log (1152091 / 1000000)) := by
  have h := reflection_log_9753_neg
  have he : Real.log (1152091 / 1000000) = -Real.log (1000000 / 1152091) := by
    rw [show ((1152091 / 1000000) : ℝ) = ((1000000 / 1152091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9754_neg : (4124549 / 25000000) ≤ -Real.log (847909 / 1000000) ∧
    -Real.log (847909 / 1000000) ≤ (164981961 / 1000000000) := by
  have h := checkLog_sound (w := (152091 / 1847909)) (n := 12)
    (lo := (4124549 / 25000000)) (hi := (164981961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 847909) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 847909) = 1/(847909 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9754 : Bounds (-164981961 / 1000000000) (-4124549 / 25000000) (Real.log (847909 / 1000000)) := by
  have h := reflection_log_9754_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9755_neg : (142062771 / 1000000000) ≤ -Real.log (1000000 / 1152649) ∧
    -Real.log (1000000 / 1152649) ≤ (35515693 / 250000000) := by
  have h := checkLog_sound (w := (152649 / 2152649)) (n := 12)
    (lo := (142062771 / 1000000000)) (hi := (35515693 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1152649 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1152649 / 1000000) = 1/(1000000 / 1152649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9755 : Bounds (142062771 / 1000000000) (35515693 / 250000000) (Real.log (1152649 / 1000000)) := by
  have h := reflection_log_9755_neg
  have he : Real.log (1152649 / 1000000) = -Real.log (1000000 / 1152649) := by
    rw [show ((1152649 / 1000000) : ℝ) = ((1000000 / 1152649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9756_neg : (82820133 / 500000000) ≤ -Real.log (847351 / 1000000) ∧
    -Real.log (847351 / 1000000) ≤ (165640267 / 1000000000) := by
  have h := checkLog_sound (w := (152649 / 1847351)) (n := 12)
    (lo := (82820133 / 500000000)) (hi := (165640267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 847351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 847351) = 1/(847351 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9756 : Bounds (-165640267 / 1000000000) (-82820133 / 500000000) (Real.log (847351 / 1000000)) := by
  have h := reflection_log_9756_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9757_neg : (11788747 / 500000000) ≤ -Real.log (976698282799 / 1000000000000) ∧
    -Real.log (976698282799 / 1000000000000) ≤ (4715499 / 200000000) := by
  have h := checkLog_sound (w := (23301717201 / 1976698282799)) (n := 12)
    (lo := (11788747 / 500000000)) (hi := (4715499 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 976698282799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 976698282799) = 1/(976698282799 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9757 : Bounds (-4715499 / 200000000) (-11788747 / 500000000) (Real.log (976698282799 / 1000000000000)) := by
  have h := reflection_log_9757_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9758_neg : (1462713 / 62500000) ≤ -Real.log (976868327719 / 1000000000000) ∧
    -Real.log (976868327719 / 1000000000000) ≤ (23403409 / 1000000000) := by
  have h := checkLog_sound (w := (23131672281 / 1976868327719)) (n := 12)
    (lo := (1462713 / 62500000)) (hi := (23403409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 976868327719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 976868327719) = 1/(976868327719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9758 : Bounds (-23403409 / 1000000000) (-1462713 / 62500000) (Real.log (976868327719 / 1000000000000)) := by
  have h := reflection_log_9758_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9759_neg : (598751 / 1953125) ≤ -Real.log (62500000000 / 84921480371) ∧
    -Real.log (62500000000 / 84921480371) ≤ (306560513 / 1000000000) := by
  have h := checkLog_sound (w := (22421480371 / 147421480371)) (n := 12)
    (lo := (598751 / 1953125)) (hi := (306560513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((84921480371 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(84921480371 / 62500000000) = 1/(62500000000 / 84921480371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9759 : Bounds (598751 / 1953125) (306560513 / 1000000000) (Real.log (84921480371 / 62500000000)) := by
  have h := reflection_log_9759_neg
  have he : Real.log (84921480371 / 62500000000) = -Real.log (62500000000 / 84921480371) := by
    rw [show ((84921480371 / 62500000000) : ℝ) = ((62500000000 / 84921480371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9760_neg : (153851519 / 500000000) ≤ -Real.log (500000000000 / 680148486283) ∧
    -Real.log (500000000000 / 680148486283) ≤ (307703039 / 1000000000) := by
  have h := checkLog_sound (w := (180148486283 / 1180148486283)) (n := 12)
    (lo := (153851519 / 500000000)) (hi := (307703039 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((680148486283 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(680148486283 / 500000000000) = 1/(500000000000 / 680148486283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9760 : Bounds (153851519 / 500000000) (307703039 / 1000000000) (Real.log (680148486283 / 500000000000)) := by
  have h := reflection_log_9760_neg
  have he : Real.log (680148486283 / 500000000000) = -Real.log (500000000000 / 680148486283) := by
    rw [show ((680148486283 / 500000000000) : ℝ) = ((500000000000 / 680148486283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9761_neg : (77242561 / 125000000) ≤ -Real.log (400000000 / 742041399) ∧
    -Real.log (400000000 / 742041399) ≤ (617940489 / 1000000000) := by
  have h := checkLog_sound (w := (342041399 / 1142041399)) (n := 12)
    (lo := (77242561 / 125000000)) (hi := (617940489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((742041399 / 400000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(742041399 / 400000000) = 1/(400000000 / 742041399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9761 : Bounds (77242561 / 125000000) (617940489 / 1000000000) (Real.log (742041399 / 400000000)) := by
  have h := reflection_log_9761_neg
  have he : Real.log (742041399 / 400000000) = -Real.log (400000000 / 742041399) := by
    rw [show ((742041399 / 400000000) : ℝ) = ((400000000 / 742041399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9762_neg : (77379901 / 125000000) ≤ -Real.log (125000000000 / 232142857143) ∧
    -Real.log (125000000000 / 232142857143) ≤ (619039209 / 1000000000) := by
  have h := checkLog_sound (w := (107142857143 / 357142857143)) (n := 12)
    (lo := (77379901 / 125000000)) (hi := (619039209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((232142857143 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(232142857143 / 125000000000) = 1/(125000000000 / 232142857143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9762 : Bounds (77379901 / 125000000) (619039209 / 1000000000) (Real.log (232142857143 / 125000000000)) := by
  have h := reflection_log_9762_neg
  have he : Real.log (232142857143 / 125000000000) = -Real.log (125000000000 / 232142857143) := by
    rw [show ((232142857143 / 125000000000) : ℝ) = ((125000000000 / 232142857143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9763_neg : (263133199 / 1000000000) ≤ -Real.log (1000 / 1301) ∧
    -Real.log (1000 / 1301) ≤ (657833 / 2500000) := by
  have h := checkLog_sound (w := (301 / 2301)) (n := 12)
    (lo := (263133199 / 1000000000)) (hi := (657833 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1301 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1301 / 1000) = 1/(1000 / 1301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9763 : Bounds (263133199 / 1000000000) (657833 / 2500000) (Real.log (1301 / 1000)) := by
  have h := reflection_log_9763_neg
  have he : Real.log (1301 / 1000) = -Real.log (1000 / 1301) := by
    rw [show ((1301 / 1000) : ℝ) = ((1000 / 1301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9764_neg : (44763067 / 125000000) ≤ -Real.log (699 / 1000) ∧
    -Real.log (699 / 1000) ≤ (358104537 / 1000000000) := by
  have h := checkLog_sound (w := (301 / 1699)) (n := 12)
    (lo := (44763067 / 125000000)) (hi := (358104537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 699) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 699) = 1/(699 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9764 : Bounds (-358104537 / 1000000000) (-44763067 / 125000000) (Real.log (699 / 1000)) := by
  have h := reflection_log_9764_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9765_neg : (150477 / 500000000) ≤ -Real.log (1000000 / 1000301) ∧
    -Real.log (1000000 / 1000301) ≤ (60191 / 200000000) := by
  have h := checkLog_sound (w := (301 / 2000301)) (n := 12)
    (lo := (150477 / 500000000)) (hi := (60191 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000301 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000301 / 1000000) = 1/(1000000 / 1000301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9765 : Bounds (150477 / 500000000) (60191 / 200000000) (Real.log (1000301 / 1000000)) := by
  have h := reflection_log_9765_neg
  have he : Real.log (1000301 / 1000000) = -Real.log (1000000 / 1000301) := by
    rw [show ((1000301 / 1000000) : ℝ) = ((1000000 / 1000301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9766_neg : (60209 / 200000000) ≤ -Real.log (999699 / 1000000) ∧
    -Real.log (999699 / 1000000) ≤ (150523 / 500000000) := by
  have h := checkLog_sound (w := (301 / 1999699)) (n := 12)
    (lo := (60209 / 200000000)) (hi := (150523 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999699) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999699) = 1/(999699 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9766 : Bounds (-150523 / 500000000) (-60209 / 200000000) (Real.log (999699 / 1000000)) := by
  have h := reflection_log_9766_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9767_neg : (70902969 / 500000000) ≤ -Real.log (1000000 / 1152353) ∧
    -Real.log (1000000 / 1152353) ≤ (141805939 / 1000000000) := by
  have h := checkLog_sound (w := (152353 / 2152353)) (n := 12)
    (lo := (70902969 / 500000000)) (hi := (141805939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1152353 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1152353 / 1000000) = 1/(1000000 / 1152353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9767 : Bounds (70902969 / 500000000) (141805939 / 1000000000) (Real.log (1152353 / 1000000)) := by
  have h := reflection_log_9767_neg
  have he : Real.log (1152353 / 1000000) = -Real.log (1000000 / 1152353) := by
    rw [show ((1152353 / 1000000) : ℝ) = ((1000000 / 1152353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9768_neg : (165291003 / 1000000000) ≤ -Real.log (847647 / 1000000) ∧
    -Real.log (847647 / 1000000) ≤ (41322751 / 250000000) := by
  have h := checkLog_sound (w := (152353 / 1847647)) (n := 12)
    (lo := (165291003 / 1000000000)) (hi := (41322751 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 847647) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 847647) = 1/(847647 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9768 : Bounds (-41322751 / 250000000) (-165291003 / 1000000000) (Real.log (847647 / 1000000)) := by
  have h := reflection_log_9768_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9769_neg : (142519007 / 1000000000) ≤ -Real.log (40000 / 46127) ∧
    -Real.log (40000 / 46127) ≤ (4453719 / 31250000) := by
  have h := checkLog_sound (w := (6127 / 86127)) (n := 12)
    (lo := (142519007 / 1000000000)) (hi := (4453719 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((46127 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(46127 / 40000) = 1/(40000 / 46127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9769 : Bounds (142519007 / 1000000000) (4453719 / 31250000) (Real.log (46127 / 40000)) := by
  have h := reflection_log_9769_neg
  have he : Real.log (46127 / 40000) = -Real.log (40000 / 46127) := by
    rw [show ((46127 / 40000) : ℝ) = ((40000 / 46127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9770_neg : (166261217 / 1000000000) ≤ -Real.log (33873 / 40000) ∧
    -Real.log (33873 / 40000) ≤ (83130609 / 500000000) := by
  have h := checkLog_sound (w := (6127 / 73873)) (n := 12)
    (lo := (166261217 / 1000000000)) (hi := (83130609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 33873) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 33873) = 1/(33873 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9770 : Bounds (-83130609 / 500000000) (-166261217 / 1000000000) (Real.log (33873 / 40000)) := by
  have h := reflection_log_9770_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9771_neg : (23742209 / 1000000000) ≤ -Real.log (1562459871 / 1600000000) ∧
    -Real.log (1562459871 / 1600000000) ≤ (2374221 / 100000000) := by
  have h := checkLog_sound (w := (37540129 / 3162459871)) (n := 12)
    (lo := (23742209 / 1000000000)) (hi := (2374221 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1562459871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1562459871) = 1/(1562459871 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9771 : Bounds (-2374221 / 100000000) (-23742209 / 1000000000) (Real.log (1562459871 / 1600000000)) := by
  have h := reflection_log_9771_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9772_neg : (2935633 / 125000000) ≤ -Real.log (976788563391 / 1000000000000) ∧
    -Real.log (976788563391 / 1000000000000) ≤ (4697013 / 200000000) := by
  have h := checkLog_sound (w := (23211436609 / 1976788563391)) (n := 12)
    (lo := (2935633 / 125000000)) (hi := (4697013 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 976788563391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 976788563391) = 1/(976788563391 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9772 : Bounds (-4697013 / 200000000) (-2935633 / 125000000) (Real.log (976788563391 / 1000000000000)) := by
  have h := reflection_log_9772_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9773_neg : (153548471 / 500000000) ≤ -Real.log (500000000000 / 679736376109) ∧
    -Real.log (500000000000 / 679736376109) ≤ (307096943 / 1000000000) := by
  have h := checkLog_sound (w := (179736376109 / 1179736376109)) (n := 12)
    (lo := (153548471 / 500000000)) (hi := (307096943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((679736376109 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(679736376109 / 500000000000) = 1/(500000000000 / 679736376109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9773 : Bounds (153548471 / 500000000) (307096943 / 1000000000) (Real.log (679736376109 / 500000000000)) := by
  have h := reflection_log_9773_neg
  have he : Real.log (679736376109 / 500000000000) = -Real.log (500000000000 / 679736376109) := by
    rw [show ((679736376109 / 500000000000) : ℝ) = ((500000000000 / 679736376109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9774_neg : (4824691 / 15625000) ≤ -Real.log (500000000000 / 680881528061) ∧
    -Real.log (500000000000 / 680881528061) ≤ (12351209 / 40000000) := by
  have h := checkLog_sound (w := (180881528061 / 1180881528061)) (n := 12)
    (lo := (4824691 / 15625000)) (hi := (12351209 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((680881528061 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(680881528061 / 500000000000) = 1/(500000000000 / 680881528061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9774 : Bounds (4824691 / 15625000) (12351209 / 40000000) (Real.log (680881528061 / 500000000000)) := by
  have h := reflection_log_9774_neg
  have he : Real.log (680881528061 / 500000000000) = -Real.log (500000000000 / 680881528061) := by
    rw [show ((680881528061 / 500000000000) : ℝ) = ((500000000000 / 680881528061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9775_neg : (77379901 / 125000000) ≤ -Real.log (500000000000 / 928571428571) ∧
    -Real.log (500000000000 / 928571428571) ≤ (619039209 / 1000000000) := by
  have h := checkLog_sound (w := (428571428571 / 1428571428571)) (n := 12)
    (lo := (77379901 / 125000000)) (hi := (619039209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((928571428571 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(928571428571 / 500000000000) = 1/(500000000000 / 928571428571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9775 : Bounds (77379901 / 125000000) (619039209 / 1000000000) (Real.log (928571428571 / 500000000000)) := by
  have h := reflection_log_9775_neg
  have he : Real.log (928571428571 / 500000000000) = -Real.log (500000000000 / 928571428571) := by
    rw [show ((928571428571 / 500000000000) : ℝ) = ((500000000000 / 928571428571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9776_neg : (77654717 / 125000000) ≤ -Real.log (500000000000 / 930615164521) ∧
    -Real.log (500000000000 / 930615164521) ≤ (621237737 / 1000000000) := by
  have h := checkLog_sound (w := (430615164521 / 1430615164521)) (n := 12)
    (lo := (77654717 / 125000000)) (hi := (621237737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((930615164521 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(930615164521 / 500000000000) = 1/(500000000000 / 930615164521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9776 : Bounds (77654717 / 125000000) (621237737 / 1000000000) (Real.log (930615164521 / 500000000000)) := by
  have h := reflection_log_9776_neg
  have he : Real.log (930615164521 / 500000000000) = -Real.log (500000000000 / 930615164521) := by
    rw [show ((930615164521 / 500000000000) : ℝ) = ((500000000000 / 930615164521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9777_neg : (263901543 / 1000000000) ≤ -Real.log (500 / 651) ∧
    -Real.log (500 / 651) ≤ (32987693 / 125000000) := by
  have h := checkLog_sound (w := (151 / 1151)) (n := 12)
    (lo := (263901543 / 1000000000)) (hi := (32987693 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((651 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(651 / 500) = 1/(500 / 651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9777 : Bounds (263901543 / 1000000000) (32987693 / 125000000) (Real.log (651 / 500)) := by
  have h := reflection_log_9777_neg
  have he : Real.log (651 / 500) = -Real.log (500 / 651) := by
    rw [show ((651 / 500) : ℝ) = ((500 / 651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9778_neg : (22471011 / 62500000) ≤ -Real.log (349 / 500) ∧
    -Real.log (349 / 500) ≤ (359536177 / 1000000000) := by
  have h := checkLog_sound (w := (151 / 849)) (n := 12)
    (lo := (22471011 / 62500000)) (hi := (359536177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 349) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 349) = 1/(349 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9778 : Bounds (-359536177 / 1000000000) (-22471011 / 62500000) (Real.log (349 / 500)) := by
  have h := reflection_log_9778_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9779_neg : (150977 / 500000000) ≤ -Real.log (500000 / 500151) ∧
    -Real.log (500000 / 500151) ≤ (60391 / 200000000) := by
  have h := checkLog_sound (w := (151 / 1000151)) (n := 12)
    (lo := (150977 / 500000000)) (hi := (60391 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500151 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500151 / 500000) = 1/(500000 / 500151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9779 : Bounds (150977 / 500000000) (60391 / 200000000) (Real.log (500151 / 500000)) := by
  have h := reflection_log_9779_neg
  have he : Real.log (500151 / 500000) = -Real.log (500000 / 500151) := by
    rw [show ((500151 / 500000) : ℝ) = ((500000 / 500151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9780_neg : (60409 / 200000000) ≤ -Real.log (499849 / 500000) ∧
    -Real.log (499849 / 500000) ≤ (151023 / 500000000) := by
  have h := checkLog_sound (w := (151 / 999849)) (n := 12)
    (lo := (60409 / 200000000)) (hi := (151023 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499849) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499849) = 1/(499849 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9780 : Bounds (-151023 / 500000000) (-60409 / 200000000) (Real.log (499849 / 500000)) := by
  have h := reflection_log_9780_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9781_neg : (8891339 / 62500000) ≤ -Real.log (500000 / 576439) ∧
    -Real.log (500000 / 576439) ≤ (5690457 / 40000000) := by
  have h := checkLog_sound (w := (76439 / 1076439)) (n := 12)
    (lo := (8891339 / 62500000)) (hi := (5690457 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((576439 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(576439 / 500000) = 1/(500000 / 576439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9781 : Bounds (8891339 / 62500000) (5690457 / 40000000) (Real.log (576439 / 500000)) := by
  have h := reflection_log_9781_neg
  have he : Real.log (576439 / 500000) = -Real.log (500000 / 576439) := by
    rw [show ((576439 / 500000) : ℝ) = ((500000 / 576439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9782_neg : (41477639 / 250000000) ≤ -Real.log (423561 / 500000) ∧
    -Real.log (423561 / 500000) ≤ (165910557 / 1000000000) := by
  have h := checkLog_sound (w := (76439 / 923561)) (n := 12)
    (lo := (41477639 / 250000000)) (hi := (165910557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 423561) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 423561) = 1/(423561 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9782 : Bounds (-165910557 / 1000000000) (-41477639 / 250000000) (Real.log (423561 / 500000)) := by
  have h := reflection_log_9782_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9783_neg : (28595007 / 200000000) ≤ -Real.log (1000000 / 1153701) ∧
    -Real.log (1000000 / 1153701) ≤ (35743759 / 250000000) := by
  have h := checkLog_sound (w := (153701 / 2153701)) (n := 12)
    (lo := (28595007 / 200000000)) (hi := (35743759 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1153701 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1153701 / 1000000) = 1/(1000000 / 1153701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9783 : Bounds (28595007 / 200000000) (35743759 / 250000000) (Real.log (1153701 / 1000000)) := by
  have h := reflection_log_9783_neg
  have he : Real.log (1153701 / 1000000) = -Real.log (1000000 / 1153701) := by
    rw [show ((1153701 / 1000000) : ℝ) = ((1000000 / 1153701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9784_neg : (166882553 / 1000000000) ≤ -Real.log (846299 / 1000000) ∧
    -Real.log (846299 / 1000000) ≤ (83441277 / 500000000) := by
  have h := checkLog_sound (w := (153701 / 1846299)) (n := 12)
    (lo := (166882553 / 1000000000)) (hi := (83441277 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 846299) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 846299) = 1/(846299 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9784 : Bounds (-83441277 / 500000000) (-166882553 / 1000000000) (Real.log (846299 / 1000000)) := by
  have h := reflection_log_9784_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9785_neg : (11953759 / 500000000) ≤ -Real.log (976376002599 / 1000000000000) ∧
    -Real.log (976376002599 / 1000000000000) ≤ (23907519 / 1000000000) := by
  have h := checkLog_sound (w := (23623997401 / 1976376002599)) (n := 12)
    (lo := (11953759 / 500000000)) (hi := (23907519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 976376002599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 976376002599) = 1/(976376002599 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9785 : Bounds (-23907519 / 1000000000) (-11953759 / 500000000) (Real.log (976376002599 / 1000000000000)) := by
  have h := reflection_log_9785_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9786_neg : (5912283 / 250000000) ≤ -Real.log (244157079279 / 250000000000) ∧
    -Real.log (244157079279 / 250000000000) ≤ (23649133 / 1000000000) := by
  have h := checkLog_sound (w := (5842920721 / 494157079279)) (n := 12)
    (lo := (5912283 / 250000000)) (hi := (23649133 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244157079279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244157079279) = 1/(244157079279 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9786 : Bounds (-23649133 / 1000000000) (-5912283 / 250000000) (Real.log (244157079279 / 250000000000)) := by
  have h := reflection_log_9786_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9787_neg : (308171981 / 1000000000) ≤ -Real.log (500000000000 / 680467512353) ∧
    -Real.log (500000000000 / 680467512353) ≤ (154085991 / 500000000) := by
  have h := checkLog_sound (w := (180467512353 / 1180467512353)) (n := 12)
    (lo := (308171981 / 1000000000)) (hi := (154085991 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((680467512353 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(680467512353 / 500000000000) = 1/(500000000000 / 680467512353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9787 : Bounds (308171981 / 1000000000) (154085991 / 500000000) (Real.log (680467512353 / 500000000000)) := by
  have h := reflection_log_9787_neg
  have he : Real.log (680467512353 / 500000000000) = -Real.log (500000000000 / 680467512353) := by
    rw [show ((680467512353 / 500000000000) : ℝ) = ((500000000000 / 680467512353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9788_neg : (309857589 / 1000000000) ≤ -Real.log (250000000000 / 340807740527) ∧
    -Real.log (250000000000 / 340807740527) ≤ (30985759 / 100000000) := by
  have h := checkLog_sound (w := (90807740527 / 590807740527)) (n := 12)
    (lo := (309857589 / 1000000000)) (hi := (30985759 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((340807740527 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(340807740527 / 250000000000) = 1/(250000000000 / 340807740527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9788 : Bounds (309857589 / 1000000000) (30985759 / 100000000) (Real.log (340807740527 / 250000000000)) := by
  have h := reflection_log_9788_neg
  have he : Real.log (340807740527 / 250000000000) = -Real.log (250000000000 / 340807740527) := by
    rw [show ((340807740527 / 250000000000) : ℝ) = ((250000000000 / 340807740527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9789_neg : (77654717 / 125000000) ≤ -Real.log (12500000000 / 23265379113) ∧
    -Real.log (12500000000 / 23265379113) ≤ (621237737 / 1000000000) := by
  have h := checkLog_sound (w := (10765379113 / 35765379113)) (n := 12)
    (lo := (77654717 / 125000000)) (hi := (621237737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23265379113 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23265379113 / 12500000000) = 1/(12500000000 / 23265379113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9789 : Bounds (77654717 / 125000000) (621237737 / 1000000000) (Real.log (23265379113 / 12500000000)) := by
  have h := reflection_log_9789_neg
  have he : Real.log (23265379113 / 12500000000) = -Real.log (12500000000 / 23265379113) := by
    rw [show ((23265379113 / 12500000000) : ℝ) = ((12500000000 / 23265379113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9790_neg : (15585943 / 25000000) ≤ -Real.log (500000000000 / 932664756447) ∧
    -Real.log (500000000000 / 932664756447) ≤ (623437721 / 1000000000) := by
  have h := checkLog_sound (w := (432664756447 / 1432664756447)) (n := 12)
    (lo := (15585943 / 25000000)) (hi := (623437721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((932664756447 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(932664756447 / 500000000000) = 1/(500000000000 / 932664756447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9790 : Bounds (15585943 / 25000000) (623437721 / 1000000000) (Real.log (932664756447 / 500000000000)) := by
  have h := reflection_log_9790_neg
  have he : Real.log (932664756447 / 500000000000) = -Real.log (500000000000 / 932664756447) := by
    rw [show ((932664756447 / 500000000000) : ℝ) = ((500000000000 / 932664756447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9791_neg : (132334649 / 500000000) ≤ -Real.log (1000 / 1303) ∧
    -Real.log (1000 / 1303) ≤ (264669299 / 1000000000) := by
  have h := checkLog_sound (w := (303 / 2303)) (n := 12)
    (lo := (132334649 / 500000000)) (hi := (264669299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1303 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1303 / 1000) = 1/(1000 / 1303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9791 : Bounds (132334649 / 500000000) (264669299 / 1000000000) (Real.log (1303 / 1000)) := by
  have h := reflection_log_9791_neg
  have he : Real.log (1303 / 1000) = -Real.log (1000 / 1303) := by
    rw [show ((1303 / 1000) : ℝ) = ((1000 / 1303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0153 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_9792_neg : (90242467 / 250000000) ≤ -Real.log (697 / 1000) ∧
    -Real.log (697 / 1000) ≤ (360969869 / 1000000000) := by
  have h := checkLog_sound (w := (303 / 1697)) (n := 12)
    (lo := (90242467 / 250000000)) (hi := (360969869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 697) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 697) = 1/(697 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9792 : Bounds (-360969869 / 1000000000) (-90242467 / 250000000) (Real.log (697 / 1000)) := by
  have h := reflection_log_9792_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9793_neg : (151477 / 500000000) ≤ -Real.log (1000000 / 1000303) ∧
    -Real.log (1000000 / 1000303) ≤ (60591 / 200000000) := by
  have h := checkLog_sound (w := (303 / 2000303)) (n := 12)
    (lo := (151477 / 500000000)) (hi := (60591 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000303 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000303 / 1000000) = 1/(1000000 / 1000303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9793 : Bounds (151477 / 500000000) (60591 / 200000000) (Real.log (1000303 / 1000000)) := by
  have h := reflection_log_9793_neg
  have he : Real.log (1000303 / 1000000) = -Real.log (1000000 / 1000303) := by
    rw [show ((1000303 / 1000000) : ℝ) = ((1000000 / 1000303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9794_neg : (60609 / 200000000) ≤ -Real.log (999697 / 1000000) ∧
    -Real.log (999697 / 1000000) ≤ (151523 / 500000000) := by
  have h := checkLog_sound (w := (303 / 1999697)) (n := 12)
    (lo := (60609 / 200000000)) (hi := (151523 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999697) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999697) = 1/(999697 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9794 : Bounds (-151523 / 500000000) (-60609 / 200000000) (Real.log (999697 / 1000000)) := by
  have h := reflection_log_9794_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9795_neg : (14271757 / 100000000) ≤ -Real.log (250000 / 288351) ∧
    -Real.log (250000 / 288351) ≤ (142717571 / 1000000000) := by
  have h := checkLog_sound (w := (38351 / 538351)) (n := 12)
    (lo := (14271757 / 100000000)) (hi := (142717571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((288351 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(288351 / 250000) = 1/(250000 / 288351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9795 : Bounds (14271757 / 100000000) (142717571 / 1000000000) (Real.log (288351 / 250000)) := by
  have h := reflection_log_9795_neg
  have he : Real.log (288351 / 250000) = -Real.log (250000 / 288351) := by
    rw [show ((288351 / 250000) : ℝ) = ((250000 / 288351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9796_neg : (6661267 / 40000000) ≤ -Real.log (211649 / 250000) ∧
    -Real.log (211649 / 250000) ≤ (41632919 / 250000000) := by
  have h := checkLog_sound (w := (38351 / 461649)) (n := 12)
    (lo := (6661267 / 40000000)) (hi := (41632919 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 211649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 211649) = 1/(211649 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9796 : Bounds (-41632919 / 250000000) (-6661267 / 40000000) (Real.log (211649 / 250000)) := by
  have h := reflection_log_9796_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9797_neg : (71715861 / 500000000) ≤ -Real.log (250000 / 288557) ∧
    -Real.log (250000 / 288557) ≤ (143431723 / 1000000000) := by
  have h := checkLog_sound (w := (38557 / 538557)) (n := 12)
    (lo := (71715861 / 500000000)) (hi := (143431723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((288557 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(288557 / 250000) = 1/(250000 / 288557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9797 : Bounds (71715861 / 500000000) (143431723 / 1000000000) (Real.log (288557 / 250000)) := by
  have h := reflection_log_9797_neg
  have he : Real.log (288557 / 250000) = -Real.log (250000 / 288557) := by
    rw [show ((288557 / 250000) : ℝ) = ((250000 / 288557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9798_neg : (167505459 / 1000000000) ≤ -Real.log (211443 / 250000) ∧
    -Real.log (211443 / 250000) ≤ (8375273 / 50000000) := by
  have h := checkLog_sound (w := (38557 / 461443)) (n := 12)
    (lo := (167505459 / 1000000000)) (hi := (8375273 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 211443) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 211443) = 1/(211443 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9798 : Bounds (-8375273 / 50000000) (-167505459 / 1000000000) (Real.log (211443 / 250000)) := by
  have h := reflection_log_9798_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9799_neg : (24073737 / 1000000000) ≤ -Real.log (61013357751 / 62500000000) ∧
    -Real.log (61013357751 / 62500000000) ≤ (12036869 / 500000000) := by
  have h := checkLog_sound (w := (1486642249 / 123513357751)) (n := 12)
    (lo := (24073737 / 1000000000)) (hi := (12036869 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61013357751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61013357751) = 1/(61013357751 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9799 : Bounds (-12036869 / 500000000) (-24073737 / 1000000000) (Real.log (61013357751 / 62500000000)) := by
  have h := reflection_log_9799_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9800_neg : (4762821 / 200000000) ≤ -Real.log (61029200799 / 62500000000) ∧
    -Real.log (61029200799 / 62500000000) ≤ (11907053 / 500000000) := by
  have h := checkLog_sound (w := (1470799201 / 123529200799)) (n := 12)
    (lo := (4762821 / 200000000)) (hi := (11907053 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61029200799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61029200799) = 1/(61029200799 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9800 : Bounds (-11907053 / 500000000) (-4762821 / 200000000) (Real.log (61029200799 / 62500000000)) := by
  have h := reflection_log_9800_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9801_neg : (61849849 / 200000000) ≤ -Real.log (50000000000 / 68120095063) ∧
    -Real.log (50000000000 / 68120095063) ≤ (154624623 / 500000000) := by
  have h := checkLog_sound (w := (18120095063 / 118120095063)) (n := 12)
    (lo := (61849849 / 200000000)) (hi := (154624623 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68120095063 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(68120095063 / 50000000000) = 1/(50000000000 / 68120095063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9801 : Bounds (61849849 / 200000000) (154624623 / 500000000) (Real.log (68120095063 / 50000000000)) := by
  have h := reflection_log_9801_neg
  have he : Real.log (68120095063 / 50000000000) = -Real.log (50000000000 / 68120095063) := by
    rw [show ((68120095063 / 50000000000) : ℝ) = ((50000000000 / 68120095063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9802_neg : (310937181 / 1000000000) ≤ -Real.log (100000000000 / 136470348983) ∧
    -Real.log (100000000000 / 136470348983) ≤ (155468591 / 500000000) := by
  have h := checkLog_sound (w := (36470348983 / 236470348983)) (n := 12)
    (lo := (310937181 / 1000000000)) (hi := (155468591 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((136470348983 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(136470348983 / 100000000000) = 1/(100000000000 / 136470348983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9802 : Bounds (310937181 / 1000000000) (155468591 / 500000000) (Real.log (136470348983 / 100000000000)) := by
  have h := reflection_log_9802_neg
  have he : Real.log (136470348983 / 100000000000) = -Real.log (100000000000 / 136470348983) := by
    rw [show ((136470348983 / 100000000000) : ℝ) = ((100000000000 / 136470348983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9803_neg : (15585943 / 25000000) ≤ -Real.log (250000000000 / 466332378223) ∧
    -Real.log (250000000000 / 466332378223) ≤ (623437721 / 1000000000) := by
  have h := checkLog_sound (w := (216332378223 / 716332378223)) (n := 12)
    (lo := (15585943 / 25000000)) (hi := (623437721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((466332378223 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(466332378223 / 250000000000) = 1/(250000000000 / 466332378223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9803 : Bounds (15585943 / 25000000) (623437721 / 1000000000) (Real.log (466332378223 / 250000000000)) := by
  have h := reflection_log_9803_neg
  have he : Real.log (466332378223 / 250000000000) = -Real.log (250000000000 / 466332378223) := by
    rw [show ((466332378223 / 250000000000) : ℝ) = ((250000000000 / 466332378223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9804_neg : (312819583 / 500000000) ≤ -Real.log (125000000000 / 233680057389) ∧
    -Real.log (125000000000 / 233680057389) ≤ (625639167 / 1000000000) := by
  have h := checkLog_sound (w := (108680057389 / 358680057389)) (n := 12)
    (lo := (312819583 / 500000000)) (hi := (625639167 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((233680057389 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(233680057389 / 125000000000) = 1/(125000000000 / 233680057389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9804 : Bounds (312819583 / 500000000) (625639167 / 1000000000) (Real.log (233680057389 / 125000000000)) := by
  have h := reflection_log_9804_neg
  have he : Real.log (233680057389 / 125000000000) = -Real.log (125000000000 / 233680057389) := by
    rw [show ((233680057389 / 125000000000) : ℝ) = ((125000000000 / 233680057389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9805_neg : (265436463 / 1000000000) ≤ -Real.log (125 / 163) ∧
    -Real.log (125 / 163) ≤ (16589779 / 62500000) := by
  have h := checkLog_sound (w := (19 / 144)) (n := 12)
    (lo := (265436463 / 1000000000)) (hi := (16589779 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((163 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(163 / 125) = 1/(125 / 163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9805 : Bounds (265436463 / 1000000000) (16589779 / 62500000) (Real.log (163 / 125)) := by
  have h := reflection_log_9805_neg
  have he : Real.log (163 / 125) = -Real.log (125 / 163) := by
    rw [show ((163 / 125) : ℝ) = ((125 / 163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9806_neg : (181202809 / 500000000) ≤ -Real.log (87 / 125) ∧
    -Real.log (87 / 125) ≤ (362405619 / 1000000000) := by
  have h := checkLog_sound (w := (19 / 106)) (n := 12)
    (lo := (181202809 / 500000000)) (hi := (362405619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 87) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 87) = 1/(87 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9806 : Bounds (-362405619 / 1000000000) (-181202809 / 500000000) (Real.log (87 / 125)) := by
  have h := reflection_log_9806_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9807_neg : (303953 / 1000000000) ≤ -Real.log (62500 / 62519) ∧
    -Real.log (62500 / 62519) ≤ (151977 / 500000000) := by
  have h := checkLog_sound (w := (19 / 125019)) (n := 12)
    (lo := (303953 / 1000000000)) (hi := (151977 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62519 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62519 / 62500) = 1/(62500 / 62519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9807 : Bounds (303953 / 1000000000) (151977 / 500000000) (Real.log (62519 / 62500)) := by
  have h := reflection_log_9807_neg
  have he : Real.log (62519 / 62500) = -Real.log (62500 / 62519) := by
    rw [show ((62519 / 62500) : ℝ) = ((62500 / 62519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9808_neg : (152023 / 500000000) ≤ -Real.log (62481 / 62500) ∧
    -Real.log (62481 / 62500) ≤ (304047 / 1000000000) := by
  have h := checkLog_sound (w := (19 / 124981)) (n := 12)
    (lo := (152023 / 500000000)) (hi := (304047 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 62481) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 62481) = 1/(62481 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9808 : Bounds (-304047 / 1000000000) (-152023 / 500000000) (Real.log (62481 / 62500)) := by
  have h := reflection_log_9808_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9809_neg : (143172641 / 1000000000) ≤ -Real.log (1000000 / 1153929) ∧
    -Real.log (1000000 / 1153929) ≤ (71586321 / 500000000) := by
  have h := checkLog_sound (w := (153929 / 2153929)) (n := 12)
    (lo := (143172641 / 1000000000)) (hi := (71586321 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1153929 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1153929 / 1000000) = 1/(1000000 / 1153929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9809 : Bounds (143172641 / 1000000000) (71586321 / 500000000) (Real.log (1153929 / 1000000)) := by
  have h := reflection_log_9809_neg
  have he : Real.log (1153929 / 1000000) = -Real.log (1000000 / 1153929) := by
    rw [show ((1153929 / 1000000) : ℝ) = ((1000000 / 1153929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9810_neg : (83575999 / 500000000) ≤ -Real.log (846071 / 1000000) ∧
    -Real.log (846071 / 1000000) ≤ (167151999 / 1000000000) := by
  have h := checkLog_sound (w := (153929 / 1846071)) (n := 12)
    (lo := (83575999 / 500000000)) (hi := (167151999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 846071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 846071) = 1/(846071 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9810 : Bounds (-167151999 / 1000000000) (-83575999 / 500000000) (Real.log (846071 / 1000000)) := by
  have h := reflection_log_9810_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9811_neg : (71943667 / 500000000) ≤ -Real.log (500000 / 577377) ∧
    -Real.log (500000 / 577377) ≤ (28777467 / 200000000) := by
  have h := checkLog_sound (w := (77377 / 1077377)) (n := 12)
    (lo := (71943667 / 500000000)) (hi := (28777467 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((577377 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(577377 / 500000) = 1/(500000 / 577377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9811 : Bounds (71943667 / 500000000) (28777467 / 200000000) (Real.log (577377 / 500000)) := by
  have h := reflection_log_9811_neg
  have he : Real.log (577377 / 500000) = -Real.log (500000 / 577377) := by
    rw [show ((577377 / 500000) : ℝ) = ((500000 / 577377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9812_neg : (168127569 / 1000000000) ≤ -Real.log (422623 / 500000) ∧
    -Real.log (422623 / 500000) ≤ (16812757 / 100000000) := by
  have h := checkLog_sound (w := (77377 / 922623)) (n := 12)
    (lo := (168127569 / 1000000000)) (hi := (16812757 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 422623) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 422623) = 1/(422623 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9812 : Bounds (-16812757 / 100000000) (-168127569 / 1000000000) (Real.log (422623 / 500000)) := by
  have h := reflection_log_9812_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9813_neg : (4848047 / 200000000) ≤ -Real.log (244012799871 / 250000000000) ∧
    -Real.log (244012799871 / 250000000000) ≤ (6060059 / 250000000) := by
  have h := checkLog_sound (w := (5987200129 / 494012799871)) (n := 12)
    (lo := (4848047 / 200000000)) (hi := (6060059 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244012799871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244012799871) = 1/(244012799871 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9813 : Bounds (-6060059 / 250000000) (-4848047 / 200000000) (Real.log (244012799871 / 250000000000)) := by
  have h := reflection_log_9813_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9814_neg : (23979357 / 1000000000) ≤ -Real.log (976305862959 / 1000000000000) ∧
    -Real.log (976305862959 / 1000000000000) ≤ (11989679 / 500000000) := by
  have h := checkLog_sound (w := (23694137041 / 1976305862959)) (n := 12)
    (lo := (23979357 / 1000000000)) (hi := (11989679 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 976305862959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 976305862959) = 1/(976305862959 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9814 : Bounds (-11989679 / 500000000) (-23979357 / 1000000000) (Real.log (976305862959 / 1000000000000)) := by
  have h := reflection_log_9814_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9815_neg : (310324639 / 1000000000) ≤ -Real.log (125000000000 / 170483475973) ∧
    -Real.log (125000000000 / 170483475973) ≤ (1939529 / 6250000) := by
  have h := checkLog_sound (w := (45483475973 / 295483475973)) (n := 12)
    (lo := (310324639 / 1000000000)) (hi := (1939529 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((170483475973 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(170483475973 / 125000000000) = 1/(125000000000 / 170483475973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9815 : Bounds (310324639 / 1000000000) (1939529 / 6250000) (Real.log (170483475973 / 125000000000)) := by
  have h := reflection_log_9815_neg
  have he : Real.log (170483475973 / 125000000000) = -Real.log (125000000000 / 170483475973) := by
    rw [show ((170483475973 / 125000000000) : ℝ) = ((125000000000 / 170483475973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9816_neg : (39001863 / 125000000) ≤ -Real.log (250000000000 / 341543763591) ∧
    -Real.log (250000000000 / 341543763591) ≤ (62402981 / 200000000) := by
  have h := checkLog_sound (w := (91543763591 / 591543763591)) (n := 12)
    (lo := (39001863 / 125000000)) (hi := (62402981 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((341543763591 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(341543763591 / 250000000000) = 1/(250000000000 / 341543763591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9816 : Bounds (39001863 / 125000000) (62402981 / 200000000) (Real.log (341543763591 / 250000000000)) := by
  have h := reflection_log_9816_neg
  have he : Real.log (341543763591 / 250000000000) = -Real.log (250000000000 / 341543763591) := by
    rw [show ((341543763591 / 250000000000) : ℝ) = ((250000000000 / 341543763591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9817_neg : (312819583 / 500000000) ≤ -Real.log (100000000000 / 186944045911) ∧
    -Real.log (100000000000 / 186944045911) ≤ (625639167 / 1000000000) := by
  have h := checkLog_sound (w := (86944045911 / 286944045911)) (n := 12)
    (lo := (312819583 / 500000000)) (hi := (625639167 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((186944045911 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(186944045911 / 100000000000) = 1/(100000000000 / 186944045911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9817 : Bounds (312819583 / 500000000) (625639167 / 1000000000) (Real.log (186944045911 / 100000000000)) := by
  have h := reflection_log_9817_neg
  have he : Real.log (186944045911 / 100000000000) = -Real.log (100000000000 / 186944045911) := by
    rw [show ((186944045911 / 100000000000) : ℝ) = ((100000000000 / 186944045911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9818_neg : (313921041 / 500000000) ≤ -Real.log (125000000000 / 234195402299) ∧
    -Real.log (125000000000 / 234195402299) ≤ (627842083 / 1000000000) := by
  have h := checkLog_sound (w := (109195402299 / 359195402299)) (n := 12)
    (lo := (313921041 / 500000000)) (hi := (627842083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((234195402299 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(234195402299 / 125000000000) = 1/(125000000000 / 234195402299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9818 : Bounds (313921041 / 500000000) (627842083 / 1000000000) (Real.log (234195402299 / 125000000000)) := by
  have h := reflection_log_9818_neg
  have he : Real.log (234195402299 / 125000000000) = -Real.log (125000000000 / 234195402299) := by
    rw [show ((234195402299 / 125000000000) : ℝ) = ((125000000000 / 234195402299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9819_neg : (1663769 / 6250000) ≤ -Real.log (200 / 261) ∧
    -Real.log (200 / 261) ≤ (266203041 / 1000000000) := by
  have h := checkLog_sound (w := (61 / 461)) (n := 12)
    (lo := (1663769 / 6250000)) (hi := (266203041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((261 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(261 / 200) = 1/(200 / 261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9819 : Bounds (1663769 / 6250000) (266203041 / 1000000000) (Real.log (261 / 200)) := by
  have h := reflection_log_9819_neg
  have he : Real.log (261 / 200) = -Real.log (200 / 261) := by
    rw [show ((261 / 200) : ℝ) = ((200 / 261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9820_neg : (363843433 / 1000000000) ≤ -Real.log (139 / 200) ∧
    -Real.log (139 / 200) ≤ (181921717 / 500000000) := by
  have h := checkLog_sound (w := (61 / 339)) (n := 12)
    (lo := (363843433 / 1000000000)) (hi := (181921717 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 139) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 139) = 1/(139 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9820 : Bounds (-181921717 / 500000000) (-363843433 / 1000000000) (Real.log (139 / 200)) := by
  have h := reflection_log_9820_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9821_neg : (304953 / 1000000000) ≤ -Real.log (200000 / 200061) ∧
    -Real.log (200000 / 200061) ≤ (152477 / 500000000) := by
  have h := checkLog_sound (w := (61 / 400061)) (n := 12)
    (lo := (304953 / 1000000000)) (hi := (152477 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200061 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200061 / 200000) = 1/(200000 / 200061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9821 : Bounds (304953 / 1000000000) (152477 / 500000000) (Real.log (200061 / 200000)) := by
  have h := reflection_log_9821_neg
  have he : Real.log (200061 / 200000) = -Real.log (200000 / 200061) := by
    rw [show ((200061 / 200000) : ℝ) = ((200000 / 200061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9822_neg : (152523 / 500000000) ≤ -Real.log (199939 / 200000) ∧
    -Real.log (199939 / 200000) ≤ (305047 / 1000000000) := by
  have h := checkLog_sound (w := (61 / 399939)) (n := 12)
    (lo := (152523 / 500000000)) (hi := (305047 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199939) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199939) = 1/(199939 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9822 : Bounds (-305047 / 1000000000) (-152523 / 500000000) (Real.log (199939 / 200000)) := by
  have h := reflection_log_9822_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9823_neg : (143628371 / 1000000000) ≤ -Real.log (200000 / 230891) ∧
    -Real.log (200000 / 230891) ≤ (35907093 / 250000000) := by
  have h := checkLog_sound (w := (30891 / 430891)) (n := 12)
    (lo := (143628371 / 1000000000)) (hi := (35907093 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((230891 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(230891 / 200000) = 1/(200000 / 230891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9823 : Bounds (143628371 / 1000000000) (35907093 / 250000000) (Real.log (230891 / 200000)) := by
  have h := reflection_log_9823_neg
  have he : Real.log (230891 / 200000) = -Real.log (200000 / 230891) := by
    rw [show ((230891 / 200000) : ℝ) = ((200000 / 230891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9824_neg : (167773889 / 1000000000) ≤ -Real.log (169109 / 200000) ∧
    -Real.log (169109 / 200000) ≤ (16777389 / 100000000) := by
  have h := checkLog_sound (w := (30891 / 369109)) (n := 12)
    (lo := (167773889 / 1000000000)) (hi := (16777389 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 169109) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 169109) = 1/(169109 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9824 : Bounds (-16777389 / 100000000) (-167773889 / 1000000000) (Real.log (169109 / 200000)) := by
  have h := reflection_log_9824_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9825_neg : (36085901 / 250000000) ≤ -Real.log (1000000 / 1155281) ∧
    -Real.log (1000000 / 1155281) ≤ (28868721 / 200000000) := by
  have h := checkLog_sound (w := (155281 / 2155281)) (n := 12)
    (lo := (36085901 / 250000000)) (hi := (28868721 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1155281 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1155281 / 1000000) = 1/(1000000 / 1155281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9825 : Bounds (36085901 / 250000000) (28868721 / 200000000) (Real.log (1155281 / 1000000)) := by
  have h := reflection_log_9825_neg
  have he : Real.log (1155281 / 1000000) = -Real.log (1000000 / 1155281) := by
    rw [show ((1155281 / 1000000) : ℝ) = ((1000000 / 1155281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9826_neg : (168751251 / 1000000000) ≤ -Real.log (844719 / 1000000) ∧
    -Real.log (844719 / 1000000) ≤ (42187813 / 250000000) := by
  have h := checkLog_sound (w := (155281 / 1844719)) (n := 12)
    (lo := (168751251 / 1000000000)) (hi := (42187813 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 844719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 844719) = 1/(844719 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9826 : Bounds (-42187813 / 250000000) (-168751251 / 1000000000) (Real.log (844719 / 1000000)) := by
  have h := reflection_log_9826_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9827_neg : (12203823 / 500000000) ≤ -Real.log (975887811039 / 1000000000000) ∧
    -Real.log (975887811039 / 1000000000000) ≤ (24407647 / 1000000000) := by
  have h := checkLog_sound (w := (24112188961 / 1975887811039)) (n := 12)
    (lo := (12203823 / 500000000)) (hi := (24407647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 975887811039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 975887811039) = 1/(975887811039 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9827 : Bounds (-24407647 / 1000000000) (-12203823 / 500000000) (Real.log (975887811039 / 1000000000000)) := by
  have h := reflection_log_9827_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9828_neg : (24145517 / 1000000000) ≤ -Real.log (39045746119 / 40000000000) ∧
    -Real.log (39045746119 / 40000000000) ≤ (12072759 / 500000000) := by
  have h := checkLog_sound (w := (954253881 / 79045746119)) (n := 12)
    (lo := (24145517 / 1000000000)) (hi := (12072759 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39045746119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39045746119) = 1/(39045746119 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9828 : Bounds (-12072759 / 500000000) (-24145517 / 1000000000) (Real.log (39045746119 / 40000000000)) := by
  have h := reflection_log_9828_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9829_neg : (15570113 / 50000000) ≤ -Real.log (12500000000 / 17066729151) ∧
    -Real.log (12500000000 / 17066729151) ≤ (311402261 / 1000000000) := by
  have h := checkLog_sound (w := (4566729151 / 29566729151)) (n := 12)
    (lo := (15570113 / 50000000)) (hi := (311402261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17066729151 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(17066729151 / 12500000000) = 1/(12500000000 / 17066729151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9829 : Bounds (15570113 / 50000000) (311402261 / 1000000000) (Real.log (17066729151 / 12500000000)) := by
  have h := reflection_log_9829_neg
  have he : Real.log (17066729151 / 12500000000) = -Real.log (12500000000 / 17066729151) := by
    rw [show ((17066729151 / 12500000000) : ℝ) = ((12500000000 / 17066729151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9830_neg : (62618971 / 200000000) ≤ -Real.log (500000000000 / 683825627221) ∧
    -Real.log (500000000000 / 683825627221) ≤ (39136857 / 125000000) := by
  have h := checkLog_sound (w := (183825627221 / 1183825627221)) (n := 12)
    (lo := (62618971 / 200000000)) (hi := (39136857 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((683825627221 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(683825627221 / 500000000000) = 1/(500000000000 / 683825627221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9830 : Bounds (62618971 / 200000000) (39136857 / 125000000) (Real.log (683825627221 / 500000000000)) := by
  have h := reflection_log_9830_neg
  have he : Real.log (683825627221 / 500000000000) = -Real.log (500000000000 / 683825627221) := by
    rw [show ((683825627221 / 500000000000) : ℝ) = ((500000000000 / 683825627221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9831_neg : (313921041 / 500000000) ≤ -Real.log (100000000000 / 187356321839) ∧
    -Real.log (100000000000 / 187356321839) ≤ (627842083 / 1000000000) := by
  have h := checkLog_sound (w := (87356321839 / 287356321839)) (n := 12)
    (lo := (313921041 / 500000000)) (hi := (627842083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((187356321839 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(187356321839 / 100000000000) = 1/(100000000000 / 187356321839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9831 : Bounds (313921041 / 500000000) (627842083 / 1000000000) (Real.log (187356321839 / 100000000000)) := by
  have h := reflection_log_9831_neg
  have he : Real.log (187356321839 / 100000000000) = -Real.log (100000000000 / 187356321839) := by
    rw [show ((187356321839 / 100000000000) : ℝ) = ((100000000000 / 187356321839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9832_neg : (315023237 / 500000000) ≤ -Real.log (15625000000 / 29339028777) ∧
    -Real.log (15625000000 / 29339028777) ≤ (25201859 / 40000000) := by
  have h := checkLog_sound (w := (13714028777 / 44964028777)) (n := 12)
    (lo := (315023237 / 500000000)) (hi := (25201859 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29339028777 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29339028777 / 15625000000) = 1/(15625000000 / 29339028777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9832 : Bounds (315023237 / 500000000) (25201859 / 40000000) (Real.log (29339028777 / 15625000000)) := by
  have h := reflection_log_9832_neg
  have he : Real.log (29339028777 / 15625000000) = -Real.log (15625000000 / 29339028777) := by
    rw [show ((29339028777 / 15625000000) : ℝ) = ((15625000000 / 29339028777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9833_neg : (26696903 / 100000000) ≤ -Real.log (500 / 653) ∧
    -Real.log (500 / 653) ≤ (266969031 / 1000000000) := by
  have h := checkLog_sound (w := (153 / 1153)) (n := 12)
    (lo := (26696903 / 100000000)) (hi := (266969031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((653 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(653 / 500) = 1/(500 / 653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9833 : Bounds (26696903 / 100000000) (266969031 / 1000000000) (Real.log (653 / 500)) := by
  have h := reflection_log_9833_neg
  have he : Real.log (653 / 500) = -Real.log (500 / 653) := by
    rw [show ((653 / 500) : ℝ) = ((500 / 653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9834_neg : (182641659 / 500000000) ≤ -Real.log (347 / 500) ∧
    -Real.log (347 / 500) ≤ (365283319 / 1000000000) := by
  have h := checkLog_sound (w := (153 / 847)) (n := 12)
    (lo := (182641659 / 500000000)) (hi := (365283319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 347) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 347) = 1/(347 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9834 : Bounds (-365283319 / 1000000000) (-182641659 / 500000000) (Real.log (347 / 500)) := by
  have h := reflection_log_9834_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9835_neg : (305953 / 1000000000) ≤ -Real.log (500000 / 500153) ∧
    -Real.log (500000 / 500153) ≤ (152977 / 500000000) := by
  have h := checkLog_sound (w := (153 / 1000153)) (n := 12)
    (lo := (305953 / 1000000000)) (hi := (152977 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500153 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500153 / 500000) = 1/(500000 / 500153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9835 : Bounds (305953 / 1000000000) (152977 / 500000000) (Real.log (500153 / 500000)) := by
  have h := reflection_log_9835_neg
  have he : Real.log (500153 / 500000) = -Real.log (500000 / 500153) := by
    rw [show ((500153 / 500000) : ℝ) = ((500000 / 500153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9836_neg : (153023 / 500000000) ≤ -Real.log (499847 / 500000) ∧
    -Real.log (499847 / 500000) ≤ (306047 / 1000000000) := by
  have h := checkLog_sound (w := (153 / 999847)) (n := 12)
    (lo := (153023 / 500000000)) (hi := (306047 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499847) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499847) = 1/(499847 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9836 : Bounds (-306047 / 1000000000) (-153023 / 500000000) (Real.log (499847 / 500000)) := by
  have h := reflection_log_9836_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9837_neg : (144083027 / 1000000000) ≤ -Real.log (50000 / 57749) ∧
    -Real.log (50000 / 57749) ≤ (36020757 / 250000000) := by
  have h := checkLog_sound (w := (7749 / 107749)) (n := 12)
    (lo := (144083027 / 1000000000)) (hi := (36020757 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((57749 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(57749 / 50000) = 1/(50000 / 57749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9837 : Bounds (144083027 / 1000000000) (36020757 / 250000000) (Real.log (57749 / 50000)) := by
  have h := reflection_log_9837_neg
  have he : Real.log (57749 / 50000) = -Real.log (50000 / 57749) := by
    rw [show ((57749 / 50000) : ℝ) = ((50000 / 57749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9838_neg : (168394983 / 1000000000) ≤ -Real.log (42251 / 50000) ∧
    -Real.log (42251 / 50000) ≤ (21049373 / 125000000) := by
  have h := checkLog_sound (w := (7749 / 92251)) (n := 12)
    (lo := (168394983 / 1000000000)) (hi := (21049373 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 42251) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 42251) = 1/(42251 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9838 : Bounds (-21049373 / 125000000) (-168394983 / 1000000000) (Real.log (42251 / 50000)) := by
  have h := reflection_log_9838_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9839_neg : (72399833 / 500000000) ≤ -Real.log (31250 / 36119) ∧
    -Real.log (31250 / 36119) ≤ (144799667 / 1000000000) := by
  have h := checkLog_sound (w := (4869 / 67369)) (n := 12)
    (lo := (72399833 / 500000000)) (hi := (144799667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36119 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36119 / 31250) = 1/(31250 / 36119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9839 : Bounds (72399833 / 500000000) (144799667 / 1000000000) (Real.log (36119 / 31250)) := by
  have h := reflection_log_9839_neg
  have he : Real.log (36119 / 31250) = -Real.log (31250 / 36119) := by
    rw [show ((36119 / 31250) : ℝ) = ((31250 / 36119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9840_neg : (84687661 / 500000000) ≤ -Real.log (26381 / 31250) ∧
    -Real.log (26381 / 31250) ≤ (169375323 / 1000000000) := by
  have h := checkLog_sound (w := (4869 / 57631)) (n := 12)
    (lo := (84687661 / 500000000)) (hi := (169375323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 26381) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 26381) = 1/(26381 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9840 : Bounds (-169375323 / 1000000000) (-84687661 / 500000000) (Real.log (26381 / 31250)) := by
  have h := reflection_log_9840_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9841_neg : (4915131 / 200000000) ≤ -Real.log (952855339 / 976562500) ∧
    -Real.log (952855339 / 976562500) ≤ (3071957 / 125000000) := by
  have h := checkLog_sound (w := (23707161 / 1929417839)) (n := 12)
    (lo := (4915131 / 200000000)) (hi := (3071957 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 952855339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 952855339) = 1/(952855339 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9841 : Bounds (-3071957 / 125000000) (-4915131 / 200000000) (Real.log (952855339 / 976562500)) := by
  have h := reflection_log_9841_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9842_neg : (4862391 / 200000000) ≤ -Real.log (2439952999 / 2500000000) ∧
    -Real.log (2439952999 / 2500000000) ≤ (6077989 / 250000000) := by
  have h := checkLog_sound (w := (60047001 / 4939952999)) (n := 12)
    (lo := (4862391 / 200000000)) (hi := (6077989 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2439952999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2439952999) = 1/(2439952999 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9842 : Bounds (-6077989 / 250000000) (-4862391 / 200000000) (Real.log (2439952999 / 2500000000)) := by
  have h := reflection_log_9842_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9843_neg : (312478011 / 1000000000) ≤ -Real.log (500000000000 / 683403943101) ∧
    -Real.log (500000000000 / 683403943101) ≤ (78119503 / 250000000) := by
  have h := checkLog_sound (w := (183403943101 / 1183403943101)) (n := 12)
    (lo := (312478011 / 1000000000)) (hi := (78119503 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((683403943101 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(683403943101 / 500000000000) = 1/(500000000000 / 683403943101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9843 : Bounds (312478011 / 1000000000) (78119503 / 250000000) (Real.log (683403943101 / 500000000000)) := by
  have h := reflection_log_9843_neg
  have he : Real.log (683403943101 / 500000000000) = -Real.log (500000000000 / 683403943101) := by
    rw [show ((683403943101 / 500000000000) : ℝ) = ((500000000000 / 683403943101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9844_neg : (78543747 / 250000000) ≤ -Real.log (500000000000 / 684564648801) ∧
    -Real.log (500000000000 / 684564648801) ≤ (314174989 / 1000000000) := by
  have h := checkLog_sound (w := (184564648801 / 1184564648801)) (n := 12)
    (lo := (78543747 / 250000000)) (hi := (314174989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((684564648801 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(684564648801 / 500000000000) = 1/(500000000000 / 684564648801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9844 : Bounds (78543747 / 250000000) (314174989 / 1000000000) (Real.log (684564648801 / 500000000000)) := by
  have h := reflection_log_9844_neg
  have he : Real.log (684564648801 / 500000000000) = -Real.log (500000000000 / 684564648801) := by
    rw [show ((684564648801 / 500000000000) : ℝ) = ((500000000000 / 684564648801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9845_neg : (315023237 / 500000000) ≤ -Real.log (500000000000 / 938848920863) ∧
    -Real.log (500000000000 / 938848920863) ≤ (25201859 / 40000000) := by
  have h := checkLog_sound (w := (438848920863 / 1438848920863)) (n := 12)
    (lo := (315023237 / 500000000)) (hi := (25201859 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((938848920863 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(938848920863 / 500000000000) = 1/(500000000000 / 938848920863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9845 : Bounds (315023237 / 500000000) (25201859 / 40000000) (Real.log (938848920863 / 500000000000)) := by
  have h := reflection_log_9845_neg
  have he : Real.log (938848920863 / 500000000000) = -Real.log (500000000000 / 938848920863) := by
    rw [show ((938848920863 / 500000000000) : ℝ) = ((500000000000 / 938848920863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9846_neg : (632252349 / 1000000000) ≤ -Real.log (250000000000 / 470461095101) ∧
    -Real.log (250000000000 / 470461095101) ≤ (12645047 / 20000000) := by
  have h := checkLog_sound (w := (220461095101 / 720461095101)) (n := 12)
    (lo := (632252349 / 1000000000)) (hi := (12645047 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((470461095101 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(470461095101 / 250000000000) = 1/(250000000000 / 470461095101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9846 : Bounds (632252349 / 1000000000) (12645047 / 20000000) (Real.log (470461095101 / 250000000000)) := by
  have h := reflection_log_9846_neg
  have he : Real.log (470461095101 / 250000000000) = -Real.log (250000000000 / 470461095101) := by
    rw [show ((470461095101 / 250000000000) : ℝ) = ((250000000000 / 470461095101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9847_neg : (133867217 / 500000000) ≤ -Real.log (1000 / 1307) ∧
    -Real.log (1000 / 1307) ≤ (53546887 / 200000000) := by
  have h := checkLog_sound (w := (307 / 2307)) (n := 12)
    (lo := (133867217 / 500000000)) (hi := (53546887 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1307 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1307 / 1000) = 1/(1000 / 1307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9847 : Bounds (133867217 / 500000000) (53546887 / 200000000) (Real.log (1307 / 1000)) := by
  have h := reflection_log_9847_neg
  have he : Real.log (1307 / 1000) = -Real.log (1000 / 1307) := by
    rw [show ((1307 / 1000) : ℝ) = ((1000 / 1307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9848_neg : (366725279 / 1000000000) ≤ -Real.log (693 / 1000) ∧
    -Real.log (693 / 1000) ≤ (2292033 / 6250000) := by
  have h := checkLog_sound (w := (307 / 1693)) (n := 12)
    (lo := (366725279 / 1000000000)) (hi := (2292033 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 693) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 693) = 1/(693 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9848 : Bounds (-2292033 / 6250000) (-366725279 / 1000000000) (Real.log (693 / 1000)) := by
  have h := reflection_log_9848_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9849_neg : (38369 / 125000000) ≤ -Real.log (1000000 / 1000307) ∧
    -Real.log (1000000 / 1000307) ≤ (306953 / 1000000000) := by
  have h := checkLog_sound (w := (307 / 2000307)) (n := 12)
    (lo := (38369 / 125000000)) (hi := (306953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000307 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000307 / 1000000) = 1/(1000000 / 1000307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9849 : Bounds (38369 / 125000000) (306953 / 1000000000) (Real.log (1000307 / 1000000)) := by
  have h := reflection_log_9849_neg
  have he : Real.log (1000307 / 1000000) = -Real.log (1000000 / 1000307) := by
    rw [show ((1000307 / 1000000) : ℝ) = ((1000000 / 1000307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9850_neg : (307047 / 1000000000) ≤ -Real.log (999693 / 1000000) ∧
    -Real.log (999693 / 1000000) ≤ (38381 / 125000000) := by
  have h := checkLog_sound (w := (307 / 1999693)) (n := 12)
    (lo := (307047 / 1000000000)) (hi := (38381 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999693) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999693) = 1/(999693 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9850 : Bounds (-38381 / 125000000) (-307047 / 1000000000) (Real.log (999693 / 1000000)) := by
  have h := reflection_log_9850_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9851_neg : (144538343 / 1000000000) ≤ -Real.log (500000 / 577753) ∧
    -Real.log (500000 / 577753) ≤ (18067293 / 125000000) := by
  have h := checkLog_sound (w := (77753 / 1077753)) (n := 12)
    (lo := (144538343 / 1000000000)) (hi := (18067293 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((577753 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(577753 / 500000) = 1/(500000 / 577753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9851 : Bounds (144538343 / 1000000000) (18067293 / 125000000) (Real.log (577753 / 500000)) := by
  have h := reflection_log_9851_neg
  have he : Real.log (577753 / 500000) = -Real.log (500000 / 577753) := by
    rw [show ((577753 / 500000) : ℝ) = ((500000 / 577753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9852_neg : (169017647 / 1000000000) ≤ -Real.log (422247 / 500000) ∧
    -Real.log (422247 / 500000) ≤ (10563603 / 62500000) := by
  have h := checkLog_sound (w := (77753 / 922247)) (n := 12)
    (lo := (169017647 / 1000000000)) (hi := (10563603 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 422247) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 422247) = 1/(422247 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9852 : Bounds (-10563603 / 62500000) (-169017647 / 1000000000) (Real.log (422247 / 500000)) := by
  have h := reflection_log_9852_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9853_neg : (907847 / 6250000) ≤ -Real.log (200000 / 231267) ∧
    -Real.log (200000 / 231267) ≤ (145255521 / 1000000000) := by
  have h := checkLog_sound (w := (31267 / 431267)) (n := 12)
    (lo := (907847 / 6250000)) (hi := (145255521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((231267 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(231267 / 200000) = 1/(200000 / 231267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9853 : Bounds (907847 / 6250000) (145255521 / 1000000000) (Real.log (231267 / 200000)) := by
  have h := reflection_log_9853_neg
  have he : Real.log (231267 / 200000) = -Real.log (200000 / 231267) := by
    rw [show ((231267 / 200000) : ℝ) = ((200000 / 231267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9854_neg : (84999891 / 500000000) ≤ -Real.log (168733 / 200000) ∧
    -Real.log (168733 / 200000) ≤ (169999783 / 1000000000) := by
  have h := checkLog_sound (w := (31267 / 368733)) (n := 12)
    (lo := (84999891 / 500000000)) (hi := (169999783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 168733) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 168733) = 1/(168733 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9854 : Bounds (-169999783 / 1000000000) (-84999891 / 500000000) (Real.log (168733 / 200000)) := by
  have h := reflection_log_9854_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9855_neg : (24744261 / 1000000000) ≤ -Real.log (39022374711 / 40000000000) ∧
    -Real.log (39022374711 / 40000000000) ≤ (12372131 / 500000000) := by
  have h := checkLog_sound (w := (977625289 / 79022374711)) (n := 12)
    (lo := (24744261 / 1000000000)) (hi := (12372131 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39022374711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39022374711) = 1/(39022374711 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9855 : Bounds (-12372131 / 500000000) (-24744261 / 1000000000) (Real.log (39022374711 / 40000000000)) := by
  have h := reflection_log_9855_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end


