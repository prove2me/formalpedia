-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Cell0046__4_q00
-- name    : CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Cell0046__4_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T12:46:13.436767+00:00
-- url     : https://prove2.me/theorems/3f92ecac-c4f3-4e9c-a227-8eb00c60eb33
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0046 (+3 modules: GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0047, GeneralCK.Cert…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0046 (+3 modules: GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0047, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0048, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0049) (piece 1 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0046 (+3 modules: GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0047, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0048, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0049) (piece 1 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0046 (+3 modules: GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0047, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0048, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0049) (piece 1 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointNextBandFamily/Cell0046 (+3 modules: GeneralCK/Certificates/Generated/MidpointNextBandFamily/Cell0047, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Cell0048, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Cell0049) (piece 1 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_DyadicFastLog
import Definitions.Def_CK_GeneralCK_Certificates_BivariateProvedProgram
import Definitions.Def_CK_GeneralCK_Certificates_ReflectionMidpointKernel
import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers
import Definitions.Def_CK_GeneralCK_ReflectionSmallRatioMidpointJet

-- ===== source module GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0046 =====
section

namespace GeneralCK.Certificates.ReflectionMidpointNextBandFamily.Endpoints0046
open GeneralCK.Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

noncomputable def lift40 (a : DyadicInterval 40) : DyadicInterval 64 :=
  ⟨a.lo*16777216, a.hi*16777216⟩

theorem lift40_contains {a : DyadicInterval 40} {x : ℝ} :
    (lift40 a).Contains x ↔ a.Contains x := by
  simp only [DyadicInterval.Contains, lift40, Int.cast_mul, Int.cast_ofNat]
  norm_num [DyadicInterval.scale]
  constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]

theorem direct {z : ℤ} {e n : ℕ} {a : DyadicInterval 40}
    (hc : DyadicFastLog.check z 1099511627776 e n (lift40 a)=true) :
    a.Contains (Real.log ((z:ℝ)/1099511627776)) := by
  apply lift40_contains.mp
  simpa only [Int.cast_ofNat] using DyadicFastLog.check_sound hc

theorem reciprocal {z : ℤ} {e n : ℕ} {a : DyadicInterval 40}
    (hc : DyadicFastLog.check 1099511627776 z e n (lift40 a.neg)=true) :
    a.Contains (Real.log ((z:ℝ)/1099511627776)) := by
  have h := lift40_contains.mp (DyadicFastLog.check_sound hc)
  have hn := DyadicInterval.neg_sound h
  rw [← Real.log_inv, inv_div] at hn
  simpa only [DyadicInterval.neg, neg_neg, Int.cast_ofNat] using hn

noncomputable def sharedTwo : DyadicInterval 64 := ⟨12786308645202655420,12786308645202662926⟩
theorem sharedTwo_eq : DyadicLogSeries.enclosure (DyadicFastLog.fraction 64 1 3) 16=sharedTwo := by rfl
noncomputable def out_w0 : DyadicInterval 40 := ⟨762123383616,762123402880⟩
theorem checked_w0 : DyadicFastLog.check 1099511627776 2199023255552 1 16 (lift40 out_w0.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w0 : out_w0.Contains (Real.log ((2199023255552:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w0
#print axioms endpoint_w0
noncomputable def out_w1 : DyadicInterval 40 := ⟨82211919296,82211919360⟩
theorem checked_w1 : DyadicFastLog.check 1099511627776 1184875151360 0 16 (lift40 out_w1.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w1 : out_w1.Contains (Real.log ((1184875151360:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w1
#print axioms endpoint_w1
noncomputable def out_w2 : DyadicInterval 40 := ⟨-88859399040,-88859398976⟩
theorem checked_w2 : DyadicFastLog.check 1014148104192 1099511627776 0 16 (lift40 out_w2)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w2 : out_w2.Contains (Real.log ((1014148104192:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w2
#print axioms endpoint_w2
noncomputable def out_w3 : DyadicInterval 40 := ⟨82268353728,82268353792⟩
theorem checked_w3 : DyadicFastLog.check 1099511627776 1184935968768 0 16 (lift40 out_w3.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w3 : out_w3.Contains (Real.log ((1184935968768:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w3
#print axioms endpoint_w3
noncomputable def out_w4 : DyadicInterval 40 := ⟨-88925337600,-88925337536⟩
theorem checked_w4 : DyadicFastLog.check 1014087286784 1099511627776 0 16 (lift40 out_w4)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w4 : out_w4.Contains (Real.log ((1014087286784:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w4
#print axioms endpoint_w4
noncomputable def out_w5 : DyadicInterval 40 := ⟨-6656983808,-6656983744⟩
theorem checked_w5 : DyadicFastLog.check 1092874755687 1099511627776 0 16 (lift40 out_w5)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w5 : out_w5.Contains (Real.log ((1092874755687:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w5
#print axioms endpoint_w5
noncomputable def out_w6 : DyadicInterval 40 := ⟨-6647479680,-6647479616⟩
theorem checked_w6 : DyadicFastLog.check 1092884202495 1099511627776 0 16 (lift40 out_w6)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w6 : out_w6.Contains (Real.log ((1092884202495:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w6
#print axioms endpoint_w6
noncomputable def out_w7 : DyadicInterval 40 := ⟨342717064576,342717064640⟩
theorem checked_w7 : DyadicFastLog.check 1099511627776 1501651437696 0 16 (lift40 out_w7.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w7 : out_w7.Contains (Real.log ((1501651437696:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w7
#print axioms endpoint_w7
noncomputable def out_w8 : DyadicInterval 40 := ⟨342942355136,342942355200⟩
theorem checked_w8 : DyadicFastLog.check 1099511627776 1501959158398 0 16 (lift40 out_w8.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w8 : out_w8.Contains (Real.log ((1501959158398:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w8
#print axioms endpoint_w8
noncomputable def out_w9 : DyadicInterval 40 := ⟨171071318336,171071318400⟩
theorem checked_w9 : DyadicFastLog.check 1099511627776 1284609221274 0 16 (lift40 out_w9.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w9 : out_w9.Contains (Real.log ((1284609221274:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w9
#print axioms endpoint_w9
noncomputable def out_w10 : DyadicInterval 40 := ⟨171193691264,171193691328⟩
theorem checked_w10 : DyadicFastLog.check 1099511627776 1284752203100 0 16 (lift40 out_w10.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w10 : out_w10.Contains (Real.log ((1284752203100:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w10
#print axioms endpoint_w10
noncomputable def out_w11 : DyadicInterval 40 := ⟨75504827712,75504827776⟩
theorem checked_w11 : DyadicFastLog.check 1099511627776 1177669337088 0 16 (lift40 out_w11.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w11 : out_w11.Contains (Real.log ((1177669337088:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w11
#print axioms endpoint_w11
noncomputable def out_w12 : DyadicInterval 40 := ⟨-81074676096,-81074676032⟩
theorem checked_w12 : DyadicFastLog.check 1021353918464 1099511627776 0 16 (lift40 out_w12)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w12 : out_w12.Contains (Real.log ((1021353918464:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w12
#print axioms endpoint_w12
noncomputable def out_w13 : DyadicInterval 40 := ⟨88919931840,88919931904⟩
theorem checked_w13 : DyadicFastLog.check 1099511627776 1192126054400 0 16 (lift40 out_w13.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w13 : out_w13.Contains (Real.log ((1192126054400:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w13
#print axioms endpoint_w13
noncomputable def out_w14 : DyadicInterval 40 := ⟨-96748867328,-96748867264⟩
theorem checked_w14 : DyadicFastLog.check 1006897201152 1099511627776 0 16 (lift40 out_w14)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w14 : out_w14.Contains (Real.log ((1006897201152:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w14
#print axioms endpoint_w14
noncomputable def out_w15 : DyadicInterval 40 := ⟨-7828935424,-7828935360⟩
theorem checked_w15 : DyadicFastLog.check 1091710498800 1099511627776 0 16 (lift40 out_w15)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w15 : out_w15.Contains (Real.log ((1091710498800:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w15
#print axioms endpoint_w15
noncomputable def out_w16 : DyadicInterval 40 := ⟨-5569848320,-5569848256⟩
theorem checked_w16 : DyadicFastLog.check 1093955863407 1099511627776 0 16 (lift40 out_w16)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w16 : out_w16.Contains (Real.log ((1093955863407:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w16
#print axioms endpoint_w16
noncomputable def out_w17 : DyadicInterval 40 := ⟨156579503744,156579503808⟩
theorem checked_w17 : DyadicFastLog.check 1099511627776 1267788869650 0 16 (lift40 out_w17.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w17 : out_w17.Contains (Real.log ((1267788869650:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w17
#print axioms endpoint_w17
noncomputable def out_w18 : DyadicInterval 40 := ⟨185668799104,185668799168⟩
theorem checked_w18 : DyadicFastLog.check 1099511627776 1301777835006 0 16 (lift40 out_w18.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w18 : out_w18.Contains (Real.log ((1301777835006:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w18
#print axioms endpoint_w18
end GeneralCK.Certificates.ReflectionMidpointNextBandFamily.Endpoints0046

namespace GeneralCK.Certificates.ReflectionMidpointNextBandFamily.Cell0046
open Set GeneralCK.Certificates.ReflectionMidpointNextBandFamily.Endpoints0046
open BivariateJetProgram (RegistersContain RegistersSound zeroBox zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
theorem lc0 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc1 : ProvedTranscendental.LogEncloses (⟨1184875151360,1184875151360⟩ : DyadicInterval 40) (⟨82211919296,82211919360⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w1
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w1
theorem lc2 : ProvedTranscendental.LogEncloses (⟨1014148104192,1014148104192⟩ : DyadicInterval 40) (⟨-88859399040,-88859398976⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w2
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w2
theorem lc3 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc4 : ProvedTranscendental.LogEncloses (⟨1184935968768,1184935968768⟩ : DyadicInterval 40) (⟨82268353728,82268353792⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w3
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w3
theorem lc5 : ProvedTranscendental.LogEncloses (⟨1014087286784,1014087286784⟩ : DyadicInterval 40) (⟨-88925337600,-88925337536⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w4
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w4
theorem lc6 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc7 : ProvedTranscendental.LogEncloses (⟨1092874755687,1092884202495⟩ : DyadicInterval 40) (⟨-6656983808,-6647479616⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w5
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w6
theorem lc8 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc9 : ProvedTranscendental.LogEncloses (⟨1184875151360,1184935968768⟩ : DyadicInterval 40) (⟨82211919296,82268353792⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w1
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w3
theorem lc10 : ProvedTranscendental.LogEncloses (⟨1014087286784,1014148104192⟩ : DyadicInterval 40) (⟨-88925337600,-88859398976⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w4
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w2
theorem lc11 : ProvedTranscendental.LogEncloses (⟨1092874755687,1092884202495⟩ : DyadicInterval 40) (⟨-6656983808,-6647479616⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w5
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w6
theorem lc12 : ProvedTranscendental.LogEncloses (⟨1501651437696,1501959158398⟩ : DyadicInterval 40) (⟨342717064576,342942355200⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w7
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
theorem lc13 : ProvedTranscendental.LogEncloses (⟨1284609221274,1284752203100⟩ : DyadicInterval 40) (⟨171071318336,171193691328⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w9
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w10
theorem lc14 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc15 : ProvedTranscendental.LogEncloses (⟨1177669337088,1177669337088⟩ : DyadicInterval 40) (⟨75504827712,75504827776⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w11
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w11
theorem lc16 : ProvedTranscendental.LogEncloses (⟨1021353918464,1021353918464⟩ : DyadicInterval 40) (⟨-81074676096,-81074676032⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w12
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w12
theorem lc17 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc18 : ProvedTranscendental.LogEncloses (⟨1192126054400,1192126054400⟩ : DyadicInterval 40) (⟨88919931840,88919931904⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w13
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w13
theorem lc19 : ProvedTranscendental.LogEncloses (⟨1006897201152,1006897201152⟩ : DyadicInterval 40) (⟨-96748867328,-96748867264⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w14
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w14
theorem lc20 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc21 : ProvedTranscendental.LogEncloses (⟨1091710498800,1093955863407⟩ : DyadicInterval 40) (⟨-7828935424,-5569848256⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w15
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w16
theorem lc22 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc23 : ProvedTranscendental.LogEncloses (⟨1177669337088,1192126054400⟩ : DyadicInterval 40) (⟨75504827712,88919931904⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w11
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w13
theorem lc24 : ProvedTranscendental.LogEncloses (⟨1006897201152,1021353918464⟩ : DyadicInterval 40) (⟨-96748867328,-81074676032⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w14
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w12
theorem lc25 : ProvedTranscendental.LogEncloses (⟨1091710498800,1093955863407⟩ : DyadicInterval 40) (⟨-7828935424,-5569848256⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w15
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w16
theorem lc26 : ProvedTranscendental.LogEncloses (⟨1501651437696,1501959158398⟩ : DyadicInterval 40) (⟨342717064576,342942355200⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w7
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
theorem lc27 : ProvedTranscendental.LogEncloses (⟨1267788869650,1301777835006⟩ : DyadicInterval 40) (⟨156579503744,185668799168⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w17
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w18
theorem ew3_ok (x : ℝ) (hx : (⟨85363523584,85363523584⟩ : DyadicInterval 40).Contains x) : (⟨758806333936,758806353266⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨85363523584,85363523584⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨82211919296,82211919360⟩ : DyadicInterval 40)) (minus:=(⟨-88859399040,-88859398976⟩ : DyadicInterval 40))
    (lc0 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc1 lc2 (by decide) hx
theorem ew6_ok (x : ℝ) (hx : (⟨85424340992,85424340992⟩ : DyadicInterval 40).Contains x) : (⟨758801600995,758801620325⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨85424340992,85424340992⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨82268353728,82268353792⟩ : DyadicInterval 40)) (minus:=(⟨-88925337600,-88925337536⟩ : DyadicInterval 40))
    (lc3 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc4 lc5 (by decide) hx
theorem ew17_ok (x : ℝ) (hx : (⟨78157709312,78157709312⟩ : DyadicInterval 40).Contains x) : (⟨759343157255,759343176585⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨78157709312,78157709312⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨75504827712,75504827776⟩ : DyadicInterval 40)) (minus:=(⟨-81074676096,-81074676032⟩ : DyadicInterval 40))
    (lc14 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc15 lc16 (by decide) hx
theorem ew20_ok (x : ℝ) (hx : (⟨92614426624,92614426624⟩ : DyadicInterval 40).Contains x) : (⟨758218193484,758218212814⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨92614426624,92614426624⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨88919931840,88919931904⟩ : DyadicInterval 40)) (minus:=(⟨-96748867328,-96748867264⟩ : DyadicInterval 40))
    (lc17 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc18 lc19 (by decide) hx
theorem bw9_ok (x : ℝ) (hx : (⟨85363523584,85424340992⟩ : DyadicInterval 40).Contains x) : (⟨765447123424,765451894784⟩ : DyadicInterval 40).Contains (Reflection.biasB x) := by
  exact ProvedTranscendental.denominator_encloses (c:=(⟨85363523584,85424340992⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (gapLog:=(⟨-6656983808,-6647479616⟩ : DyadicInterval 40))
    (lc6 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc7 (by decide) hx
theorem bw23_ok (x : ℝ) (hx : (⟨78157709312,92614426624⟩ : DyadicInterval 40).Contains x) : (⟨764908307744,766037870592⟩ : DyadicInterval 40).Contains (Reflection.biasB x) := by
  exact ProvedTranscendental.denominator_encloses (c:=(⟨78157709312,92614426624⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (gapLog:=(⟨-7828935424,-5569848256⟩ : DyadicInterval 40))
    (lc20 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc21 (by decide) hx
theorem brcenter6_contact (y : ℝ) (hy : (⟨9766916060986,9773397259506⟩ : DyadicInterval 40).Contains y) : (⟨85363523584,85424340992⟩ : DyadicInterval 40).Contains (Reflection.biasContact y) := by
  exact ProvedTranscendental.contact_bracket (Y:=(⟨9766916060986,9773397259506⟩ : DyadicInterval 40)) (c:=(⟨85363523584,85424340992⟩ : DyadicInterval 40)) (elo:=(⟨758806333936,758806353266⟩ : DyadicInterval 40)) (ehi:=(⟨758801600995,758801620325⟩ : DyadicInterval 40))
    (by decide) (by decide) (by decide) (by decide)
    (ew3_ok _ (DyadicContact.point_contains 40 85363523584)) (ew6_ok _ (DyadicContact.point_contains 40 85424340992))
    (by decide) (by decide) hy
theorem brcenter6_jet (y : ℝ) (hy : (⟨9766916060986,9773397259506⟩ : DyadicInterval 40).Contains y) : (⟨⟨85363523584,85424340992⟩,⟨-9533405785,-9519776759⟩,⟨2114018221,2118619488⟩⟩ : DyadicJetEnclosure 40).Contains reflectionContactJet y := by
  exact ProvedTranscendental.contact_jet (c:=(⟨85363523584,85424340992⟩ : DyadicInterval 40)) (B:=(⟨765447123424,765451894784⟩ : DyadicInterval 40)) (by decide) brcenter6_contact bw9_ok (by decide) (by decide) (by decide) hy
theorem brwhole6_contact (y : ℝ) (hy : (⟨9001765954803,10681950338282⟩ : DyadicInterval 40).Contains y) : (⟨78157709312,92614426624⟩ : DyadicInterval 40).Contains (Reflection.biasContact y) := by
  exact ProvedTranscendental.contact_bracket (Y:=(⟨9001765954803,10681950338282⟩ : DyadicInterval 40)) (c:=(⟨78157709312,92614426624⟩ : DyadicInterval 40)) (elo:=(⟨759343157255,759343176585⟩ : DyadicInterval 40)) (ehi:=(⟨758218193484,758218212814⟩ : DyadicInterval 40))
    (by decide) (by decide) (by decide) (by decide)
    (ew17_ok _ (DyadicContact.point_contains 40 78157709312)) (ew20_ok _ (DyadicContact.point_contains 40 92614426624))
    (by decide) (by decide) hy
theorem brwhole6_jet (y : ℝ) (hy : (⟨9001765954803,10681950338282⟩ : DyadicInterval 40).Contains y) : (⟨⟨78157709312,92614426624⟩,⟨-11213673498,-7974315317⟩,⟨1613268899,2709552760⟩⟩ : DyadicJetEnclosure 40).Contains reflectionContactJet y := by
  exact ProvedTranscendental.contact_jet (c:=(⟨78157709312,92614426624⟩ : DyadicInterval 40)) (B:=(⟨764908307744,766037870592⟩ : DyadicInterval 40)) (by decide) brwhole6_contact bw23_ok (by decide) (by decide) (by decide) hy
noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨169984497654,170094448817⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨755470957322,755483608159⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨84992248827,85047224409⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0
theorem centerAccepted0 : StepValid centerStep0.shape centerBoxes0 centerStep0.proposed := by
  dsimp only [StepValid,centerStep0]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep1 : Instruction 40 := ⟨.mul 4 0,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1
theorem centerAccepted1 : StepValid centerStep1.shape centerBoxes1 centerStep1.proposed := by
  dsimp only [StepValid,centerStep1]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep2 : Instruction 40 := ⟨.add 5 0,⟨⟨3298534883328,3298534883328⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2
theorem centerAccepted2 : StepValid centerStep2.shape centerBoxes2 centerStep2.proposed := by
  dsimp only [StepValid,centerStep2]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep3 : Instruction 40 := ⟨.mul 6 6,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3
theorem centerAccepted3 : StepValid centerStep3.shape centerBoxes3 centerStep3.proposed := by
  dsimp only [StepValid,centerStep3]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep4 : Instruction 40 := ⟨.inv 6,⟨⟨14214759247177,14223953787544⟩,⟨0,0⟩,⟨-184009751456131,-183771935967528⟩,⟨0,0⟩,⟨0,0⟩,⟨4751698408956214,4760925005338258⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4
theorem centerAccepted4 : StepValid centerStep4.shape centerBoxes4 centerStep4.proposed := by
  dsimp only [StepValid,centerStep4]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep5 : Instruction 40 := ⟨.mul 6 0,⟨⟨9766916060986,9773397259506⟩,⟨0,0⟩,⟨-126434634663855,-126269115202654⟩,⟨0,0⟩,⟨0,0⟩,⟨3264876928296485,3271271272030712⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5
theorem centerAccepted5 : StepValid centerStep5.shape centerBoxes5 centerStep5.proposed := by
  dsimp only [StepValid,centerStep5]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep6 : Instruction 40 := ⟨.contact 0,⟨⟨85363523584,85424340992⟩,⟨0,0⟩,⟨1093261551691,1096261873981⟩,⟨0,0⟩,⟨0,0⟩,⟨-483146886953,-253248932185⟩⟩⟩
noncomputable def centerBoxes7 := centerStep6.proposed :: centerBoxes6
theorem centerAccepted6 : StepValid centerStep6.shape centerBoxes6 centerStep6.proposed := by
  dsimp only [StepValid,centerStep6]
  exact ⟨by decide,by decide,(⟨⟨85363523584,85424340992⟩,⟨-9533405785,-9519776759⟩,⟨2114018221,2118619488⟩⟩ : DyadicJetEnclosure 40),brcenter6_jet,by decide⟩
noncomputable def centerStep7 : Instruction 40 := ⟨.log 10,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes8 := centerStep7.proposed :: centerBoxes7
theorem centerAccepted7 : StepValid centerStep7.shape centerBoxes7 centerStep7.proposed := by
  dsimp only [StepValid,centerStep7]
  exact ⟨by decide,by decide,lc0,by decide⟩
noncomputable def centerStep8 : Instruction 40 := ⟨.add 6 1,⟨⟨1184875151360,1184935968768⟩,⟨0,0⟩,⟨1093261551691,1096261873981⟩,⟨0,0⟩,⟨0,0⟩,⟨-483146886953,-253248932185⟩⟩⟩
noncomputable def centerBoxes9 := centerStep8.proposed :: centerBoxes8
theorem centerAccepted8 : StepValid centerStep8.shape centerBoxes8 centerStep8.proposed := by
  dsimp only [StepValid,centerStep8]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep9 : Instruction 40 := ⟨.log 0,⟨⟨82211919296,82268353792⟩,⟨0,0⟩,⟨1014446197910,1017282433636⟩,⟨0,0⟩,⟨0,0⟩,⟨-1389541814011,-1170953711139⟩⟩⟩
noncomputable def centerBoxes10 := centerStep9.proposed :: centerBoxes9
theorem centerAccepted9 : StepValid centerStep9.shape centerBoxes9 centerStep9.proposed := by
  dsimp only [StepValid,centerStep9]
  exact ⟨by decide,by decide,lc9,by decide⟩
noncomputable def centerStep10 : Instruction 40 := ⟨.mul 1 0,⟨⟨88594661355,88660027814⟩,⟨0,0⟩,⟨1174950032465,1178343341699⟩,⟨0,0⟩,⟨0,0⟩,⟨483709549652,747751853521⟩⟩⟩
noncomputable def centerBoxes11 := centerStep10.proposed :: centerBoxes10
theorem centerAccepted10 : StepValid centerStep10.shape centerBoxes10 centerStep10.proposed := by
  dsimp only [StepValid,centerStep10]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep11 : Instruction 40 := ⟨.neg 4,⟨⟨-85424340992,-85363523584⟩,⟨0,0⟩,⟨-1096261873981,-1093261551691⟩,⟨0,0⟩,⟨0,0⟩,⟨253248932185,483146886953⟩⟩⟩
noncomputable def centerBoxes12 := centerStep11.proposed :: centerBoxes11
theorem centerAccepted11 : StepValid centerStep11.shape centerBoxes11 centerStep11.proposed := by
  dsimp only [StepValid,centerStep11]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep12 : Instruction 40 := ⟨.add 10 0,⟨⟨1014087286784,1014148104192⟩,⟨0,0⟩,⟨-1096261873981,-1093261551691⟩,⟨0,0⟩,⟨0,0⟩,⟨253248932185,483146886953⟩⟩⟩
noncomputable def centerBoxes13 := centerStep12.proposed :: centerBoxes12
theorem centerAccepted12 : StepValid centerStep12.shape centerBoxes12 centerStep12.proposed := by
  dsimp only [StepValid,centerStep12]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep13 : Instruction 40 := ⟨.log 0,⟨⟨-88925337600,-88859398976⟩,⟨0,0⟩,⟨-1188608409985,-1185284263033⟩,⟨0,0⟩,⟨0,0⟩,⟨-1010359412866,-753901950168⟩⟩⟩
noncomputable def centerBoxes14 := centerStep13.proposed :: centerBoxes13
theorem centerAccepted13 : StepValid centerStep13.shape centerBoxes13 centerStep13.proposed := by
  dsimp only [StepValid,centerStep13]
  exact ⟨by decide,by decide,lc10,by decide⟩
noncomputable def centerStep14 : Instruction 40 := ⟨.mul 1 0,⟨⟨-82021381370,-81955646976⟩,⟨0,0⟩,⟨-1007973333987,-1004533483068⟩,⟨0,0⟩,⟨0,0⟩,⟨1386100249921,1654394722999⟩⟩⟩
noncomputable def centerBoxes15 := centerStep14.proposed :: centerBoxes14
theorem centerAccepted14 : StepValid centerStep14.shape centerBoxes14 centerStep14.proposed := by
  dsimp only [StepValid,centerStep14]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep15 : Instruction 40 := ⟨.add 4 0,⟨⟨6573279985,6704380838⟩,⟨0,0⟩,⟨166976698478,173809858631⟩,⟨0,0⟩,⟨0,0⟩,⟨1869809799573,2402146576520⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15
theorem centerAccepted15 : StepValid centerStep15.shape centerBoxes15 centerStep15.proposed := by
  dsimp only [StepValid,centerStep15]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep16 : Instruction 40 := ⟨.mul 0 15,⟨⟨3286639992,3352190419⟩,⟨0,0⟩,⟨83488349239,86904929316⟩,⟨0,0⟩,⟨0,0⟩,⟨934904899786,1201073288260⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16
theorem centerAccepted16 : StepValid centerStep16.shape centerBoxes16 centerStep16.proposed := by
  dsimp only [StepValid,centerStep16]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨-3352190419,-3286639992⟩,⟨0,0⟩,⟨-86904929316,-83488349239⟩,⟨0,0⟩,⟨0,0⟩,⟨-1201073288260,-934904899786⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17
theorem centerAccepted17 : StepValid centerStep17.shape centerBoxes17 centerStep17.proposed := by
  dsimp only [StepValid,centerStep17]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep18 : Instruction 40 := ⟨.add 10 0,⟨⟨758771193197,758836762888⟩,⟨0,0⟩,⟨-86904929316,-83488349239⟩,⟨0,0⟩,⟨0,0⟩,⟨-1201073288260,-934904899786⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18
theorem centerAccepted18 : StepValid centerStep18.shape centerBoxes18 centerStep18.proposed := by
  dsimp only [StepValid,centerStep18]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep19 : Instruction 40 := ⟨.mul 12 12,⟨⟨6627425281,6636872089⟩,⟨0,0⟩,⟨169756564448,170343715836⟩,⟨0,0⟩,⟨0,0⟩,⟨2099019759015,2146720135261⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19
theorem centerAccepted19 : StepValid centerStep19.shape centerBoxes19 centerStep19.proposed := by
  dsimp only [StepValid,centerStep19]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep20 : Instruction 40 := ⟨.neg 0,⟨⟨-6636872089,-6627425281⟩,⟨0,0⟩,⟨-170343715836,-169756564448⟩,⟨0,0⟩,⟨0,0⟩,⟨-2146720135261,-2099019759015⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20
theorem centerAccepted20 : StepValid centerStep20.shape centerBoxes20 centerStep20.proposed := by
  dsimp only [StepValid,centerStep20]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep21 : Instruction 40 := ⟨.add 19 0,⟨⟨1092874755687,1092884202495⟩,⟨0,0⟩,⟨-170343715836,-169756564448⟩,⟨0,0⟩,⟨0,0⟩,⟨-2146720135261,-2099019759015⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21
theorem centerAccepted21 : StepValid centerStep21.shape centerBoxes21 centerStep21.proposed := by
  dsimp only [StepValid,centerStep21]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep22 : Instruction 40 := ⟨.log 0,⟨⟨-6656983808,-6647479616⟩,⟨0,0⟩,⟨-171378188860,-170785995511⟩,⟨0,0⟩,⟨0,0⟩,⟨-2186469158859,-2138276562592⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22
theorem centerAccepted22 : StepValid centerStep22.shape centerBoxes22 centerStep22.proposed := by
  dsimp only [StepValid,centerStep22]
  exact ⟨by decide,by decide,lc7,by decide⟩
noncomputable def centerStep23 : Instruction 40 := ⟨.mul 0 22,⟨⟨-3328491904,-3323739808⟩,⟨0,0⟩,⟨-85689094430,-85392997755⟩,⟨0,0⟩,⟨0,0⟩,⟨-1093234579430,-1069138281296⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23
theorem centerAccepted23 : StepValid centerStep23.shape centerBoxes23 centerStep23.proposed := by
  dsimp only [StepValid,centerStep23]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep24 : Instruction 40 := ⟨.neg 0,⟨⟨3323739808,3328491904⟩,⟨0,0⟩,⟨85392997755,85689094430⟩,⟨0,0⟩,⟨0,0⟩,⟨1069138281296,1093234579430⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24
theorem centerAccepted24 : StepValid centerStep24.shape centerBoxes24 centerStep24.proposed := by
  dsimp only [StepValid,centerStep24]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep25 : Instruction 40 := ⟨.add 17 0,⟨⟨765447123424,765451894784⟩,⟨0,0⟩,⟨85392997755,85689094430⟩,⟨0,0⟩,⟨0,0⟩,⟨1069138281296,1093234579430⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25
theorem centerAccepted25 : StepValid centerStep25.shape centerBoxes25 centerStep25.proposed := by
  dsimp only [StepValid,centerStep25]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep26 : Instruction 40 := ⟨.add 24 26,⟨⟨1269496125430,1269606076593⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26
theorem centerAccepted26 : StepValid centerStep26.shape centerBoxes26 centerStep26.proposed := by
  dsimp only [StepValid,centerStep26]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep27 : Instruction 40 := ⟨.neg 27,⟨⟨-170094448817,-169984497654⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27
theorem centerAccepted27 : StepValid centerStep27.shape centerBoxes27 centerStep27.proposed := by
  dsimp only [StepValid,centerStep27]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep28 : Instruction 40 := ⟨.add 26 0,⟨⟨929417178959,929527130122⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28
theorem centerAccepted28 : StepValid centerStep28.shape centerBoxes28 centerStep28.proposed := by
  dsimp only [StepValid,centerStep28]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep29 : Instruction 40 := ⟨.inv 0,⟨⟨1300581532736,1300735393087⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29
theorem centerAccepted29 : StepValid centerStep29.shape centerBoxes29 centerStep29.proposed := by
  dsimp only [StepValid,centerStep29]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep30 : Instruction 40 := ⟨.mul 3 0,⟨⟨1501651437696,1501959158398⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30
theorem centerAccepted30 : StepValid centerStep30.shape centerBoxes30 centerStep30.proposed := by
  dsimp only [StepValid,centerStep30]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨342717064576,342942355200⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31
theorem centerAccepted31 : StepValid centerStep31.shape centerBoxes31 centerStep31.proposed := by
  dsimp only [StepValid,centerStep31]
  exact ⟨by decide,by decide,lc12,by decide⟩
noncomputable def centerStep32 : Instruction 40 := ⟨.mul 0 31,⟨⟨171358532288,171471177600⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32
theorem centerAccepted32 : StepValid centerStep32.shape centerBoxes32 centerStep32.proposed := by
  dsimp only [StepValid,centerStep32]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep33 : Instruction 40 := ⟨.inv 20,⟨⟨1192060424525,1192131915438⟩,⟨0,0⟩,⟨1285052768957,1288734002176⟩,⟨0,0⟩,⟨0,0⟩,⟨2202625230662,2488651629667⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33
theorem centerAccepted33 : StepValid centerStep33.shape centerBoxes33 centerStep33.proposed := by
  dsimp only [StepValid,centerStep33]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep34 : Instruction 40 := ⟨.mul 25 0,⟨⟨1284609221274,1284752203100⟩,⟨0,0⟩,⟨2570105537914,2577468004351⟩,⟨0,0⟩,⟨0,0⟩,⟨4405281877713,4977286793922⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34
theorem centerAccepted34 : StepValid centerStep34.shape centerBoxes34 centerStep34.proposed := by
  dsimp only [StepValid,centerStep34]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨171071318336,171193691328⟩,⟨0,0⟩,⟨2199537713754,2206084149228⟩,⟨0,0⟩,⟨0,0⟩,⟨-656224246870,-139988267485⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35
theorem centerAccepted35 : StepValid centerStep35.shape centerBoxes35 centerStep35.proposed := by
  dsimp only [StepValid,centerStep35]
  exact ⟨by decide,by decide,lc13,by decide⟩
noncomputable def centerStep36 : Instruction 40 := ⟨.mul 0 35,⟨⟨85535659168,85596845664⟩,⟨0,0⟩,⟨1099768856877,1103042074614⟩,⟨0,0⟩,⟨0,0⟩,⟨-328112123435,-69994133742⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36
theorem centerAccepted36 : StepValid centerStep36.shape centerBoxes36 centerStep36.proposed := by
  dsimp only [StepValid,centerStep36]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep37 : Instruction 40 := ⟨.mul 40 11,⟨⟨1530894246848,1530903789568⟩,⟨0,0⟩,⟨170785995510,171378188860⟩,⟨0,0⟩,⟨0,0⟩,⟨2138276562592,2186469158860⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37
theorem centerAccepted37 : StepValid centerStep37.shape centerBoxes37 centerStep37.proposed := by
  dsimp only [StepValid,centerStep37]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep38 : Instruction 40 := ⟨.add 0 17,⟨⟨1524257374759,1524276364287⟩,⟨0,0⟩,⟨442279674,1621624412⟩,⟨0,0⟩,⟨0,0⟩,⟨-8443572669,87449399845⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38
theorem centerAccepted38 : StepValid centerStep38.shape centerBoxes38 centerStep38.proposed := by
  dsimp only [StepValid,centerStep38]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep39 : Instruction 40 := ⟨.mul 20 0,⟨⟨1051887545131,1051991550433⟩,⟨0,0⟩,⟨-120172936132,-114621055958⟩,⟨0,0⟩,⟨0,0⟩,⟨-1671157199538,-1235775670557⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39
theorem centerAccepted39 : StepValid centerStep39.shape centerBoxes39 centerStep39.proposed := by
  dsimp only [StepValid,centerStep39]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep40 : Instruction 40 := ⟨.mul 43 41,⟨⟨1510941914644,1510967216318⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40
theorem centerAccepted40 : StepValid centerStep40.shape centerBoxes40 centerStep40.proposed := by
  dsimp only [StepValid,centerStep40]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep41 : Instruction 40 := ⟨.mul 19 19,⟨⟨1086277945085,1086296724737⟩,⟨0,0⟩,⟨-338633901324,-337463759746⟩,⟨0,0⟩,⟨0,0⟩,⟨-4215142747548,-4119917729967⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41
theorem centerAccepted41 : StepValid centerStep41.shape centerBoxes41 centerStep41.proposed := by
  dsimp only [StepValid,centerStep41]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep42 : Instruction 40 := ⟨.mul 1 0,⟨⟨1492756271711,1492807076167⟩,⟨0,0⟩,⟨-465356354866,-463740561166⟩,⟨0,0⟩,⟨0,0⟩,⟨-5792519462963,-5661564849189⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42
theorem centerAccepted42 : StepValid centerStep42.shape centerBoxes42 centerStep42.proposed := by
  dsimp only [StepValid,centerStep42]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep43 : Instruction 40 := ⟨.mul 17 17,⟨⟨532881402939,532888046318⟩,⟨0,0⟩,⟨118896104126,119309115134⟩,⟨0,0⟩,⟨0,0⟩,⟨1501868220704,1535520097920⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43
theorem centerAccepted43 : StepValid centerStep43.shape centerBoxes43 centerStep43.proposed := by
  dsimp only [StepValid,centerStep43]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep44 : Instruction 40 := ⟨.mul 18 0,⟨⟨370976101299,370983038704⟩,⟨0,0⟩,⟨124157869626,124589935119⟩,⟨0,0⟩,⟨0,0⟩,⟨1582184637369,1617432087823⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44
theorem centerAccepted44 : StepValid centerStep44.shape centerBoxes44 centerStep44.proposed := by
  dsimp only [StepValid,centerStep44]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep45 : Instruction 40 := ⟨.mul 2 0,⟨⟨503657158214,503683718594⟩,⟨0,0⟩,⟨11548876461,12689334991⟩,⟨0,0⟩,⟨0,0⟩,⟨88159260662,181039222892⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45
theorem centerAccepted45 : StepValid centerStep45.shape centerBoxes45 centerStep45.proposed := by
  dsimp only [StepValid,centerStep45]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep46 : Instruction 40 := ⟨.inv 0,⟨⟨2400168548209,2400295121193⟩,⟨0,0⟩,⟨-60473971974,-55033047576⟩,⟨0,0⟩,⟨0,0⟩,⟨-860260762070,-417051905803⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46
theorem centerAccepted46 : StepValid centerStep46.shape centerBoxes46 centerStep46.proposed := by
  dsimp only [StepValid,centerStep46]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep47 : Instruction 40 := ⟨.mul 7 0,⟨⟨2296208005715,2296556145703⟩,⟨0,0⟩,⟨-320204544401,-302860308500⟩,⟨0,0⟩,⟨0,0⟩,⟨-4459836085166,-3083393433331⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47
theorem centerAccepted47 : StepValid centerStep47.shape centerBoxes47 centerStep47.proposed := by
  dsimp only [StepValid,centerStep47]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep48 : Instruction 40 := ⟨.neg 11,⟨⟨-85596845664,-85535659168⟩,⟨0,0⟩,⟨-1103042074614,-1099768856877⟩,⟨0,0⟩,⟨0,0⟩,⟨69994133742,328112123435⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48
theorem centerAccepted48 : StepValid centerStep48.shape centerBoxes48 centerStep48.proposed := by
  dsimp only [StepValid,centerStep48]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep49 : Instruction 40 := ⟨.mul 0 10,⟨⟨-118664728419,-118578427001⟩,⟨0,0⟩,⟨-1529296941121,-1524648379298⟩,⟨0,0⟩,⟨0,0⟩,⟨86971560314,454641382887⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49
theorem centerAccepted49 : StepValid centerStep49.shape centerBoxes49 centerStep49.proposed := by
  dsimp only [StepValid,centerStep49]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep50 : Instruction 40 := ⟨.mul 53 43,⟨⟨170727047168,170848681984⟩,⟨0,0⟩,⟨2186523103382,2192523747962⟩,⟨0,0⟩,⟨0,0⟩,⟨-966293773906,-506497864370⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50
theorem centerAccepted50 : StepValid centerStep50.shape centerBoxes50 centerStep50.proposed := by
  dsimp only [StepValid,centerStep50]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep51 : Instruction 40 := ⟨.inv 29,⟨⟨1106179242828,1106188804640⟩,⟨0,0⟩,⟨171821669210,172418944091⟩,⟨0,0⟩,⟨0,0⟩,⟨2177932295845,2226621792566⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51
theorem centerAccepted51 : StepValid centerStep51.shape centerBoxes51 centerStep51.proposed := by
  dsimp only [StepValid,centerStep51]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep52 : Instruction 40 := ⟨.mul 1 0,⟨⟨171762363394,171886221596⟩,⟨0,0⟩,⟨2226462199495,2232630116169⟩,⟨0,0⟩,⟨0,0⟩,⟨49397107332,524053787987⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52
theorem centerAccepted52 : StepValid centerStep52.shape centerBoxes52 centerStep52.proposed := by
  dsimp only [StepValid,centerStep52]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep53 : Instruction 40 := ⟨.neg 2,⟨⟨-170848681984,-170727047168⟩,⟨0,0⟩,⟨-2192523747962,-2186523103382⟩,⟨0,0⟩,⟨0,0⟩,⟨506497864370,966293773906⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53
theorem centerAccepted53 : StepValid centerStep53.shape centerBoxes53 centerStep53.proposed := by
  dsimp only [StepValid,centerStep53]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep54 : Instruction 40 := ⟨.add 1 0,⟨⟨913681410,1159174428⟩,⟨0,0⟩,⟨33938451533,46107012787⟩,⟨0,0⟩,⟨0,0⟩,⟨555894971702,1490347561893⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54
theorem centerAccepted54 : StepValid centerStep54.shape centerBoxes54 centerStep54.proposed := by
  dsimp only [StepValid,centerStep54]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep55 : Instruction 40 := ⟨.mul 36 0,⟨⟨630530060,800013523⟩,⟨0,0⟩,⟨23329249773,31751746591⟩,⟨0,0⟩,⟨0,0⟩,⟨375067415146,1022644377036⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55
theorem centerAccepted55 : StepValid centerStep55.shape centerBoxes55 centerStep55.proposed := by
  dsimp only [StepValid,centerStep55]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep56 : Instruction 40 := ⟨.add 6 0,⟨⟨-118034198359,-117778413478⟩,⟨0,0⟩,⟨-1505967691348,-1492896632707⟩,⟨0,0⟩,⟨0,0⟩,⟨462038975460,1477285759923⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56
theorem centerAccepted56 : StepValid centerStep56.shape centerBoxes56 centerStep56.proposed := by
  dsimp only [StepValid,centerStep56]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep57 : Instruction 40 := ⟨.mul 0 10,⟨⟨-257675228982,-257103277988⟩,⟨0,0⟩,⟨-3281716269326,-3252412667958⟩,⟨0,0⟩,⟨0,0⟩,⟨1202723462097,3483006082665⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57
theorem centerAccepted57 : StepValid centerStep57.shape centerBoxes57 centerStep57.proposed := by
  dsimp only [StepValid,centerStep57]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep58 : Instruction 40 := ⟨.mul 54 51,⟨⟨341454094336,341697363968⟩,⟨0,0⟩,⟨4373046206764,4385047495924⟩,⟨0,0⟩,⟨0,0⟩,⟨-1932587547812,-1012995728740⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58
theorem centerAccepted58 : StepValid centerStep58.shape centerBoxes58 centerStep58.proposed := by
  dsimp only [StepValid,centerStep58]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep59 : Instruction 40 := ⟨.mul 0 7,⟨⟨343524726789,343772443191⟩,⟨0,0⟩,⟨4452924398990,4465260232337⟩,⟨0,0⟩,⟨0,0⟩,⟨98794214666,1048107575973⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59
theorem centerAccepted59 : StepValid centerStep59.shape centerBoxes59 centerStep59.proposed := by
  dsimp only [StepValid,centerStep59]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep60 : Instruction 40 := ⟨.mul 57 53,⟨⟨256090570752,256273022976⟩,⟨0,0⟩,⟨3279784655073,3288785621943⟩,⟨0,0⟩,⟨0,0⟩,⟨-1449440660859,-759746796555⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60
theorem centerAccepted60 : StepValid centerStep60.shape centerBoxes60 centerStep60.proposed := by
  dsimp only [StepValid,centerStep60]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep61 : Instruction 40 := ⟨.mul 39 35,⟨⟨760826731496,760838050683⟩,⟨0,0⟩,⟨-33711392911,-33006850853⟩,⟨0,0⟩,⟨0,0⟩,⟨-458358003602,-400997922880⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61
theorem centerAccepted61 : StepValid centerStep61.shape centerBoxes61 centerStep61.proposed := by
  dsimp only [StepValid,centerStep61]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep62 : Instruction 40 := ⟨.inv 0,⟨⟨1588939746808,1588963386234⟩,⟨0,0⟩,⟨68931748602,70405214246⟩,⟨0,0⟩,⟨0,0⟩,⟨843427819317,963505842851⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62
theorem centerAccepted62 : StepValid centerStep62.shape centerBoxes62 centerStep62.proposed := by
  dsimp only [StepValid,centerStep62]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep63 : Instruction 40 := ⟨.mul 2 0,⟨⟨370084750693,370353928146⟩,⟨0,0⟩,⟨4755777781845,4769210950625⟩,⟨0,0⟩,⟨0,0⟩,⟨-1486979860023,-452178951408⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63
theorem centerAccepted63 : StepValid centerStep63.shape centerBoxes63 centerStep63.proposed := by
  dsimp only [StepValid,centerStep63]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep64 : Instruction 40 := ⟨.neg 0,⟨⟨-370353928146,-370084750693⟩,⟨0,0⟩,⟨-4769210950625,-4755777781845⟩,⟨0,0⟩,⟨0,0⟩,⟨452178951408,1486979860023⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64
theorem centerAccepted64 : StepValid centerStep64.shape centerBoxes64 centerStep64.proposed := by
  dsimp only [StepValid,centerStep64]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep65 : Instruction 40 := ⟨.add 5 0,⟨⟨-26829201357,-26312307502⟩,⟨0,0⟩,⟨-316286551635,-290517549508⟩,⟨0,0⟩,⟨0,0⟩,⟨550973166074,2535087435996⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65
theorem centerAccepted65 : StepValid centerStep65.shape centerBoxes65 centerStep65.proposed := by
  dsimp only [StepValid,centerStep65]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep66 : Instruction 40 := ⟨.mul 18 0,⟨⟨-56038304375,-54950333956⟩,⟨0,0⟩,⟨-653381785372,-598900342795⟩,⟨0,0⟩,⟨0,0⟩,⟨1384480729372,5588096659007⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66
theorem centerAccepted66 : StepValid centerStep66.shape centerBoxes66 centerStep66.proposed := by
  dsimp only [StepValid,centerStep66]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep67 : Instruction 40 := ⟨.add 9 0,⟨⟨-313713533357,-312053611944⟩,⟨0,0⟩,⟨-3935098054698,-3851313010753⟩,⟨0,0⟩,⟨0,0⟩,⟨2587204191469,9071102741672⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67
theorem centerAccepted67 : StepValid centerStep67.shape centerBoxes67 centerStep67.proposed := by
  dsimp only [StepValid,centerStep67]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep68 : Instruction 40 := ⟨.mul 61 29,⟨⟨118339794751,118425581522⟩,⟨0,0⟩,⟨1515627206805,1519897150297⟩,⟨0,0⟩,⟨0,0⟩,⟨-669573284693,-341052141399⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68
theorem centerAccepted68 : StepValid centerStep68.shape centerBoxes68 centerStep68.proposed := by
  dsimp only [StepValid,centerStep68]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep69 : Instruction 40 := ⟨.mul 27 25,⟨⟨526467661401,526483326546⟩,⟨0,0⟩,⟨-46656843939,-45677607643⟩,⟨0,0⟩,⟨0,0⟩,⟨-632605480279,-552648397782⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69
theorem centerAccepted69 : StepValid centerStep69.shape centerBoxes69 centerStep69.proposed := by
  dsimp only [StepValid,centerStep69]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨2296228120927,2296296445631⟩,⟨0,0⟩,⟨199220377698,203503373059⟩,⟨0,0⟩,⟨0,0⟩,⟨2444914297496,2795308190767⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70
theorem centerAccepted70 : StepValid centerStep70.shape centerBoxes70 centerStep70.proposed := by
  dsimp only [StepValid,centerStep70]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep71 : Instruction 40 := ⟨.mul 2 0,⟨⟨247141692427,247328209226⟩,⟨0,0⟩,⟨3186688910967,3196177594190⟩,⟨0,0⟩,⟨0,0⟩,⟨-586006034067,151440757527⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71
theorem centerAccepted71 : StepValid centerStep71.shape centerBoxes71 centerStep71.proposed := by
  dsimp only [StepValid,centerStep71]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep72 : Instruction 40 := ⟨.mul 65 39,⟨⟨13303877596,13322107721⟩,⟨0,0⟩,⟨170384459947,170964371582⟩,⟨0,0⟩,⟨0,0⟩,⟨-75347784932,-39468764337⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72
theorem centerAccepted72 : StepValid centerStep72.shape centerBoxes72 centerStep72.proposed := by
  dsimp only [StepValid,centerStep72]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep73 : Instruction 40 := ⟨.add 54 0,⟨⟨772075070793,772158870609⟩,⟨0,0⟩,⟨83479530631,87476022343⟩,⟨0,0⟩,⟨0,0⟩,⟨-1276421073192,-974373664123⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73
theorem centerAccepted73 : StepValid centerStep73.shape centerBoxes73 centerStep73.proposed := by
  dsimp only [StepValid,centerStep73]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep74 : Instruction 40 := ⟨.mul 0 0,⟨⟨542149714365,542267408910⟩,⟨0,0⟩,⟨117238349996,122864342518⟩,⟨0,0⟩,⟨0,0⟩,⟨-1780119459479,-1354487833342⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74
theorem centerAccepted74 : StepValid centerStep74.shape centerBoxes74 centerStep74.proposed := by
  dsimp only [StepValid,centerStep74]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep75 : Instruction 40 := ⟨.mul 7 0,⟨⟨-154720169006,-153868110448⟩,⟨0,0⟩,⟨-1975804146190,-1932287795428⟩,⟨0,0⟩,⟨0,0⟩,⟨780672383978,4160363259614⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75
theorem centerAccepted75 : StepValid centerStep75.shape centerBoxes75 centerStep75.proposed := by
  dsimp only [StepValid,centerStep75]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep76 : Instruction 40 := ⟨.mul 79 28,⟨⟨4592416011430,4593112291406⟩,⟨0,0⟩,⟨-640409088802,-605720617000⟩,⟨0,0⟩,⟨0,0⟩,⟨-8919672170332,-6166786866662⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76
theorem centerAccepted76 : StepValid centerStep76.shape centerBoxes76 centerStep76.proposed := by
  dsimp only [StepValid,centerStep76]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep77 : Instruction 40 := ⟨.mul 0 3,⟨⟨3224786193764,3225625186599⟩,⟨0,0⟩,⟨-101067440157,-59912594972⟩,⟨0,0⟩,⟨0,0⟩,⟨-11698093830143,-8492026762248⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77
theorem centerAccepted77 : StepValid centerStep77.shape centerBoxes77 centerStep77.proposed := by
  dsimp only [StepValid,centerStep77]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep78 : Instruction 40 := ⟨.add 45 29,⟨⟨85761686624,85935518432⟩,⟨0,0⟩,⟨-1103042074614,-1099768856877⟩,⟨0,0⟩,⟨0,0⟩,⟨69994133742,328112123435⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78
theorem centerAccepted78 : StepValid centerStep78.shape centerBoxes78 centerStep78.proposed := by
  dsimp only [StepValid,centerStep78]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep79 : Instruction 40 := ⟨.mul 1 0,⟨⟨251532676865,252108086605⟩,⟨0,0⟩,⟨-3243881638465,-3230213798072⟩,⟨0,0⟩,⟨0,0⟩,⟨-589157598057,502986467044⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79
theorem centerAccepted79 : StepValid centerStep79.shape centerBoxes79 centerStep79.proposed := by
  dsimp only [StepValid,centerStep79]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep80 : Instruction 40 := ⟨.add 4 0,⟨⟨96812507859,98239976157⟩,⟨0,0⟩,⟨-5219685784655,-5162501593500⟩,⟨0,0⟩,⟨0,0⟩,⟨191514785921,4663349726658⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80
theorem centerAccepted80 : StepValid centerStep80.shape centerBoxes80 centerStep80.proposed := by
  dsimp only [StepValid,centerStep80]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep81 : Instruction 40 := ⟨.mul 81 81,⟨⟨26279603337,26313611232⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81
theorem centerAccepted81 : StepValid centerStep81.shape centerBoxes81 centerStep81.proposed := by
  dsimp only [StepValid,centerStep81]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep82 : Instruction 40 := ⟨.neg 0,⟨⟨-26313611232,-26279603337⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82
theorem centerAccepted82 : StepValid centerStep82.shape centerBoxes82 centerStep82.proposed := by
  dsimp only [StepValid,centerStep82]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep83 : Instruction 40 := ⟨.add 81 0,⟨⟨1073198016544,1073232024439⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83
theorem centerAccepted83 : StepValid centerStep83.shape centerBoxes83 centerStep83.proposed := by
  dsimp only [StepValid,centerStep83]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep84 : Instruction 40 := ⟨.inv 0,⟨⟨1126434724351,1126470419232⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes85 := centerStep84.proposed :: centerBoxes84
theorem centerAccepted84 : StepValid centerStep84.shape centerBoxes84 centerStep84.proposed := by
  dsimp only [StepValid,centerStep84]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep85 : Instruction 40 := ⟨.mul 13 0,⟨⟨253193306147,253392419413⟩,⟨0,0⟩,⟨3264719493943,3274544282674⟩,⟨0,0⟩,⟨0,0⟩,⟨-600374244521,155153914985⟩⟩⟩
noncomputable def centerBoxes86 := centerStep85.proposed :: centerBoxes85
theorem centerAccepted85 : StepValid centerStep85.shape centerBoxes85 centerStep85.proposed := by
  dsimp only [StepValid,centerStep85]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep86 : Instruction 40 := ⟨.add 5 0,⟨⟨350005814006,351632395570⟩,⟨0,0⟩,⟨-1954966290712,-1887957310826⟩,⟨0,0⟩,⟨0,0⟩,⟨-408859458600,4818503641643⟩⟩⟩
noncomputable def centerBoxes87 := centerStep86.proposed :: centerBoxes86
theorem centerAccepted86 : StepValid centerStep86.shape centerBoxes86 centerStep86.proposed := by
  dsimp only [StepValid,centerStep86]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep87 : Instruction 40 := ⟨.mul 0 68,⟨⟨241538445260,242681916262⟩,⟨0,0⟩,⟨-1377028529607,-1329452997265⟩,⟨0,0⟩,⟨0,0⟩,⟨-379576692484,3336961498954⟩⟩⟩
noncomputable def centerBoxes88 := centerStep87.proposed :: centerBoxes87
theorem centerAccepted87 : StepValid centerStep87.shape centerBoxes87 centerStep87.proposed := by
  dsimp only [StepValid,centerStep87]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep88 : Instruction 40 := ⟨.mul 0 69,⟨⟨166685289798,167488869691⟩,⟨0,0⟩,⟨-969548752065,-935793908052⟩,⟨0,0⟩,⟨0,0⟩,⟨-325169679395,2315332239825⟩⟩⟩
noncomputable def centerBoxes89 := centerStep88.proposed :: centerBoxes88
theorem centerAccepted88 : StepValid centerStep88.shape centerBoxes88 centerStep88.proposed := by
  dsimp only [StepValid,centerStep88]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep89 : Instruction 40 := ⟨.mul 90 63,⟨⟨525936294354,525948379931⟩,⟨0,0⟩,⟨58673258320,58877691336⟩,⟨0,0⟩,⟨0,0⟩,⟨734601527147,751170595897⟩⟩⟩
noncomputable def centerBoxes90 := centerStep89.proposed :: centerBoxes89
theorem centerAccepted89 : StepValid centerStep89.shape centerBoxes89 centerStep89.proposed := by
  dsimp only [StepValid,centerStep89]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep90 : Instruction 40 := ⟨.inv 0,⟨⟨2298563634273,2298616453348⟩,⟨0,0⟩,⟨-257326279805,-256421015872⟩,⟨0,0⟩,⟨0,0⟩,⟨-3225796902853,-3152830521778⟩⟩⟩
noncomputable def centerBoxes91 := centerStep90.proposed :: centerBoxes90
theorem centerAccepted90 : StepValid centerStep90.shape centerBoxes90 centerStep90.proposed := by
  dsimp only [StepValid,centerStep90]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep91 : Instruction 40 := ⟨.mul 2 0,⟨⟨348460840084,350148795064⟩,⟨0,0⟩,⟨-2066117305337,-1995179861808⟩,⟨0,0⟩,⟨0,0⟩,⟨-734699827445,4816239251469⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91
theorem centerAccepted91 : StepValid centerStep91.shape centerBoxes91 centerStep91.proposed := by
  dsimp only [StepValid,centerStep91]
  exact ⟨by decide,by decide⟩
noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91]
theorem centerAccepted : Accepted centerProgram centerInitial :=
  ⟨centerAccepted0,⟨centerAccepted1,⟨centerAccepted2,⟨centerAccepted3,⟨centerAccepted4,⟨centerAccepted5,⟨centerAccepted6,⟨centerAccepted7,⟨centerAccepted8,⟨centerAccepted9,⟨centerAccepted10,⟨centerAccepted11,⟨centerAccepted12,⟨centerAccepted13,⟨centerAccepted14,⟨centerAccepted15,⟨centerAccepted16,⟨centerAccepted17,⟨centerAccepted18,⟨centerAccepted19,⟨centerAccepted20,⟨centerAccepted21,⟨centerAccepted22,⟨centerAccepted23,⟨centerAccepted24,⟨centerAccepted25,⟨centerAccepted26,⟨centerAccepted27,⟨centerAccepted28,⟨centerAccepted29,⟨centerAccepted30,⟨centerAccepted31,⟨centerAccepted32,⟨centerAccepted33,⟨centerAccepted34,⟨centerAccepted35,⟨centerAccepted36,⟨centerAccepted37,⟨centerAccepted38,⟨centerAccepted39,⟨centerAccepted40,⟨centerAccepted41,⟨centerAccepted42,⟨centerAccepted43,⟨centerAccepted44,⟨centerAccepted45,⟨centerAccepted46,⟨centerAccepted47,⟨centerAccepted48,⟨centerAccepted49,⟨centerAccepted50,⟨centerAccepted51,⟨centerAccepted52,⟨centerAccepted53,⟨centerAccepted54,⟨centerAccepted55,⟨centerAccepted56,⟨centerAccepted57,⟨centerAccepted58,⟨centerAccepted59,⟨centerAccepted60,⟨centerAccepted61,⟨centerAccepted62,⟨centerAccepted63,⟨centerAccepted64,⟨centerAccepted65,⟨centerAccepted66,⟨centerAccepted67,⟨centerAccepted68,⟨centerAccepted69,⟨centerAccepted70,⟨centerAccepted71,⟨centerAccepted72,⟨centerAccepted73,⟨centerAccepted74,⟨centerAccepted75,⟨centerAccepted76,⟨centerAccepted77,⟨centerAccepted78,⟨centerAccepted79,⟨centerAccepted80,⟨centerAccepted81,⟨centerAccepted82,⟨centerAccepted83,⟨centerAccepted84,⟨centerAccepted85,⟨centerAccepted86,⟨centerAccepted87,⟨centerAccepted88,⟨centerAccepted89,⟨centerAccepted90,⟨centerAccepted91,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
noncomputable def center_output : DyadicBivariateJetEnclosure 40 := ⟨⟨348460840084,350148795064⟩,⟨0,0⟩,⟨-2066117305337,-1995179861808⟩,⟨0,0⟩,⟨0,0⟩,⟨-734699827445,4816239251469⟩⟩
theorem center_output_eq : (finalBoxes centerProgram centerInitial).getD 0 (zeroBox 40)=center_output := rfl
noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨169984497654,170094448817⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨755470957322,755483608159⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨77763234752,92276238484⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0
theorem wholeAccepted0 : StepValid wholeStep0.shape wholeBoxes0 wholeStep0.proposed := by
  dsimp only [StepValid,wholeStep0]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 4 0,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1
theorem wholeAccepted1 : StepValid wholeStep1.shape wholeBoxes1 wholeStep1.proposed := by
  dsimp only [StepValid,wholeStep1]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep2 : Instruction 40 := ⟨.add 5 0,⟨⟨3298534883328,3298534883328⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2
theorem wholeAccepted2 : StepValid wholeStep2.shape wholeBoxes2 wholeStep2.proposed := by
  dsimp only [StepValid,wholeStep2]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep3 : Instruction 40 := ⟨.mul 6 6,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3
theorem wholeAccepted3 : StepValid wholeStep3.shape wholeBoxes3 wholeStep3.proposed := by
  dsimp only [StepValid,wholeStep3]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep4 : Instruction 40 := ⟨.inv 6,⟨⟨13101160596443,15546238829572⟩,⟨0,0⟩,⟨-219811719713191,-156106042571801⟩,⟨0,0⟩,⟨0,0⟩,⟨3720143165643698,6215933339627022⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4
theorem wholeAccepted4 : StepValid wholeStep4.shape wholeBoxes4 wholeStep4.proposed := by
  dsimp only [StepValid,wholeStep4]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep5 : Instruction 40 := ⟨.mul 6 0,⟨⟨9001765954803,10681950338282⟩,⟨0,0⟩,⟨-151034465602203,-107259967467568⟩,⟨0,0⟩,⟨0,0⟩,⟨2556098587523356,4271019631685018⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5
theorem wholeAccepted5 : StepValid wholeStep5.shape wholeBoxes5 wholeStep5.proposed := by
  dsimp only [StepValid,wholeStep5]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep6 : Instruction 40 := ⟨.contact 0,⟨⟨78157709312,92614426624⟩,⟨0,0⟩,⟨777913375238,1540366778689⟩,⟨0,0⟩,⟨0,0⟩,⟨-28206557714103,32588619227725⟩⟩⟩
noncomputable def wholeBoxes7 := wholeStep6.proposed :: wholeBoxes6
theorem wholeAccepted6 : StepValid wholeStep6.shape wholeBoxes6 wholeStep6.proposed := by
  dsimp only [StepValid,wholeStep6]
  exact ⟨by decide,by decide,(⟨⟨78157709312,92614426624⟩,⟨-11213673498,-7974315317⟩,⟨1613268899,2709552760⟩⟩ : DyadicJetEnclosure 40),brwhole6_jet,by decide⟩
noncomputable def wholeStep7 : Instruction 40 := ⟨.log 10,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes8 := wholeStep7.proposed :: wholeBoxes7
theorem wholeAccepted7 : StepValid wholeStep7.shape wholeBoxes7 wholeStep7.proposed := by
  dsimp only [StepValid,wholeStep7]
  exact ⟨by decide,by decide,lc0,by decide⟩
noncomputable def wholeStep8 : Instruction 40 := ⟨.add 6 1,⟨⟨1177669337088,1192126054400⟩,⟨0,0⟩,⟨777913375238,1540366778689⟩,⟨0,0⟩,⟨0,0⟩,⟨-28206557714103,32588619227725⟩⟩⟩
noncomputable def wholeBoxes9 := wholeStep8.proposed :: wholeBoxes8
theorem wholeAccepted8 : StepValid wholeStep8.shape wholeBoxes8 wholeStep8.proposed := by
  dsimp only [StepValid,wholeStep8]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep9 : Instruction 40 := ⟨.log 0,⟨⟨75504827712,88919931904⟩,⟨0,0⟩,⟨717478490063,1438138135105⟩,⟨0,0⟩,⟨0,0⟩,⟨-28215643683871,29957643435496⟩⟩⟩
noncomputable def wholeBoxes10 := wholeStep9.proposed :: wholeBoxes9
theorem wholeAccepted9 : StepValid wholeStep9.shape wholeBoxes9 wholeStep9.proposed := by
  dsimp only [StepValid,wholeStep9]
  exact ⟨by decide,by decide,lc23,by decide⟩
noncomputable def wholeStep10 : Instruction 40 := ⟨.mul 1 0,⟨⟨80872014585,96409864981⟩,⟨0,0⟩,⟨821900023892,1683848722455⟩,⟨0,0⟩,⟨0,0⟩,⟨-31858195998816,39146093953076⟩⟩⟩
noncomputable def wholeBoxes11 := wholeStep10.proposed :: wholeBoxes10
theorem wholeAccepted10 : StepValid wholeStep10.shape wholeBoxes10 wholeStep10.proposed := by
  dsimp only [StepValid,wholeStep10]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep11 : Instruction 40 := ⟨.neg 4,⟨⟨-92614426624,-78157709312⟩,⟨0,0⟩,⟨-1540366778689,-777913375238⟩,⟨0,0⟩,⟨0,0⟩,⟨-32588619227725,28206557714103⟩⟩⟩
noncomputable def wholeBoxes12 := wholeStep11.proposed :: wholeBoxes11
theorem wholeAccepted11 : StepValid wholeStep11.shape wholeBoxes11 wholeStep11.proposed := by
  dsimp only [StepValid,wholeStep11]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep12 : Instruction 40 := ⟨.add 10 0,⟨⟨1006897201152,1021353918464⟩,⟨0,0⟩,⟨-1540366778689,-777913375238⟩,⟨0,0⟩,⟨0,0⟩,⟨-32588619227725,28206557714103⟩⟩⟩
noncomputable def wholeBoxes13 := wholeStep12.proposed :: wholeBoxes12
theorem wholeAccepted12 : StepValid wholeStep12.shape wholeBoxes12 wholeStep12.proposed := by
  dsimp only [StepValid,wholeStep12]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep13 : Instruction 40 := ⟨.log 0,⟨⟨-96748867328,-81074676032⟩,⟨0,0⟩,⟨-1682049748745,-837442130503⟩,⟨0,0⟩,⟨0,0⟩,⟨-38159346637559,30163160398091⟩⟩⟩
noncomputable def wholeBoxes14 := wholeStep13.proposed :: wholeBoxes13
theorem wholeAccepted13 : StepValid wholeStep13.shape wholeBoxes13 wholeStep13.proposed := by
  dsimp only [StepValid,wholeStep13]
  exact ⟨by decide,by decide,lc24,by decide⟩
noncomputable def wholeStep14 : Instruction 40 := ⟨.mul 1 0,⟨⟨-89871568664,-74245567139⟩,⟨0,0⟩,⟨-1505121897076,-631361577890⟩,⟨0,0⟩,⟨0,0⟩,⟨-36743800461179,35599551820319⟩⟩⟩
noncomputable def wholeBoxes15 := wholeStep14.proposed :: wholeBoxes14
theorem wholeAccepted14 : StepValid wholeStep14.shape wholeBoxes14 wholeStep14.proposed := by
  dsimp only [StepValid,wholeStep14]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep15 : Instruction 40 := ⟨.add 4 0,⟨⟨-8999554079,22164297842⟩,⟨0,0⟩,⟨-683221873184,1052487144565⟩,⟨0,0⟩,⟨0,0⟩,⟨-68601996459995,74745645773395⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15
theorem wholeAccepted15 : StepValid wholeStep15.shape wholeBoxes15 wholeStep15.proposed := by
  dsimp only [StepValid,wholeStep15]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 0 15,⟨⟨-4499777040,11082148921⟩,⟨0,0⟩,⟨-341610936592,526243572283⟩,⟨0,0⟩,⟨0,0⟩,⟨-34300998229998,37372822886698⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16
theorem wholeAccepted16 : StepValid wholeStep16.shape wholeBoxes16 wholeStep16.proposed := by
  dsimp only [StepValid,wholeStep16]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨-11082148921,4499777040⟩,⟨0,0⟩,⟨-526243572283,341610936592⟩,⟨0,0⟩,⟨0,0⟩,⟨-37372822886698,34300998229998⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17
theorem wholeAccepted17 : StepValid wholeStep17.shape wholeBoxes17 wholeStep17.proposed := by
  dsimp only [StepValid,wholeStep17]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep18 : Instruction 40 := ⟨.add 10 0,⟨⟨751041234695,766623179920⟩,⟨0,0⟩,⟨-526243572283,341610936592⟩,⟨0,0⟩,⟨0,0⟩,⟨-37372822886698,34300998229998⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18
theorem wholeAccepted18 : StepValid wholeStep18.shape wholeBoxes18 wholeStep18.proposed := by
  dsimp only [StepValid,wholeStep18]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep19 : Instruction 40 := ⟨.mul 12 12,⟨⟨5555764369,7801128976⟩,⟨0,0⟩,⟨110594423770,259497366640⟩,⟨0,0⟩,⟨0,0⟩,⟨-3651048155653,9806001066196⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19
theorem wholeAccepted19 : StepValid wholeStep19.shape wholeBoxes19 wholeStep19.proposed := by
  dsimp only [StepValid,wholeStep19]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep20 : Instruction 40 := ⟨.neg 0,⟨⟨-7801128976,-5555764369⟩,⟨0,0⟩,⟨-259497366640,-110594423770⟩,⟨0,0⟩,⟨0,0⟩,⟨-9806001066196,3651048155653⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20
theorem wholeAccepted20 : StepValid wholeStep20.shape wholeBoxes20 wholeStep20.proposed := by
  dsimp only [StepValid,wholeStep20]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep21 : Instruction 40 := ⟨.add 19 0,⟨⟨1091710498800,1093955863407⟩,⟨0,0⟩,⟨-259497366640,-110594423770⟩,⟨0,0⟩,⟨0,0⟩,⟨-9806001066196,3651048155653⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21
theorem wholeAccepted21 : StepValid wholeStep21.shape wholeBoxes21 wholeStep21.proposed := by
  dsimp only [StepValid,wholeStep21]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep22 : Instruction 40 := ⟨.log 0,⟨⟨-7828935424,-5569848256⟩,⟨0,0⟩,⟨-261351679142,-111156088622⟩,⟨0,0⟩,⟨0,0⟩,⟨-9938195408673,3665900340476⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22
theorem wholeAccepted22 : StepValid wholeStep22.shape wholeBoxes22 wholeStep22.proposed := by
  dsimp only [StepValid,wholeStep22]
  exact ⟨by decide,by decide,lc21,by decide⟩
noncomputable def wholeStep23 : Instruction 40 := ⟨.mul 0 22,⟨⟨-3914467712,-2784924128⟩,⟨0,0⟩,⟨-130675839571,-55578044311⟩,⟨0,0⟩,⟨0,0⟩,⟨-4969097704337,1832950170238⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23
theorem wholeAccepted23 : StepValid wholeStep23.shape wholeBoxes23 wholeStep23.proposed := by
  dsimp only [StepValid,wholeStep23]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep24 : Instruction 40 := ⟨.neg 0,⟨⟨2784924128,3914467712⟩,⟨0,0⟩,⟨55578044311,130675839571⟩,⟨0,0⟩,⟨0,0⟩,⟨-1832950170238,4969097704337⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24
theorem wholeAccepted24 : StepValid wholeStep24.shape wholeBoxes24 wholeStep24.proposed := by
  dsimp only [StepValid,wholeStep24]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep25 : Instruction 40 := ⟨.add 17 0,⟨⟨764908307744,766037870592⟩,⟨0,0⟩,⟨55578044311,130675839571⟩,⟨0,0⟩,⟨0,0⟩,⟨-1832950170238,4969097704337⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25
theorem wholeAccepted25 : StepValid wholeStep25.shape wholeBoxes25 wholeStep25.proposed := by
  dsimp only [StepValid,wholeStep25]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep26 : Instruction 40 := ⟨.add 24 26,⟨⟨1269496125430,1269606076593⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26
theorem wholeAccepted26 : StepValid wholeStep26.shape wholeBoxes26 wholeStep26.proposed := by
  dsimp only [StepValid,wholeStep26]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep27 : Instruction 40 := ⟨.neg 27,⟨⟨-170094448817,-169984497654⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27
theorem wholeAccepted27 : StepValid wholeStep27.shape wholeBoxes27 wholeStep27.proposed := by
  dsimp only [StepValid,wholeStep27]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep28 : Instruction 40 := ⟨.add 26 0,⟨⟨929417178959,929527130122⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28
theorem wholeAccepted28 : StepValid wholeStep28.shape wholeBoxes28 wholeStep28.proposed := by
  dsimp only [StepValid,wholeStep28]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep29 : Instruction 40 := ⟨.inv 0,⟨⟨1300581532736,1300735393087⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29
theorem wholeAccepted29 : StepValid wholeStep29.shape wholeBoxes29 wholeStep29.proposed := by
  dsimp only [StepValid,wholeStep29]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep30 : Instruction 40 := ⟨.mul 3 0,⟨⟨1501651437696,1501959158398⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30
theorem wholeAccepted30 : StepValid wholeStep30.shape wholeBoxes30 wholeStep30.proposed := by
  dsimp only [StepValid,wholeStep30]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨342717064576,342942355200⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31
theorem wholeAccepted31 : StepValid wholeStep31.shape wholeBoxes31 wholeStep31.proposed := by
  dsimp only [StepValid,wholeStep31]
  exact ⟨by decide,by decide,lc12,by decide⟩
noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 0 31,⟨⟨171358532288,171471177600⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32
theorem wholeAccepted32 : StepValid wholeStep32.shape wholeBoxes32 wholeStep32.proposed := by
  dsimp only [StepValid,wholeStep32]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep33 : Instruction 40 := ⟨.inv 20,⟨⟨1183650248713,1200644731391⟩,⟨0,0⟩,⟨901526242207,1836764721492⟩,⟨0,0⟩,⟨0,0⟩,⟨-32260780489076,44479155014429⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33
theorem wholeAccepted33 : StepValid wholeStep33.shape wholeBoxes33 wholeStep33.proposed := by
  dsimp only [StepValid,wholeStep33]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep34 : Instruction 40 := ⟨.mul 25 0,⟨⟨1267788869650,1301777835006⟩,⟨0,0⟩,⟨1803052484415,3673529442982⟩,⟨0,0⟩,⟨0,0⟩,⟨-64503504493168,88958310028814⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34
theorem wholeAccepted34 : StepValid wholeStep34.shape wholeBoxes34 wholeStep34.proposed := by
  dsimp only [StepValid,wholeStep34]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨156579503744,185668799168⟩,⟨0,0⟩,⟨1522899775055,3185931375666⟩,⟨0,0⟩,⟨0,0⟩,⟨-65173285483410,75041297475021⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35
theorem wholeAccepted35 : StepValid wholeStep35.shape wholeBoxes35 wholeStep35.proposed := by
  dsimp only [StepValid,wholeStep35]
  exact ⟨by decide,by decide,lc27,by decide⟩
noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 0 35,⟨⟨78289751872,92834399584⟩,⟨0,0⟩,⟨761449887527,1592965687833⟩,⟨0,0⟩,⟨0,0⟩,⟨-32586642741705,37520648737511⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36
theorem wholeAccepted36 : StepValid wholeStep36.shape wholeBoxes36 wholeStep36.proposed := by
  dsimp only [StepValid,wholeStep36]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep37 : Instruction 40 := ⟨.mul 40 11,⟨⟨1529816615488,1532075741184⟩,⟨0,0⟩,⟨111156088622,261351679142⟩,⟨0,0⟩,⟨0,0⟩,⟨-3665900340476,9938195408674⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37
theorem wholeAccepted37 : StepValid wholeStep37.shape wholeBoxes37 wholeStep37.proposed := by
  dsimp only [StepValid,wholeStep37]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep38 : Instruction 40 := ⟨.add 0 17,⟨⟨1522015486512,1526519976815⟩,⟨0,0⟩,⟨-148341278018,150757255372⟩,⟨0,0⟩,⟨0,0⟩,⟨-13471901406672,13589243564327⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38
theorem wholeAccepted38 : StepValid wholeStep38.shape wholeBoxes38 wholeStep38.proposed := by
  dsimp only [StepValid,wholeStep38]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep39 : Instruction 40 := ⟨.mul 20 0,⟨⟨1039640110516,1064350361810⟩,⟨0,0⟩,⟨-834045920810,579393532022⟩,⟨0,0⟩,⟨0,0⟩,⟨-61424455175889,57239154034418⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39
theorem wholeAccepted39 : StepValid wholeStep39.shape wholeBoxes39 wholeStep39.proposed := by
  dsimp only [StepValid,wholeStep39]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep40 : Instruction 40 := ⟨.mul 43 41,⟨⟨1510941914644,1510967216318⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40
theorem wholeAccepted40 : StepValid wholeStep40.shape wholeBoxes40 wholeStep40.proposed := by
  dsimp only [StepValid,wholeStep40]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 19 19,⟨⟨1083964719500,1088428171973⟩,⟨0,0⟩,⟨-516372284938,-219619493760⟩,⟨0,0⟩,⟨0,0⟩,⟨-19490655606882,7387687984649⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41
theorem wholeAccepted41 : StepValid wholeStep41.shape wholeBoxes41 wholeStep41.proposed := by
  dsimp only [StepValid,wholeStep41]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep42 : Instruction 40 := ⟨.mul 1 0,⟨⟨1489577451764,1495736146506⟩,⟨0,0⟩,⟨-709607405913,-301799717267⟩,⟨0,0⟩,⟨0,0⟩,⟨-26784383996113,10152284038842⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42
theorem wholeAccepted42 : StepValid wholeStep42.shape wholeBoxes42 wholeStep42.proposed := by
  dsimp only [StepValid,wholeStep42]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep43 : Instruction 40 := ⟨.mul 17 17,⟨⟨532131452251,533704241372⟩,⟨0,0⟩,⟨77329073648,182085644852⟩,⟨0,0⟩,⟨0,0⟩,⟨-2548441127696,6955075512891⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43
theorem wholeAccepted43 : StepValid wholeStep43.shape wholeBoxes43 wholeStep43.proposed := by
  dsimp only [StepValid,wholeStep43]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep44 : Instruction 40 := ⟨.mul 18 0,⟨⟨370193237030,371835686189⟩,⟨0,0⟩,⟨80694441108,190290620115⟩,⟨0,0⟩,⟨0,0⟩,⟨-2657416278005,7300939746828⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44
theorem wholeAccepted44 : StepValid wholeStep44.shape wholeBoxes44 wholeStep44.proposed := by
  dsimp only [StepValid,wholeStep44]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 2 0,⟨⟨501524026435,505831918776⟩,⟨0,0⟩,⟨-130655040945,157251947328⟩,⟨0,0⟩,⟨0,0⟩,⟨-12918687072934,13320963140123⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45
theorem wholeAccepted45 : StepValid wholeStep45.shape wholeBoxes45 wholeStep45.proposed := by
  dsimp only [StepValid,wholeStep45]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep46 : Instruction 40 := ⟨.inv 0,⟨⟨2389975354936,2410504294696⟩,⟨0,0⟩,⟨-755809242238,627974973723⟩,⟨0,0⟩,⟨0,0⟩,⟨-64419125965702,62565807354226⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46
theorem wholeAccepted46 : StepValid wholeStep46.shape wholeBoxes46 wholeStep46.proposed := by
  dsimp only [StepValid,wholeStep46]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep47 : Instruction 40 := ⟨.mul 7 0,⟨⟨2259834438642,2333418813764⟩,⟨0,0⟩,⟨-2560152201589,1878121099934⟩,⟨0,0⟩,⟨0,0⟩,⟨-197975125920795,187199407764579⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47
theorem wholeAccepted47 : StepValid wholeStep47.shape wholeBoxes47 wholeStep47.proposed := by
  dsimp only [StepValid,wholeStep47]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep48 : Instruction 40 := ⟨.neg 11,⟨⟨-92834399584,-78289751872⟩,⟨0,0⟩,⟨-1592965687833,-761449887527⟩,⟨0,0⟩,⟨0,0⟩,⟨-37520648737511,32586642741705⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48
theorem wholeAccepted48 : StepValid wholeStep48.shape wholeBoxes48 wholeStep48.proposed := by
  dsimp only [StepValid,wholeStep48]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep49 : Instruction 40 := ⟨.mul 0 10,⟨⟨-128887736993,-108373765019⟩,⟨0,0⟩,⟨-2224341555251,-1041523635231⟩,⟨0,0⟩,⟨0,0⟩,⟨-53676441328175,46809347743724⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49
theorem wholeAccepted49 : StepValid wholeStep49.shape wholeBoxes49 wholeStep49.proposed := by
  dsimp only [StepValid,wholeStep49]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 53 43,⟨⟨156315418624,185228853248⟩,⟨0,0⟩,⟨1555826750476,3080733557378⟩,⟨0,0⟩,⟨0,0⟩,⟨-56413115428206,65177238455450⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50
theorem wholeAccepted50 : StepValid wholeStep50.shape wholeBoxes50 wholeStep50.proposed := by
  dsimp only [StepValid,wholeStep50]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep51 : Instruction 40 := ⟨.inv 29,⟨⟨1105095607650,1107368501946⟩,⟨0,0⟩,⟨111720605946,263219242163⟩,⟨0,0⟩,⟨0,0⟩,⟨-3680824815286,10071778299489⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51
theorem wholeAccepted51 : StepValid wholeStep51.shape wholeBoxes51 wholeStep51.proposed := by
  dsimp only [StepValid,wholeStep51]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep52 : Instruction 40 := ⟨.mul 1 0,⟨⟨157109282126,186552458889⟩,⟨0,0⟩,⟨1579611272520,3147090958654⟩,⟨0,0⟩,⟨0,0⟩,⟨-57120147418358,68814753429734⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52
theorem wholeAccepted52 : StepValid wholeStep52.shape wholeBoxes52 wholeStep52.proposed := by
  dsimp only [StepValid,wholeStep52]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep53 : Instruction 40 := ⟨.neg 2,⟨⟨-185228853248,-156315418624⟩,⟨0,0⟩,⟨-3080733557378,-1555826750476⟩,⟨0,0⟩,⟨0,0⟩,⟨-65177238455450,56413115428206⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53
theorem wholeAccepted53 : StepValid wholeStep53.shape wholeBoxes53 wholeStep53.proposed := by
  dsimp only [StepValid,wholeStep53]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep54 : Instruction 40 := ⟨.add 1 0,⟨⟨-28119571122,30237040265⟩,⟨0,0⟩,⟨-1501122284858,1591264208178⟩,⟨0,0⟩,⟨0,0⟩,⟨-122297385873808,125227868857940⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54
theorem wholeAccepted54 : StepValid wholeStep54.shape wholeBoxes54 wholeStep54.proposed := by
  dsimp only [StepValid,wholeStep54]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 36 0,⟨⟨-19606081907,21082465500⟩,⟨0,0⟩,⟨-1061114005599,1122951080948⟩,⟨0,0⟩,⟨0,0⟩,⟨-87821571949135,89706560808651⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55
theorem wholeAccepted55 : StepValid wholeStep55.shape wholeBoxes55 wholeStep55.proposed := by
  dsimp only [StepValid,wholeStep55]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep56 : Instruction 40 := ⟨.add 6 0,⟨⟨-148493818900,-87291299519⟩,⟨0,0⟩,⟨-3285455560850,81427445717⟩,⟨0,0⟩,⟨0,0⟩,⟨-141498013277310,136515908552375⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56
theorem wholeAccepted56 : StepValid wholeStep56.shape wholeBoxes56 wholeStep56.proposed := by
  dsimp only [StepValid,wholeStep56]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep57 : Instruction 40 := ⟨.mul 0 10,⟨⟨-325549070289,-189742472276⟩,⟨0,0⟩,⟨-7287649297254,280592037914⟩,⟨0,0⟩,⟨0,0⟩,⟨-322414573112369,312506364244091⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57
theorem wholeAccepted57 : StepValid wholeStep57.shape wholeBoxes57 wholeStep57.proposed := by
  dsimp only [StepValid,wholeStep57]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 54 51,⟨⟨312630837248,370457706496⟩,⟨0,0⟩,⟨3111653500952,6161467114756⟩,⟨0,0⟩,⟨0,0⟩,⟨-112826230856412,130354476910900⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58
theorem wholeAccepted58 : StepValid wholeStep58.shape wholeBoxes58 wholeStep58.proposed := by
  dsimp only [StepValid,wholeStep58]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep59 : Instruction 40 := ⟨.mul 0 7,⟨⟨314218564252,373104917778⟩,⟨0,0⟩,⟨3159222545040,6294181917306⟩,⟨0,0⟩,⟨0,0⟩,⟨-114240294836713,137629506859467⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59
theorem wholeAccepted59 : StepValid wholeStep59.shape wholeBoxes59 wholeStep59.proposed := by
  dsimp only [StepValid,wholeStep59]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 57 53,⟨⟨234473127936,277843279872⟩,⟨0,0⟩,⟨2333740125714,4621100336067⟩,⟨0,0⟩,⟨0,0⟩,⟨-84619673142309,97765857683175⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60
theorem wholeAccepted60 : StepValid wholeStep60.shape wholeBoxes60 wholeStep60.proposed := by
  dsimp only [StepValid,wholeStep60]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 39 35,⟨⟨759481217922,762167128529⟩,⟨0,0⟩,⟨-125610018303,53077208007⟩,⟨0,0⟩,⟨0,0⟩,⟨-8717283739626,7476520732342⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61
theorem wholeAccepted61 : StepValid wholeStep61.shape wholeBoxes61 wholeStep61.proposed := by
  dsimp only [StepValid,wholeStep61]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep62 : Instruction 40 := ⟨.inv 0,⟨⟨1586168931147,1591778428600⟩,⟨0,0⟩,⟨-111243244418,263263018009⟩,⟨0,0⟩,⟨0,0⟩,⟨-15706656956318,18357427186812⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62
theorem wholeAccepted62 : StepValid wholeStep62.shape wholeBoxes62 wholeStep62.proposed := by
  dsimp only [StepValid,wholeStep62]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep63 : Instruction 40 := ⟨.mul 2 0,⟨⟨338253804075,402237619194⟩,⟨0,0⟩,⟨3338571234858,6756557642567⟩,⟨0,0⟩,⟨0,0⟩,⟨-127409195389200,148388790635403⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63
theorem wholeAccepted63 : StepValid wholeStep63.shape wholeBoxes63 wholeStep63.proposed := by
  dsimp only [StepValid,wholeStep63]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep64 : Instruction 40 := ⟨.neg 0,⟨⟨-402237619194,-338253804075⟩,⟨0,0⟩,⟨-6756557642567,-3338571234858⟩,⟨0,0⟩,⟨0,0⟩,⟨-148388790635403,127409195389200⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64
theorem wholeAccepted64 : StepValid wholeStep64.shape wholeBoxes64 wholeStep64.proposed := by
  dsimp only [StepValid,wholeStep64]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep65 : Instruction 40 := ⟨.add 5 0,⟨⟨-88019054942,34851113703⟩,⟨0,0⟩,⟨-3597335097527,2955610682448⟩,⟨0,0⟩,⟨0,0⟩,⟨-262629085472116,265038702248667⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65
theorem wholeAccepted65 : StepValid wholeStep65.shape wholeBoxes65 wholeStep65.proposed := by
  dsimp only [StepValid,wholeStep65]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 18 0,⟨⟨-186796859245,73962150414⟩,⟨0,0⟩,⟨-7784728805078,6477439228437⟩,⟨0,0⟩,⟨0,0⟩,⟨-586109663737106,595074496621039⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66
theorem wholeAccepted66 : StepValid wholeStep66.shape wholeBoxes66 wholeStep66.proposed := by
  dsimp only [StepValid,wholeStep66]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep67 : Instruction 40 := ⟨.add 9 0,⟨⟨-512345929534,-115780321862⟩,⟨0,0⟩,⟨-15072378102332,6758031266351⟩,⟨0,0⟩,⟨0,0⟩,⟨-908524236849475,907580860865130⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67
theorem wholeAccepted67 : StepValid wholeStep67.shape wholeBoxes67 wholeStep67.proposed := by
  dsimp only [StepValid,wholeStep67]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 61 29,⟨⟨108190983122,128582334931⟩,⟨0,0⟩,⟨1064343143178,2151285076304⟩,⟨0,0⟩,⟨0,0⟩,⟨-40711316801402,46811857104829⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68
theorem wholeAccepted68 : StepValid wholeStep68.shape wholeBoxes68 wholeStep68.proposed := by
  dsimp only [StepValid,wholeStep68]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 27 25,⟨⟨524607203602,528324318849⟩,⟨0,0⟩,⟨-174412062710,73960750718⟩,⟨0,0⟩,⟨0,0⟩,⟨-12154567815276,10440066574808⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69
theorem wholeAccepted69 : StepValid wholeStep69.shape wholeBoxes69 wholeStep69.proposed := by
  dsimp only [StepValid,wholeStep69]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨2288226713183,2304439991129⟩,⟨0,0⟩,⟨-324887097544,766139178961⟩,⟨0,0⟩,⟨0,0⟩,⟨-46076064561710,53900746660204⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70
theorem wholeAccepted70 : StepValid wholeStep70.shape wholeBoxes70 wholeStep70.proposed := by
  dsimp only [StepValid,wholeStep70]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 2 0,⟨⟨225159508504,269492624983⟩,⟨0,0⟩,⟨2177042616150,4598422789666⟩,⟨0,0⟩,⟨0,0⟩,⟨-91985570200733,107413295150419⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71
theorem wholeAccepted71 : StepValid wholeStep71.shape wholeBoxes71 wholeStep71.proposed := by
  dsimp only [StepValid,wholeStep71]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 65 39,⟨⟨12180853768,14443416873⟩,⟨0,0⟩,⟨121237548435,240223476320⟩,⟨0,0⟩,⟨0,0⟩,⟨-4398872685924,5082264501958⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72
theorem wholeAccepted72 : StepValid wholeStep72.shape wholeBoxes72 wholeStep72.proposed := by
  dsimp only [StepValid,wholeStep72]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep73 : Instruction 40 := ⟨.add 54 0,⟨⟨763222088463,781066596793⟩,⟨0,0⟩,⟨-405006023848,581834412912⟩,⟨0,0⟩,⟨0,0⟩,⟨-41771695572622,39383262731956⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73
theorem wholeAccepted73 : StepValid wholeStep73.shape wholeBoxes73 wholeStep73.proposed := by
  dsimp only [StepValid,wholeStep73]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 0 0,⟨⟨529787900011,554850911273⟩,⟨0,0⟩,⟨-575413062922,826642326120⟩,⟨0,0⟩,⟨0,0⟩,⟨-59775852687914,56569628717086⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74
theorem wholeAccepted74 : StepValid wholeStep74.shape wholeBoxes74 wholeStep74.proposed := by
  dsimp only [StepValid,wholeStep74]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep75 : Instruction 40 := ⟨.mul 7 0,⟨⟨-258547157400,-55787507864⟩,⟨0,0⟩,⟨-7991229318668,3678460731986⟩,⟨0,0⟩,⟨0,0⟩,⟨-507495907302048,501626044763536⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75
theorem wholeAccepted75 : StepValid wholeStep75.shape wholeBoxes75 wholeStep75.proposed := by
  dsimp only [StepValid,wholeStep75]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep76 : Instruction 40 := ⟨.mul 79 28,⟨⟨4519668877284,4666837627528⟩,⟨0,0⟩,⟨-5120304403178,3756242199868⟩,⟨0,0⟩,⟨0,0⟩,⟨-395950251841590,374398815529158⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76
theorem wholeAccepted76 : StepValid wholeStep76.shape wholeBoxes76 wholeStep76.proposed := by
  dsimp only [StepValid,wholeStep76]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 0 3,⟨⟨3137312087057,3315209126885⟩,⟨0,0⟩,⟨-5356374537046,5137919327309⟩,⟨0,0⟩,⟨0,0⟩,⟨-463991068483582,437100173304531⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77
theorem wholeAccepted77 : StepValid wholeStep77.shape wholeBoxes77 wholeStep77.proposed := by
  dsimp only [StepValid,wholeStep77]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep78 : Instruction 40 := ⟨.add 45 29,⟨⟨78524132704,93181425728⟩,⟨0,0⟩,⟨-1592965687833,-761449887527⟩,⟨0,0⟩,⟨0,0⟩,⟨-37520648737511,32586642741705⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78
theorem wholeAccepted78 : StepValid wholeStep78.shape wholeBoxes78 wholeStep78.proposed := by
  dsimp only [StepValid,wholeStep78]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 1 0,⟨⟨224058304100,280957386194⟩,⟨0,0⟩,⟨-5256996703987,-1737268837707⟩,⟨0,0⟩,⟨0,0⟩,⟨-167340844944298,150818045279910⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79
theorem wholeAccepted79 : StepValid wholeStep79.shape wholeBoxes79 wholeStep79.proposed := by
  dsimp only [StepValid,wholeStep79]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep80 : Instruction 40 := ⟨.add 4 0,⟨⟨-34488853300,225169878330⟩,⟨0,0⟩,⟨-13248226022655,1941191894279⟩,⟨0,0⟩,⟨0,0⟩,⟨-674836752246346,652444090043446⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80
theorem wholeAccepted80 : StepValid wholeStep80.shape wholeBoxes80 wholeStep80.proposed := by
  dsimp only [StepValid,wholeStep80]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep81 : Instruction 40 := ⟨.mul 81 81,⟨⟨26279603337,26313611232⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81
theorem wholeAccepted81 : StepValid wholeStep81.shape wholeBoxes81 wholeStep81.proposed := by
  dsimp only [StepValid,wholeStep81]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep82 : Instruction 40 := ⟨.neg 0,⟨⟨-26313611232,-26279603337⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82
theorem wholeAccepted82 : StepValid wholeStep82.shape wholeBoxes82 wholeStep82.proposed := by
  dsimp only [StepValid,wholeStep82]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep83 : Instruction 40 := ⟨.add 81 0,⟨⟨1073198016544,1073232024439⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83
theorem wholeAccepted83 : StepValid wholeStep83.shape wholeBoxes83 wholeStep83.proposed := by
  dsimp only [StepValid,wholeStep83]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep84 : Instruction 40 := ⟨.inv 0,⟨⟨1126434724351,1126470419232⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes85 := wholeStep84.proposed :: wholeBoxes84
theorem wholeAccepted84 : StepValid wholeStep84.shape wholeBoxes84 wholeStep84.proposed := by
  dsimp only [StepValid,wholeStep84]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep85 : Instruction 40 := ⟨.mul 13 0,⟨⟨230672857375,276100281776⟩,⟨0,0⟩,⟨2230350582270,4711170957018⟩,⟨0,0⟩,⟨0,0⟩,⟨-94240953173826,110046948629300⟩⟩⟩
noncomputable def wholeBoxes86 := wholeStep85.proposed :: wholeBoxes85
theorem wholeAccepted85 : StepValid wholeStep85.shape wholeBoxes85 wholeStep85.proposed := by
  dsimp only [StepValid,wholeStep85]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep86 : Instruction 40 := ⟨.add 5 0,⟨⟨196184004075,501270160106⟩,⟨0,0⟩,⟨-11017875440385,6652362851297⟩,⟨0,0⟩,⟨0,0⟩,⟨-769077705420172,762491038672746⟩⟩⟩
noncomputable def wholeBoxes87 := wholeStep86.proposed :: wholeBoxes86
theorem wholeAccepted86 : StepValid wholeStep86.shape wholeBoxes86 wholeStep86.proposed := by
  dsimp only [StepValid,wholeStep86]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep87 : Instruction 40 := ⟨.mul 0 68,⟨⟨134007019958,349505466274⟩,⟨0,0⟩,⟨-7922016180423,4794032913126⟩,⟨0,0⟩,⟨0,0⟩,⟨-560116250693415,557823608563729⟩⟩⟩
noncomputable def wholeBoxes88 := wholeStep87.proposed :: wholeBoxes87
theorem wholeAccepted87 : StepValid wholeStep87.shape wholeBoxes87 wholeStep87.proposed := by
  dsimp only [StepValid,wholeStep87]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep88 : Instruction 40 := ⟨.mul 0 69,⟨⟨91535910293,243689093581⟩,⟨0,0⟩,⟨-5690823164259,3451179187487⟩,⟨0,0⟩,⟨0,0⟩,⟨-407337758456041,407423354045527⟩⟩⟩
noncomputable def wholeBoxes89 := wholeStep88.proposed :: wholeBoxes88
theorem wholeAccepted88 : StepValid wholeStep88.shape wholeBoxes88 wholeStep88.proposed := by
  dsimp only [StepValid,wholeStep88]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep89 : Instruction 40 := ⟨.mul 90 63,⟨⟨525566075807,526351008795⟩,⟨0,0⟩,⟨38187498231,89788459062⟩,⟨0,0⟩,⟨0,0⟩,⟨-1259435346754,3414308469444⟩⟩⟩
noncomputable def wholeBoxes90 := wholeStep89.proposed :: wholeBoxes89
theorem wholeAccepted89 : StepValid wholeStep89.shape wholeBoxes89 wholeStep89.proposed := by
  dsimp only [StepValid,wholeStep89]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep90 : Instruction 40 := ⟨.inv 0,⟨⟨2296805362608,2300235641653⟩,⟨0,0⟩,⟨-392975542470,-166636425609⟩,⟨0,0⟩,⟨0,0⟩,⟨-14919163387354,5646421156884⟩⟩⟩
noncomputable def wholeBoxes91 := wholeStep90.proposed :: wholeBoxes90
theorem wholeAccepted90 : StepValid wholeStep90.shape wholeBoxes90 wholeStep90.proposed := by
  dsimp only [StepValid,wholeStep90]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 2 0,⟨⟨191212320380,509810287019⟩,⟨0,0⟩,⟨-11992595433656,7206174046481⟩,⟨0,0⟩,⟨0,0⟩,⟨-857945383924022,857670238575502⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91
theorem wholeAccepted91 : StepValid wholeStep91.shape wholeBoxes91 wholeStep91.proposed := by
  dsimp only [StepValid,wholeStep91]
  exact ⟨by decide,by decide⟩
noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91]
theorem wholeAccepted : Accepted wholeProgram wholeInitial :=
  ⟨wholeAccepted0,⟨wholeAccepted1,⟨wholeAccepted2,⟨wholeAccepted3,⟨wholeAccepted4,⟨wholeAccepted5,⟨wholeAccepted6,⟨wholeAccepted7,⟨wholeAccepted8,⟨wholeAccepted9,⟨wholeAccepted10,⟨wholeAccepted11,⟨wholeAccepted12,⟨wholeAccepted13,⟨wholeAccepted14,⟨wholeAccepted15,⟨wholeAccepted16,⟨wholeAccepted17,⟨wholeAccepted18,⟨wholeAccepted19,⟨wholeAccepted20,⟨wholeAccepted21,⟨wholeAccepted22,⟨wholeAccepted23,⟨wholeAccepted24,⟨wholeAccepted25,⟨wholeAccepted26,⟨wholeAccepted27,⟨wholeAccepted28,⟨wholeAccepted29,⟨wholeAccepted30,⟨wholeAccepted31,⟨wholeAccepted32,⟨wholeAccepted33,⟨wholeAccepted34,⟨wholeAccepted35,⟨wholeAccepted36,⟨wholeAccepted37,⟨wholeAccepted38,⟨wholeAccepted39,⟨wholeAccepted40,⟨wholeAccepted41,⟨wholeAccepted42,⟨wholeAccepted43,⟨wholeAccepted44,⟨wholeAccepted45,⟨wholeAccepted46,⟨wholeAccepted47,⟨wholeAccepted48,⟨wholeAccepted49,⟨wholeAccepted50,⟨wholeAccepted51,⟨wholeAccepted52,⟨wholeAccepted53,⟨wholeAccepted54,⟨wholeAccepted55,⟨wholeAccepted56,⟨wholeAccepted57,⟨wholeAccepted58,⟨wholeAccepted59,⟨wholeAccepted60,⟨wholeAccepted61,⟨wholeAccepted62,⟨wholeAccepted63,⟨wholeAccepted64,⟨wholeAccepted65,⟨wholeAccepted66,⟨wholeAccepted67,⟨wholeAccepted68,⟨wholeAccepted69,⟨wholeAccepted70,⟨wholeAccepted71,⟨wholeAccepted72,⟨wholeAccepted73,⟨wholeAccepted74,⟨wholeAccepted75,⟨wholeAccepted76,⟨wholeAccepted77,⟨wholeAccepted78,⟨wholeAccepted79,⟨wholeAccepted80,⟨wholeAccepted81,⟨wholeAccepted82,⟨wholeAccepted83,⟨wholeAccepted84,⟨wholeAccepted85,⟨wholeAccepted86,⟨wholeAccepted87,⟨wholeAccepted88,⟨wholeAccepted89,⟨wholeAccepted90,⟨wholeAccepted91,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
noncomputable def whole_output : DyadicBivariateJetEnclosure 40 := ⟨⟨191212320380,509810287019⟩,⟨0,0⟩,⟨-11992595433656,7206174046481⟩,⟨0,0⟩,⟨0,0⟩,⟨-857945383924022,857670238575502⟩⟩
theorem whole_output_eq : (finalBoxes wholeProgram wholeInitial).getD 0 (zeroBox 40)=whole_output := rfl
open GeneralCK.Reflection GeneralCK.Reflection.SmallRatio GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed
theorem sameShape : shapes centerProgram=shapes wholeProgram := by decide
theorem scalar_program (a e r : ℝ) :
    (evalRealProgram wholeProgram [a,e,r,2]).getD 0 0=ReflectionMidpointKernel.scalarCore a e r := rfl
attribute [local irreducible] wholeProgram centerProgram
noncomputable def reflection_log_0_out : DyadicInterval 64 := ⟨-12786308645202662930,-12786308645202655416⟩
theorem reflection_log_0_checked : DyadicFastLog.check 1 2 1 16 reflection_log_0_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointNextBandFamily.Endpoints0046.sharedTwo_eq]
  decide
theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := DyadicFastLog.check_sound reflection_log_0_checked
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1):ℝ)=((1 / 2):ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [he]
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_0_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_1_out : DyadicInterval 64 := ⟨-2653390181757751383,-2653390181757751338⟩
theorem reflection_log_1_checked : DyadicFastLog.check 10000 11547 0 16 reflection_log_1_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointNextBandFamily.Endpoints0046.sharedTwo_eq]
  decide
theorem reflection_log_1 : Bounds (143840569 / 1000000000) (14384057 / 100000000) (Real.log (11547 / 10000)) := by
  have h := DyadicFastLog.check_sound reflection_log_1_checked
  have he : Real.log (11547 / 10000) = -Real.log (10000 / 11547) := by
    rw [show ((11547 / 10000):ℝ)=((10000 / 11547):ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [he]
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_1_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_2_out : DyadicInterval 64 := ⟨-3100227786151241053,-3100227786151241006⟩
theorem reflection_log_2_checked : DyadicFastLog.check 8453 10000 0 16 reflection_log_2_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointNextBandFamily.Endpoints0046.sharedTwo_eq]
  decide
theorem reflection_log_2 : Bounds (-84031843 / 500000000) (-33612737 / 200000000) (Real.log (8453 / 10000)) := by
  have h := DyadicFastLog.check_sound reflection_log_2_checked
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_2_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_3_out : DyadicInterval 64 := ⟨-2651792576935057079,-2651792576935057034⟩
theorem reflection_log_3_checked : DyadicFastLog.check 5000 5773 0 16 reflection_log_3_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointNextBandFamily.Endpoints0046.sharedTwo_eq]
  decide
theorem reflection_log_3 : Bounds (143753963 / 1000000000) (35938491 / 250000000) (Real.log (5773 / 5000)) := by
  have h := DyadicFastLog.check_sound reflection_log_3_checked
  have he : Real.log (5773 / 5000) = -Real.log (5000 / 5773) := by
    rw [show ((5773 / 5000):ℝ)=((5000 / 5773):ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [he]
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_3_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_4_out : DyadicInterval 64 := ⟨-3098045643358880399,-3098045643358880352⟩
theorem reflection_log_4_checked : DyadicFastLog.check 4227 5000 0 16 reflection_log_4_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointNextBandFamily.Endpoints0046.sharedTwo_eq]
  decide
theorem reflection_log_4 : Bounds (-167945391 / 1000000000) (-16794539 / 100000000) (Real.log (4227 / 5000)) := by
  have h := DyadicFastLog.check_sound reflection_log_4_checked
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_4_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_5_out : DyadicInterval 64 := ⟨-240984498099499945,-240984498099499898⟩
theorem reflection_log_5_checked : DyadicFastLog.check 2000000 2026299 0 16 reflection_log_5_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointNextBandFamily.Endpoints0046.sharedTwo_eq]
  decide
theorem reflection_log_5 : Bounds (2612759 / 200000000) (3265949 / 250000000) (Real.log (2026299 / 2000000)) := by
  have h := DyadicFastLog.check_sound reflection_log_5_checked
  have he : Real.log (2026299 / 2000000) = -Real.log (2000000 / 2026299) := by
    rw [show ((2026299 / 2000000):ℝ)=((2000000 / 2026299):ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [he]
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_5_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_6_out : DyadicInterval 64 := ⟨-244174388420392683,-244174388420392636⟩
theorem reflection_log_6_checked : DyadicFastLog.check 1973701 2000000 0 16 reflection_log_6_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointNextBandFamily.Endpoints0046.sharedTwo_eq]
  decide
theorem reflection_log_6 : Bounds (-13236721 / 1000000000) (-165459 / 12500000) (Real.log (1973701 / 2000000)) := by
  have h := DyadicFastLog.check_sound reflection_log_6_checked
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_6_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_7_out : DyadicInterval 64 := ⟨-230479909787566609,-230479909787566564⟩
theorem reflection_log_7_checked : DyadicFastLog.check 25000000000 25314318033 0 16 reflection_log_7_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointNextBandFamily.Endpoints0046.sharedTwo_eq]
  decide
theorem reflection_log_7 : Bounds (624717 / 50000000) (12494341 / 1000000000) (Real.log (25314318033 / 25000000000)) := by
  have h := DyadicFastLog.check_sound reflection_log_7_checked
  have he : Real.log (25314318033 / 25000000000) = -Real.log (25000000000 / 25314318033) := by
    rw [show ((25314318033 / 25000000000):ℝ)=((25000000000 / 25314318033):ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [he]
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_7_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_8_out : DyadicInterval 64 := ⟨-233396078382436711,-233396078382436666⟩
theorem reflection_log_8_checked : DyadicFastLog.check 24685681967 25000000000 0 16 reflection_log_8_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointNextBandFamily.Endpoints0046.sharedTwo_eq]
  decide
theorem reflection_log_8 : Bounds (-12652427 / 1000000000) (-6326213 / 500000000) (Real.log (24685681967 / 25000000000)) := by
  have h := DyadicFastLog.check_sound reflection_log_8_checked
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_8_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
theorem entropy_bound {a z : ℝ} (ha : Bounds (773 / 5000) (1547 / 10000) a) (hz : Bounds (406621 / 5000000) (17 / 200) z) :
  Bounds (171774208257 / 250000000000) (42944271181 / 62500000000) ((biasE a+biasE (a*z))/2) := by
  let x0 : ℝ := Real.log (2 / 1)
  have hx0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x0 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x1 : ℝ := (1 / 1)+(1547 / 10000)
  have hx1 : Bounds (11547 / 10000) (11547 / 10000) x1 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1547 / 10000) : ℝ)) <;> norm_num
  let x2 : ℝ := (1 / 1)+(1547 / 10000)
  have hx2 : Bounds (11547 / 10000) (11547 / 10000) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1547 / 10000) : ℝ)) <;> norm_num
  let x3 : ℝ := Real.log x2
  have hx3 : Bounds (143840569 / 1000000000) (14384057 / 100000000) x3 := by
    exact bounds_log hx2 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x4 : ℝ := x1*x3
  have hx4 : Bounds (648799629 / 3906250000) (166092706179 / 1000000000000) x4 := by
    apply bounds_mul hx1 hx3 <;> norm_num
  let x5 : ℝ := -(1547 / 10000)
  have hx5 : Bounds (-1547 / 10000) (-1547 / 10000) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1547 / 10000) : ℝ))
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (8453 / 10000) (8453 / 10000) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-(1547 / 10000)
  have hx7 : Bounds (8453 / 10000) (8453 / 10000) x7 := by
    exact hx6
  let x8 : ℝ := -(1547 / 10000)
  have hx8 : Bounds (-1547 / 10000) (-1547 / 10000) x8 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1547 / 10000) : ℝ))
  let x9 : ℝ := (1 / 1)+x8
  have hx9 : Bounds (8453 / 10000) (8453 / 10000) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx8 <;> norm_num
  let x10 : ℝ := (1 / 1)-(1547 / 10000)
  have hx10 : Bounds (8453 / 10000) (8453 / 10000) x10 := by
    exact hx9
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (-84031843 / 500000000) (-33612737 / 200000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x12 : ℝ := x7*x11
  have hx12 : Bounds (-8879014611 / 62500000000) (-14206423293 / 100000000000) x12 := by
    apply bounds_mul hx7 hx11 <;> norm_num
  let x13 : ℝ := x4+x12
  have hx13 : Bounds (1501779453 / 62500000000) (24028473249 / 1000000000000) x13 := by
    apply bounds_add hx4 hx12 <;> norm_num
  let x14 : ℝ := (2 / 1)⁻¹
  have hx14 : Bounds (1 / 2) (1 / 2) x14 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x15 : ℝ := x13*x14
  have hx15 : Bounds (1501779453 / 125000000000) (96113893 / 8000000000) x15 := by
    apply bounds_mul hx13 hx14 <;> norm_num
  let x16 : ℝ := x13/(2 / 1)
  have hx16 : Bounds (1501779453 / 125000000000) (96113893 / 8000000000) x16 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx15
  let x17 : ℝ := -x16
  have hx17 : Bounds (-96113893 / 8000000000) (-1501779453 / 125000000000) x17 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx16
  let x18 : ℝ := x0+x17
  have hx18 : Bounds (5449063547 / 8000000000) (21285404543 / 31250000000) x18 := by
    apply bounds_add hx0 hx17 <;> norm_num
  let x19 : ℝ := x0-x16
  have hx19 : Bounds (5449063547 / 8000000000) (21285404543 / 31250000000) x19 := by
    exact hx18
  let x20 : ℝ := biasE (1547 / 10000)
  have hx20 : Bounds (5449063547 / 8000000000) (21285404543 / 31250000000) x20 := by
    simpa +zetaDelta only [biasE, div_one] using hx19
  let x21 : ℝ := Real.log (2 / 1)
  have hx21 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x21 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x22 : ℝ := (1 / 1)+(773 / 5000)
  have hx22 : Bounds (5773 / 5000) (5773 / 5000) x22 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((773 / 5000) : ℝ)) <;> norm_num
  let x23 : ℝ := (1 / 1)+(773 / 5000)
  have hx23 : Bounds (5773 / 5000) (5773 / 5000) x23 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((773 / 5000) : ℝ)) <;> norm_num
  let x24 : ℝ := Real.log x23
  have hx24 : Bounds (143753963 / 1000000000) (35938491 / 250000000) x24 := by
    exact bounds_log hx23 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x25 : ℝ := x22*x24
  have hx25 : Bounds (165978325679 / 1000000000000) (33195665367 / 200000000000) x25 := by
    apply bounds_mul hx22 hx24 <;> norm_num
  let x26 : ℝ := -(773 / 5000)
  have hx26 : Bounds (-773 / 5000) (-773 / 5000) x26 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((773 / 5000) : ℝ))
  let x27 : ℝ := (1 / 1)+x26
  have hx27 : Bounds (4227 / 5000) (4227 / 5000) x27 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx26 <;> norm_num
  let x28 : ℝ := (1 / 1)-(773 / 5000)
  have hx28 : Bounds (4227 / 5000) (4227 / 5000) x28 := by
    exact hx27
  let x29 : ℝ := -(773 / 5000)
  have hx29 : Bounds (-773 / 5000) (-773 / 5000) x29 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((773 / 5000) : ℝ))
  let x30 : ℝ := (1 / 1)+x29
  have hx30 : Bounds (4227 / 5000) (4227 / 5000) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx29 <;> norm_num
  let x31 : ℝ := (1 / 1)-(773 / 5000)
  have hx31 : Bounds (4227 / 5000) (4227 / 5000) x31 := by
    exact hx30
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (-167945391 / 1000000000) (-16794539 / 100000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x33 : ℝ := x28*x32
  have hx33 : Bounds (-8873814597 / 62500000000) (-70990516353 / 500000000000) x33 := by
    apply bounds_mul hx28 hx32 <;> norm_num
  let x34 : ℝ := x25+x33
  have hx34 : Bounds (23997292127 / 1000000000000) (23997294129 / 1000000000000) x34 := by
    apply bounds_add hx25 hx33 <;> norm_num
  let x35 : ℝ := (2 / 1)⁻¹
  have hx35 : Bounds (1 / 2) (1 / 2) x35 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x36 : ℝ := x34*x35
  have hx36 : Bounds (11998646063 / 1000000000000) (2399729413 / 200000000000) x36 := by
    apply bounds_mul hx34 hx35 <;> norm_num
  let x37 : ℝ := x34/(2 / 1)
  have hx37 : Bounds (11998646063 / 1000000000000) (2399729413 / 200000000000) x37 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx36
  let x38 : ℝ := -x37
  have hx38 : Bounds (-2399729413 / 200000000000) (-11998646063 / 1000000000000) x38 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx37
  let x39 : ℝ := x21+x38
  have hx39 : Bounds (136229706587 / 200000000000) (681148534937 / 1000000000000) x39 := by
    apply bounds_add hx21 hx38 <;> norm_num
  let x40 : ℝ := x21-x37
  have hx40 : Bounds (136229706587 / 200000000000) (681148534937 / 1000000000000) x40 := by
    exact hx39
  let x41 : ℝ := biasE (773 / 5000)
  have hx41 : Bounds (136229706587 / 200000000000) (681148534937 / 1000000000000) x41 := by
    simpa +zetaDelta only [biasE, div_one] using hx40
  let x42 : ℝ := biasE a
  have hx42 : Bounds (5449063547 / 8000000000) (681148534937 / 1000000000000) x42 := by
    exact bounds_biasE ha (by norm_num) (by norm_num) hx20.1 hx41.2
  let x43 : ℝ := a*z
  have hx43 : Bounds (314318033 / 25000000000) (26299 / 2000000) x43 := by
    apply bounds_mul ha hz <;> norm_num
  let x44 : ℝ := Real.log (2 / 1)
  have hx44 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x44 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x45 : ℝ := (1 / 1)+(26299 / 2000000)
  have hx45 : Bounds (2026299 / 2000000) (2026299 / 2000000) x45 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((26299 / 2000000) : ℝ)) <;> norm_num
  let x46 : ℝ := (1 / 1)+(26299 / 2000000)
  have hx46 : Bounds (2026299 / 2000000) (2026299 / 2000000) x46 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((26299 / 2000000) : ℝ)) <;> norm_num
  let x47 : ℝ := Real.log x46
  have hx47 : Bounds (2612759 / 200000000) (3265949 / 250000000) x47 := by
    exact bounds_log hx46 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x48 : ℝ := x45*x47
  have hx48 : Bounds (3308894343 / 250000000000) (6617789193 / 500000000000) x48 := by
    apply bounds_mul hx45 hx47 <;> norm_num
  let x49 : ℝ := -(26299 / 2000000)
  have hx49 : Bounds (-26299 / 2000000) (-26299 / 2000000) x49 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((26299 / 2000000) : ℝ))
  let x50 : ℝ := (1 / 1)+x49
  have hx50 : Bounds (1973701 / 2000000) (1973701 / 2000000) x50 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx49 <;> norm_num
  let x51 : ℝ := (1 / 1)-(26299 / 2000000)
  have hx51 : Bounds (1973701 / 2000000) (1973701 / 2000000) x51 := by
    exact hx50
  let x52 : ℝ := -(26299 / 2000000)
  have hx52 : Bounds (-26299 / 2000000) (-26299 / 2000000) x52 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((26299 / 2000000) : ℝ))
  let x53 : ℝ := (1 / 1)+x52
  have hx53 : Bounds (1973701 / 2000000) (1973701 / 2000000) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx52 <;> norm_num
  let x54 : ℝ := (1 / 1)-(26299 / 2000000)
  have hx54 : Bounds (1973701 / 2000000) (1973701 / 2000000) x54 := by
    exact hx53
  let x55 : ℝ := Real.log x54
  have hx55 : Bounds (-13236721 / 1000000000) (-165459 / 12500000) x55 := by
    exact bounds_log hx54 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x56 : ℝ := x51*x55
  have hx56 : Bounds (-6531332369 / 500000000000) (-10450131 / 800000000) x56 := by
    apply bounds_mul hx51 hx55 <;> norm_num
  let x57 : ℝ := x48+x56
  have hx57 : Bounds (86456317 / 500000000000) (43228659 / 250000000000) x57 := by
    apply bounds_add hx48 hx56 <;> norm_num
  let x58 : ℝ := (2 / 1)⁻¹
  have hx58 : Bounds (1 / 2) (1 / 2) x58 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x59 : ℝ := x57*x58
  have hx59 : Bounds (86456317 / 1000000000000) (43228659 / 500000000000) x59 := by
    apply bounds_mul hx57 hx58 <;> norm_num
  let x60 : ℝ := x57/(2 / 1)
  have hx60 : Bounds (86456317 / 1000000000000) (43228659 / 500000000000) x60 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx59
  let x61 : ℝ := -x60
  have hx61 : Bounds (-43228659 / 500000000000) (-86456317 / 1000000000000) x61 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx60
  let x62 : ℝ := x44+x61
  have hx62 : Bounds (346530361341 / 500000000000) (693060724683 / 1000000000000) x62 := by
    apply bounds_add hx44 hx61 <;> norm_num
  let x63 : ℝ := x44-x60
  have hx63 : Bounds (346530361341 / 500000000000) (693060724683 / 1000000000000) x63 := by
    exact hx62
  let x64 : ℝ := biasE (26299 / 2000000)
  have hx64 : Bounds (346530361341 / 500000000000) (693060724683 / 1000000000000) x64 := by
    simpa +zetaDelta only [biasE, div_one] using hx63
  let x65 : ℝ := Real.log (2 / 1)
  have hx65 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x65 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x66 : ℝ := (1 / 1)+(314318033 / 25000000000)
  have hx66 : Bounds (25314318033 / 25000000000) (25314318033 / 25000000000) x66 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((314318033 / 25000000000) : ℝ)) <;> norm_num
  let x67 : ℝ := (1 / 1)+(314318033 / 25000000000)
  have hx67 : Bounds (25314318033 / 25000000000) (25314318033 / 25000000000) x67 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((314318033 / 25000000000) : ℝ)) <;> norm_num
  let x68 : ℝ := Real.log x67
  have hx68 : Bounds (624717 / 50000000) (12494341 / 1000000000) x68 := by
    exact bounds_log hx67 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x69 : ℝ := x66*x68
  have hx69 : Bounds (6325713927 / 500000000000) (3162857217 / 250000000000) x69 := by
    apply bounds_mul hx66 hx68 <;> norm_num
  let x70 : ℝ := -(314318033 / 25000000000)
  have hx70 : Bounds (-314318033 / 25000000000) (-314318033 / 25000000000) x70 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((314318033 / 25000000000) : ℝ))
  let x71 : ℝ := (1 / 1)+x70
  have hx71 : Bounds (24685681967 / 25000000000) (24685681967 / 25000000000) x71 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx70 <;> norm_num
  let x72 : ℝ := (1 / 1)-(314318033 / 25000000000)
  have hx72 : Bounds (24685681967 / 25000000000) (24685681967 / 25000000000) x72 := by
    exact hx71
  let x73 : ℝ := -(314318033 / 25000000000)
  have hx73 : Bounds (-314318033 / 25000000000) (-314318033 / 25000000000) x73 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((314318033 / 25000000000) : ℝ))
  let x74 : ℝ := (1 / 1)+x73
  have hx74 : Bounds (24685681967 / 25000000000) (24685681967 / 25000000000) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx73 <;> norm_num
  let x75 : ℝ := (1 / 1)-(314318033 / 25000000000)
  have hx75 : Bounds (24685681967 / 25000000000) (24685681967 / 25000000000) x75 := by
    exact hx74
  let x76 : ℝ := Real.log x75
  have hx76 : Bounds (-12652427 / 1000000000) (-6326213 / 500000000) x76 := by
    exact bounds_log hx75 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x77 : ℝ := x72*x76
  have hx77 : Bounds (-6246675781 / 500000000000) (-12493350573 / 1000000000000) x77 := by
    apply bounds_mul hx72 hx76 <;> norm_num
  let x78 : ℝ := x69+x77
  have hx78 : Bounds (39519073 / 250000000000) (31615659 / 200000000000) x78 := by
    apply bounds_add hx69 hx77 <;> norm_num
  let x79 : ℝ := (2 / 1)⁻¹
  have hx79 : Bounds (1 / 2) (1 / 2) x79 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x80 : ℝ := x78*x79
  have hx80 : Bounds (39519073 / 500000000000) (19759787 / 250000000000) x80 := by
    apply bounds_mul hx78 hx79 <;> norm_num
  let x81 : ℝ := x78/(2 / 1)
  have hx81 : Bounds (39519073 / 500000000000) (19759787 / 250000000000) x81 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx80
  let x82 : ℝ := -x81
  have hx82 : Bounds (-19759787 / 250000000000) (-39519073 / 500000000000) x82 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx81
  let x83 : ℝ := x65+x82
  have hx83 : Bounds (173267035213 / 250000000000) (346534071427 / 500000000000) x83 := by
    apply bounds_add hx65 hx82 <;> norm_num
  let x84 : ℝ := x65-x81
  have hx84 : Bounds (173267035213 / 250000000000) (346534071427 / 500000000000) x84 := by
    exact hx83
  let x85 : ℝ := biasE (314318033 / 25000000000)
  have hx85 : Bounds (173267035213 / 250000000000) (346534071427 / 500000000000) x85 := by
    simpa +zetaDelta only [biasE, div_one] using hx84
  let x86 : ℝ := biasE x43
  have hx86 : Bounds (346530361341 / 500000000000) (346534071427 / 500000000000) x86 := by
    exact bounds_biasE hx43 (by norm_num) (by norm_num) hx64.1 hx85.2
  let x87 : ℝ := x42+x86
  have hx87 : Bounds (1374193666057 / 1000000000000) (1374216677791 / 1000000000000) x87 := by
    apply bounds_add hx42 hx86 <;> norm_num
  let x88 : ℝ := (2 / 1)⁻¹
  have hx88 : Bounds (1 / 2) (1 / 2) x88 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x89 : ℝ := x87*x88
  have hx89 : Bounds (171774208257 / 250000000000) (42944271181 / 62500000000) x89 := by
    apply bounds_mul hx87 hx88 <;> norm_num
  let x90 : ℝ := x87/(2 / 1)
  have hx90 : Bounds (171774208257 / 250000000000) (42944271181 / 62500000000) x90 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx89
  simpa +zetaDelta only [div_one] using hx90
noncomputable def inputJets (a e : ℝ) : List BivariateJet2 :=
  [BivariateJet2.const a,BivariateJet2.const e,BivariateJet2.coordinateZ id,BivariateJet2.const 2]

def constantBox (v : DyadicInterval 40) : DyadicBivariateJetEnclosure 40 :=
  ⟨v,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩

def inputBoxes (a e s : DyadicInterval 40) : List (DyadicBivariateJetEnclosure 40) :=
  [constantBox a,constantBox e,DyadicBivariateJetEnclosure.coordinateZ s,DyadicBivariateJetEnclosure.const 40 2]

theorem constant_contains {v : DyadicInterval 40} {x t : ℝ} (h : v.Contains x) :
    (constantBox v).Contains (BivariateJet2.const x) t := by
  simpa [constantBox,DyadicBivariateJetEnclosure.Contains,BivariateJet2.const,
    DyadicInterval.Contains,DyadicInterval.scale] using h

theorem inputs_contain {av ev sv : DyadicInterval 40} {a e s : ℝ}
    (ha : av.Contains a) (he : ev.Contains e) (hs : sv.Contains s) :
    RegistersContain (inputBoxes av ev sv) (inputJets a e) s := by
  exact ((((RegistersContain.nil 40 s).cons (DyadicBivariateJetEnclosure.contains_const 40 2 s)).cons
    (DyadicBivariateJetEnclosure.contains_coordinateZ (f := id) hs)).cons
    (constant_contains he)).cons (constant_contains ha)

theorem inputs_sound (a e : ℝ) (i : ℕ) (s : ℝ) :
    ((inputJets a e).getD i zeroJet).DirectionalSoundAt 0 1 s := by
  have hc (x : ℝ) : (BivariateJet2.const x).DirectionalSoundAt 0 1 s := by
    simpa only [BivariateJet2.DirectionalSoundAt,BivariateJet2.projection_const] using Jet2.soundAt_const x s
  have hv : (BivariateJet2.coordinateZ id).DirectionalSoundAt 0 1 s := by
    simpa [BivariateJet2.DirectionalSoundAt,BivariateJet2.projection,BivariateJet2.coordinateZ,
      Jet2.variableJet] using Jet2.soundAt_variable s
  have h : RegistersSound (inputJets a e) 0 1 s :=
    ((((RegistersSound.nil 0 1 s).cons (hc 2)).cons hv).cons (hc e)).cons (hc a)
  exact h i

noncomputable def outputJet (a e : ℝ) : Jet2 :=
  ((finalJets wholeProgram (inputJets a e)).getD 0 zeroJet).projection 0 1

theorem output_value (a e s : ℝ) : (outputJet a e).value s=PFormula a e s := by
  change ((finalJets wholeProgram (inputJets a e)).getD 0 zeroJet).value s=_
  rw [finalJet_value]
  change (evalRealProgram wholeProgram [a,e,s,2]).getD 0 0=_
  rw [scalar_program,ReflectionMidpointKernel.scalarCore_eq]

theorem center_inputs_eq : centerInitial=inputBoxes ⟨169984497654,170094448817⟩ ⟨755470957322,755483608159⟩ ⟨84992248827,85047224409⟩ := rfl
theorem whole_inputs_eq : wholeInitial=inputBoxes ⟨169984497654,170094448817⟩ ⟨755470957322,755483608159⟩ ⟨77763234752,92276238484⟩ := rfl
noncomputable def centerUpper : ℝ := (43768599383 / 137438953472)
noncomputable def secondUpper : ℝ := (428835119287751 / 549755813888)


theorem center_inputs {a z : ℝ} (ha : Bounds (773/5000) (1547/10000) a)
    (hz : Bounds (406621/5000000) (17/200) z) :
    RegistersContain centerInitial (inputJets a ((biasE a+biasE (a*z))/2)) (a/2) := by
  rw [center_inputs_eq]
  apply inputs_contain
  · norm_num [DyadicInterval.Contains,DyadicInterval.scale]
    constructor <;> linarith [ha.1,ha.2]
  · have h := entropy_bound ha hz
    norm_num [DyadicInterval.Contains,DyadicInterval.scale]
    constructor <;> linarith [h.1,h.2]
  · norm_num [DyadicInterval.Contains,DyadicInterval.scale]
    constructor <;> linarith [ha.1,ha.2]

theorem whole_inputs {a z s : ℝ} (ha : Bounds (773/5000) (1547/10000) a)
    (hz : Bounds (406621/5000000) (17/200) z) (hs : s∈Icc (a*(1-z)/2) (a*(1+z)/2)) :
    RegistersContain wholeInitial (inputJets a ((biasE a+biasE (a*z))/2)) s := by
  rw [whole_inputs_eq]
  apply inputs_contain
  · norm_num [DyadicInterval.Contains,DyadicInterval.scale]
    constructor <;> linarith [ha.1,ha.2]
  · have h := entropy_bound ha hz
    norm_num [DyadicInterval.Contains,DyadicInterval.scale]
    constructor <;> linarith [h.1,h.2]
  · have hb : a*z≤(1547/10000:ℝ)*(17/200) :=
      mul_le_mul ha.2 hz.2 (by linarith [hz.1]) (by norm_num)
    norm_num [DyadicInterval.Contains,DyadicInterval.scale]
    constructor <;> nlinarith [ha.1,ha.2,hs.1,hs.2]

theorem curvature_pos {a z : ℝ} (ha : Bounds (773/5000) (1547/10000) a)
    (hz : Bounds (406621/5000000) (17/200) z) : 0<curvature a (a*z) := by
  have ha0 : 0<a := by linarith [ha.1]
  have ha1 : a<1 := by linarith [ha.2]
  have hz0 : 0<z := by linarith [hz.1]
  have hz1 : z<1 := by linarith [hz.2]
  let e := (biasE a+biasE (a*z))/2
  have he0 : 0<e := by have h := entropy_bound ha hz; dsimp [e]; linarith [h.1]
  apply curvature_pos_of_midpoint_jet (j := outputJet a e) (p0 := centerUpper) (M := secondUpper)
    ha0 ha1 hz0 hz1
  · exact Accepted.preserves_soundOn wholeProgram (fun s hs => whole_inputs ha hz hs)
      (fun i s _ => inputs_sound a e i s) wholeAccepted 0
  · intro s hs
    have hs0 : 0<s := by nlinarith [hs.1,mul_pos ha0 (sub_pos.mpr hz1)]
    rw [output_value,← P_eq_formula ha0 ha1 he0 hs0]
  · have hh := (Accepted.encloses centerProgram (center_inputs ha hz) centerAccepted).2 0
    rw [center_output_eq,finalJets_eq_of_shapes_eq sameShape] at hh
    have hv := hh.1.2
    norm_num [center_output,DyadicInterval.scale] at hv
    change (1099511627776:ℝ)*(outputJet a e).value (a/2) ≤ _ at hv
    unfold centerUpper
    linarith
  · intro s hs
    have hh := (Accepted.encloses wholeProgram (whole_inputs ha hz hs) wholeAccepted).2 0
    rw [whole_output_eq] at hh
    have hv := hh.2.2.2.2.2.2
    norm_num [whole_output,DyadicInterval.scale] at hv
    have hproj : (outputJet a e).second s =
        ((finalJets wholeProgram (inputJets a e)).getD 0 zeroJet).secondZZ s := by
      simp [outputJet,BivariateJet2.projection]
    rw [hproj]
    unfold secondUpper
    change (1099511627776:ℝ)*((finalJets wholeProgram (inputJets a e)).getD 0 zeroJet).secondZZ s ≤ _ at hv
    linarith
  · have hb0 : 0≤a*z := (mul_pos ha0 hz0).le
    have hb : a*z≤(26299/2000000:ℝ) := by
      have h := mul_le_mul ha.2 hz.2 hz0.le (by norm_num : (0:ℝ)≤1547/10000)
      norm_num at h
      exact h
    have hb2 := mul_self_le_mul_self hb0 hb
    have hle : centerUpper+secondUpper*(a*z)^2/24 ≤
        centerUpper+secondUpper*(26299/2000000:ℝ)^2/24 := by
      unfold centerUpper secondUpper
      nlinarith
    apply hle.trans_lt
    exact lt_of_lt_of_le (by norm_num [centerUpper,secondUpper] :
      centerUpper+secondUpper*(26299/2000000:ℝ)^2/24 < 2*(773/5000:ℝ)/(1-(773/5000:ℝ)^2)^2)
      (LowRatioFamily.base_mono (by norm_num) ha.1 ha1)

#print axioms entropy_bound
#print axioms curvature_pos
end GeneralCK.Certificates.ReflectionMidpointNextBandFamily.Cell0046

end


