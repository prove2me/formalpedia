-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointFamily_Cell0421__3
-- name    : CK_GeneralCK_Certificates_Generated_MidpointFamily_Cell0421__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T12:09:04.364492+00:00
-- url     : https://prove2.me/theorems/c0508ba0-8df8-44d7-bea7-e51392b5a53d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointFamily.Cell0421 (+2 modules: GeneralCK.Certificates.Generated.MidpointFamily.Cell0422, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointFamily.Cell0421 (+2 modules: GeneralCK.Certificates.Generated.MidpointFamily.Cell0422, GeneralCK.Certificates.Generated.MidpointFamily.Cell0423)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointFamily.Cell0421 (+2 modules: GeneralCK.Certificates.Generated.MidpointFamily.Cell0422, GeneralCK.Certificates.Generated.MidpointFamily.Cell0423)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointFamily.Cell0421 (+2 modules: GeneralCK.Certificates.Generated.MidpointFamily.Cell0422, GeneralCK.Certificates.Generated.MidpointFamily.Cell0423) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointFamily/Cell0421 (+2 modules: GeneralCK/Certificates/Generated/MidpointFamily/Cell0422, GeneralCK/Certificates/Generated/MidpointFamily/Cell0423).lean)

import Definitions.Def_CK_GeneralCK_Certificates_DyadicFastLog
import Definitions.Def_CK_GeneralCK_Certificates_BivariateProvedProgram
import Definitions.Def_CK_GeneralCK_Certificates_ReflectionMidpointKernel
import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers
import Definitions.Def_CK_GeneralCK_ReflectionSmallRatioMidpointJet

-- ===== source module GeneralCK.Certificates.Generated.MidpointFamily.Cell0421 =====
section

namespace GeneralCK.Certificates.ReflectionMidpointFamily.Endpoints0421
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
noncomputable def out_w1 : DyadicInterval 40 := ⟨148780502976,148780503040⟩
theorem checked_w1 : DyadicFastLog.check 1099511627776 1258828070912 0 16 (lift40 out_w1.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w1 : out_w1.Contains (Real.log ((1258828070912:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w1
#print axioms endpoint_w1
noncomputable def out_w2 : DyadicInterval 40 := ⟨-172110830592,-172110830528⟩
theorem checked_w2 : DyadicFastLog.check 940195184640 1099511627776 0 16 (lift40 out_w2)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w2 : out_w2.Contains (Real.log ((940195184640:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w2
#print axioms endpoint_w2
noncomputable def out_w3 : DyadicInterval 40 := ⟨149036916416,149036916480⟩
theorem checked_w3 : DyadicFastLog.check 1099511627776 1259121672192 0 16 (lift40 out_w3.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w3 : out_w3.Contains (Real.log ((1259121672192:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w3
#print axioms endpoint_w3
noncomputable def out_w4 : DyadicInterval 40 := ⟨-172454236352,-172454236288⟩
theorem checked_w4 : DyadicFastLog.check 939901583360 1099511627776 0 16 (lift40 out_w4)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w4 : out_w4.Contains (Real.log ((939901583360:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w4
#print axioms endpoint_w4
noncomputable def out_w5 : DyadicInterval 40 := ⟨-23417319936,-23417319872⟩
theorem checked_w5 : DyadicFastLog.check 1076341917120 1099511627776 0 16 (lift40 out_w5)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w5 : out_w5.Contains (Real.log ((1076341917120:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w5
#print axioms endpoint_w5
noncomputable def out_w6 : DyadicInterval 40 := ⟨-23330327552,-23330327488⟩
theorem checked_w6 : DyadicFastLog.check 1076427079680 1099511627776 0 16 (lift40 out_w6)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w6 : out_w6.Contains (Real.log ((1076427079680:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w6
#print axioms endpoint_w6
noncomputable def out_w7 : DyadicInterval 40 := ⟨645765201344,645765202752⟩
theorem checked_w7 : DyadicFastLog.check 1099511627776 1978197617222 0 16 (lift40 out_w7.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w7 : out_w7.Contains (Real.log ((1978197617222:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w7
#print axioms endpoint_w7
noncomputable def out_w8 : DyadicInterval 40 := ⟨646962473984,646962475456⟩
theorem checked_w8 : DyadicFastLog.check 1099511627776 1980352875800 0 16 (lift40 out_w8.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w8 : out_w8.Contains (Real.log ((1980352875800:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w8
#print axioms endpoint_w8
noncomputable def out_w9 : DyadicInterval 40 := ⟨320891333568,320891333632⟩
theorem checked_w9 : DyadicFastLog.check 1099511627776 1472136981714 0 16 (lift40 out_w9.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w9 : out_w9.Contains (Real.log ((1472136981714:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w9
#print axioms endpoint_w9
noncomputable def out_w10 : DyadicInterval 40 := ⟨321491152704,321491152768⟩
theorem checked_w10 : DyadicFastLog.check 1099511627776 1472940299144 0 16 (lift40 out_w10.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w10 : out_w10.Contains (Real.log ((1472940299144:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w10
#print axioms endpoint_w10
noncomputable def out_w11 : DyadicInterval 40 := ⟨147426931776,147426931840⟩
theorem checked_w11 : DyadicFastLog.check 1099511627776 1257279324160 0 16 (lift40 out_w11.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w11 : out_w11.Contains (Real.log ((1257279324160:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w11
#print axioms endpoint_w11
noncomputable def out_w12 : DyadicInterval 40 := ⟨-170301138176,-170301138112⟩
theorem checked_w12 : DyadicFastLog.check 941743931392 1099511627776 0 16 (lift40 out_w12)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w12 : out_w12.Contains (Real.log ((941743931392:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w12
#print axioms endpoint_w12
noncomputable def out_w13 : DyadicInterval 40 := ⟨150386679232,150386679296⟩
theorem checked_w13 : DyadicFastLog.check 1099511627776 1260668321792 0 16 (lift40 out_w13.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w13 : out_w13.Contains (Real.log ((1260668321792:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w13
#print axioms endpoint_w13
noncomputable def out_w14 : DyadicInterval 40 := ⟨-174265021568,-174265021504⟩
theorem checked_w14 : DyadicFastLog.check 938354933760 1099511627776 0 16 (lift40 out_w14)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w14 : out_w14.Contains (Real.log ((938354933760:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w14
#print axioms endpoint_w14
noncomputable def out_w15 : DyadicInterval 40 := ⟨-23878342336,-23878342272⟩
theorem checked_w15 : DyadicFastLog.check 1075890704295 1099511627776 0 16 (lift40 out_w15)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w15 : out_w15.Contains (Real.log ((1075890704295:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w15
#print axioms endpoint_w15
noncomputable def out_w16 : DyadicInterval 40 := ⟨-22874206400,-22874206336⟩
theorem checked_w16 : DyadicFastLog.check 1076873717095 1099511627776 0 16 (lift40 out_w16)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w16 : out_w16.Contains (Real.log ((1076873717095:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w16
#print axioms endpoint_w16
noncomputable def out_w17 : DyadicInterval 40 := ⟨317728069952,317728070016⟩
theorem checked_w17 : DyadicFastLog.check 1099511627776 1467907772160 0 16 (lift40 out_w17.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w17 : out_w17.Contains (Real.log ((1467907772160:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w17
#print axioms endpoint_w17
noncomputable def out_w18 : DyadicInterval 40 := ⟨324651700800,324651700864⟩
theorem checked_w18 : DyadicFastLog.check 1099511627776 1477180359702 0 16 (lift40 out_w18.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w18 : out_w18.Contains (Real.log ((1477180359702:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w18
#print axioms endpoint_w18
end GeneralCK.Certificates.ReflectionMidpointFamily.Endpoints0421

namespace GeneralCK.Certificates.ReflectionMidpointFamily.Cell0421
open Set GeneralCK.Certificates.ReflectionMidpointFamily.Endpoints0421
open BivariateJetProgram (RegistersContain RegistersSound zeroBox zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
theorem lc0 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc1 : ProvedTranscendental.LogEncloses (⟨1258828070912,1258828070912⟩ : DyadicInterval 40) (⟨148780502976,148780503040⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w1
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w1
theorem lc2 : ProvedTranscendental.LogEncloses (⟨940195184640,940195184640⟩ : DyadicInterval 40) (⟨-172110830592,-172110830528⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w2
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w2
theorem lc3 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc4 : ProvedTranscendental.LogEncloses (⟨1259121672192,1259121672192⟩ : DyadicInterval 40) (⟨149036916416,149036916480⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w3
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w3
theorem lc5 : ProvedTranscendental.LogEncloses (⟨939901583360,939901583360⟩ : DyadicInterval 40) (⟨-172454236352,-172454236288⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w4
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w4
theorem lc6 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc7 : ProvedTranscendental.LogEncloses (⟨1076341917120,1076427079680⟩ : DyadicInterval 40) (⟨-23417319936,-23330327488⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w5
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w6
theorem lc8 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc9 : ProvedTranscendental.LogEncloses (⟨1258828070912,1259121672192⟩ : DyadicInterval 40) (⟨148780502976,149036916480⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w1
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w3
theorem lc10 : ProvedTranscendental.LogEncloses (⟨939901583360,940195184640⟩ : DyadicInterval 40) (⟨-172454236352,-172110830528⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w4
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w2
theorem lc11 : ProvedTranscendental.LogEncloses (⟨1076341917120,1076427079680⟩ : DyadicInterval 40) (⟨-23417319936,-23330327488⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w5
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w6
theorem lc12 : ProvedTranscendental.LogEncloses (⟨1978197617222,1980352875800⟩ : DyadicInterval 40) (⟨645765201344,646962475456⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w7
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
theorem lc13 : ProvedTranscendental.LogEncloses (⟨1472136981714,1472940299144⟩ : DyadicInterval 40) (⟨320891333568,321491152768⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w9
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w10
theorem lc14 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc15 : ProvedTranscendental.LogEncloses (⟨1257279324160,1257279324160⟩ : DyadicInterval 40) (⟨147426931776,147426931840⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w11
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w11
theorem lc16 : ProvedTranscendental.LogEncloses (⟨941743931392,941743931392⟩ : DyadicInterval 40) (⟨-170301138176,-170301138112⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w12
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w12
theorem lc17 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc18 : ProvedTranscendental.LogEncloses (⟨1260668321792,1260668321792⟩ : DyadicInterval 40) (⟨150386679232,150386679296⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w13
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w13
theorem lc19 : ProvedTranscendental.LogEncloses (⟨938354933760,938354933760⟩ : DyadicInterval 40) (⟨-174265021568,-174265021504⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w14
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w14
theorem lc20 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc21 : ProvedTranscendental.LogEncloses (⟨1075890704295,1076873717095⟩ : DyadicInterval 40) (⟨-23878342336,-22874206336⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w15
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w16
theorem lc22 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc23 : ProvedTranscendental.LogEncloses (⟨1257279324160,1260668321792⟩ : DyadicInterval 40) (⟨147426931776,150386679296⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w11
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w13
theorem lc24 : ProvedTranscendental.LogEncloses (⟨938354933760,941743931392⟩ : DyadicInterval 40) (⟨-174265021568,-170301138112⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w14
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w12
theorem lc25 : ProvedTranscendental.LogEncloses (⟨1075890704295,1076873717095⟩ : DyadicInterval 40) (⟨-23878342336,-22874206336⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w15
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w16
theorem lc26 : ProvedTranscendental.LogEncloses (⟨1978197617222,1980352875800⟩ : DyadicInterval 40) (⟨645765201344,646962475456⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w7
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
theorem lc27 : ProvedTranscendental.LogEncloses (⟨1467907772160,1477180359702⟩ : DyadicInterval 40) (⟨317728069952,324651700864⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w17
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w18
theorem ew3_ok (x : ℝ) (hx : (⟨159316443136,159316443136⟩ : DyadicInterval 40).Contains x) : (⟨750540377624,750540396953⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨159316443136,159316443136⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨148780502976,148780503040⟩ : DyadicInterval 40)) (minus:=(⟨-172110830592,-172110830528⟩ : DyadicInterval 40))
    (lc0 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc1 lc2 (by decide) hx
theorem ew6_ok (x : ℝ) (hx : (⟨159610044416,159610044416⟩ : DyadicInterval 40).Contains x) : (⟨750497493944,750497513274⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨159610044416,159610044416⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨149036916416,149036916480⟩ : DyadicInterval 40)) (minus:=(⟨-172454236352,-172454236288⟩ : DyadicInterval 40))
    (lc3 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc4 lc5 (by decide) hx
theorem ew17_ok (x : ℝ) (hx : (⟨157767696384,157767696384⟩ : DyadicInterval 40).Contains x) : (⟨750765263669,750765282999⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨157767696384,157767696384⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨147426931776,147426931840⟩ : DyadicInterval 40)) (minus:=(⟨-170301138176,-170301138112⟩ : DyadicInterval 40))
    (lc14 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc15 lc16 (by decide) hx
theorem ew20_ok (x : ℝ) (hx : (⟨161156694016,161156694016⟩ : DyadicInterval 40).Contains x) : (⟨750270266631,750270285961⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨161156694016,161156694016⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨150386679232,150386679296⟩ : DyadicInterval 40)) (minus:=(⟨-174265021568,-174265021504⟩ : DyadicInterval 40))
    (lc17 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc18 lc19 (by decide) hx
theorem bw9_ok (x : ℝ) (hx : (⟨159316443136,159610044416⟩ : DyadicInterval 40).Contains x) : (⟨773788547360,773832062848⟩ : DyadicInterval 40).Contains (Reflection.biasB x) := by
  exact ProvedTranscendental.denominator_encloses (c:=(⟨159316443136,159610044416⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (gapLog:=(⟨-23417319936,-23330327488⟩ : DyadicInterval 40))
    (lc6 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc7 (by decide) hx
theorem bw23_ok (x : ℝ) (hx : (⟨157767696384,161156694016⟩ : DyadicInterval 40).Contains x) : (⟨773560486784,774062574048⟩ : DyadicInterval 40).Contains (Reflection.biasB x) := by
  exact ProvedTranscendental.denominator_encloses (c:=(⟨157767696384,161156694016⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (gapLog:=(⟨-23878342336,-22874206336⟩ : DyadicInterval 40))
    (lc20 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc21 (by decide) hx
theorem brcenter6_contact (y : ℝ) (hy : (⟨5170071430718,5179707446524⟩ : DyadicInterval 40).Contains y) : (⟨159316443136,159610044416⟩ : DyadicInterval 40).Contains (Reflection.biasContact y) := by
  exact ProvedTranscendental.contact_bracket (Y:=(⟨5170071430718,5179707446524⟩ : DyadicInterval 40)) (c:=(⟨159316443136,159610044416⟩ : DyadicInterval 40)) (elo:=(⟨750540377624,750540396953⟩ : DyadicInterval 40)) (ehi:=(⟨750497493944,750497513274⟩ : DyadicInterval 40))
    (by decide) (by decide) (by decide) (by decide)
    (ew3_ok _ (DyadicContact.point_contains 40 159316443136)) (ew6_ok _ (DyadicContact.point_contains 40 159610044416))
    (by decide) (by decide) hy
theorem brcenter6_jet (y : ℝ) (hy : (⟨5170071430718,5179707446524⟩ : DyadicInterval 40).Contains y) : (⟨⟨159316443136,159610044416⟩,⟨-32922904282,-32800048320⟩,⟨13298016554,13376304677⟩⟩ : DyadicJetEnclosure 40).Contains reflectionContactJet y := by
  exact ProvedTranscendental.contact_jet (c:=(⟨159316443136,159610044416⟩ : DyadicInterval 40)) (B:=(⟨773788547360,773832062848⟩ : DyadicInterval 40)) (by decide) brcenter6_contact bw9_ok (by decide) (by decide) (by decide) hy
theorem brwhole6_contact (y : ℝ) (hy : (⟨5118882604663,5232120280162⟩ : DyadicInterval 40).Contains y) : (⟨157767696384,161156694016⟩ : DyadicInterval 40).Contains (Reflection.biasContact y) := by
  exact ProvedTranscendental.contact_bracket (Y:=(⟨5118882604663,5232120280162⟩ : DyadicInterval 40)) (c:=(⟨157767696384,161156694016⟩ : DyadicInterval 40)) (elo:=(⟨750765263669,750765282999⟩ : DyadicInterval 40)) (ehi:=(⟨750270266631,750270285961⟩ : DyadicInterval 40))
    (by decide) (by decide) (by decide) (by decide)
    (ew17_ok _ (DyadicContact.point_contains 40 157767696384)) (ew20_ok _ (DyadicContact.point_contains 40 161156694016))
    (by decide) (by decide) hy
theorem brwhole6_jet (y : ℝ) (hy : (⟨5118882604663,5232120280162⟩ : DyadicInterval 40).Contains y) : (⟨⟨157767696384,161156694016⟩,⟨-33573948606,-32155857752⟩,⟨12889601148,13793291176⟩⟩ : DyadicJetEnclosure 40).Contains reflectionContactJet y := by
  exact ProvedTranscendental.contact_jet (c:=(⟨157767696384,161156694016⟩ : DyadicInterval 40)) (B:=(⟨773560486784,774062574048⟩ : DyadicInterval 40)) (by decide) brwhole6_contact bw23_ok (by decide) (by decide) (by decide) hy
noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨313910569730,314460325544⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨739320214593,739403237991⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨156955284865,157230162772⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
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
noncomputable def centerStep4 : Instruction 40 := ⟨.inv 6,⟨⟨7688892501928,7702358163056⟩,⟨0,0⟩,⟨-53956974872559,-53768479034447⟩,⟨0,0⟩,⟨0,0⟩,⟨752006699782272,755964621682256⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4
theorem centerAccepted4 : StepValid centerStep4.shape centerBoxes4 centerStep4.proposed := by
  dsimp only [StepValid,centerStep4]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep5 : Instruction 40 := ⟨.mul 6 0,⟨⟨5170071430718,5179707446524⟩,⟨0,0⟩,⟨-36285166000170,-36154345669353⟩,⟨0,0⟩,⟨0,0⟩,⟨505655184186619,508373604205646⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5
theorem centerAccepted5 : StepValid centerStep5.shape centerBoxes5 centerStep5.proposed := by
  dsimp only [StepValid,centerStep5]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep6 : Instruction 40 := ⟨.contact 0,⟨⟨159316443136,159610044416⟩,⟨0,0⟩,⟨1078537284168,1086494236989⟩,⟨0,0⟩,⟨0,0⟩,⟨-844013317371,-516612139287⟩⟩⟩
noncomputable def centerBoxes7 := centerStep6.proposed :: centerBoxes6
theorem centerAccepted6 : StepValid centerStep6.shape centerBoxes6 centerStep6.proposed := by
  dsimp only [StepValid,centerStep6]
  exact ⟨by decide,by decide,(⟨⟨159316443136,159610044416⟩,⟨-32922904282,-32800048320⟩,⟨13298016554,13376304677⟩⟩ : DyadicJetEnclosure 40),brcenter6_jet,by decide⟩
noncomputable def centerStep7 : Instruction 40 := ⟨.log 10,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes8 := centerStep7.proposed :: centerBoxes7
theorem centerAccepted7 : StepValid centerStep7.shape centerBoxes7 centerStep7.proposed := by
  dsimp only [StepValid,centerStep7]
  exact ⟨by decide,by decide,lc0,by decide⟩
noncomputable def centerStep8 : Instruction 40 := ⟨.add 6 1,⟨⟨1258828070912,1259121672192⟩,⟨0,0⟩,⟨1078537284168,1086494236989⟩,⟨0,0⟩,⟨0,0⟩,⟨-844013317371,-516612139287⟩⟩⟩
noncomputable def centerBoxes9 := centerStep8.proposed :: centerBoxes8
theorem centerAccepted8 : StepValid centerStep8.shape centerBoxes8 centerStep8.proposed := by
  dsimp only [StepValid,centerStep8]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep9 : Instruction 40 := ⟨.log 0,⟨⟨148780502976,149036916480⟩,⟨0,0⟩,⟨941818659087,948988249219⟩,⟨0,0⟩,⟨0,0⟩,⟨-1556267107054,-1257866994049⟩⟩⟩
noncomputable def centerBoxes10 := centerStep9.proposed :: centerBoxes9
theorem centerAccepted9 : StepValid centerStep9.shape centerBoxes9 centerStep9.proposed := by
  dsimp only [StepValid,centerStep9]
  exact ⟨by decide,by decide,lc9,by decide⟩
noncomputable def centerStep10 : Instruction 40 := ⟨.mul 1 0,⟨⟨170338420094,170671784415⟩,⟨0,0⟩,⟨1224228149461,1234020075664⟩,⟨0,0⟩,⟨0,0⟩,⟨-48881435761,365471743850⟩⟩⟩
noncomputable def centerBoxes11 := centerStep10.proposed :: centerBoxes10
theorem centerAccepted10 : StepValid centerStep10.shape centerBoxes10 centerStep10.proposed := by
  dsimp only [StepValid,centerStep10]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep11 : Instruction 40 := ⟨.neg 4,⟨⟨-159610044416,-159316443136⟩,⟨0,0⟩,⟨-1086494236989,-1078537284168⟩,⟨0,0⟩,⟨0,0⟩,⟨516612139287,844013317371⟩⟩⟩
noncomputable def centerBoxes12 := centerStep11.proposed :: centerBoxes11
theorem centerAccepted11 : StepValid centerStep11.shape centerBoxes11 centerStep11.proposed := by
  dsimp only [StepValid,centerStep11]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep12 : Instruction 40 := ⟨.add 10 0,⟨⟨939901583360,940195184640⟩,⟨0,0⟩,⟨-1086494236989,-1078537284168⟩,⟨0,0⟩,⟨0,0⟩,⟨516612139287,844013317371⟩⟩⟩
noncomputable def centerBoxes13 := centerStep12.proposed :: centerBoxes12
theorem centerAccepted12 : StepValid centerStep12.shape centerBoxes12 centerStep12.proposed := by
  dsimp only [StepValid,centerStep12]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep13 : Instruction 40 := ⟨.log 0,⟨⟨-172454236352,-172110830528⟩,⟨0,0⟩,⟨-1270998015357,-1261295850378⟩,⟨0,0⟩,⟨0,0⟩,⟨-865078173066,-459545280929⟩⟩⟩
noncomputable def centerBoxes14 := centerStep13.proposed :: centerBoxes13
theorem centerAccepted13 : StepValid centerStep13.shape centerBoxes13 centerStep13.proposed := by
  dsimp only [StepValid,centerStep13]
  exact ⟨by decide,by decide,lc10,by decide⟩
noncomputable def centerStep14 : Instruction 40 := ⟨.mul 1 0,⟨⟨-147466055377,-147126449634⟩,⟨0,0⟩,⟨-918005995112,-907787973951⟩,⟨0,0⟩,⟨0,0⟩,⟨1602359768389,2038197777708⟩⟩⟩
noncomputable def centerBoxes15 := centerStep14.proposed :: centerBoxes14
theorem centerAccepted14 : StepValid centerStep14.shape centerBoxes14 centerStep14.proposed := by
  dsimp only [StepValid,centerStep14]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep15 : Instruction 40 := ⟨.add 4 0,⟨⟨22872364717,23545334781⟩,⟨0,0⟩,⟨306222154349,326232101713⟩,⟨0,0⟩,⟨0,0⟩,⟨1553478332628,2403669521558⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15
theorem centerAccepted15 : StepValid centerStep15.shape centerBoxes15 centerStep15.proposed := by
  dsimp only [StepValid,centerStep15]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep16 : Instruction 40 := ⟨.mul 0 15,⟨⟨11436182358,11772667391⟩,⟨0,0⟩,⟨153111077174,163116050857⟩,⟨0,0⟩,⟨0,0⟩,⟨776739166314,1201834760779⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16
theorem centerAccepted16 : StepValid centerStep16.shape centerBoxes16 centerStep16.proposed := by
  dsimp only [StepValid,centerStep16]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨-11772667391,-11436182358⟩,⟨0,0⟩,⟨-163116050857,-153111077174⟩,⟨0,0⟩,⟨0,0⟩,⟨-1201834760779,-776739166314⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17
theorem centerAccepted17 : StepValid centerStep17.shape centerBoxes17 centerStep17.proposed := by
  dsimp only [StepValid,centerStep17]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep18 : Instruction 40 := ⟨.add 10 0,⟨⟨750350716225,750687220522⟩,⟨0,0⟩,⟨-163116050857,-153111077174⟩,⟨0,0⟩,⟨0,0⟩,⟨-1201834760779,-776739166314⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18
theorem centerAccepted18 : StepValid centerStep18.shape centerBoxes18 centerStep18.proposed := by
  dsimp only [StepValid,centerStep18]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep19 : Instruction 40 := ⟨.mul 12 12,⟨⟨23084548096,23169710656⟩,⟨0,0⟩,⟨312554628004,315440763050⟩,⟨0,0⟩,⟨0,0⟩,⟨1870884571446,1997550350095⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19
theorem centerAccepted19 : StepValid centerStep19.shape centerBoxes19 centerStep19.proposed := by
  dsimp only [StepValid,centerStep19]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep20 : Instruction 40 := ⟨.neg 0,⟨⟨-23169710656,-23084548096⟩,⟨0,0⟩,⟨-315440763050,-312554628004⟩,⟨0,0⟩,⟨0,0⟩,⟨-1997550350095,-1870884571446⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20
theorem centerAccepted20 : StepValid centerStep20.shape centerBoxes20 centerStep20.proposed := by
  dsimp only [StepValid,centerStep20]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep21 : Instruction 40 := ⟨.add 19 0,⟨⟨1076341917120,1076427079680⟩,⟨0,0⟩,⟨-315440763050,-312554628004⟩,⟨0,0⟩,⟨0,0⟩,⟨-1997550350095,-1870884571446⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21
theorem centerAccepted21 : StepValid centerStep21.shape centerBoxes21 centerStep21.proposed := by
  dsimp only [StepValid,centerStep21]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep22 : Instruction 40 := ⟨.log 0,⟨⟨-23417319936,-23330327488⟩,⟨0,0⟩,⟨-322231050684,-319257527326⟩,⟨0,0⟩,⟨0,0⟩,⟨-2134985741013,-2003707263535⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22
theorem centerAccepted22 : StepValid centerStep22.shape centerBoxes22 centerStep22.proposed := by
  dsimp only [StepValid,centerStep22]
  exact ⟨by decide,by decide,lc7,by decide⟩
noncomputable def centerStep23 : Instruction 40 := ⟨.mul 0 22,⟨⟨-11708659968,-11665163744⟩,⟨0,0⟩,⟨-161115525342,-159628763663⟩,⟨0,0⟩,⟨0,0⟩,⟨-1067492870507,-1001853631767⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23
theorem centerAccepted23 : StepValid centerStep23.shape centerBoxes23 centerStep23.proposed := by
  dsimp only [StepValid,centerStep23]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep24 : Instruction 40 := ⟨.neg 0,⟨⟨11665163744,11708659968⟩,⟨0,0⟩,⟨159628763663,161115525342⟩,⟨0,0⟩,⟨0,0⟩,⟨1001853631767,1067492870507⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24
theorem centerAccepted24 : StepValid centerStep24.shape centerBoxes24 centerStep24.proposed := by
  dsimp only [StepValid,centerStep24]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep25 : Instruction 40 := ⟨.add 17 0,⟨⟨773788547360,773832062848⟩,⟨0,0⟩,⟨159628763663,161115525342⟩,⟨0,0⟩,⟨0,0⟩,⟨1001853631767,1067492870507⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25
theorem centerAccepted25 : StepValid centerStep25.shape centerBoxes25 centerStep25.proposed := by
  dsimp only [StepValid,centerStep25]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep26 : Instruction 40 := ⟨.add 24 26,⟨⟨1413422197506,1413971953320⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26
theorem centerAccepted26 : StepValid centerStep26.shape centerBoxes26 centerStep26.proposed := by
  dsimp only [StepValid,centerStep26]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep27 : Instruction 40 := ⟨.neg 27,⟨⟨-314460325544,-313910569730⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27
theorem centerAccepted27 : StepValid centerStep27.shape centerBoxes27 centerStep27.proposed := by
  dsimp only [StepValid,centerStep27]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep28 : Instruction 40 := ⟨.add 26 0,⟨⟨785051302232,785601058046⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28
theorem centerAccepted28 : StepValid centerStep28.shape centerBoxes28 centerStep28.proposed := by
  dsimp only [StepValid,centerStep28]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep29 : Instruction 40 := ⟨.inv 0,⟨⟨1538854622499,1539932251788⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29
theorem centerAccepted29 : StepValid centerStep29.shape centerBoxes29 centerStep29.proposed := by
  dsimp only [StepValid,centerStep29]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep30 : Instruction 40 := ⟨.mul 3 0,⟨⟨1978197617222,1980352875800⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30
theorem centerAccepted30 : StepValid centerStep30.shape centerBoxes30 centerStep30.proposed := by
  dsimp only [StepValid,centerStep30]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨645765201344,646962475456⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31
theorem centerAccepted31 : StepValid centerStep31.shape centerBoxes31 centerStep31.proposed := by
  dsimp only [StepValid,centerStep31]
  exact ⟨by decide,by decide,lc12,by decide⟩
noncomputable def centerStep32 : Instruction 40 := ⟨.mul 0 31,⟨⟨322882600672,323481237728⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32
theorem centerAccepted32 : StepValid centerStep32.shape centerBoxes32 centerStep32.proposed := by
  dsimp only [StepValid,centerStep32]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep33 : Instruction 40 := ⟨.inv 20,⟨⟨1285824304745,1286225963460⟩,⟨0,0⟩,⟨1475022927379,1486833431826⟩,⟨0,0⟩,⟨0,0⟩,⟨2229115321041,2730931565256⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33
theorem centerAccepted33 : StepValid centerStep33.shape centerBoxes33 centerStep33.proposed := by
  dsimp only [StepValid,centerStep33]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep34 : Instruction 40 := ⟨.mul 25 0,⟨⟨1472136981714,1472940299144⟩,⟨0,0⟩,⟨2950045854758,2973666863652⟩,⟨0,0⟩,⟨0,0⟩,⟨4458539061923,5461674467688⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34
theorem centerAccepted34 : StepValid centerStep34.shape centerBoxes34 centerStep34.proposed := by
  dsimp only [StepValid,centerStep34]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨320891333568,321491152768⟩,⟨0,0⟩,⟨2202132511184,2220976263985⟩,⟨0,0⟩,⟨0,0⟩,⟨-1158113401582,-331269632231⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35
theorem centerAccepted35 : StepValid centerStep35.shape centerBoxes35 centerStep35.proposed := by
  dsimp only [StepValid,centerStep35]
  exact ⟨by decide,by decide,lc13,by decide⟩
noncomputable def centerStep36 : Instruction 40 := ⟨.mul 0 35,⟨⟨160445666784,160745576384⟩,⟨0,0⟩,⟨1101066255592,1110488131993⟩,⟨0,0⟩,⟨0,0⟩,⟨-579056700791,-165634816115⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36
theorem centerAccepted36 : StepValid centerStep36.shape centerBoxes36 centerStep36.proposed := by
  dsimp only [StepValid,centerStep36]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep37 : Instruction 40 := ⟨.mul 40 11,⟨⟨1547577094720,1547664125696⟩,⟨0,0⟩,⟨319257527326,322231050684⟩,⟨0,0⟩,⟨0,0⟩,⟨2003707263534,2134985741014⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37
theorem centerAccepted37 : StepValid centerStep37.shape centerBoxes37 centerStep37.proposed := by
  dsimp only [StepValid,centerStep37]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep38 : Instruction 40 := ⟨.add 0 17,⟨⟨1524407384064,1524579577600⟩,⟨0,0⟩,⟨3816764276,9676422680⟩,⟨0,0⟩,⟨0,0⟩,⟨6156913439,264101169568⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38
theorem centerAccepted38 : StepValid centerStep38.shape centerBoxes38 centerStep38.proposed := by
  dsimp only [StepValid,centerStep38]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep39 : Instruction 40 := ⟨.mul 20 0,⟨⟨1040316576519,1040900684142⟩,⟨0,0⟩,⟨-223571522027,-205672849714⟩,⟨0,0⟩,⟨0,0⟩,⟨-1665129864009,-897651557788⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39
theorem centerAccepted39 : StepValid centerStep39.shape centerBoxes39 centerStep39.proposed := by
  dsimp only [StepValid,centerStep39]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep40 : Instruction 40 := ⟨.mul 43 41,⟨⟨1478640429186,1478806475982⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40
theorem centerAccepted40 : StepValid centerStep40.shape centerBoxes40 centerStep40.proposed := by
  dsimp only [StepValid,centerStep40]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep41 : Instruction 40 := ⟨.mul 19 19,⟨⟨1053660455499,1053827198001⟩,⟨0,0⟩,⟨-617635995482,-611936498008⟩,⟨0,0⟩,⟨0,0⟩,⟨-3733524671372,-3481925180214⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41
theorem centerAccepted41 : StepValid centerStep41.shape centerBoxes41 centerStep41.proposed := by
  dsimp only [StepValid,centerStep41]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep42 : Instruction 40 := ⟨.mul 1 0,⟨⟨1416979055771,1417362441289⟩,⟨0,0⟩,⟨-830699818761,-822941770865⟩,⟨0,0⟩,⟨0,0⟩,⟨-5021466188067,-4682547426332⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42
theorem centerAccepted42 : StepValid centerStep42.shape centerBoxes42 centerStep42.proposed := by
  dsimp only [StepValid,centerStep42]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep43 : Instruction 40 := ⟨.mul 17 17,⟨⟨544558784918,544620035264⟩,⟨0,0⟩,⟨224679586884,226784976500⟩,⟨0,0⟩,⟨0,0⟩,⟨1456472470783,1549812482274⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43
theorem centerAccepted43 : StepValid centerStep43.shape centerBoxes43 centerStep43.proposed := by
  dsimp only [StepValid,centerStep43]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep44 : Instruction 40 := ⟨.mul 18 0,⟨⟨383236830324,383301490144⟩,⟨0,0⟩,⟨237179607879,239415593826⟩,⟨0,0⟩,⟨0,0⟩,⟨1586432120498,1685975581698⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44
theorem centerAccepted44 : StepValid centerStep44.shape centerBoxes44 centerStep44.proposed := by
  dsimp only [StepValid,centerStep44]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep45 : Instruction 40 := ⟨.mul 2 0,⟨⟨493890694969,494107676623⟩,⟨0,0⟩,⟨16070824518,21788832547⟩,⟨0,0⟩,⟨0,0⟩,⟨-67811347660,186213419402⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45
theorem centerAccepted45 : StepValid centerStep45.shape centerBoxes45 centerStep45.proposed := by
  dsimp only [StepValid,centerStep45]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep46 : Instruction 40 := ⟨.inv 0,⟨⟨2446684957167,2447759862515⟩,⟨0,0⟩,⟨-107987111932,-79578291246⟩,⟨0,0⟩,⟨0,0⟩,⟨-917711315888,345606270705⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46
theorem centerAccepted46 : StepValid centerStep46.shape centerBoxes46 centerStep46.proposed := by
  dsimp only [StepValid,centerStep46]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep47 : Instruction 40 := ⟨.mul 7 0,⟨⟨2314961346619,2317278736434⟩,⟨0,0⟩,⟨-599951141984,-532966881115⟩,⟨0,0⟩,⟨0,0⟩,⟨-4545973020575,-1626397600964⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47
theorem centerAccepted47 : StepValid centerStep47.shape centerBoxes47 centerStep47.proposed := by
  dsimp only [StepValid,centerStep47]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep48 : Instruction 40 := ⟨.neg 11,⟨⟨-160745576384,-160445666784⟩,⟨0,0⟩,⟨-1110488131993,-1101066255592⟩,⟨0,0⟩,⟨0,0⟩,⟨165634816115,579056700791⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48
theorem centerAccepted48 : StepValid centerStep48.shape centerBoxes48 centerStep48.proposed := by
  dsimp only [StepValid,centerStep48]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep49 : Instruction 40 := ⟨.mul 0 10,⟨⟨-222889341735,-222448360715⟩,⟨0,0⟩,⟨-1541214232335,-1527119742292⟩,⟨0,0⟩,⟨0,0⟩,⟨171485896247,794375545883⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49
theorem centerAccepted49 : StepValid centerStep49.shape centerBoxes49 centerStep49.proposed := by
  dsimp only [StepValid,centerStep49]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep50 : Instruction 40 := ⟨.mul 53 43,⟨⟨318632886272,319220088832⟩,⟨0,0⟩,⟨2157074568336,2172988473978⟩,⟨0,0⟩,⟨0,0⟩,⟨-1688026634742,-1033224278574⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50
theorem centerAccepted50 : StepValid centerStep50.shape centerBoxes50 centerStep50.proposed := by
  dsimp only [StepValid,centerStep50]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep51 : Instruction 40 := ⟨.inv 29,⟨⟨1123091236216,1123180097687⟩,⟨0,0⟩,⟨326104173869,329167508412⟩,⟨0,0⟩,⟨0,0⟩,⟨2141366421545,2277412463845⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51
theorem centerAccepted51 : StepValid centerStep51.shape centerBoxes51 centerStep51.proposed := by
  dsimp only [StepValid,centerStep51]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep52 : Instruction 40 := ⟨.mul 1 0,⟨⟨325466137057,326091731548⟩,⟨0,0⟩,⟨2297837507019,2315331846833⟩,⟨0,0⟩,⟨0,0⟩,⟨175727003002,906898167414⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52
theorem centerAccepted52 : StepValid centerStep52.shape centerBoxes52 centerStep52.proposed := by
  dsimp only [StepValid,centerStep52]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep53 : Instruction 40 := ⟨.neg 2,⟨⟨-319220088832,-318632886272⟩,⟨0,0⟩,⟨-2172988473978,-2157074568336⟩,⟨0,0⟩,⟨0,0⟩,⟨1033224278574,1688026634742⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53
theorem centerAccepted53 : StepValid centerStep53.shape centerBoxes53 centerStep53.proposed := by
  dsimp only [StepValid,centerStep53]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep54 : Instruction 40 := ⟨.add 1 0,⟨⟨6246048225,7458845276⟩,⟨0,0⟩,⟨124849033041,158257278497⟩,⟨0,0⟩,⟨0,0⟩,⟨1208951281576,2594924802156⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54
theorem centerAccepted54 : StepValid centerStep54.shape centerBoxes54 centerStep54.proposed := by
  dsimp only [StepValid,centerStep54]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep55 : Instruction 40 := ⟨.mul 36 0,⟨⟨4262553156,5092497148⟩,⟨0,0⟩,⟨84095430772,107179746330⟩,⟨0,0⟩,⟨0,0⟩,⟨769927788412,1732490815847⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55
theorem centerAccepted55 : StepValid centerStep55.shape centerBoxes55 centerStep55.proposed := by
  dsimp only [StepValid,centerStep55]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep56 : Instruction 40 := ⟨.add 6 0,⟨⟨-218626788579,-217355863567⟩,⟨0,0⟩,⟨-1457118801563,-1419939995962⟩,⟨0,0⟩,⟨0,0⟩,⟨941413684659,2526866361730⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56
theorem centerAccepted56 : StepValid centerStep56.shape centerBoxes56 centerStep56.proposed := by
  dsimp only [StepValid,centerStep56]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep57 : Instruction 40 := ⟨.mul 0 10,⟨⟨-486712340675,-483670484519⟩,⟨0,0⟩,⟨-3228142403866,-3138245076761⟩,⟨0,0⟩,⟨0,0⟩,⟨2231696915941,6094067828839⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57
theorem centerAccepted57 : StepValid centerStep57.shape centerBoxes57 centerStep57.proposed := by
  dsimp only [StepValid,centerStep57]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep58 : Instruction 40 := ⟨.mul 54 51,⟨⟨637265772544,638440177664⟩,⟨0,0⟩,⟨4314149136672,4345976947956⟩,⟨0,0⟩,⟨0,0⟩,⟨-3376053269484,-2066448557148⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58
theorem centerAccepted58 : StepValid centerStep58.shape centerBoxes58 centerStep58.proposed := by
  dsimp only [StepValid,centerStep58]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep59 : Instruction 40 := ⟨.mul 0 7,⟨⟨650932274115,652183463095⟩,⟨0,0⟩,⟨4595675014038,4630663693664⟩,⟨0,0⟩,⟨0,0⟩,⟨351454006006,1813796334826⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59
theorem centerAccepted59 : StepValid centerStep59.shape centerBoxes59 centerStep59.proposed := by
  dsimp only [StepValid,centerStep59]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep60 : Instruction 40 := ⟨.mul 57 53,⟨⟨477949329408,478830133248⟩,⟨0,0⟩,⟨3235611852504,3259482710967⟩,⟨0,0⟩,⟨0,0⟩,⟨-2532039952113,-1549836417861⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60
theorem centerAccepted60 : StepValid centerStep60.shape centerBoxes60 centerStep60.proposed := by
  dsimp only [StepValid,centerStep60]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep61 : Instruction 40 := ⟨.mul 39 35,⟨⟨757482710933,757585246515⟩,⟨0,0⟩,⟨-65741048156,-62229516641⟩,⟨0,0⟩,⟨0,0⟩,⟨-517571841443,-362321078982⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61
theorem centerAccepted61 : StepValid centerStep61.shape centerBoxes61 centerStep61.proposed := by
  dsimp only [StepValid,centerStep61]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep62 : Instruction 40 := ⟨.inv 0,⟨⟨1595762094333,1595978102426⟩,⟨0,0⟩,⟨131078983205,138513093136⟩,⟨0,0⟩,⟨0,0⟩,⟨784719884771,1114540708380⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62
theorem centerAccepted62 : StepValid centerStep62.shape centerBoxes62 centerStep62.proposed := by
  dsimp only [StepValid,centerStep62]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep63 : Instruction 40 := ⟨.mul 2 0,⟨⟨693665627187,695038040654⟩,⟨0,0⟩,⟨4752942785055,4791570313303⟩,⟨0,0⟩,⟨0,0⟩,⟨-2562758301790,-942720787403⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63
theorem centerAccepted63 : StepValid centerStep63.shape centerBoxes63 centerStep63.proposed := by
  dsimp only [StepValid,centerStep63]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep64 : Instruction 40 := ⟨.neg 0,⟨⟨-695038040654,-693665627187⟩,⟨0,0⟩,⟨-4791570313303,-4752942785055⟩,⟨0,0⟩,⟨0,0⟩,⟨942720787403,2562758301790⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64
theorem centerAccepted64 : StepValid centerStep64.shape centerBoxes64 centerStep64.proposed := by
  dsimp only [StepValid,centerStep64]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep65 : Instruction 40 := ⟨.add 5 0,⟨⟨-44105766539,-41482164092⟩,⟨0,0⟩,⟨-195895299265,-122279091391⟩,⟨0,0⟩,⟨0,0⟩,⟨1294174793409,4376554636616⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65
theorem centerAccepted65 : StepValid centerStep65.shape centerBoxes65 centerStep65.proposed := by
  dsimp only [StepValid,centerStep65]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep66 : Instruction 40 := ⟨.mul 18 0,⟨⟨-92955228825,-87338418276⟩,⟨0,0⟩,⟨-392752001005,-233385494599⟩,⟨0,0⟩,⟨0,0⟩,⟨2904719191610,9619958145793⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66
theorem centerAccepted66 : StepValid centerStep66.shape centerBoxes66 centerStep66.proposed := by
  dsimp only [StepValid,centerStep66]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep67 : Instruction 40 := ⟨.add 9 0,⟨⟨-579667569500,-571008902795⟩,⟨0,0⟩,⟨-3620894404871,-3371630571360⟩,⟨0,0⟩,⟨0,0⟩,⟨5136416107551,15714025974632⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67
theorem centerAccepted67 : StepValid centerStep67.shape centerBoxes67 centerStep67.proposed := by
  dsimp only [StepValid,centerStep67]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep68 : Instruction 40 := ⟨.mul 61 29,⟨⟨220882759385,221314816460⟩,⟨0,0⟩,⟨1495880745353,1507934374920⟩,⟨0,0⟩,⟨0,0⟩,⟨-1161926342488,-658790127515⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68
theorem centerAccepted68 : StepValid centerStep68.shape centerBoxes68 centerStep68.proposed := by
  dsimp only [StepValid,centerStep68]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep69 : Instruction 40 := ⟨.mul 27 25,⟨⟨521849922154,521991210679⟩,⟨0,0⟩,⟨-90622908631,-85713708784⟩,⟨0,0⟩,⟨0,0⟩,⟨-708374519162,-489178709206⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69
theorem centerAccepted69 : StepValid centerStep69.shape centerBoxes69 centerStep69.proposed := by
  dsimp only [StepValid,centerStep69]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨2315988842114,2316615885703⟩,⟨0,0⟩,⟨380297578002,402296638997⟩,⟨0,0⟩,⟨0,0⟩,⟨2295298923646,3284366202760⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70
theorem centerAccepted70 : StepValid centerStep70.shape centerBoxes70 centerStep70.proposed := by
  dsimp only [StepValid,centerStep70]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep71 : Instruction 40 := ⟨.mul 2 0,⟨⟨465262934222,466299224675⟩,⟨0,0⟩,⟨3227291284735,3258118280756⟩,⟨0,0⟩,⟨0,0⟩,⟨-952227687124,376896587522⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71
theorem centerAccepted71 : StepValid centerStep71.shape centerBoxes71 centerStep71.proposed := by
  dsimp only [StepValid,centerStep71]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep72 : Instruction 40 := ⟨.mul 65 39,⟨⟨46784869018,46957988818⟩,⟨0,0⟩,⟨316723274621,319651463147⟩,⟨0,0⟩,⟨0,0⟩,⟨-248312492261,-151708328368⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72
theorem centerAccepted72 : StepValid centerStep72.shape centerBoxes72 centerStep72.proposed := by
  dsimp only [StepValid,centerStep72]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep73 : Instruction 40 := ⟨.add 54 0,⟨⟨797135585243,797645209340⟩,⟨0,0⟩,⟨153607223764,166540385973⟩,⟨0,0⟩,⟨0,0⟩,⟨-1450147253040,-928447494682⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73
theorem centerAccepted73 : StepValid centerStep73.shape centerBoxes73 centerStep73.proposed := by
  dsimp only [StepValid,centerStep73]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep74 : Instruction 40 := ⟨.mul 0 0,⟨⟨577915799349,578654980912⟩,⟨0,0⟩,⟨222727583990,241634808906⟩,⟨0,0⟩,⟨0,0⟩,⟨-2061111135905,-1295780451764⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74
theorem centerAccepted74 : StepValid centerStep74.shape centerBoxes74 centerStep74.proposed := by
  dsimp only [StepValid,centerStep74]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep75 : Instruction 40 := ⟨.mul 7 0,⟨⟨-305069558058,-300128764587⟩,⟨0,0⟩,⟨-2033008463623,-1887836342678⟩,⟨0,0⟩,⟨0,0⟩,⟨1781199843597,7990682589017⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75
theorem centerAccepted75 : StepValid centerStep75.shape centerBoxes75 centerStep75.proposed := by
  dsimp only [StepValid,centerStep75]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep76 : Instruction 40 := ⟨.mul 79 28,⟨⟨4629922693238,4634557472868⟩,⟨0,0⟩,⟨-1199902283968,-1065933762230⟩,⟨0,0⟩,⟨0,0⟩,⟨-9091946041150,-3252795201928⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76
theorem centerAccepted76 : StepValid centerStep76.shape centerBoxes76 centerStep76.proposed := by
  dsimp only [StepValid,centerStep76]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep77 : Instruction 40 := ⟨.mul 0 3,⟨⟨3356650391382,3362158682325⟩,⟨0,0⟩,⟨-223650874735,-70806657312⟩,⟨0,0⟩,⟨0,0⟩,⟨-13071805706788,-6565668794734⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77
theorem centerAccepted77 : StepValid centerStep77.shape centerBoxes77 centerStep77.proposed := by
  dsimp only [StepValid,centerStep77]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep78 : Instruction 40 := ⟨.add 45 29,⟨⟨162137024288,163035570944⟩,⟨0,0⟩,⟨-1110488131993,-1101066255592⟩,⟨0,0⟩,⟨0,0⟩,⟨165634816115,579056700791⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78
theorem centerAccepted78 : StepValid centerStep78.shape centerBoxes78 centerStep78.proposed := by
  dsimp only [StepValid,centerStep78]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep79 : Instruction 40 := ⟨.mul 1 0,⟨⟨494980946344,498540848983⟩,⟨0,0⟩,⟨-3428886304987,-3371837791279⟩,⟨0,0⟩,⟨0,0⟩,⟨-1290814447442,1254253036215⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79
theorem centerAccepted79 : StepValid centerStep79.shape centerBoxes79 centerStep79.proposed := by
  dsimp only [StepValid,centerStep79]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep80 : Instruction 40 := ⟨.add 4 0,⟨⟨189911388286,198412084396⟩,⟨0,0⟩,⟨-5461894768610,-5259674133957⟩,⟨0,0⟩,⟨0,0⟩,⟨490385396155,9244935625232⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80
theorem centerAccepted80 : StepValid centerStep80.shape centerBoxes80 centerStep80.proposed := by
  dsimp only [StepValid,centerStep80]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep81 : Instruction 40 := ⟨.mul 81 81,⟨⟨89621467657,89935653106⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81
theorem centerAccepted81 : StepValid centerStep81.shape centerBoxes81 centerStep81.proposed := by
  dsimp only [StepValid,centerStep81]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep82 : Instruction 40 := ⟨.neg 0,⟨⟨-89935653106,-89621467657⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82
theorem centerAccepted82 : StepValid centerStep82.shape centerBoxes82 centerStep82.proposed := by
  dsimp only [StepValid,centerStep82]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep83 : Instruction 40 := ⟨.add 81 0,⟨⟨1009575974670,1009890160119⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83
theorem centerAccepted83 : StepValid centerStep83.shape centerBoxes83 centerStep83.proposed := by
  dsimp only [StepValid,centerStep83]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep84 : Instruction 40 := ⟨.inv 0,⟨⟨1197086443016,1197458982728⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes85 := centerStep84.proposed :: centerBoxes84
theorem centerAccepted84 : StepValid centerStep84.shape centerBoxes84 centerStep84.proposed := by
  dsimp only [StepValid,centerStep84]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep85 : Instruction 40 := ⟨.mul 13 0,⟨⟨506552124529,507838372165⟩,⟨0,0⟩,⟨3513693304394,3548359929557⟩,⟨0,0⟩,⟨0,0⟩,⟨-1037054605649,410471515614⟩⟩⟩
noncomputable def centerBoxes86 := centerStep85.proposed :: centerBoxes85
theorem centerAccepted85 : StepValid centerStep85.shape centerBoxes85 centerStep85.proposed := by
  dsimp only [StepValid,centerStep85]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep86 : Instruction 40 := ⟨.add 5 0,⟨⟨696463512815,706250456561⟩,⟨0,0⟩,⟨-1948201464216,-1711314204400⟩,⟨0,0⟩,⟨0,0⟩,⟨-546669209494,9655407140846⟩⟩⟩
noncomputable def centerBoxes87 := centerStep86.proposed :: centerBoxes86
theorem centerAccepted86 : StepValid centerStep86.shape centerBoxes86 centerStep86.proposed := by
  dsimp only [StepValid,centerStep86]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep87 : Instruction 40 := ⟨.mul 0 68,⟨⟨475294560297,482189709354⟩,⟨0,0⟩,⟨-1434901357771,-1264854397610⟩,⟨0,0⟩,⟨0,0⟩,⟨-668598309399,6678225071931⟩⟩⟩
noncomputable def centerBoxes88 := centerStep87.proposed :: centerBoxes87
theorem centerAccepted87 : StepValid centerStep87.shape centerBoxes87 centerStep87.proposed := by
  dsimp only [StepValid,centerStep87]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep88 : Instruction 40 := ⟨.mul 0 69,⟨⟨324360020146,329213119294⟩,⟨0,0⟩,⟨-1051207612493,-929373768729⟩,⟨0,0⟩,⟨0,0⟩,⟨-631274926444,4649508994089⟩⟩⟩
noncomputable def centerBoxes89 := centerStep88.proposed :: centerBoxes88
theorem centerAccepted88 : StepValid centerStep88.shape centerBoxes88 centerStep88.proposed := by
  dsimp only [StepValid,centerStep88]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep89 : Instruction 40 := ⟨.mul 90 63,⟨⟨520301468790,520389160494⟩,⟨0,0⟩,⟨107335628678,108347504583⟩,⟨0,0⟩,⟨0,0⟩,⟨673654214577,717871157563⟩⟩⟩
noncomputable def centerBoxes90 := centerStep89.proposed :: centerBoxes89
theorem centerAccepted89 : StepValid centerStep89.shape centerBoxes89 centerStep89.proposed := by
  dsimp only [StepValid,centerStep89]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep90 : Instruction 40 := ⟨.inv 0,⟨⟨2323118756868,2323510295726⟩,⟨0,0⟩,⟨-483847456746,-479167191002⟩,⟨0,0⟩,⟨0,0⟩,⟨-3008130919880,-2805811212666⟩⟩⟩
noncomputable def centerBoxes91 := centerStep90.proposed :: centerBoxes90
theorem centerAccepted90 : StepValid centerStep90.shape centerBoxes90 centerStep90.proposed := by
  dsimp only [StepValid,centerStep90]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep91 : Instruction 40 := ⟨.mul 2 0,⟨⟨685328674789,695699847864⟩,⟨0,0⟩,⟨-2366305708230,-2104996669005⟩,⟨0,0⟩,⟨0,0⟩,⟨-1424668078562,9922893965272⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91
theorem centerAccepted91 : StepValid centerStep91.shape centerBoxes91 centerStep91.proposed := by
  dsimp only [StepValid,centerStep91]
  exact ⟨by decide,by decide⟩
noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91]
theorem centerAccepted : Accepted centerProgram centerInitial :=
  ⟨centerAccepted0,⟨centerAccepted1,⟨centerAccepted2,⟨centerAccepted3,⟨centerAccepted4,⟨centerAccepted5,⟨centerAccepted6,⟨centerAccepted7,⟨centerAccepted8,⟨centerAccepted9,⟨centerAccepted10,⟨centerAccepted11,⟨centerAccepted12,⟨centerAccepted13,⟨centerAccepted14,⟨centerAccepted15,⟨centerAccepted16,⟨centerAccepted17,⟨centerAccepted18,⟨centerAccepted19,⟨centerAccepted20,⟨centerAccepted21,⟨centerAccepted22,⟨centerAccepted23,⟨centerAccepted24,⟨centerAccepted25,⟨centerAccepted26,⟨centerAccepted27,⟨centerAccepted28,⟨centerAccepted29,⟨centerAccepted30,⟨centerAccepted31,⟨centerAccepted32,⟨centerAccepted33,⟨centerAccepted34,⟨centerAccepted35,⟨centerAccepted36,⟨centerAccepted37,⟨centerAccepted38,⟨centerAccepted39,⟨centerAccepted40,⟨centerAccepted41,⟨centerAccepted42,⟨centerAccepted43,⟨centerAccepted44,⟨centerAccepted45,⟨centerAccepted46,⟨centerAccepted47,⟨centerAccepted48,⟨centerAccepted49,⟨centerAccepted50,⟨centerAccepted51,⟨centerAccepted52,⟨centerAccepted53,⟨centerAccepted54,⟨centerAccepted55,⟨centerAccepted56,⟨centerAccepted57,⟨centerAccepted58,⟨centerAccepted59,⟨centerAccepted60,⟨centerAccepted61,⟨centerAccepted62,⟨centerAccepted63,⟨centerAccepted64,⟨centerAccepted65,⟨centerAccepted66,⟨centerAccepted67,⟨centerAccepted68,⟨centerAccepted69,⟨centerAccepted70,⟨centerAccepted71,⟨centerAccepted72,⟨centerAccepted73,⟨centerAccepted74,⟨centerAccepted75,⟨centerAccepted76,⟨centerAccepted77,⟨centerAccepted78,⟨centerAccepted79,⟨centerAccepted80,⟨centerAccepted81,⟨centerAccepted82,⟨centerAccepted83,⟨centerAccepted84,⟨centerAccepted85,⟨centerAccepted86,⟨centerAccepted87,⟨centerAccepted88,⟨centerAccepted89,⟨centerAccepted90,⟨centerAccepted91,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
noncomputable def center_output : DyadicBivariateJetEnclosure 40 := ⟨⟨685328674789,695699847864⟩,⟨0,0⟩,⟨-2366305708230,-2104996669005⟩,⟨0,0⟩,⟨0,0⟩,⟨-1424668078562,9922893965272⟩⟩
theorem center_output_eq : (finalBoxes centerProgram centerInitial).getD 0 (zeroBox 40)=center_output := rfl
noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨313910569730,314460325544⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨739320214593,739403237991⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨155382983237,158802464400⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
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
noncomputable def wholeStep4 : Instruction 40 := ⟨.inv 6,⟨⟨7612764853381,7780297394411⟩,⟨0,0⟩,⟨-55054467834888,-52709027579906⟩,⟨0,0⟩,⟨0,0⟩,⟨729890293980494,779146162397344⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4
theorem wholeAccepted4 : StepValid wholeStep4.shape wholeBoxes4 wholeStep4.proposed := by
  dsimp only [StepValid,wholeStep4]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep5 : Instruction 40 := ⟨.mul 6 0,⟨⟨5118882604663,5232120280162⟩,⟨0,0⟩,⟨-37023211719305,-35441962228437⟩,⟨0,0⟩,⟨0,0⟩,⟨490783940017542,523962803840603⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5
theorem wholeAccepted5 : StepValid wholeStep5.shape wholeBoxes5 wholeStep5.proposed := by
  dsimp only [StepValid,wholeStep5]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep6 : Instruction 40 := ⟨.contact 0,⟨⟨157767696384,161156694016⟩,⟨0,0⟩,⟨1036520821680,1130515927338⟩,⟨0,0⟩,⟨0,0⟩,⟨-2606454177658,1286006284937⟩⟩⟩
noncomputable def wholeBoxes7 := wholeStep6.proposed :: wholeBoxes6
theorem wholeAccepted6 : StepValid wholeStep6.shape wholeBoxes6 wholeStep6.proposed := by
  dsimp only [StepValid,wholeStep6]
  exact ⟨by decide,by decide,(⟨⟨157767696384,161156694016⟩,⟨-33573948606,-32155857752⟩,⟨12889601148,13793291176⟩⟩ : DyadicJetEnclosure 40),brwhole6_jet,by decide⟩
noncomputable def wholeStep7 : Instruction 40 := ⟨.log 10,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes8 := wholeStep7.proposed :: wholeBoxes7
theorem wholeAccepted7 : StepValid wholeStep7.shape wholeBoxes7 wholeStep7.proposed := by
  dsimp only [StepValid,wholeStep7]
  exact ⟨by decide,by decide,lc0,by decide⟩
noncomputable def wholeStep8 : Instruction 40 := ⟨.add 6 1,⟨⟨1257279324160,1260668321792⟩,⟨0,0⟩,⟨1036520821680,1130515927338⟩,⟨0,0⟩,⟨0,0⟩,⟨-2606454177658,1286006284937⟩⟩⟩
noncomputable def wholeBoxes9 := wholeStep8.proposed :: wholeBoxes8
theorem wholeAccepted8 : StepValid wholeStep8.shape wholeBoxes8 wholeStep8.proposed := by
  dsimp only [StepValid,wholeStep8]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep9 : Instruction 40 := ⟨.log 0,⟨⟨147426931776,150386679296⟩,⟨0,0⟩,⟨904017873827,988654934198⟩,⟨0,0⟩,⟨0,0⟩,⟨-3168362629379,381350817955⟩⟩⟩
noncomputable def wholeBoxes10 := wholeStep9.proposed :: wholeBoxes9
theorem wholeAccepted9 : StepValid wholeStep9.shape wholeBoxes9 wholeStep9.proposed := by
  dsimp only [StepValid,wholeStep9]
  exact ⟨by decide,by decide,lc23,by decide⟩
noncomputable def wholeStep10 : Instruction 40 := ⟨.mul 1 0,⟨⟨168581057683,172429029234⟩,⟨0,0⟩,⟨1172715261323,1288190554016⟩,⟨0,0⟩,⟨0,0⟩,⟨-2284799564712,2646207039958⟩⟩⟩
noncomputable def wholeBoxes11 := wholeStep10.proposed :: wholeBoxes10
theorem wholeAccepted10 : StepValid wholeStep10.shape wholeBoxes10 wholeStep10.proposed := by
  dsimp only [StepValid,wholeStep10]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep11 : Instruction 40 := ⟨.neg 4,⟨⟨-161156694016,-157767696384⟩,⟨0,0⟩,⟨-1130515927338,-1036520821680⟩,⟨0,0⟩,⟨0,0⟩,⟨-1286006284937,2606454177658⟩⟩⟩
noncomputable def wholeBoxes12 := wholeStep11.proposed :: wholeBoxes11
theorem wholeAccepted11 : StepValid wholeStep11.shape wholeBoxes11 wholeStep11.proposed := by
  dsimp only [StepValid,wholeStep11]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep12 : Instruction 40 := ⟨.add 10 0,⟨⟨938354933760,941743931392⟩,⟨0,0⟩,⟨-1130515927338,-1036520821680⟩,⟨0,0⟩,⟨0,0⟩,⟨-1286006284937,2606454177658⟩⟩⟩
noncomputable def wholeBoxes13 := wholeStep12.proposed :: wholeBoxes12
theorem wholeAccepted12 : StepValid wholeStep12.shape wholeBoxes12 wholeStep12.proposed := by
  dsimp only [StepValid,wholeStep12]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep13 : Instruction 40 := ⟨.log 0,⟨⟨-174265021568,-170301138112⟩,⟨0,0⟩,⟨-1324675091241,-1210166222344⟩,⟨0,0⟩,⟨0,0⟩,⟨-3102818611730,1722139597357⟩⟩⟩
noncomputable def wholeBoxes14 := wholeStep13.proposed :: wholeBoxes13
theorem wholeAccepted13 : StepValid wholeStep13.shape wholeBoxes13 wholeStep13.proposed := by
  dsimp only [StepValid,wholeStep13]
  exact ⟨by decide,by decide,lc24,by decide⟩
noncomputable def wholeStep14 : Instruction 40 := ⟨.mul 1 0,⟨⟨-149259928108,-145339902858⟩,⟨0,0⟩,⟨-974054321555,-853611766565⟩,⟨0,0⟩,⟨0,0⟩,⟨-789031598276,4402912060136⟩⟩⟩
noncomputable def wholeBoxes15 := wholeStep14.proposed :: wholeBoxes14
theorem wholeAccepted14 : StepValid wholeStep14.shape wholeBoxes14 wholeStep14.proposed := by
  dsimp only [StepValid,wholeStep14]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep15 : Instruction 40 := ⟨.add 4 0,⟨⟨19321129575,27089126376⟩,⟨0,0⟩,⟨198660939768,434578787451⟩,⟨0,0⟩,⟨0,0⟩,⟨-3073831162988,7049119100094⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15
theorem wholeAccepted15 : StepValid wholeStep15.shape wholeBoxes15 wholeStep15.proposed := by
  dsimp only [StepValid,wholeStep15]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 0 15,⟨⟨9660564787,13544563188⟩,⟨0,0⟩,⟨99330469884,217289393726⟩,⟨0,0⟩,⟨0,0⟩,⟨-1536915581494,3524559550047⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16
theorem wholeAccepted16 : StepValid wholeStep16.shape wholeBoxes16 wholeStep16.proposed := by
  dsimp only [StepValid,wholeStep16]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨-13544563188,-9660564787⟩,⟨0,0⟩,⟨-217289393726,-99330469884⟩,⟨0,0⟩,⟨0,0⟩,⟨-3524559550047,1536915581494⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17
theorem wholeAccepted17 : StepValid wholeStep17.shape wholeBoxes17 wholeStep17.proposed := by
  dsimp only [StepValid,wholeStep17]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep18 : Instruction 40 := ⟨.add 10 0,⟨⟨748578820428,752462838093⟩,⟨0,0⟩,⟨-217289393726,-99330469884⟩,⟨0,0⟩,⟨0,0⟩,⟨-3524559550047,1536915581494⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18
theorem wholeAccepted18 : StepValid wholeStep18.shape wholeBoxes18 wholeStep18.proposed := by
  dsimp only [StepValid,wholeStep18]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep19 : Instruction 40 := ⟨.mul 12 12,⟨⟨22637910681,23620923481⟩,⟨0,0⟩,⟨297458431832,331402060298⟩,⟨0,0⟩,⟨0,0⟩,⟨1190215471797,2701771851808⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19
theorem wholeAccepted19 : StepValid wholeStep19.shape wholeBoxes19 wholeStep19.proposed := by
  dsimp only [StepValid,wholeStep19]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep20 : Instruction 40 := ⟨.neg 0,⟨⟨-23620923481,-22637910681⟩,⟨0,0⟩,⟨-331402060298,-297458431832⟩,⟨0,0⟩,⟨0,0⟩,⟨-2701771851808,-1190215471797⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20
theorem wholeAccepted20 : StepValid wholeStep20.shape wholeBoxes20 wholeStep20.proposed := by
  dsimp only [StepValid,wholeStep20]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep21 : Instruction 40 := ⟨.add 19 0,⟨⟨1075890704295,1076873717095⟩,⟨0,0⟩,⟨-331402060298,-297458431832⟩,⟨0,0⟩,⟨0,0⟩,⟨-2701771851808,-1190215471797⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21
theorem wholeAccepted21 : StepValid wholeStep21.shape wholeBoxes21 wholeStep21.proposed := by
  dsimp only [StepValid,wholeStep21]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep22 : Instruction 40 := ⟨.log 0,⟨⟨-23878342336,-22874206336⟩,⟨0,0⟩,⟨-338677913391,-303711567463⟩,⟨0,0⟩,⟨0,0⟩,⟨-2865410131933,-1299128481990⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22
theorem wholeAccepted22 : StepValid wholeStep22.shape wholeBoxes22 wholeStep22.proposed := by
  dsimp only [StepValid,wholeStep22]
  exact ⟨by decide,by decide,lc21,by decide⟩
noncomputable def wholeStep23 : Instruction 40 := ⟨.mul 0 22,⟨⟨-11939171168,-11437103168⟩,⟨0,0⟩,⟨-169338956696,-151855783731⟩,⟨0,0⟩,⟨0,0⟩,⟨-1432705065967,-649564240995⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23
theorem wholeAccepted23 : StepValid wholeStep23.shape wholeBoxes23 wholeStep23.proposed := by
  dsimp only [StepValid,wholeStep23]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep24 : Instruction 40 := ⟨.neg 0,⟨⟨11437103168,11939171168⟩,⟨0,0⟩,⟨151855783731,169338956696⟩,⟨0,0⟩,⟨0,0⟩,⟨649564240995,1432705065967⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24
theorem wholeAccepted24 : StepValid wholeStep24.shape wholeBoxes24 wholeStep24.proposed := by
  dsimp only [StepValid,wholeStep24]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep25 : Instruction 40 := ⟨.add 17 0,⟨⟨773560486784,774062574048⟩,⟨0,0⟩,⟨151855783731,169338956696⟩,⟨0,0⟩,⟨0,0⟩,⟨649564240995,1432705065967⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25
theorem wholeAccepted25 : StepValid wholeStep25.shape wholeBoxes25 wholeStep25.proposed := by
  dsimp only [StepValid,wholeStep25]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep26 : Instruction 40 := ⟨.add 24 26,⟨⟨1413422197506,1413971953320⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26
theorem wholeAccepted26 : StepValid wholeStep26.shape wholeBoxes26 wholeStep26.proposed := by
  dsimp only [StepValid,wholeStep26]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep27 : Instruction 40 := ⟨.neg 27,⟨⟨-314460325544,-313910569730⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27
theorem wholeAccepted27 : StepValid wholeStep27.shape wholeBoxes27 wholeStep27.proposed := by
  dsimp only [StepValid,wholeStep27]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep28 : Instruction 40 := ⟨.add 26 0,⟨⟨785051302232,785601058046⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28
theorem wholeAccepted28 : StepValid wholeStep28.shape wholeBoxes28 wholeStep28.proposed := by
  dsimp only [StepValid,wholeStep28]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep29 : Instruction 40 := ⟨.inv 0,⟨⟨1538854622499,1539932251788⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29
theorem wholeAccepted29 : StepValid wholeStep29.shape wholeBoxes29 wholeStep29.proposed := by
  dsimp only [StepValid,wholeStep29]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep30 : Instruction 40 := ⟨.mul 3 0,⟨⟨1978197617222,1980352875800⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30
theorem wholeAccepted30 : StepValid wholeStep30.shape wholeBoxes30 wholeStep30.proposed := by
  dsimp only [StepValid,wholeStep30]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨645765201344,646962475456⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31
theorem wholeAccepted31 : StepValid wholeStep31.shape wholeBoxes31 wholeStep31.proposed := by
  dsimp only [StepValid,wholeStep31]
  exact ⟨by decide,by decide,lc12,by decide⟩
noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 0 31,⟨⟨322882600672,323481237728⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32
theorem wholeAccepted32 : StepValid wholeStep32.shape wholeBoxes32 wholeStep32.proposed := by
  dsimp only [StepValid,wholeStep32]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep33 : Instruction 40 := ⟨.inv 20,⟨⟨1283709699968,1288345993739⟩,⟨0,0⟩,⟨1412901945693,1552179898505⟩,⟨0,0⟩,⟨0,0⟩,⟨-468426865173,5505751665985⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33
theorem wholeAccepted33 : StepValid wholeStep33.shape wholeBoxes33 wholeStep33.proposed := by
  dsimp only [StepValid,wholeStep33]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep34 : Instruction 40 := ⟨.mul 25 0,⟨⟨1467907772160,1477180359702⟩,⟨0,0⟩,⟨2825803891386,3104359797010⟩,⟨0,0⟩,⟨0,0⟩,⟨-927267261655,11011503331968⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34
theorem wholeAccepted34 : StepValid wholeStep34.shape wholeBoxes34 wholeStep34.proposed := by
  dsimp only [StepValid,wholeStep34]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨317728069952,324651700864⟩,⟨0,0⟩,⟨2103334380249,2325268493262⟩,⟨0,0⟩,⟨0,0⟩,⟨-5612076807710,4224362695127⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35
theorem wholeAccepted35 : StepValid wholeStep35.shape wholeBoxes35 wholeStep35.proposed := by
  dsimp only [StepValid,wholeStep35]
  exact ⟨by decide,by decide,lc27,by decide⟩
noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 0 35,⟨⟨158864034976,162325850432⟩,⟨0,0⟩,⟨1051667190124,1162634246631⟩,⟨0,0⟩,⟨0,0⟩,⟨-2806038403855,2112181347564⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36
theorem wholeAccepted36 : StepValid wholeStep36.shape wholeBoxes36 wholeStep36.proposed := by
  dsimp only [StepValid,wholeStep36]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep37 : Instruction 40 := ⟨.mul 40 11,⟨⟨1547120973568,1548125148096⟩,⟨0,0⟩,⟨303711567462,338677913392⟩,⟨0,0⟩,⟨0,0⟩,⟨1299128481990,2865410131934⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37
theorem wholeAccepted37 : StepValid wholeStep37.shape wholeBoxes37 wholeStep37.proposed := by
  dsimp only [StepValid,wholeStep37]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep38 : Instruction 40 := ⟨.add 0 17,⟨⟨1523500050087,1525487237415⟩,⟨0,0⟩,⟨-27690492836,41219481560⟩,⟨0,0⟩,⟨0,0⟩,⟨-1402643369818,1675194660137⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38
theorem wholeAccepted38 : StepValid wholeStep38.shape wholeBoxes38 wholeStep38.proposed := by
  dsimp only [StepValid,wholeStep38]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep39 : Instruction 40 := ⟨.mul 20 0,⟨⟨1037242209728,1043983917171⟩,⟨0,0⟩,⟨-320422499302,-109424807091⟩,⟨0,0⟩,⟨0,0⟩,⟨-5866259684179,3289733771162⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39
theorem wholeAccepted39 : StepValid wholeStep39.shape wholeBoxes39 wholeStep39.proposed := by
  dsimp only [StepValid,wholeStep39]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep40 : Instruction 40 := ⟨.mul 43 41,⟨⟨1478640429186,1478806475982⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40
theorem wholeAccepted40 : StepValid wholeStep40.shape wholeBoxes40 wholeStep40.proposed := by
  dsimp only [StepValid,wholeStep40]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 19 19,⟨⟨1052777231587,1054701899712⟩,⟨0,0⟩,⟨-649157606906,-582136202360⟩,⟨0,0⟩,⟨0,0⟩,⟨-5131342874178,-2129517154834⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41
theorem wholeAccepted41 : StepValid wholeStep41.shape wholeBoxes41 wholeStep41.proposed := by
  dsimp only [StepValid,wholeStep41]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep42 : Instruction 40 := ⟨.mul 1 0,⟨⟨1415791282443,1418538885923⟩,⟨0,0⟩,⟨-873095335033,-782865867315⟩,⟨0,0⟩,⟨0,0⟩,⟨-6901485060388,-2863807967317⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42
theorem wholeAccepted42 : StepValid wholeStep42.shape wholeBoxes42 wholeStep42.proposed := by
  dsimp only [StepValid,wholeStep42]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep43 : Instruction 40 := ⟨.mul 17 17,⟨⟨544237833958,544944549385⟩,⟨0,0⟩,⟨213676019454,238431218726⟩,⟨0,0⟩,⟨0,0⟩,⟨955946979072,2069426142898⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43
theorem wholeAccepted43 : StepValid wholeStep43.shape wholeBoxes43 wholeStep43.proposed := by
  dsimp only [StepValid,wholeStep43]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep44 : Instruction 40 := ⟨.mul 18 0,⟨⟨382898073224,383644128861⟩,⟨0,0⟩,⟨225497377354,251785444881⟩,⟨0,0⟩,⟨0,0⟩,⟨1053100390712,2240414261174⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44
theorem wholeAccepted44 : StepValid wholeStep44.shape wholeBoxes44 wholeStep44.proposed := by
  dsimp only [StepValid,wholeStep44]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 2 0,⟨⟨493040492196,494959854355⟩,⟨0,0⟩,⟨-14279683592,52213738206⟩,⟨0,0⟩,⟨0,0⟩,⟨-1451925769147,1572061407829⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45
theorem wholeAccepted45 : StepValid wholeStep45.shape wholeBoxes45 wholeStep45.proposed := by
  dsimp only [StepValid,wholeStep45]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep46 : Instruction 40 := ⟨.inv 0,⟨⟨2442472473227,2451980798231⟩,⟨0,0⟩,⟨-259668496831,71015485598⟩,⟨0,0⟩,⟨0,0⟩,⟨-7833191015172,7275691731236⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46
theorem wholeAccepted46 : StepValid wholeStep46.shape wholeBoxes46 wholeStep46.proposed := by
  dsimp only [StepValid,wholeStep46]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep47 : Instruction 40 := ⟨.mul 7 0,⟨⟨2304146205760,2328150475083⟩,⟨0,0⟩,⟨-961117211862,-175648942215⟩,⟨0,0⟩,⟨0,0⟩,⟨-20561120856457,14395915467845⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47
theorem wholeAccepted47 : StepValid wholeStep47.shape wholeBoxes47 wholeStep47.proposed := by
  dsimp only [StepValid,wholeStep47]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep48 : Instruction 40 := ⟨.neg 11,⟨⟨-162325850432,-158864034976⟩,⟨0,0⟩,⟨-1162634246631,-1051667190124⟩,⟨0,0⟩,⟨0,0⟩,⟨-2112181347564,2806038403855⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48
theorem wholeAccepted48 : StepValid wholeStep48.shape wholeBoxes48 wholeStep48.proposed := by
  dsimp only [StepValid,wholeStep48]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep49 : Instruction 40 := ⟨.mul 0 10,⟨⟨-225214546969,-220124425361⟩,⟨0,0⟩,⟨-1619150400453,-1453117996815⟩,⟨0,0⟩,⟨0,0⟩,⟨-3264976338362,4158799930512⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49
theorem wholeAccepted49 : StepValid wholeStep49.shape wholeBoxes49 wholeStep49.proposed := by
  dsimp only [StepValid,wholeStep49]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 53 43,⟨⟨315535392768,322313388032⟩,⟨0,0⟩,⟨2073041643360,2261031854676⟩,⟨0,0⟩,⟨0,0⟩,⟨-5212908355316,2572012569874⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50
theorem wholeAccepted50 : StepValid wholeStep50.shape wholeBoxes50 wholeStep50.proposed := by
  dsimp only [StepValid,wholeStep50]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep51 : Instruction 40 := ⟨.inv 29,⟨⟨1122625429911,1123651142992⟩,⟨0,0⟩,⟨310096155765,346113506101⟩,⟨0,0⟩,⟨0,0⟩,⟨1412094625389,3034931405573⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51
theorem wholeAccepted51 : StepValid wholeStep51.shape wholeBoxes51 wholeStep51.proposed := by
  dsimp only [StepValid,wholeStep51]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep52 : Instruction 40 := ⟨.mul 1 0,⟨⟨322168540113,329389701496⟩,⟨0,0⟩,⟨2205611579852,2412132784815⟩,⟨0,0⟩,⟨0,0⟩,⟨-3752793519037,4941640520848⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52
theorem wholeAccepted52 : StepValid wholeStep52.shape wholeBoxes52 wholeStep52.proposed := by
  dsimp only [StepValid,wholeStep52]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep53 : Instruction 40 := ⟨.neg 2,⟨⟨-322313388032,-315535392768⟩,⟨0,0⟩,⟨-2261031854676,-2073041643360⟩,⟨0,0⟩,⟨0,0⟩,⟨-2572012569874,5212908355316⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53
theorem wholeAccepted53 : StepValid wholeStep53.shape wholeBoxes53 wholeStep53.proposed := by
  dsimp only [StepValid,wholeStep53]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep54 : Instruction 40 := ⟨.add 1 0,⟨⟨-144847919,13854308728⟩,⟨0,0⟩,⟨-55420274824,339091141455⟩,⟨0,0⟩,⟨0,0⟩,⟨-6324806088911,10154548876164⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54
theorem wholeAccepted54 : StepValid wholeStep54.shape wholeBoxes54 wholeStep54.proposed := by
  dsimp only [StepValid,wholeStep54]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 36 0,⟨⟨-99128262,9481348084⟩,⟨0,0⟩,⟨-40665410440,232089365990⟩,⟨0,0⟩,⟨0,0⟩,⟨-4506886119341,6990647348814⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55
theorem wholeAccepted55 : StepValid wholeStep55.shape wholeBoxes55 wholeStep55.proposed := by
  dsimp only [StepValid,wholeStep55]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep56 : Instruction 40 := ⟨.add 6 0,⟨⟨-225313675231,-210643077277⟩,⟨0,0⟩,⟨-1659815810893,-1221028630825⟩,⟨0,0⟩,⟨0,0⟩,⟨-7771862457703,11149447279326⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56
theorem wholeAccepted56 : StepValid wholeStep56.shape wholeBoxes56 wholeStep56.proposed := by
  dsimp only [StepValid,wholeStep56]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep57 : Instruction 40 := ⟨.mul 0 10,⟨⟨-502463813287,-467925854468⟩,⟨0,0⟩,⟨-3716047337520,-2659200578317⟩,⟨0,0⟩,⟨0,0⟩,⟨-19037102545755,27253153757078⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57
theorem wholeAccepted57 : StepValid wholeStep57.shape wholeBoxes57 wholeStep57.proposed := by
  dsimp only [StepValid,wholeStep57]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 54 51,⟨⟨631070785536,644626776064⟩,⟨0,0⟩,⟨4146083286720,4522063709352⟩,⟨0,0⟩,⟨0,0⟩,⟨-10425816710632,5144025139748⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58
theorem wholeAccepted58 : StepValid wholeStep58.shape wholeBoxes58 wholeStep58.proposed := by
  dsimp only [StepValid,wholeStep58]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep59 : Instruction 40 := ⟨.mul 0 7,⟨⟨644337080226,658779402991⟩,⟨0,0⟩,⟨4411223159705,4824265569630⟩,⟨0,0⟩,⟨0,0⟩,⟨-7505587038073,9883281041694⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59
theorem wholeAccepted59 : StepValid wholeStep59.shape wholeBoxes59 wholeStep59.proposed := by
  dsimp only [StepValid,wholeStep59]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 57 53,⟨⟨473303089152,483470082048⟩,⟨0,0⟩,⟨3109562465040,3391547782014⟩,⟨0,0⟩,⟨0,0⟩,⟨-7819362532974,3858018854811⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60
theorem wholeAccepted60 : StepValid wholeStep60.shape wholeBoxes60 wholeStep60.proposed := by
  dsimp only [StepValid,wholeStep60]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 39 35,⟨⟨756942005810,758125353404⟩,⟨0,0⟩,⟨-84715525855,-43424204321⟩,⟨0,0⟩,⟨0,0⟩,⟨-1368533870527,483666739058⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61
theorem wholeAccepted61 : StepValid wholeStep61.shape wholeBoxes61 wholeStep61.proposed := by
  dsimp only [StepValid,wholeStep61]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep62 : Instruction 40 := ⟨.inv 0,⟨⟨1594625234714,1597118154807⟩,⟨0,0⟩,⟨91337575899,178746460494⟩,⟨0,0⟩,⟨0,0⟩,⟨-1010054644360,2927563107703⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62
theorem wholeAccepted62 : StepValid wholeStep62.shape wholeBoxes62 wholeStep62.proposed := by
  dsimp only [StepValid,wholeStep62]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep63 : Instruction 40 := ⟨.mul 2 0,⟨⟨686432985848,702274378769⟩,⟨0,0⟩,⟨4549126181246,5005059485003⟩,⟨0,0⟩,⟨0,0⟩,⟨-11285680799926,7994054116127⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63
theorem wholeAccepted63 : StepValid wholeStep63.shape wholeBoxes63 wholeStep63.proposed := by
  dsimp only [StepValid,wholeStep63]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep64 : Instruction 40 := ⟨.neg 0,⟨⟨-702274378769,-686432985848⟩,⟨0,0⟩,⟨-5005059485003,-4549126181246⟩,⟨0,0⟩,⟨0,0⟩,⟨-7994054116127,11285680799926⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64
theorem wholeAccepted64 : StepValid wholeStep64.shape wholeBoxes64 wholeStep64.proposed := by
  dsimp only [StepValid,wholeStep64]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep65 : Instruction 40 := ⟨.add 5 0,⟨⟨-57937298543,-27653582857⟩,⟨0,0⟩,⟨-593836325298,275139388384⟩,⟨0,0⟩,⟨0,0⟩,⟨-15499641154200,21168961841620⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65
theorem wholeAccepted65 : StepValid wholeStep65.shape wholeBoxes65 wholeStep65.proposed := by
  dsimp only [StepValid,wholeStep65]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 18 0,⟨⟨-122678783672,-57951090653⟩,⟨0,0⟩,⟨-1252995389485,633236079575⟩,⟨0,0⟩,⟨0,0⟩,⟨-34059157562936,46945639944687⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66
theorem wholeAccepted66 : StepValid wholeStep66.shape wholeBoxes66 wholeStep66.proposed := by
  dsimp only [StepValid,wholeStep66]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep67 : Instruction 40 := ⟨.add 9 0,⟨⟨-625142596959,-525876945121⟩,⟨0,0⟩,⟨-4969042727005,-2025964498742⟩,⟨0,0⟩,⟨0,0⟩,⟨-53096260108691,74198793701765⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67
theorem wholeAccepted67 : StepValid wholeStep67.shape wholeBoxes67 wholeStep67.proposed := by
  dsimp only [StepValid,wholeStep67]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 61 29,⟨⟨218605321918,223592432982⟩,⟨0,0⟩,⟨1432160402567,1574544889287⟩,⟨0,0⟩,⟨0,0⟩,⟨-3878783025050,2114532952883⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68
theorem wholeAccepted68 : StepValid wholeStep68.shape wholeBoxes68 wholeStep68.proposed := by
  dsimp only [StepValid,wholeStep68]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 27 25,⟨⟨521105175866,522735764639⟩,⟨0,0⟩,⟨-117144419490,-59432465150⟩,⟨0,0⟩,⟨0,0⟩,⟨-1909445013424,704755427711⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69
theorem wholeAccepted69 : StepValid wholeStep69.shape wholeBoxes69 wholeStep69.proposed := by
  dsimp only [StepValid,wholeStep69]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨2312690084347,2319926716532⟩,⟨0,0⟩,⟨262941398194,521519418832⟩,⟨0,0⟩,⟨0,0⟩,⟨-3077735555153,8735201434087⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70
theorem wholeAccepted70 : StepValid wholeStep70.shape wholeBoxes70 wholeStep70.proposed := by
  dsimp only [StepValid,wholeStep70]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 2 0,⟨⟨459809926165,471771326274⟩,⟨0,0⟩,⟨3064654766793,3428282571568⟩,⟨0,0⟩,⟨0,0⟩,⟨-8124972947298,7731612552370⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71
theorem wholeAccepted71 : StepValid wholeStep71.shape wholeBoxes71 wholeStep71.proposed := by
  dsimp only [StepValid,wholeStep71]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 65 39,⟨⟨46330064024,47413020046⟩,⟨0,0⟩,⟨304384719633,332602841306⟩,⟨0,0⟩,⟨0,0⟩,⟨-766830474705,378348799839⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72
theorem wholeAccepted72 : StepValid wholeStep72.shape wholeBoxes72 wholeStep72.proposed := by
  dsimp only [StepValid,wholeStep72]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep73 : Instruction 40 := ⟨.add 54 0,⟨⟨794908884452,799875858139⟩,⟨0,0⟩,⟨87095325907,233272371422⟩,⟨0,0⟩,⟨0,0⟩,⟨-4291390024752,1915264381333⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73
theorem wholeAccepted73 : StepValid wholeStep73.shape wholeBoxes73 wholeStep73.proposed := by
  dsimp only [StepValid,wholeStep73]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 0 0,⟨⟨574691634556,581895972968⟩,⟨0,0⟩,⟨125933817538,339403301536⟩,⟨0,0⟩,⟨0,0⟩,⟨-6230027216340,2885626126684⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74
theorem wholeAccepted74 : StepValid wholeStep74.shape wholeBoxes74 wholeStep74.proposed := by
  dsimp only [StepValid,wholeStep74]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep75 : Instruction 40 := ⟨.mul 7 0,⟨⟨-330845032023,-274864834106⟩,⟨0,0⟩,⟨-2822745421954,-1119161007035⟩,⟨0,0⟩,⟨0,0⟩,⟨-32808608704396,42346400514583⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75
theorem wholeAccepted75 : StepValid wholeStep75.shape wholeBoxes75 wholeStep75.proposed := by
  dsimp only [StepValid,wholeStep75]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep76 : Instruction 40 := ⟨.mul 79 28,⟨⟨4608292411520,4656300950166⟩,⟨0,0⟩,⟨-1922234423724,-351297884430⟩,⟨0,0⟩,⟨0,0⟩,⟨-41122241712914,28791830935690⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76
theorem wholeAccepted76 : StepValid wholeStep76.shape wholeBoxes76 wholeStep76.proposed := by
  dsimp only [StepValid,wholeStep76]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 0 3,⟨⟨3331636053253,3387379109216⟩,⟨0,0⟩,⟨-1033357129713,733904521693⟩,⟨0,0⟩,⟨0,0⟩,⟨-48904894532285,29000825659959⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77
theorem wholeAccepted77 : StepValid wholeStep77.shape wholeBoxes77 wholeStep77.proposed := by
  dsimp only [StepValid,wholeStep77]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep78 : Instruction 40 := ⟨.add 45 29,⟨⟨160556750240,164617202752⟩,⟨0,0⟩,⟨-1162634246631,-1051667190124⟩,⟨0,0⟩,⟨0,0⟩,⟨-2112181347564,2806038403855⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78
theorem wholeAccepted78 : StepValid wholeStep78.shape wholeBoxes78 wholeStep78.proposed := by
  dsimp only [StepValid,wholeStep78]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 1 0,⟨⟨486503866061,507153230156⟩,⟨0,0⟩,⟨-3736560137291,-3076783302451⟩,⟨0,0⟩,⟨0,0⟩,⟨-15381257045881,15172175556042⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79
theorem wholeAccepted79 : StepValid wholeStep79.shape wholeBoxes79 wholeStep79.proposed := by
  dsimp only [StepValid,wholeStep79]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep80 : Instruction 40 := ⟨.add 4 0,⟨⟨155658834038,232288396050⟩,⟨0,0⟩,⟨-6559305559245,-4195944309486⟩,⟨0,0⟩,⟨0,0⟩,⟨-48189865750277,57518576070625⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80
theorem wholeAccepted80 : StepValid wholeStep80.shape wholeBoxes80 wholeStep80.proposed := by
  dsimp only [StepValid,wholeStep80]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep81 : Instruction 40 := ⟨.mul 81 81,⟨⟨89621467657,89935653106⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81
theorem wholeAccepted81 : StepValid wholeStep81.shape wholeBoxes81 wholeStep81.proposed := by
  dsimp only [StepValid,wholeStep81]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep82 : Instruction 40 := ⟨.neg 0,⟨⟨-89935653106,-89621467657⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82
theorem wholeAccepted82 : StepValid wholeStep82.shape wholeBoxes82 wholeStep82.proposed := by
  dsimp only [StepValid,wholeStep82]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep83 : Instruction 40 := ⟨.add 81 0,⟨⟨1009575974670,1009890160119⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83
theorem wholeAccepted83 : StepValid wholeStep83.shape wholeBoxes83 wholeStep83.proposed := by
  dsimp only [StepValid,wholeStep83]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep84 : Instruction 40 := ⟨.inv 0,⟨⟨1197086443016,1197458982728⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes85 := wholeStep84.proposed :: wholeBoxes84
theorem wholeAccepted84 : StepValid wholeStep84.shape wholeBoxes84 wholeStep84.proposed := by
  dsimp only [StepValid,wholeStep84]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep85 : Instruction 40 := ⟨.mul 13 0,⟨⟨500615195939,513797942804⟩,⟨0,0⟩,⟨3336623807492,3733682897886⟩,⟨0,0⟩,⟨0,0⟩,⟨-8848766665473,8420364703678⟩⟩⟩
noncomputable def wholeBoxes86 := wholeStep85.proposed :: wholeBoxes85
theorem wholeAccepted85 : StepValid wholeStep85.shape wholeBoxes85 wholeStep85.proposed := by
  dsimp only [StepValid,wholeStep85]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep86 : Instruction 40 := ⟨.add 5 0,⟨⟨656274029977,746086338854⟩,⟨0,0⟩,⟨-3222681751753,-462261411600⟩,⟨0,0⟩,⟨0,0⟩,⟨-57038632415750,65938940774303⟩⟩⟩
noncomputable def wholeBoxes87 := wholeStep86.proposed :: wholeBoxes86
theorem wholeAccepted86 : StepValid wholeStep86.shape wholeBoxes86 wholeStep86.proposed := by
  dsimp only [StepValid,wholeStep86]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep87 : Instruction 40 := ⟨.mul 0 68,⟨⟨446810044411,510592366479⟩,⟨0,0⟩,⟨-2352921824633,-374008877765⟩,⟨0,0⟩,⟨0,0⟩,⟨-41343122277632,47442684593284⟩⟩⟩
noncomputable def wholeBoxes88 := wholeStep87.proposed :: wholeBoxes87
theorem wholeAccepted87 : StepValid wholeStep87.shape wholeBoxes87 wholeStep87.proposed := by
  dsimp only [StepValid,wholeStep87]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep88 : Instruction 40 := ⟨.mul 0 69,⟨⟨304200999381,349429484404⟩,⟨0,0⟩,⟨-1711152926626,-295000951342⟩,⟨0,0⟩,⟨0,0⟩,⟨-29862781385391,34111621401432⟩⟩⟩
noncomputable def wholeBoxes89 := wholeStep88.proposed :: wholeBoxes88
theorem wholeAccepted88 : StepValid wholeStep88.shape wholeBoxes88 wholeStep88.proposed := by
  dsimp only [StepValid,wholeStep88]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep89 : Instruction 40 := ⟨.mul 90 63,⟨⟨520148119075,520544175433⟩,⟨0,0⟩,⟨102109016202,113877625062⟩,⟨0,0⟩,⟨0,0⟩,⟨436772073994,963470269983⟩⟩⟩
noncomputable def wholeBoxes90 := wholeStep89.proposed :: wholeBoxes89
theorem wholeAccepted89 : StepValid wholeStep89.shape wholeBoxes89 wholeStep89.proposed := by
  dsimp only [StepValid,wholeStep89]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep90 : Instruction 40 := ⟨.inv 0,⟨⟨2322426946010,2324195311452⟩,⟨0,0⟩,⟨-508843217042,-455563123841⟩,⟨0,0⟩,⟨0,0⟩,⟨-4126381670631,-1725869424177⟩⟩⟩
noncomputable def wholeBoxes91 := wholeStep90.proposed :: wholeBoxes90
theorem wholeAccepted90 : StepValid wholeStep90.shape wholeBoxes90 wholeStep90.proposed := by
  dsimp only [StepValid,wholeStep90]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 2 0,⟨⟨642543998733,738639181996⟩,⟨0,0⟩,⟨-3778821730718,-749151618991⟩,⟨0,0⟩,⟨0,0⟩,⟨-64192165875836,73212937826310⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91
theorem wholeAccepted91 : StepValid wholeStep91.shape wholeBoxes91 wholeStep91.proposed := by
  dsimp only [StepValid,wholeStep91]
  exact ⟨by decide,by decide⟩
noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91]
theorem wholeAccepted : Accepted wholeProgram wholeInitial :=
  ⟨wholeAccepted0,⟨wholeAccepted1,⟨wholeAccepted2,⟨wholeAccepted3,⟨wholeAccepted4,⟨wholeAccepted5,⟨wholeAccepted6,⟨wholeAccepted7,⟨wholeAccepted8,⟨wholeAccepted9,⟨wholeAccepted10,⟨wholeAccepted11,⟨wholeAccepted12,⟨wholeAccepted13,⟨wholeAccepted14,⟨wholeAccepted15,⟨wholeAccepted16,⟨wholeAccepted17,⟨wholeAccepted18,⟨wholeAccepted19,⟨wholeAccepted20,⟨wholeAccepted21,⟨wholeAccepted22,⟨wholeAccepted23,⟨wholeAccepted24,⟨wholeAccepted25,⟨wholeAccepted26,⟨wholeAccepted27,⟨wholeAccepted28,⟨wholeAccepted29,⟨wholeAccepted30,⟨wholeAccepted31,⟨wholeAccepted32,⟨wholeAccepted33,⟨wholeAccepted34,⟨wholeAccepted35,⟨wholeAccepted36,⟨wholeAccepted37,⟨wholeAccepted38,⟨wholeAccepted39,⟨wholeAccepted40,⟨wholeAccepted41,⟨wholeAccepted42,⟨wholeAccepted43,⟨wholeAccepted44,⟨wholeAccepted45,⟨wholeAccepted46,⟨wholeAccepted47,⟨wholeAccepted48,⟨wholeAccepted49,⟨wholeAccepted50,⟨wholeAccepted51,⟨wholeAccepted52,⟨wholeAccepted53,⟨wholeAccepted54,⟨wholeAccepted55,⟨wholeAccepted56,⟨wholeAccepted57,⟨wholeAccepted58,⟨wholeAccepted59,⟨wholeAccepted60,⟨wholeAccepted61,⟨wholeAccepted62,⟨wholeAccepted63,⟨wholeAccepted64,⟨wholeAccepted65,⟨wholeAccepted66,⟨wholeAccepted67,⟨wholeAccepted68,⟨wholeAccepted69,⟨wholeAccepted70,⟨wholeAccepted71,⟨wholeAccepted72,⟨wholeAccepted73,⟨wholeAccepted74,⟨wholeAccepted75,⟨wholeAccepted76,⟨wholeAccepted77,⟨wholeAccepted78,⟨wholeAccepted79,⟨wholeAccepted80,⟨wholeAccepted81,⟨wholeAccepted82,⟨wholeAccepted83,⟨wholeAccepted84,⟨wholeAccepted85,⟨wholeAccepted86,⟨wholeAccepted87,⟨wholeAccepted88,⟨wholeAccepted89,⟨wholeAccepted90,⟨wholeAccepted91,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
noncomputable def whole_output : DyadicBivariateJetEnclosure 40 := ⟨⟨642543998733,738639181996⟩,⟨0,0⟩,⟨-3778821730718,-749151618991⟩,⟨0,0⟩,⟨0,0⟩,⟨-64192165875836,73212937826310⟩⟩
theorem whole_output_eq : (finalBoxes wholeProgram wholeInitial).getD 0 (zeroBox 40)=whole_output := rfl
open GeneralCK.Reflection GeneralCK.Reflection.SmallRatio GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed
theorem sameShape : shapes centerProgram=shapes wholeProgram := by decide
theorem scalar_program (a e r : ℝ) :
    (evalRealProgram wholeProgram [a,e,r,2]).getD 0 0=ReflectionMidpointKernel.scalarCore a e r := rfl
attribute [local irreducible] wholeProgram centerProgram
noncomputable def reflection_log_0_out : DyadicInterval 64 := ⟨-12786308645202662930,-12786308645202655416⟩
theorem reflection_log_0_checked : DyadicFastLog.check 1 2 1 16 reflection_log_0_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointFamily.Endpoints0421.sharedTwo_eq]
  decide
theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := DyadicFastLog.check_sound reflection_log_0_checked
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1):ℝ)=((1 / 2):ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [he]
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_0_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_1_out : DyadicInterval 64 := ⟨-4640031761581636947,-4640031761581636896⟩
theorem reflection_log_1_checked : DyadicFastLog.check 500 643 0 16 reflection_log_1_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointFamily.Endpoints0421.sharedTwo_eq]
  decide
theorem reflection_log_1 : Bounds (2012293 / 8000000) (125768313 / 500000000) (Real.log (643 / 500)) := by
  have h := DyadicFastLog.check_sound reflection_log_1_checked
  have he : Real.log (643 / 500) = -Real.log (500 / 643) := by
    rw [show ((643 / 500):ℝ)=((500 / 643):ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [he]
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_1_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_2_out : DyadicInterval 64 := ⟨-6214197410622815977,-6214197410622815922⟩
theorem reflection_log_2_checked : DyadicFastLog.check 357 500 0 16 reflection_log_2_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointFamily.Endpoints0421.sharedTwo_eq]
  decide
theorem reflection_log_2 : Bounds (-336872317 / 1000000000) (-84218079 / 250000000) (Real.log (357 / 500)) := by
  have h := DyadicFastLog.check_sound reflection_log_2_checked
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_2_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_3_out : DyadicInterval 64 := ⟨-4632858226949640541,-4632858226949640492⟩
theorem reflection_log_3_checked : DyadicFastLog.check 2000 2571 0 16 reflection_log_3_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointFamily.Endpoints0421.sharedTwo_eq]
  decide
theorem reflection_log_3 : Bounds (251147747 / 1000000000) (62786937 / 250000000) (Real.log (2571 / 2000)) := by
  have h := DyadicFastLog.check_sound reflection_log_3_checked
  have he : Real.log (2571 / 2000) = -Real.log (2000 / 2571) := by
    rw [show ((2571 / 2000):ℝ)=((2000 / 2571):ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [he]
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_3_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_4_out : DyadicInterval 64 := ⟨-6201284043575544723,-6201284043575544674⟩
theorem reflection_log_4_checked : DyadicFastLog.check 1429 2000 0 16 reflection_log_4_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointFamily.Endpoints0421.sharedTwo_eq]
  decide
theorem reflection_log_4 : Bounds (-168086141 / 500000000) (-336172281 / 1000000000) (Real.log (1429 / 2000)) := by
  have h := DyadicFastLog.check_sound reflection_log_4_checked
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_4_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_5_out : DyadicInterval 64 := ⟨-52682388094647239,-52682388094647192⟩
theorem reflection_log_5_checked : DyadicFastLog.check 50000 50143 0 16 reflection_log_5_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointFamily.Endpoints0421.sharedTwo_eq]
  decide
theorem reflection_log_5 : Bounds (2855917 / 1000000000) (1427959 / 500000000) (Real.log (50143 / 50000)) := by
  have h := DyadicFastLog.check_sound reflection_log_5_checked
  have he : Real.log (50143 / 50000) = -Real.log (50000 / 50143) := by
    rw [show ((50143 / 50000):ℝ)=((50000 / 50143):ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [he]
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_5_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_6_out : DyadicInterval 64 := ⟨-52833275699573519,-52833275699573474⟩
theorem reflection_log_6_checked : DyadicFastLog.check 49857 50000 0 16 reflection_log_6_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointFamily.Endpoints0421.sharedTwo_eq]
  decide
theorem reflection_log_6 : Bounds (-1432049 / 500000000) (-2864097 / 1000000000) (Real.log (49857 / 50000)) := by
  have h := DyadicFastLog.check_sound reflection_log_6_checked
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_6_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_7_out : DyadicInterval 64 := ⟨-5265793776745393,-5265793776745348⟩
theorem reflection_log_7_checked : DyadicFastLog.check 2000000 2000571 0 16 reflection_log_7_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointFamily.Endpoints0421.sharedTwo_eq]
  decide
theorem reflection_log_7 : Bounds (285459 / 1000000000) (14273 / 50000000) (Real.log (2000571 / 2000000)) := by
  have h := DyadicFastLog.check_sound reflection_log_7_checked
  have he : Real.log (2000571 / 2000000) = -Real.log (2000000 / 2000571) := by
    rw [show ((2000571 / 2000000):ℝ)=((2000000 / 2000571):ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [he]
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_7_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_8_out : DyadicInterval 64 := ⟨-5267297375527807,-5267297375527762⟩
theorem reflection_log_8_checked : DyadicFastLog.check 1999429 2000000 0 16 reflection_log_8_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointFamily.Endpoints0421.sharedTwo_eq]
  decide
theorem reflection_log_8 : Bounds (-285541 / 1000000000) (-14277 / 50000000) (Real.log (1999429 / 2000000)) := by
  have h := DyadicFastLog.check_sound reflection_log_8_checked
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_8_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
theorem entropy_bound {a z : ℝ} (ha : Bounds (571 / 2000) (143 / 500) a) (hz : Bounds (1 / 1000) (1 / 100) z) :
  Bounds (336203909043 / 500000000000) (336241663713 / 500000000000) ((biasE a+biasE (a*z))/2) := by
  let x0 : ℝ := Real.log (2 / 1)
  have hx0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x0 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x1 : ℝ := (1 / 1)+(143 / 500)
  have hx1 : Bounds (643 / 500) (643 / 500) x1 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((143 / 500) : ℝ)) <;> norm_num
  let x2 : ℝ := (1 / 1)+(143 / 500)
  have hx2 : Bounds (643 / 500) (643 / 500) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((143 / 500) : ℝ)) <;> norm_num
  let x3 : ℝ := Real.log x2
  have hx3 : Bounds (2012293 / 8000000) (125768313 / 500000000) x3 := by
    exact bounds_log hx2 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x4 : ℝ := x1*x3
  have hx4 : Bounds (1293904399 / 4000000000) (80869025259 / 250000000000) x4 := by
    apply bounds_mul hx1 hx3 <;> norm_num
  let x5 : ℝ := -(143 / 500)
  have hx5 : Bounds (-143 / 500) (-143 / 500) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((143 / 500) : ℝ))
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (357 / 500) (357 / 500) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-(143 / 500)
  have hx7 : Bounds (357 / 500) (357 / 500) x7 := by
    exact hx6
  let x8 : ℝ := -(143 / 500)
  have hx8 : Bounds (-143 / 500) (-143 / 500) x8 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((143 / 500) : ℝ))
  let x9 : ℝ := (1 / 1)+x8
  have hx9 : Bounds (357 / 500) (357 / 500) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx8 <;> norm_num
  let x10 : ℝ := (1 / 1)-(143 / 500)
  have hx10 : Bounds (357 / 500) (357 / 500) x10 := by
    exact hx9
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (-336872317 / 1000000000) (-84218079 / 250000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x12 : ℝ := x7*x11
  have hx12 : Bounds (-120263417169 / 500000000000) (-30065854203 / 125000000000) x12 := by
    apply bounds_mul hx7 hx11 <;> norm_num
  let x13 : ℝ := x4+x12
  have hx13 : Bounds (20737316353 / 250000000000) (20737316853 / 250000000000) x13 := by
    apply bounds_add hx4 hx12 <;> norm_num
  let x14 : ℝ := (2 / 1)⁻¹
  have hx14 : Bounds (1 / 2) (1 / 2) x14 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x15 : ℝ := x13*x14
  have hx15 : Bounds (20737316353 / 500000000000) (20737316853 / 500000000000) x15 := by
    apply bounds_mul hx13 hx14 <;> norm_num
  let x16 : ℝ := x13/(2 / 1)
  have hx16 : Bounds (20737316353 / 500000000000) (20737316853 / 500000000000) x16 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx15
  let x17 : ℝ := -x16
  have hx17 : Bounds (-20737316853 / 500000000000) (-20737316353 / 500000000000) x17 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx16
  let x18 : ℝ := x0+x17
  have hx18 : Bounds (325836273147 / 500000000000) (325836274147 / 500000000000) x18 := by
    apply bounds_add hx0 hx17 <;> norm_num
  let x19 : ℝ := x0-x16
  have hx19 : Bounds (325836273147 / 500000000000) (325836274147 / 500000000000) x19 := by
    exact hx18
  let x20 : ℝ := biasE (143 / 500)
  have hx20 : Bounds (325836273147 / 500000000000) (325836274147 / 500000000000) x20 := by
    simpa +zetaDelta only [biasE, div_one] using hx19
  let x21 : ℝ := Real.log (2 / 1)
  have hx21 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x21 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x22 : ℝ := (1 / 1)+(571 / 2000)
  have hx22 : Bounds (2571 / 2000) (2571 / 2000) x22 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((571 / 2000) : ℝ)) <;> norm_num
  let x23 : ℝ := (1 / 1)+(571 / 2000)
  have hx23 : Bounds (2571 / 2000) (2571 / 2000) x23 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((571 / 2000) : ℝ)) <;> norm_num
  let x24 : ℝ := Real.log x23
  have hx24 : Bounds (251147747 / 1000000000) (62786937 / 250000000) x24 := by
    exact bounds_log hx23 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x25 : ℝ := x22*x24
  have hx25 : Bounds (10089075899 / 31250000000) (161425215027 / 500000000000) x25 := by
    apply bounds_mul hx22 hx24 <;> norm_num
  let x26 : ℝ := -(571 / 2000)
  have hx26 : Bounds (-571 / 2000) (-571 / 2000) x26 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((571 / 2000) : ℝ))
  let x27 : ℝ := (1 / 1)+x26
  have hx27 : Bounds (1429 / 2000) (1429 / 2000) x27 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx26 <;> norm_num
  let x28 : ℝ := (1 / 1)-(571 / 2000)
  have hx28 : Bounds (1429 / 2000) (1429 / 2000) x28 := by
    exact hx27
  let x29 : ℝ := -(571 / 2000)
  have hx29 : Bounds (-571 / 2000) (-571 / 2000) x29 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((571 / 2000) : ℝ))
  let x30 : ℝ := (1 / 1)+x29
  have hx30 : Bounds (1429 / 2000) (1429 / 2000) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx29 <;> norm_num
  let x31 : ℝ := (1 / 1)-(571 / 2000)
  have hx31 : Bounds (1429 / 2000) (1429 / 2000) x31 := by
    exact hx30
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (-168086141 / 500000000) (-336172281 / 1000000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x33 : ℝ := x28*x32
  have hx33 : Bounds (-240195095489 / 1000000000000) (-120097547387 / 500000000000) x33 := by
    apply bounds_mul hx28 hx32 <;> norm_num
  let x34 : ℝ := x25+x33
  have hx34 : Bounds (82655333279 / 1000000000000) (1033191691 / 12500000000) x34 := by
    apply bounds_add hx25 hx33 <;> norm_num
  let x35 : ℝ := (2 / 1)⁻¹
  have hx35 : Bounds (1 / 2) (1 / 2) x35 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x36 : ℝ := x34*x35
  have hx36 : Bounds (41327666639 / 1000000000000) (1033191691 / 25000000000) x36 := by
    apply bounds_mul hx34 hx35 <;> norm_num
  let x37 : ℝ := x34/(2 / 1)
  have hx37 : Bounds (41327666639 / 1000000000000) (1033191691 / 25000000000) x37 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx36
  let x38 : ℝ := -x37
  have hx38 : Bounds (-1033191691 / 25000000000) (-41327666639 / 1000000000000) x38 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx37
  let x39 : ℝ := x21+x38
  have hx39 : Bounds (16295487809 / 25000000000) (651819514361 / 1000000000000) x39 := by
    apply bounds_add hx21 hx38 <;> norm_num
  let x40 : ℝ := x21-x37
  have hx40 : Bounds (16295487809 / 25000000000) (651819514361 / 1000000000000) x40 := by
    exact hx39
  let x41 : ℝ := biasE (571 / 2000)
  have hx41 : Bounds (16295487809 / 25000000000) (651819514361 / 1000000000000) x41 := by
    simpa +zetaDelta only [biasE, div_one] using hx40
  let x42 : ℝ := biasE a
  have hx42 : Bounds (325836273147 / 500000000000) (651819514361 / 1000000000000) x42 := by
    exact bounds_biasE ha (by norm_num) (by norm_num) hx20.1 hx41.2
  let x43 : ℝ := a*z
  have hx43 : Bounds (571 / 2000000) (143 / 50000) x43 := by
    apply bounds_mul ha hz <;> norm_num
  let x44 : ℝ := Real.log (2 / 1)
  have hx44 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x44 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x45 : ℝ := (1 / 1)+(143 / 50000)
  have hx45 : Bounds (50143 / 50000) (50143 / 50000) x45 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((143 / 50000) : ℝ)) <;> norm_num
  let x46 : ℝ := (1 / 1)+(143 / 50000)
  have hx46 : Bounds (50143 / 50000) (50143 / 50000) x46 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((143 / 50000) : ℝ)) <;> norm_num
  let x47 : ℝ := Real.log x46
  have hx47 : Bounds (2855917 / 1000000000) (1427959 / 500000000) x47 := by
    exact bounds_log hx46 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x48 : ℝ := x45*x47
  have hx48 : Bounds (1432042461 / 500000000000) (1432042963 / 500000000000) x48 := by
    apply bounds_mul hx45 hx47 <;> norm_num
  let x49 : ℝ := -(143 / 50000)
  have hx49 : Bounds (-143 / 50000) (-143 / 50000) x49 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((143 / 50000) : ℝ))
  let x50 : ℝ := (1 / 1)+x49
  have hx50 : Bounds (49857 / 50000) (49857 / 50000) x50 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx49 <;> norm_num
  let x51 : ℝ := (1 / 1)-(143 / 50000)
  have hx51 : Bounds (49857 / 50000) (49857 / 50000) x51 := by
    exact hx50
  let x52 : ℝ := -(143 / 50000)
  have hx52 : Bounds (-143 / 50000) (-143 / 50000) x52 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((143 / 50000) : ℝ))
  let x53 : ℝ := (1 / 1)+x52
  have hx53 : Bounds (49857 / 50000) (49857 / 50000) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx52 <;> norm_num
  let x54 : ℝ := (1 / 1)-(143 / 50000)
  have hx54 : Bounds (49857 / 50000) (49857 / 50000) x54 := by
    exact hx53
  let x55 : ℝ := Real.log x54
  have hx55 : Bounds (-1432049 / 500000000) (-2864097 / 1000000000) x55 := by
    exact bounds_log hx54 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x56 : ℝ := x51*x55
  have hx56 : Bounds (-71397667 / 25000000000) (-1427952841 / 500000000000) x56 := by
    apply bounds_mul hx51 hx55 <;> norm_num
  let x57 : ℝ := x48+x56
  have hx57 : Bounds (4089121 / 500000000000) (2045061 / 250000000000) x57 := by
    apply bounds_add hx48 hx56 <;> norm_num
  let x58 : ℝ := (2 / 1)⁻¹
  have hx58 : Bounds (1 / 2) (1 / 2) x58 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x59 : ℝ := x57*x58
  have hx59 : Bounds (4089121 / 1000000000000) (2045061 / 500000000000) x59 := by
    apply bounds_mul hx57 hx58 <;> norm_num
  let x60 : ℝ := x57/(2 / 1)
  have hx60 : Bounds (4089121 / 1000000000000) (2045061 / 500000000000) x60 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx59
  let x61 : ℝ := -x60
  have hx61 : Bounds (-2045061 / 500000000000) (-4089121 / 1000000000000) x61 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx60
  let x62 : ℝ := x44+x61
  have hx62 : Bounds (346571544939 / 500000000000) (693143091879 / 1000000000000) x62 := by
    apply bounds_add hx44 hx61 <;> norm_num
  let x63 : ℝ := x44-x60
  have hx63 : Bounds (346571544939 / 500000000000) (693143091879 / 1000000000000) x63 := by
    exact hx62
  let x64 : ℝ := biasE (143 / 50000)
  have hx64 : Bounds (346571544939 / 500000000000) (693143091879 / 1000000000000) x64 := by
    simpa +zetaDelta only [biasE, div_one] using hx63
  let x65 : ℝ := Real.log (2 / 1)
  have hx65 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x65 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x66 : ℝ := (1 / 1)+(571 / 2000000)
  have hx66 : Bounds (2000571 / 2000000) (2000571 / 2000000) x66 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((571 / 2000000) : ℝ)) <;> norm_num
  let x67 : ℝ := (1 / 1)+(571 / 2000000)
  have hx67 : Bounds (2000571 / 2000000) (2000571 / 2000000) x67 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((571 / 2000000) : ℝ)) <;> norm_num
  let x68 : ℝ := Real.log x67
  have hx68 : Bounds (285459 / 1000000000) (14273 / 50000000) x68 := by
    exact bounds_log hx67 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x69 : ℝ := x66*x68
  have hx69 : Bounds (142770249 / 500000000000) (285541499 / 1000000000000) x69 := by
    apply bounds_mul hx66 hx68 <;> norm_num
  let x70 : ℝ := -(571 / 2000000)
  have hx70 : Bounds (-571 / 2000000) (-571 / 2000000) x70 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((571 / 2000000) : ℝ))
  let x71 : ℝ := (1 / 1)+x70
  have hx71 : Bounds (1999429 / 2000000) (1999429 / 2000000) x71 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx70 <;> norm_num
  let x72 : ℝ := (1 / 1)-(571 / 2000000)
  have hx72 : Bounds (1999429 / 2000000) (1999429 / 2000000) x72 := by
    exact hx71
  let x73 : ℝ := -(571 / 2000000)
  have hx73 : Bounds (-571 / 2000000) (-571 / 2000000) x73 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((571 / 2000000) : ℝ))
  let x74 : ℝ := (1 / 1)+x73
  have hx74 : Bounds (1999429 / 2000000) (1999429 / 2000000) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx73 <;> norm_num
  let x75 : ℝ := (1 / 1)-(571 / 2000000)
  have hx75 : Bounds (1999429 / 2000000) (1999429 / 2000000) x75 := by
    exact hx74
  let x76 : ℝ := Real.log x75
  have hx76 : Bounds (-285541 / 1000000000) (-14277 / 50000000) x76 := by
    exact bounds_log hx75 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x77 : ℝ := x72*x76
  have hx77 : Bounds (-285459479 / 1000000000000) (-142729239 / 500000000000) x77 := by
    apply bounds_mul hx72 hx76 <;> norm_num
  let x78 : ℝ := x69+x77
  have hx78 : Bounds (81019 / 1000000000000) (83021 / 1000000000000) x78 := by
    apply bounds_add hx69 hx77 <;> norm_num
  let x79 : ℝ := (2 / 1)⁻¹
  have hx79 : Bounds (1 / 2) (1 / 2) x79 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x80 : ℝ := x78*x79
  have hx80 : Bounds (40509 / 1000000000000) (41511 / 1000000000000) x80 := by
    apply bounds_mul hx78 hx79 <;> norm_num
  let x81 : ℝ := x78/(2 / 1)
  have hx81 : Bounds (40509 / 1000000000000) (41511 / 1000000000000) x81 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx80
  let x82 : ℝ := -x81
  have hx82 : Bounds (-41511 / 1000000000000) (-40509 / 1000000000000) x82 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx81
  let x83 : ℝ := x65+x82
  have hx83 : Bounds (693147138489 / 1000000000000) (693147140491 / 1000000000000) x83 := by
    apply bounds_add hx65 hx82 <;> norm_num
  let x84 : ℝ := x65-x81
  have hx84 : Bounds (693147138489 / 1000000000000) (693147140491 / 1000000000000) x84 := by
    exact hx83
  let x85 : ℝ := biasE (571 / 2000000)
  have hx85 : Bounds (693147138489 / 1000000000000) (693147140491 / 1000000000000) x85 := by
    simpa +zetaDelta only [biasE, div_one] using hx84
  let x86 : ℝ := biasE x43
  have hx86 : Bounds (346571544939 / 500000000000) (693147140491 / 1000000000000) x86 := by
    exact bounds_biasE hx43 (by norm_num) (by norm_num) hx64.1 hx85.2
  let x87 : ℝ := x42+x86
  have hx87 : Bounds (336203909043 / 250000000000) (336241663713 / 250000000000) x87 := by
    apply bounds_add hx42 hx86 <;> norm_num
  let x88 : ℝ := (2 / 1)⁻¹
  have hx88 : Bounds (1 / 2) (1 / 2) x88 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x89 : ℝ := x87*x88
  have hx89 : Bounds (336203909043 / 500000000000) (336241663713 / 500000000000) x89 := by
    apply bounds_mul hx87 hx88 <;> norm_num
  let x90 : ℝ := x87/(2 / 1)
  have hx90 : Bounds (336203909043 / 500000000000) (336241663713 / 500000000000) x90 := by
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

theorem center_inputs_eq : centerInitial=inputBoxes ⟨313910569730,314460325544⟩ ⟨739320214593,739403237991⟩ ⟨156955284865,157230162772⟩ := rfl
theorem whole_inputs_eq : wholeInitial=inputBoxes ⟨313910569730,314460325544⟩ ⟨739320214593,739403237991⟩ ⟨155382983237,158802464400⟩ := rfl
noncomputable def centerUpper : ℝ := (86962480983 / 137438953472)
noncomputable def secondUpper : ℝ := (36606468913155 / 549755813888)


theorem center_inputs {a z : ℝ} (ha : Bounds (571/2000) (143/500) a)
    (hz : Bounds (1/1000) (1/100) z) :
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

theorem whole_inputs {a z s : ℝ} (ha : Bounds (571/2000) (143/500) a)
    (hz : Bounds (1/1000) (1/100) z) (hs : s∈Icc (a*(1-z)/2) (a*(1+z)/2)) :
    RegistersContain wholeInitial (inputJets a ((biasE a+biasE (a*z))/2)) s := by
  rw [whole_inputs_eq]
  apply inputs_contain
  · norm_num [DyadicInterval.Contains,DyadicInterval.scale]
    constructor <;> linarith [ha.1,ha.2]
  · have h := entropy_bound ha hz
    norm_num [DyadicInterval.Contains,DyadicInterval.scale]
    constructor <;> linarith [h.1,h.2]
  · have hb : a*z≤(143/500:ℝ)*(1/100) :=
      mul_le_mul ha.2 hz.2 (by linarith [hz.1]) (by norm_num)
    norm_num [DyadicInterval.Contains,DyadicInterval.scale]
    constructor <;> nlinarith [ha.1,ha.2,hs.1,hs.2]

theorem curvature_pos {a z : ℝ} (ha : Bounds (571/2000) (143/500) a)
    (hz : Bounds (1/1000) (1/100) z) : 0<curvature a (a*z) := by
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
    have hb : a*z≤(143/50000:ℝ) := by
      have h := mul_le_mul ha.2 hz.2 hz0.le (by norm_num : (0:ℝ)≤143/500)
      norm_num at h
      exact h
    have hb2 := mul_self_le_mul_self hb0 hb
    have hle : centerUpper+secondUpper*(a*z)^2/24 ≤
        centerUpper+secondUpper*(143/50000:ℝ)^2/24 := by
      unfold centerUpper secondUpper
      nlinarith
    apply hle.trans_lt
    exact lt_of_lt_of_le (by norm_num [centerUpper,secondUpper] :
      centerUpper+secondUpper*(143/50000:ℝ)^2/24 < 2*(571/2000:ℝ)/(1-(571/2000:ℝ)^2)^2)
      (LowRatioFamily.base_mono (by norm_num) ha.1 ha1)

#print axioms entropy_bound
#print axioms curvature_pos
end GeneralCK.Certificates.ReflectionMidpointFamily.Cell0421

end

-- ===== source module GeneralCK.Certificates.Generated.MidpointFamily.Cell0422 =====
section

namespace GeneralCK.Certificates.ReflectionMidpointFamily.Endpoints0422
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
noncomputable def out_w1 : DyadicInterval 40 := ⟨149031422464,149031422528⟩
theorem checked_w1 : DyadicFastLog.check 1099511627776 1259115380736 0 16 (lift40 out_w1.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w1 : out_w1.Contains (Real.log ((1259115380736:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w1
#print axioms endpoint_w1
noncomputable def out_w2 : DyadicInterval 40 := ⟨-172446876544,-172446876480⟩
theorem checked_w2 : DyadicFastLog.check 939907874816 1099511627776 0 16 (lift40 out_w2)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w2 : out_w2.Contains (Real.log ((939907874816:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w2
#print axioms endpoint_w2
noncomputable def out_w3 : DyadicInterval 40 := ⟨149287777344,149287777408⟩
theorem checked_w3 : DyadicFastLog.check 1099511627776 1259408982016 0 16 (lift40 out_w3.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w3 : out_w3.Contains (Real.log ((1259408982016:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w3
#print axioms endpoint_w3
noncomputable def out_w4 : DyadicInterval 40 := ⟨-172790387264,-172790387200⟩
theorem checked_w4 : DyadicFastLog.check 939614273536 1099511627776 0 16 (lift40 out_w4)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w4 : out_w4.Contains (Real.log ((939614273536:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w4
#print axioms endpoint_w4
noncomputable def out_w5 : DyadicInterval 40 := ⟨-23502609920,-23502609856⟩
theorem checked_w5 : DyadicFastLog.check 1076258427676 1099511627776 0 16 (lift40 out_w5)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w5 : out_w5.Contains (Real.log ((1076258427676:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w5
#print axioms endpoint_w5
noncomputable def out_w6 : DyadicInterval 40 := ⟨-23415454016,-23415453952⟩
theorem checked_w6 : DyadicFastLog.check 1076343743676 1099511627776 0 16 (lift40 out_w6)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w6 : out_w6.Contains (Real.log ((1076343743676:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w6
#print axioms endpoint_w6
noncomputable def out_w7 : DyadicInterval 40 := ⟨646962473984,646962475456⟩
theorem checked_w7 : DyadicFastLog.check 1099511627776 1980352875794 0 16 (lift40 out_w7.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w7 : out_w7.Contains (Real.log ((1980352875794:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w7
#print axioms endpoint_w7
noncomputable def out_w8 : DyadicInterval 40 := ⟨648160119616,648160121088⟩
theorem checked_w8 : DyadicFastLog.check 1099511627776 1982511155060 0 16 (lift40 out_w8.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w8 : out_w8.Contains (Real.log ((1982511155060:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w8
#print axioms endpoint_w8
noncomputable def out_w9 : DyadicInterval 40 := ⟨321478298944,321478299008⟩
theorem checked_w9 : DyadicFastLog.check 1099511627776 1472923079936 0 16 (lift40 out_w9.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w9 : out_w9.Contains (Real.log ((1472923079936:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w9
#print axioms endpoint_w9
noncomputable def out_w10 : DyadicInterval 40 := ⟨322078164544,322078164608⟩
theorem checked_w10 : DyadicFastLog.check 1099511627776 1473726888632 0 16 (lift40 out_w10.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w10 : out_w10.Contains (Real.log ((1473726888632:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w10
#print axioms endpoint_w10
noncomputable def out_w11 : DyadicInterval 40 := ⟨147676326720,147676326784⟩
theorem checked_w11 : DyadicFastLog.check 1099511627776 1257564536832 0 16 (lift40 out_w11.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w11 : out_w11.Contains (Real.log ((1257564536832:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w11
#print axioms endpoint_w11
noncomputable def out_w12 : DyadicInterval 40 := ⟨-170634182208,-170634182144⟩
theorem checked_w12 : DyadicFastLog.check 941458718720 1099511627776 0 16 (lift40 out_w12)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w12 : out_w12.Contains (Real.log ((941458718720:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w12
#print axioms endpoint_w12
noncomputable def out_w13 : DyadicInterval 40 := ⟨150639975424,150639975488⟩
theorem checked_w13 : DyadicFastLog.check 1099511627776 1260958777344 0 16 (lift40 out_w13.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w13 : out_w13.Contains (Real.log ((1260958777344:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w13
#print axioms endpoint_w13
noncomputable def out_w14 : DyadicInterval 40 := ⟨-174605413760,-174605413696⟩
theorem checked_w14 : DyadicFastLog.check 938064478208 1099511627776 0 16 (lift40 out_w14)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w14 : out_w14.Contains (Real.log ((938064478208:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w14
#print axioms endpoint_w14
noncomputable def out_w15 : DyadicInterval 40 := ⟨-23965438336,-23965438272⟩
theorem checked_w15 : DyadicFastLog.check 1075805482752 1099511627776 0 16 (lift40 out_w15)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w15 : out_w15.Contains (Real.log ((1075805482752:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w15
#print axioms endpoint_w15
noncomputable def out_w16 : DyadicInterval 40 := ⟨-22957855424,-22957855360⟩
theorem checked_w16 : DyadicFastLog.check 1076791793415 1099511627776 0 16 (lift40 out_w16)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w16 : out_w16.Contains (Real.log ((1076791793415:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w16
#print axioms endpoint_w16
noncomputable def out_w17 : DyadicInterval 40 := ⟨318310508864,318310508928⟩
theorem checked_w17 : DyadicFastLog.check 1099511627776 1468685565740 0 16 (lift40 out_w17.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w17 : out_w17.Contains (Real.log ((1468685565740:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w17
#print axioms endpoint_w17
noncomputable def out_w18 : DyadicInterval 40 := ⟨325245389184,325245389248⟩
theorem checked_w18 : DyadicFastLog.check 1099511627776 1477978188114 0 16 (lift40 out_w18.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w18 : out_w18.Contains (Real.log ((1477978188114:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w18
#print axioms endpoint_w18
end GeneralCK.Certificates.ReflectionMidpointFamily.Endpoints0422

namespace GeneralCK.Certificates.ReflectionMidpointFamily.Cell0422
open Set GeneralCK.Certificates.ReflectionMidpointFamily.Endpoints0422
open BivariateJetProgram (RegistersContain RegistersSound zeroBox zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
theorem lc0 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc1 : ProvedTranscendental.LogEncloses (⟨1259115380736,1259115380736⟩ : DyadicInterval 40) (⟨149031422464,149031422528⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w1
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w1
theorem lc2 : ProvedTranscendental.LogEncloses (⟨939907874816,939907874816⟩ : DyadicInterval 40) (⟨-172446876544,-172446876480⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w2
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w2
theorem lc3 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc4 : ProvedTranscendental.LogEncloses (⟨1259408982016,1259408982016⟩ : DyadicInterval 40) (⟨149287777344,149287777408⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w3
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w3
theorem lc5 : ProvedTranscendental.LogEncloses (⟨939614273536,939614273536⟩ : DyadicInterval 40) (⟨-172790387264,-172790387200⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w4
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w4
theorem lc6 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc7 : ProvedTranscendental.LogEncloses (⟨1076258427676,1076343743676⟩ : DyadicInterval 40) (⟨-23502609920,-23415453952⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w5
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w6
theorem lc8 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc9 : ProvedTranscendental.LogEncloses (⟨1259115380736,1259408982016⟩ : DyadicInterval 40) (⟨149031422464,149287777408⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w1
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w3
theorem lc10 : ProvedTranscendental.LogEncloses (⟨939614273536,939907874816⟩ : DyadicInterval 40) (⟨-172790387264,-172446876480⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w4
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w2
theorem lc11 : ProvedTranscendental.LogEncloses (⟨1076258427676,1076343743676⟩ : DyadicInterval 40) (⟨-23502609920,-23415453952⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w5
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w6
theorem lc12 : ProvedTranscendental.LogEncloses (⟨1980352875794,1982511155060⟩ : DyadicInterval 40) (⟨646962473984,648160121088⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w7
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
theorem lc13 : ProvedTranscendental.LogEncloses (⟨1472923079936,1473726888632⟩ : DyadicInterval 40) (⟨321478298944,322078164608⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w9
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w10
theorem lc14 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc15 : ProvedTranscendental.LogEncloses (⟨1257564536832,1257564536832⟩ : DyadicInterval 40) (⟨147676326720,147676326784⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w11
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w11
theorem lc16 : ProvedTranscendental.LogEncloses (⟨941458718720,941458718720⟩ : DyadicInterval 40) (⟨-170634182208,-170634182144⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w12
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w12
theorem lc17 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc18 : ProvedTranscendental.LogEncloses (⟨1260958777344,1260958777344⟩ : DyadicInterval 40) (⟨150639975424,150639975488⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w13
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w13
theorem lc19 : ProvedTranscendental.LogEncloses (⟨938064478208,938064478208⟩ : DyadicInterval 40) (⟨-174605413760,-174605413696⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w14
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w14
theorem lc20 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc21 : ProvedTranscendental.LogEncloses (⟨1075805482752,1076791793415⟩ : DyadicInterval 40) (⟨-23965438336,-22957855360⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w15
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w16
theorem lc22 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc23 : ProvedTranscendental.LogEncloses (⟨1257564536832,1260958777344⟩ : DyadicInterval 40) (⟨147676326720,150639975488⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w11
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w13
theorem lc24 : ProvedTranscendental.LogEncloses (⟨938064478208,941458718720⟩ : DyadicInterval 40) (⟨-174605413760,-170634182144⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w14
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w12
theorem lc25 : ProvedTranscendental.LogEncloses (⟨1075805482752,1076791793415⟩ : DyadicInterval 40) (⟨-23965438336,-22957855360⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w15
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w16
theorem lc26 : ProvedTranscendental.LogEncloses (⟨1980352875794,1982511155060⟩ : DyadicInterval 40) (⟨646962473984,648160121088⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w7
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
theorem lc27 : ProvedTranscendental.LogEncloses (⟨1468685565740,1477978188114⟩ : DyadicInterval 40) (⟨318310508864,325245389248⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w17
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w18
theorem ew3_ok (x : ℝ) (hx : (⟨159603752960,159603752960⟩ : DyadicInterval 40).Contains x) : (⟨750498413728,750498433058⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨159603752960,159603752960⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨149031422464,149031422528⟩ : DyadicInterval 40)) (minus:=(⟨-172446876544,-172446876480⟩ : DyadicInterval 40))
    (lc0 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc1 lc2 (by decide) hx
theorem ew6_ok (x : ℝ) (hx : (⟨159897354240,159897354240⟩ : DyadicInterval 40).Contains x) : (⟨750455451698,750455471028⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨159897354240,159897354240⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨149287777344,149287777408⟩ : DyadicInterval 40)) (minus:=(⟨-172790387264,-172790387200⟩ : DyadicInterval 40))
    (lc3 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc4 lc5 (by decide) hx
theorem ew17_ok (x : ℝ) (hx : (⟨158052909056,158052909056⟩ : DyadicInterval 40).Contains x) : (⟨750724016674,750724036004⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨158052909056,158052909056⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨147676326720,147676326784⟩ : DyadicInterval 40)) (minus:=(⟨-170634182208,-170634182144⟩ : DyadicInterval 40))
    (lc14 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc15 lc16 (by decide) hx
theorem ew20_ok (x : ℝ) (hx : (⟨161447149568,161447149568⟩ : DyadicInterval 40).Contains x) : (⟨750227346157,750227365486⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨161447149568,161447149568⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨150639975424,150639975488⟩ : DyadicInterval 40)) (minus:=(⟨-174605413760,-174605413696⟩ : DyadicInterval 40))
    (lc17 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc18 lc19 (by decide) hx
theorem bw9_ok (x : ℝ) (hx : (⟨159603752960,159897354240⟩ : DyadicInterval 40).Contains x) : (⟨773831110592,773874707840⟩ : DyadicInterval 40).Contains (Reflection.biasB x) := by
  exact ProvedTranscendental.denominator_encloses (c:=(⟨159603752960,159897354240⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (gapLog:=(⟨-23502609920,-23415453952⟩ : DyadicInterval 40))
    (lc6 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc7 (by decide) hx
theorem bw23_ok (x : ℝ) (hx : (⟨158052909056,161447149568⟩ : DyadicInterval 40).Contains x) : (⟨773602311296,774106122048⟩ : DyadicInterval 40).Contains (Reflection.biasB x) := by
  exact ProvedTranscendental.denominator_encloses (c:=(⟨158052909056,161447149568⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (gapLog:=(⟨-23965438336,-22957855360⟩ : DyadicInterval 40))
    (lc20 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc21 (by decide) hx
theorem brcenter6_contact (y : ℝ) (hy : (⟨5160483500729,5170087009711⟩ : DyadicInterval 40).Contains y) : (⟨159603752960,159897354240⟩ : DyadicInterval 40).Contains (Reflection.biasContact y) := by
  exact ProvedTranscendental.contact_bracket (Y:=(⟨5160483500729,5170087009711⟩ : DyadicInterval 40)) (c:=(⟨159603752960,159897354240⟩ : DyadicInterval 40)) (elo:=(⟨750498413728,750498433058⟩ : DyadicInterval 40)) (ehi:=(⟨750455451698,750455471028⟩ : DyadicInterval 40))
    (by decide) (by decide) (by decide) (by decide)
    (ew3_ok _ (DyadicContact.point_contains 40 159603752960)) (ew6_ok _ (DyadicContact.point_contains 40 159897354240))
    (by decide) (by decide) hy
theorem brcenter6_jet (y : ℝ) (hy : (⟨5160483500729,5170087009711⟩ : DyadicInterval 40).Contains y) : (⟨⟨159603752960,159897354240⟩,⟨-33039720869,-32916643612⟩,⟨13367862275,13446436959⟩⟩ : DyadicJetEnclosure 40).Contains reflectionContactJet y := by
  exact ProvedTranscendental.contact_jet (c:=(⟨159603752960,159897354240⟩ : DyadicInterval 40)) (B:=(⟨773831110592,773874707840⟩ : DyadicInterval 40)) (by decide) brcenter6_contact bw9_ok (by decide) (by decide) (by decide) hy
theorem brwhole6_contact (y : ℝ) (hy : (⟨5109389604676,5222402333763⟩ : DyadicInterval 40).Contains y) : (⟨158052909056,161447149568⟩ : DyadicInterval 40).Contains (Reflection.biasContact y) := by
  exact ProvedTranscendental.contact_bracket (Y:=(⟨5109389604676,5222402333763⟩ : DyadicInterval 40)) (c:=(⟨158052909056,161447149568⟩ : DyadicInterval 40)) (elo:=(⟨750724016674,750724036004⟩ : DyadicInterval 40)) (ehi:=(⟨750227346157,750227365486⟩ : DyadicInterval 40))
    (by decide) (by decide) (by decide) (by decide)
    (ew17_ok _ (DyadicContact.point_contains 40 158052909056)) (ew20_ok _ (DyadicContact.point_contains 40 161447149568))
    (by decide) (by decide) hy
theorem brwhole6_jet (y : ℝ) (hy : (⟨5109389604676,5222402333763⟩ : DyadicInterval 40).Contains y) : (⟨⟨158052909056,161447149568⟩,⟨-33693257793,-32270410153⟩,⟨12957380488,13865787581⟩⟩ : DyadicJetEnclosure 40).Contains reflectionContactJet y := by
  exact ProvedTranscendental.contact_jet (c:=(⟨158052909056,161447149568⟩ : DyadicInterval 40)) (B:=(⟨773602311296,774106122048⟩ : DyadicInterval 40)) (by decide) brwhole6_contact bw23_ok (by decide) (by decide) (by decide) hy
noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨314460325543,315010081358⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨739239261480,739322442384⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨157230162771,157505040679⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
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
noncomputable def centerStep4 : Instruction 40 := ⟨.inv 6,⟨⟨7675473841363,7688892501978⟩,⟨0,0⟩,⟨-53768479035147,-53580969224137⟩,⟨0,0⟩,⟨0,0⟩,⟨748076359149744,752006699796954⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4
theorem centerAccepted4 : StepValid centerStep4.shape centerBoxes4 centerStep4.proposed := by
  dsimp only [StepValid,centerStep4]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep5 : Instruction 40 := ⟨.mul 6 0,⟨⟨5160483500729,5170087009711⟩,⟨0,0⟩,⟨-36154454613587,-36024317631594⟩,⟨0,0⟩,⟨0,0⟩,⟨502957314227845,505656707885479⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5
theorem centerAccepted5 : StepValid centerStep5.shape centerBoxes5 centerStep5.proposed := by
  dsimp only [StepValid,centerStep5]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep6 : Instruction 40 := ⟨.contact 0,⟨⟨159603752960,159897354240⟩,⟨0,0⟩,⟨1078478476160,1086421515178⟩,⟨0,0⟩,⟨0,0⟩,⟨-844642578299,-518402939774⟩⟩⟩
noncomputable def centerBoxes7 := centerStep6.proposed :: centerBoxes6
theorem centerAccepted6 : StepValid centerStep6.shape centerBoxes6 centerStep6.proposed := by
  dsimp only [StepValid,centerStep6]
  exact ⟨by decide,by decide,(⟨⟨159603752960,159897354240⟩,⟨-33039720869,-32916643612⟩,⟨13367862275,13446436959⟩⟩ : DyadicJetEnclosure 40),brcenter6_jet,by decide⟩
noncomputable def centerStep7 : Instruction 40 := ⟨.log 10,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes8 := centerStep7.proposed :: centerBoxes7
theorem centerAccepted7 : StepValid centerStep7.shape centerBoxes7 centerStep7.proposed := by
  dsimp only [StepValid,centerStep7]
  exact ⟨by decide,by decide,lc0,by decide⟩
noncomputable def centerStep8 : Instruction 40 := ⟨.add 6 1,⟨⟨1259115380736,1259408982016⟩,⟨0,0⟩,⟨1078478476160,1086421515178⟩,⟨0,0⟩,⟨0,0⟩,⟨-844642578299,-518402939774⟩⟩⟩
noncomputable def centerBoxes9 := centerStep8.proposed :: centerBoxes8
theorem centerAccepted8 : StepValid centerStep8.shape centerBoxes8 centerStep8.proposed := by
  dsimp only [StepValid,centerStep8]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep9 : Instruction 40 := ⟨.log 0,⟨⟨149031422464,149287777408⟩,⟨0,0⟩,⟨941552459746,948708201712⟩,⟨0,0⟩,⟨0,0⟩,⟨-1556165041029,-1258871538003⟩⟩⟩
noncomputable def centerBoxes10 := centerStep9.proposed :: centerBoxes9
theorem centerAccepted9 : StepValid centerStep9.shape centerBoxes9 centerStep9.proposed := by
  dsimp only [StepValid,centerStep9]
  exact ⟨by decide,by decide,lc9,by decide⟩
noncomputable def centerStep10 : Instruction 40 := ⟨.mul 1 0,⟨⟨170664640097,170998071347⟩,⟨0,0⟩,⟨1224407574440,1234185296088⟩,⟨0,0⟩,⟨0,0⟩,⟨-50072157472,362953106141⟩⟩⟩
noncomputable def centerBoxes11 := centerStep10.proposed :: centerBoxes10
theorem centerAccepted10 : StepValid centerStep10.shape centerBoxes10 centerStep10.proposed := by
  dsimp only [StepValid,centerStep10]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep11 : Instruction 40 := ⟨.neg 4,⟨⟨-159897354240,-159603752960⟩,⟨0,0⟩,⟨-1086421515178,-1078478476160⟩,⟨0,0⟩,⟨0,0⟩,⟨518402939774,844642578299⟩⟩⟩
noncomputable def centerBoxes12 := centerStep11.proposed :: centerBoxes11
theorem centerAccepted11 : StepValid centerStep11.shape centerBoxes11 centerStep11.proposed := by
  dsimp only [StepValid,centerStep11]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep12 : Instruction 40 := ⟨.add 10 0,⟨⟨939614273536,939907874816⟩,⟨0,0⟩,⟨-1086421515178,-1078478476160⟩,⟨0,0⟩,⟨0,0⟩,⟨518402939774,844642578299⟩⟩⟩
noncomputable def centerBoxes13 := centerStep12.proposed :: centerBoxes12
theorem centerAccepted12 : StepValid centerStep12.shape centerBoxes12 centerStep12.proposed := by
  dsimp only [StepValid,centerStep12]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep13 : Instruction 40 := ⟨.log 0,⟨⟨-172790387264,-172446876480⟩,⟨0,0⟩,⟨-1271301556658,-1261612607592⟩,⟨0,0⟩,⟨0,0⟩,⟨-863500454703,-459233855597⟩⟩⟩
noncomputable def centerBoxes14 := centerStep13.proposed :: centerBoxes13
theorem centerAccepted13 : StepValid centerStep13.shape centerBoxes13 centerStep13.proposed := by
  dsimp only [StepValid,centerStep13]
  exact ⟨by decide,by decide,lc10,by decide⟩
noncomputable def centerStep14 : Instruction 40 := ⟨.mul 1 0,⟨⟨-147708347579,-147368652112⟩,⟨0,0⟩,⟨-917612942253,-907408338595⟩,⟨0,0⟩,⟨0,0⟩,⟨1604064063570,2038576961726⟩⟩⟩
noncomputable def centerBoxes15 := centerStep14.proposed :: centerBoxes14
theorem centerAccepted14 : StepValid centerStep14.shape centerBoxes14 centerStep14.proposed := by
  dsimp only [StepValid,centerStep14]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep15 : Instruction 40 := ⟨.add 4 0,⟨⟨22956292518,23629419235⟩,⟨0,0⟩,⟨306794632187,326776957493⟩,⟨0,0⟩,⟨0,0⟩,⟨1553991906098,2401530067867⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15
theorem centerAccepted15 : StepValid centerStep15.shape centerBoxes15 centerStep15.proposed := by
  dsimp only [StepValid,centerStep15]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep16 : Instruction 40 := ⟨.mul 0 15,⟨⟨11478146259,11814709618⟩,⟨0,0⟩,⟨153397316093,163388478747⟩,⟨0,0⟩,⟨0,0⟩,⟨776995953049,1200765033934⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16
theorem centerAccepted16 : StepValid centerStep16.shape centerBoxes16 centerStep16.proposed := by
  dsimp only [StepValid,centerStep16]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨-11814709618,-11478146259⟩,⟨0,0⟩,⟨-163388478747,-153397316093⟩,⟨0,0⟩,⟨0,0⟩,⟨-1200765033934,-776995953049⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17
theorem centerAccepted17 : StepValid centerStep17.shape centerBoxes17 centerStep17.proposed := by
  dsimp only [StepValid,centerStep17]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep18 : Instruction 40 := ⟨.add 10 0,⟨⟨750308673998,750645256621⟩,⟨0,0⟩,⟨-163388478747,-153397316093⟩,⟨0,0⟩,⟨0,0⟩,⟨-1200765033934,-776995953049⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18
theorem centerAccepted18 : StepValid centerStep18.shape centerBoxes18 centerStep18.proposed := by
  dsimp only [StepValid,centerStep18]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep19 : Instruction 40 := ⟨.mul 12 12,⟨⟨23167884100,23253200100⟩,⟨0,0⟩,⟨313101213180,315987428380⟩,⟨0,0⟩,⟨0,0⟩,⟨1870029718686,1996473027083⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19
theorem centerAccepted19 : StepValid centerStep19.shape centerBoxes19 centerStep19.proposed := by
  dsimp only [StepValid,centerStep19]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep20 : Instruction 40 := ⟨.neg 0,⟨⟨-23253200100,-23167884100⟩,⟨0,0⟩,⟨-315987428380,-313101213180⟩,⟨0,0⟩,⟨0,0⟩,⟨-1996473027083,-1870029718686⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20
theorem centerAccepted20 : StepValid centerStep20.shape centerBoxes20 centerStep20.proposed := by
  dsimp only [StepValid,centerStep20]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep21 : Instruction 40 := ⟨.add 19 0,⟨⟨1076258427676,1076343743676⟩,⟨0,0⟩,⟨-315987428380,-313101213180⟩,⟨0,0⟩,⟨0,0⟩,⟨-1996473027083,-1870029718686⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21
theorem centerAccepted21 : StepValid centerStep21.shape centerBoxes21 centerStep21.proposed := by
  dsimp only [StepValid,centerStep21]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep22 : Instruction 40 := ⟨.log 0,⟨⟨-23502609920,-23415453952⟩,⟨0,0⟩,⟨-322814523725,-319840596077⟩,⟨0,0⟩,⟨0,0⟩,⟨-2134385738540,-2003320882668⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22
theorem centerAccepted22 : StepValid centerStep22.shape centerBoxes22 centerStep22.proposed := by
  dsimp only [StepValid,centerStep22]
  exact ⟨by decide,by decide,lc7,by decide⟩
noncomputable def centerStep23 : Instruction 40 := ⟨.mul 0 22,⟨⟨-11751304960,-11707726976⟩,⟨0,0⟩,⟨-161407261863,-159920298038⟩,⟨0,0⟩,⟨0,0⟩,⟨-1067192869270,-1001660441334⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23
theorem centerAccepted23 : StepValid centerStep23.shape centerBoxes23 centerStep23.proposed := by
  dsimp only [StepValid,centerStep23]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep24 : Instruction 40 := ⟨.neg 0,⟨⟨11707726976,11751304960⟩,⟨0,0⟩,⟨159920298038,161407261863⟩,⟨0,0⟩,⟨0,0⟩,⟨1001660441334,1067192869270⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24
theorem centerAccepted24 : StepValid centerStep24.shape centerBoxes24 centerStep24.proposed := by
  dsimp only [StepValid,centerStep24]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep25 : Instruction 40 := ⟨.add 17 0,⟨⟨773831110592,773874707840⟩,⟨0,0⟩,⟨159920298038,161407261863⟩,⟨0,0⟩,⟨0,0⟩,⟨1001660441334,1067192869270⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25
theorem centerAccepted25 : StepValid centerStep25.shape centerBoxes25 centerStep25.proposed := by
  dsimp only [StepValid,centerStep25]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep26 : Instruction 40 := ⟨.add 24 26,⟨⟨1413971953319,1414521709134⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26
theorem centerAccepted26 : StepValid centerStep26.shape centerBoxes26 centerStep26.proposed := by
  dsimp only [StepValid,centerStep26]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep27 : Instruction 40 := ⟨.neg 27,⟨⟨-315010081358,-314460325543⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27
theorem centerAccepted27 : StepValid centerStep27.shape centerBoxes27 centerStep27.proposed := by
  dsimp only [StepValid,centerStep27]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep28 : Instruction 40 := ⟨.add 26 0,⟨⟨784501546418,785051302233⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28
theorem centerAccepted28 : StepValid centerStep28.shape centerBoxes28 centerStep28.proposed := by
  dsimp only [StepValid,centerStep28]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep29 : Instruction 40 := ⟨.inv 0,⟨⟨1539932251785,1541011391418⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29
theorem centerAccepted29 : StepValid centerStep29.shape centerBoxes29 centerStep29.proposed := by
  dsimp only [StepValid,centerStep29]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep30 : Instruction 40 := ⟨.mul 3 0,⟨⟨1980352875794,1982511155060⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30
theorem centerAccepted30 : StepValid centerStep30.shape centerBoxes30 centerStep30.proposed := by
  dsimp only [StepValid,centerStep30]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨646962473984,648160121088⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31
theorem centerAccepted31 : StepValid centerStep31.shape centerBoxes31 centerStep31.proposed := by
  dsimp only [StepValid,centerStep31]
  exact ⟨by decide,by decide,lc12,by decide⟩
noncomputable def centerStep32 : Instruction 40 := ⟨.mul 0 31,⟨⟨323481236992,324080060544⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32
theorem centerAccepted32 : StepValid centerStep32.shape centerBoxes32 centerStep32.proposed := by
  dsimp only [StepValid,centerStep32]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep33 : Instruction 40 := ⟨.inv 20,⟨⟨1286217353856,1286619258204⟩,⟨0,0⟩,⟨1475844355563,1487643263119⟩,⟨0,0⟩,⟨0,0⟩,⟨2230282158818,2730742597338⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33
theorem centerAccepted33 : StepValid centerStep33.shape centerBoxes33 centerStep33.proposed := by
  dsimp only [StepValid,centerStep33]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep34 : Instruction 40 := ⟨.mul 25 0,⟨⟨1472923079936,1473726888632⟩,⟨0,0⟩,⟨2951688711125,2975286526238⟩,⟨0,0⟩,⟨0,0⟩,⟨4460873156206,5461295762106⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34
theorem centerAccepted34 : StepValid centerStep34.shape centerBoxes34 centerStep34.proposed := by
  dsimp only [StepValid,centerStep34]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨321478298944,322078164608⟩,⟨0,0⟩,⟨2202182836241,2220999980331⟩,⟨0,0⟩,⟨0,0⟩,⟨-1158244194090,-333930995421⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35
theorem centerAccepted35 : StepValid centerStep35.shape centerBoxes35 centerStep35.proposed := by
  dsimp only [StepValid,centerStep35]
  exact ⟨by decide,by decide,lc13,by decide⟩
noncomputable def centerStep36 : Instruction 40 := ⟨.mul 0 35,⟨⟨160739149472,161039082304⟩,⟨0,0⟩,⟨1101091418120,1110499990166⟩,⟨0,0⟩,⟨0,0⟩,⟨-579122097045,-166965497710⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36
theorem centerAccepted36 : StepValid centerStep36.shape centerBoxes36 centerStep36.proposed := by
  dsimp only [StepValid,centerStep36]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep37 : Instruction 40 := ⟨.mul 40 11,⟨⟨1547662221184,1547749415680⟩,⟨0,0⟩,⟨319840596076,322814523726⟩,⟨0,0⟩,⟨0,0⟩,⟨2003320882668,2134385738540⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37
theorem centerAccepted37 : StepValid centerStep37.shape centerBoxes37 centerStep37.proposed := by
  dsimp only [StepValid,centerStep37]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep38 : Instruction 40 := ⟨.add 0 17,⟨⟨1524409021084,1524581531580⟩,⟨0,0⟩,⟨3853167696,9713310546⟩,⟨0,0⟩,⟨0,0⟩,⟨6847855585,264356019854⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38
theorem centerAccepted38 : StepValid centerStep38.shape centerBoxes38 centerStep38.proposed := by
  dsimp only [StepValid,centerStep38]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep39 : Instruction 40 := ⟨.mul 20 0,⟨⟨1040259404580,1040843831118⟩,⟨0,0⟩,⟨-223924864283,-206045116987⟩,⟨0,0⟩,⟨0,0⟩,⟨-1663193211360,-897856970346⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39
theorem centerAccepted39 : StepValid centerStep39.shape centerBoxes39 centerStep39.proposed := by
  dsimp only [StepValid,centerStep39]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep40 : Instruction 40 := ⟨.mul 43 41,⟨⟨1478478522960,1478644884768⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40
theorem centerAccepted40 : StepValid centerStep40.shape centerBoxes40 centerStep40.proposed := by
  dsimp only [StepValid,centerStep40]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep41 : Instruction 40 := ⟨.mul 19 19,⟨⟨1053497001652,1053664031634⟩,⟨0,0⟩,⟨-618658471680,-612959082718⟩,⟨0,0⟩,⟨0,0⟩,⟨-3730490575299,-3479339629566⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41
theorem centerAccepted41 : StepValid centerStep41.shape centerBoxes41 centerStep41.proposed := by
  dsimp only [StepValid,centerStep41]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep42 : Instruction 40 := ⟨.mul 1 0,⟨⟨1416604110040,1416988134806⟩,⟨0,0⟩,⟨-831984093173,-824226698797⟩,⟨0,0⟩,⟨0,0⟩,⟨-5016837173427,-4678557994699⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42
theorem centerAccepted42 : StepValid centerStep42.shape centerBoxes42 centerStep42.proposed := by
  dsimp only [StepValid,centerStep42]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep43 : Instruction 40 := ⟨.mul 17 17,⟨⟨544618694875,544680063681⟩,⟨0,0⟩,⟨225102306716,227208143074⟩,⟨0,0⟩,⟨0,0⟩,⟨1456447559535,1549644137592⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43
theorem centerAccepted43 : StepValid centerStep43.shape centerBoxes43 centerStep43.proposed := by
  dsimp only [StepValid,centerStep43]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep44 : Instruction 40 := ⟨.mul 18 0,⟨⟨383300075104,383364863545⟩,⟨0,0⟩,⟨237638916591,239875546878⟩,⟨0,0⟩,⟨0,0⟩,⟨1586671979329,1686071457447⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44
theorem centerAccepted44 : StepValid centerStep44.shape centerBoxes44 centerStep44.proposed := by
  dsimp only [StepValid,centerStep44]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep45 : Instruction 40 := ⟨.mul 2 0,⟨⟨493841491125,494058861428⟩,⟨0,0⟩,⟨16086048705,21804815520⟩,⟨0,0⟩,⟨0,0⟩,⟨-67974115068,185641455971⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45
theorem centerAccepted45 : StepValid centerStep45.shape centerBoxes45 centerStep45.proposed := by
  dsimp only [StepValid,centerStep45]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep46 : Instruction 40 := ⟨.inv 0,⟨⟨2446926700434,2448003744807⟩,⟨0,0⟩,⟨-108087860189,-79669418269⟩,⟨0,0⟩,⟨0,0⟩,⟨-915048619734,346496928701⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46
theorem centerAccepted46 : StepValid centerStep46.shape centerBoxes46 centerStep46.proposed := by
  dsimp only [StepValid,centerStep46]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep47 : Instruction 40 := ⟨.mul 7 0,⟨⟨2315062840756,2317383038041⟩,⟨0,0⟩,⟨-600877218692,-533922648047⟩,⟨0,0⟩,⟨0,0⟩,⟨-4539374396296,-1626116394911⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47
theorem centerAccepted47 : StepValid centerStep47.shape centerBoxes47 centerStep47.proposed := by
  dsimp only [StepValid,centerStep47]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep48 : Instruction 40 := ⟨.neg 11,⟨⟨-161039082304,-160739149472⟩,⟨0,0⟩,⟨-1110499990166,-1101091418120⟩,⟨0,0⟩,⟨0,0⟩,⟨166965497710,579122097045⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48
theorem centerAccepted48 : StepValid centerStep48.shape centerBoxes48 centerStep48.proposed := by
  dsimp only [StepValid,centerStep48]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep49 : Instruction 40 := ⟨.mul 0 10,⟨⟨-223296602366,-222855496300⟩,⟨0,0⟩,⟨-1541240634146,-1527162608652⟩,⟨0,0⟩,⟨0,0⟩,⟨173148507699,794291513956⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49
theorem centerAccepted49 : StepValid centerStep49.shape centerBoxes49 centerStep49.proposed := by
  dsimp only [StepValid,centerStep49]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep50 : Instruction 40 := ⟨.mul 53 43,⟨⟨319207505920,319794708480⟩,⟨0,0⟩,⟨2156956952320,2172843030356⟩,⟨0,0⟩,⟨0,0⟩,⟨-1689285156598,-1036805879548⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50
theorem centerAccepted50 : StepValid centerStep50.shape centerBoxes50 centerStep50.proposed := by
  dsimp only [StepValid,centerStep50]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep51 : Instruction 40 := ⟨.inv 29,⟨⟨1123178191648,1123267227022⟩,⟨0,0⟩,⟨326725041593,329789122504⟩,⟨0,0⟩,⟨0,0⟩,⟨2141483726829,2277325864667⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51
theorem centerAccepted51 : StepValid centerStep51.shape centerBoxes51 centerStep51.proposed := by
  dsimp only [StepValid,centerStep51]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep52 : Instruction 40 := ⟨.mul 1 0,⟨⟨326078324414,326704062364⟩,⟨0,0⟩,⟨2298238627933,2315708281235⟩,⟨0,0⟩,⟨0,0⟩,⟨177826883218,906692549294⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52
theorem centerAccepted52 : StepValid centerStep52.shape centerBoxes52 centerStep52.proposed := by
  dsimp only [StepValid,centerStep52]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep53 : Instruction 40 := ⟨.neg 2,⟨⟨-319794708480,-319207505920⟩,⟨0,0⟩,⟨-2172843030356,-2156956952320⟩,⟨0,0⟩,⟨0,0⟩,⟨1036805879548,1689285156598⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53
theorem centerAccepted53 : StepValid centerStep53.shape centerBoxes53 centerStep53.proposed := by
  dsimp only [StepValid,centerStep53]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep54 : Instruction 40 := ⟨.add 1 0,⟨⟨6283615934,7496556444⟩,⟨0,0⟩,⟨125395597577,158751328915⟩,⟨0,0⟩,⟨0,0⟩,⟨1214632762766,2595977705892⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54
theorem centerAccepted54 : StepValid centerStep54.shape centerBoxes54 centerStep54.proposed := by
  dsimp only [StepValid,centerStep54]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep55 : Instruction 40 := ⟨.mul 36 0,⟨⟨4287950595,5117958186⟩,⟨0,0⟩,⟨84456181493,107504131132⟩,⟨0,0⟩,⟨0,0⟩,⟨773499431042,1732865085465⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55
theorem centerAccepted55 : StepValid centerStep55.shape centerBoxes55 centerStep55.proposed := by
  dsimp only [StepValid,centerStep55]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep56 : Instruction 40 := ⟨.add 6 0,⟨⟨-219008651771,-217737538114⟩,⟨0,0⟩,⟨-1456784452653,-1419658477520⟩,⟨0,0⟩,⟨0,0⟩,⟨946647938741,2527156599421⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56
theorem centerAccepted56 : StepValid centerStep56.shape centerBoxes56 centerStep56.proposed := by
  dsimp only [StepValid,centerStep56]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep57 : Instruction 40 := ⟨.mul 0 10,⟨⟨-487611032150,-484567677356⟩,⟨0,0⟩,⟨-3227675526864,-3137873188831⟩,⟨0,0⟩,⟨0,0⟩,⟨2243449691474,6095264154372⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57
theorem centerAccepted57 : StepValid centerStep57.shape centerBoxes57 centerStep57.proposed := by
  dsimp only [StepValid,centerStep57]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep58 : Instruction 40 := ⟨.mul 54 51,⟨⟨638415011840,639589416960⟩,⟨0,0⟩,⟨4313913904640,4345686060712⟩,⟨0,0⟩,⟨0,0⟩,⟨-3378570313196,-2073611759096⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58
theorem centerAccepted58 : StepValid centerStep58.shape centerBoxes58 centerStep58.proposed := by
  dsimp only [StepValid,centerStep58]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep59 : Instruction 40 := ⟨.mul 0 7,⟨⟨652156648829,653408124728⟩,⟨0,0⟩,⟨4596477255868,4631416562468⟩,⟨0,0⟩,⟨0,0⟩,⟨355653766436,1813385098586⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59
theorem centerAccepted59 : StepValid centerStep59.shape centerBoxes59 centerStep59.proposed := by
  dsimp only [StepValid,centerStep59]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep60 : Instruction 40 := ⟨.mul 57 53,⟨⟨478811258880,479692062720⟩,⟨0,0⟩,⟨3235435428480,3259264545534⟩,⟨0,0⟩,⟨0,0⟩,⟨-2533927734897,-1555208819322⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60
theorem centerAccepted60 : StepValid centerStep60.shape centerBoxes60 centerStep60.proposed := by
  dsimp only [StepValid,centerStep60]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep61 : Instruction 40 := ⟨.mul 39 35,⟨⟨757465617764,757568341372⟩,⟨0,0⟩,⟨-65864797125,-62352922242⟩,⟨0,0⟩,⟨0,0⟩,⟨-517484131785,-362491195638⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61
theorem centerAccepted61 : StepValid centerStep61.shape centerBoxes61 centerStep61.proposed := by
  dsimp only [StepValid,centerStep61]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep62 : Instruction 40 := ⟨.inv 0,⟨⟨1595797703775,1596014117689⟩,⟨0,0⟩,⟨131344783966,138780089294⟩,⟨0,0⟩,⟨0,0⟩,⟨785199232009,1114497351517⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62
theorem centerAccepted62 : StepValid centerStep62.shape centerBoxes62 centerStep62.proposed := by
  dsimp only [StepValid,centerStep62]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep63 : Instruction 40 := ⟨.mul 2 0,⟨⟨694932084536,696304872913⟩,⟨0,0⟩,⟨4753010024468,4791585465914⟩,⟨0,0⟩,⟨0,0⟩,⟨-2563235348654,-948185588635⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63
theorem centerAccepted63 : StepValid centerStep63.shape centerBoxes63 centerStep63.proposed := by
  dsimp only [StepValid,centerStep63]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep64 : Instruction 40 := ⟨.neg 0,⟨⟨-696304872913,-694932084536⟩,⟨0,0⟩,⟨-4791585465914,-4753010024468⟩,⟨0,0⟩,⟨0,0⟩,⟨948185588635,2563235348654⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64
theorem centerAccepted64 : StepValid centerStep64.shape centerBoxes64 centerStep64.proposed := by
  dsimp only [StepValid,centerStep64]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep65 : Instruction 40 := ⟨.add 5 0,⟨⟨-44148224084,-41523959808⟩,⟨0,0⟩,⟨-195108210046,-121593462000⟩,⟨0,0⟩,⟨0,0⟩,⟨1303839355071,4376620447240⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65
theorem centerAccepted65 : StepValid centerStep65.shape centerBoxes65 centerStep65.proposed := by
  dsimp only [StepValid,centerStep65]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep66 : Instruction 40 := ⟨.mul 18 0,⟨⟨-93048898318,-87430249871⟩,⟨0,0⟩,⟨-391055322295,-231892812240⟩,⟨0,0⟩,⟨0,0⟩,⟨2924785657794,9619892319844⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66
theorem centerAccepted66 : StepValid centerStep66.shape centerBoxes66 centerStep66.proposed := by
  dsimp only [StepValid,centerStep66]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep67 : Instruction 40 := ⟨.add 9 0,⟨⟨-580659930468,-571997927227⟩,⟨0,0⟩,⟨-3618730849159,-3369766001071⟩,⟨0,0⟩,⟨0,0⟩,⟨5168235349268,15715156474216⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67
theorem centerAccepted67 : StepValid centerStep67.shape centerBoxes67 centerStep67.proposed := by
  dsimp only [StepValid,centerStep67]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep68 : Instruction 40 := ⟨.mul 61 29,⟨⟨221281334971,221713483573⟩,⟨0,0⟩,⟨1495807098879,1507843362751⟩,⟨0,0⟩,⟨0,0⟩,⟨-1162627463928,-661096046926⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68
theorem centerAccepted68 : StepValid centerStep68.shape centerBoxes68 centerStep68.proposed := by
  dsimp only [StepValid,centerStep68]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep69 : Instruction 40 := ⟨.mul 27 25,⟨⟨521826370545,521967914983⟩,⟨0,0⟩,⟨-90791518744,-85881699842⟩,⟨0,0⟩,⟨0,0⟩,⟨-708213694614,-489368290210⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69
theorem centerAccepted69 : StepValid centerStep69.shape centerBoxes69 centerStep69.proposed := by
  dsimp only [StepValid,centerStep69]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨2316092205885,2316720441614⟩,⟨0,0⟩,⟨381076939640,403081521503⟩,⟨0,0⟩,⟨0,0⟩,⟨2296840704269,3284475463715⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70
theorem centerAccepted70 : StepValid centerStep70.shape centerBoxes70 centerStep70.proposed := by
  dsimp only [StepValid,centerStep70]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep71 : Instruction 40 := ⟨.mul 2 0,⟨⟨466123288091,467160279709⟩,⟨0,0⟩,⟨3227571484922,3258374044467⟩,⟨0,0⟩,⟨0,0⟩,⟨-950603545192,375276330339⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71
theorem centerAccepted71 : StepValid centerStep71.shape centerBoxes71 centerStep71.proposed := by
  dsimp only [StepValid,centerStep71]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep72 : Instruction 40 := ⟨.mul 65 39,⟨⟨46956137735,47129600938⟩,⟨0,0⟩,⟨317293189743,320221761663⟩,⟨0,0⟩,⟨0,0⟩,⟨-248957638099,-152516462747⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72
theorem centerAccepted72 : StepValid centerStep72.shape centerBoxes72 centerStep72.proposed := by
  dsimp only [StepValid,centerStep72]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep73 : Instruction 40 := ⟨.add 54 0,⟨⟨797264811733,797774857559⟩,⟨0,0⟩,⟨153904710996,166824445570⟩,⟨0,0⟩,⟨0,0⟩,⟨-1449722672033,-929512415796⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73
theorem centerAccepted73 : StepValid centerStep73.shape centerBoxes73 centerStep73.proposed := by
  dsimp only [StepValid,centerStep73]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep74 : Instruction 40 := ⟨.mul 0 0,⟨⟨578103190516,578843103862⟩,⟨0,0⟩,⟨223195111970,242086295298⟩,⟨0,0⟩,⟨0,0⟩,⟨-2060670591374,-1297370809956⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74
theorem centerAccepted74 : StepValid centerStep74.shape centerBoxes74 centerStep74.proposed := by
  dsimp only [StepValid,centerStep74]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep75 : Instruction 40 := ⟨.mul 7 0,⟨⟨-305691170471,-300746093397⟩,⟨0,0⟩,⟨-2032945492978,-1887874184762⟩,⟨0,0⟩,⟨0,0⟩,⟨1798777219828,7993483626410⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75
theorem centerAccepted75 : StepValid centerStep75.shape centerBoxes75 centerStep75.proposed := by
  dsimp only [StepValid,centerStep75]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep76 : Instruction 40 := ⟨.mul 79 28,⟨⟨4630125681512,4634766076082⟩,⟨0,0⟩,⟨-1201754437384,-1067845296094⟩,⟨0,0⟩,⟨0,0⟩,⟨-9078748792592,-3252232789822⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76
theorem centerAccepted76 : StepValid centerStep76.shape centerBoxes76 centerStep76.proposed := by
  dsimp only [StepValid,centerStep76]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep77 : Instruction 40 := ⟨.mul 0 3,⟨⟨3357341738383,3362856519894⟩,⟨0,0⟩,⟨-223855131678,-71089014418⟩,⟨0,0⟩,⟨0,0⟩,⟨-13062969647169,-6571411098699⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77
theorem centerAccepted77 : StepValid centerStep77.shape centerBoxes77 centerStep77.proposed := by
  dsimp only [StepValid,centerStep77]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep78 : Instruction 40 := ⟨.add 45 29,⟨⟨162442154688,163340911072⟩,⟨0,0⟩,⟨-1110499990166,-1101091418120⟩,⟨0,0⟩,⟨0,0⟩,⟨166965497710,579122097045⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78
theorem centerAccepted78 : StepValid centerStep78.shape centerBoxes78 centerStep78.proposed := by
  dsimp only [StepValid,centerStep78]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep79 : Instruction 40 := ⟨.mul 1 0,⟨⟨496014605238,499578207168⟩,⟨0,0⟩,⟨-3429719830300,-3372668314574⟩,⟨0,0⟩,⟨0,0⟩,⟨-1288395762228,1252567549004⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79
theorem centerAccepted79 : StepValid centerStep79.shape centerBoxes79 centerStep79.proposed := by
  dsimp only [StepValid,centerStep79]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep80 : Instruction 40 := ⟨.add 4 0,⟨⟨190323434767,198832113771⟩,⟨0,0⟩,⟨-5462665323278,-5260542499336⟩,⟨0,0⟩,⟨0,0⟩,⟨510381457600,9246051175414⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80
theorem centerAccepted80 : StepValid centerStep80.shape centerBoxes80 centerStep80.proposed := by
  dsimp only [StepValid,centerStep80]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep81 : Instruction 40 := ⟨.mul 81 81,⟨⟨89935653105,90250388310⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81
theorem centerAccepted81 : StepValid centerStep81.shape centerBoxes81 centerStep81.proposed := by
  dsimp only [StepValid,centerStep81]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep82 : Instruction 40 := ⟨.neg 0,⟨⟨-90250388310,-89935653105⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82
theorem centerAccepted82 : StepValid centerStep82.shape centerBoxes82 centerStep82.proposed := by
  dsimp only [StepValid,centerStep82]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep83 : Instruction 40 := ⟨.add 81 0,⟨⟨1009261239466,1009575974671⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83
theorem centerAccepted83 : StepValid centerStep83.shape centerBoxes83 centerStep83.proposed := by
  dsimp only [StepValid,centerStep83]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep84 : Instruction 40 := ⟨.inv 0,⟨⟨1197458982726,1197832406855⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes85 := centerStep84.proposed :: centerBoxes84
theorem centerAccepted84 : StepValid centerStep84.shape centerBoxes84 centerStep84.proposed := by
  dsimp only [StepValid,centerStep84]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep85 : Instruction 40 := ⟨.mul 13 0,⟨⟨507646762691,508934792589⟩,⟨0,0⟩,⟨3515091945710,3549745110029⟩,⟨0,0⟩,⟨0,0⟩,⟨-1035608631812,408834375781⟩⟩⟩
noncomputable def centerBoxes86 := centerStep85.proposed :: centerBoxes85
theorem centerAccepted85 : StepValid centerStep85.shape centerBoxes85 centerStep85.proposed := by
  dsimp only [StepValid,centerStep85]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep86 : Instruction 40 := ⟨.add 5 0,⟨⟨697970197458,707766906360⟩,⟨0,0⟩,⟨-1947573377568,-1710797389307⟩,⟨0,0⟩,⟨0,0⟩,⟨-525227174212,9654885551195⟩⟩⟩
noncomputable def centerBoxes87 := centerStep86.proposed :: centerBoxes86
theorem centerAccepted86 : StepValid centerStep86.shape centerBoxes86 centerStep86.proposed := by
  dsimp only [StepValid,centerStep86]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep87 : Instruction 40 := ⟨.mul 0 68,⟨⟨476296093752,483198046871⟩,⟨0,0⟩,⟨-1434798537895,-1264827802199⟩,⟨0,0⟩,⟨0,0⟩,⟨-654160962320,6677051829928⟩⟩⟩
noncomputable def centerBoxes88 := centerStep87.proposed :: centerBoxes87
theorem centerAccepted87 : StepValid centerStep87.shape centerBoxes87 centerStep87.proposed := by
  dsimp only [StepValid,centerStep87]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep88 : Instruction 40 := ⟨.mul 0 69,⟨⟨325025294417,329883116040⟩,⟨0,0⟩,⟨-1051351965080,-929570718244⟩,⟨0,0⟩,⟨0,0⟩,⟨-621373839956,4648314868866⟩⟩⟩
noncomputable def centerBoxes89 := centerStep88.proposed :: centerBoxes88
theorem centerAccepted88 : StepValid centerStep88.shape centerBoxes88 centerStep88.proposed := by
  dsimp only [StepValid,centerStep88]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep89 : Instruction 40 := ⟨.mul 90 63,⟨⟨520273114220,520360971768⟩,⟨0,0⟩,⟨107519884311,108531831811⟩,⟨0,0⟩,⟨0,0⟩,⟨673450563140,717590991011⟩⟩⟩
noncomputable def centerBoxes90 := centerStep89.proposed :: centerBoxes89
theorem centerAccepted89 : StepValid centerStep89.shape centerBoxes89 centerStep89.proposed := by
  dsimp only [StepValid,centerStep89]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep90 : Instruction 40 := ⟨.inv 0,⟨⟨2323244603658,2323636925632⟩,⟨0,0⟩,⟨-484723436807,-480041749024⟩,⟨0,0⟩,⟨0,0⟩,⟨-3006517622786,-2804508510787⟩⟩⟩
noncomputable def centerBoxes91 := centerStep90.proposed :: centerBoxes90
theorem centerAccepted90 : StepValid centerStep90.shape centerBoxes90 centerStep90.proposed := by
  dsimp only [StepValid,centerStep90]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep91 : Instruction 40 := ⟨.mul 2 0,⟨⟨686771510396,697153690975⟩,⟨0,0⟩,⟨-2367289494621,-2106067646025⟩,⟨0,0⟩,⟨0,0⟩,⟨-1403515028982,9921395524056⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91
theorem centerAccepted91 : StepValid centerStep91.shape centerBoxes91 centerStep91.proposed := by
  dsimp only [StepValid,centerStep91]
  exact ⟨by decide,by decide⟩
noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91]
theorem centerAccepted : Accepted centerProgram centerInitial :=
  ⟨centerAccepted0,⟨centerAccepted1,⟨centerAccepted2,⟨centerAccepted3,⟨centerAccepted4,⟨centerAccepted5,⟨centerAccepted6,⟨centerAccepted7,⟨centerAccepted8,⟨centerAccepted9,⟨centerAccepted10,⟨centerAccepted11,⟨centerAccepted12,⟨centerAccepted13,⟨centerAccepted14,⟨centerAccepted15,⟨centerAccepted16,⟨centerAccepted17,⟨centerAccepted18,⟨centerAccepted19,⟨centerAccepted20,⟨centerAccepted21,⟨centerAccepted22,⟨centerAccepted23,⟨centerAccepted24,⟨centerAccepted25,⟨centerAccepted26,⟨centerAccepted27,⟨centerAccepted28,⟨centerAccepted29,⟨centerAccepted30,⟨centerAccepted31,⟨centerAccepted32,⟨centerAccepted33,⟨centerAccepted34,⟨centerAccepted35,⟨centerAccepted36,⟨centerAccepted37,⟨centerAccepted38,⟨centerAccepted39,⟨centerAccepted40,⟨centerAccepted41,⟨centerAccepted42,⟨centerAccepted43,⟨centerAccepted44,⟨centerAccepted45,⟨centerAccepted46,⟨centerAccepted47,⟨centerAccepted48,⟨centerAccepted49,⟨centerAccepted50,⟨centerAccepted51,⟨centerAccepted52,⟨centerAccepted53,⟨centerAccepted54,⟨centerAccepted55,⟨centerAccepted56,⟨centerAccepted57,⟨centerAccepted58,⟨centerAccepted59,⟨centerAccepted60,⟨centerAccepted61,⟨centerAccepted62,⟨centerAccepted63,⟨centerAccepted64,⟨centerAccepted65,⟨centerAccepted66,⟨centerAccepted67,⟨centerAccepted68,⟨centerAccepted69,⟨centerAccepted70,⟨centerAccepted71,⟨centerAccepted72,⟨centerAccepted73,⟨centerAccepted74,⟨centerAccepted75,⟨centerAccepted76,⟨centerAccepted77,⟨centerAccepted78,⟨centerAccepted79,⟨centerAccepted80,⟨centerAccepted81,⟨centerAccepted82,⟨centerAccepted83,⟨centerAccepted84,⟨centerAccepted85,⟨centerAccepted86,⟨centerAccepted87,⟨centerAccepted88,⟨centerAccepted89,⟨centerAccepted90,⟨centerAccepted91,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
noncomputable def center_output : DyadicBivariateJetEnclosure 40 := ⟨⟨686771510396,697153690975⟩,⟨0,0⟩,⟨-2367289494621,-2106067646025⟩,⟨0,0⟩,⟨0,0⟩,⟨-1403515028982,9921395524056⟩⟩
theorem center_output_eq : (finalBoxes centerProgram centerInitial).getD 0 (zeroBox 40)=center_output := rfl
noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨314460325543,315010081358⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨739239261480,739322442384⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨155655112365,159080091086⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
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
noncomputable def wholeStep4 : Instruction 40 := ⟨.inv 6,⟨⟨7599479050845,7766695235681⟩,⟨0,0⟩,⟨-54862134569658,-52525212453685⟩,⟨0,0⟩,⟨0,0⟩,⟨726075544085618,775066799508664⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4
theorem wholeAccepted4 : StepValid wholeStep4.shape wholeBoxes4 wholeStep4.proposed := by
  dsimp only [StepValid,wholeStep4]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep5 : Instruction 40 := ⟨.mul 6 0,⟨⟨5109389604676,5222402333763⟩,⟨0,0⟩,⟨-36889839361211,-35314496256744⟩,⟨0,0⟩,⟨0,0⟩,⟨488165414015876,521162545941021⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5
theorem wholeAccepted5 : StepValid wholeStep5.shape wholeBoxes5 wholeStep5.proposed := by
  dsimp only [StepValid,wholeStep5]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep6 : Instruction 40 := ⟨.contact 0,⟨⟨158052909056,161447149568⟩,⟨0,0⟩,⟨1036472238912,1130446314655⟩,⟨0,0⟩,⟨0,0⟩,⟨-2603740187508,1280859941588⟩⟩⟩
noncomputable def wholeBoxes7 := wholeStep6.proposed :: wholeBoxes6
theorem wholeAccepted6 : StepValid wholeStep6.shape wholeBoxes6 wholeStep6.proposed := by
  dsimp only [StepValid,wholeStep6]
  exact ⟨by decide,by decide,(⟨⟨158052909056,161447149568⟩,⟨-33693257793,-32270410153⟩,⟨12957380488,13865787581⟩⟩ : DyadicJetEnclosure 40),brwhole6_jet,by decide⟩
noncomputable def wholeStep7 : Instruction 40 := ⟨.log 10,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes8 := wholeStep7.proposed :: wholeBoxes7
theorem wholeAccepted7 : StepValid wholeStep7.shape wholeBoxes7 wholeStep7.proposed := by
  dsimp only [StepValid,wholeStep7]
  exact ⟨by decide,by decide,lc0,by decide⟩
noncomputable def wholeStep8 : Instruction 40 := ⟨.add 6 1,⟨⟨1257564536832,1260958777344⟩,⟨0,0⟩,⟨1036472238912,1130446314655⟩,⟨0,0⟩,⟨0,0⟩,⟨-2603740187508,1280859941588⟩⟩⟩
noncomputable def wholeBoxes9 := wholeStep8.proposed :: wholeBoxes8
theorem wholeAccepted8 : StepValid wholeStep8.shape wholeBoxes8 wholeStep8.proposed := by
  dsimp only [StepValid,wholeStep8]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep9 : Instruction 40 := ⟨.log 0,⟨⟨147676326720,150639975488⟩,⟨0,0⟩,⟨903767275366,988369845951⟩,⟨0,0⟩,⟨0,0⟩,⟨-3164960163219,377008238457⟩⟩⟩
noncomputable def wholeBoxes10 := wholeStep9.proposed :: wholeBoxes9
theorem wholeAccepted9 : StepValid wholeStep9.shape wholeBoxes9 wholeStep9.proposed := by
  dsimp only [StepValid,wholeStep9]
  exact ⟨by decide,by decide,lc23,by decide⟩
noncomputable def wholeStep10 : Instruction 40 := ⟨.mul 1 0,⟨⟨168904545182,172759245571⟩,⟨0,0⟩,⟨1172891723434,1288375676854⟩,⟨0,0⟩,⟨0,0⟩,⟨-2282515445652,2640207328442⟩⟩⟩
noncomputable def wholeBoxes11 := wholeStep10.proposed :: wholeBoxes10
theorem wholeAccepted10 : StepValid wholeStep10.shape wholeBoxes10 wholeStep10.proposed := by
  dsimp only [StepValid,wholeStep10]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep11 : Instruction 40 := ⟨.neg 4,⟨⟨-161447149568,-158052909056⟩,⟨0,0⟩,⟨-1130446314655,-1036472238912⟩,⟨0,0⟩,⟨0,0⟩,⟨-1280859941588,2603740187508⟩⟩⟩
noncomputable def wholeBoxes12 := wholeStep11.proposed :: wholeBoxes11
theorem wholeAccepted11 : StepValid wholeStep11.shape wholeBoxes11 wholeStep11.proposed := by
  dsimp only [StepValid,wholeStep11]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep12 : Instruction 40 := ⟨.add 10 0,⟨⟨938064478208,941458718720⟩,⟨0,0⟩,⟨-1130446314655,-1036472238912⟩,⟨0,0⟩,⟨0,0⟩,⟨-1280859941588,2603740187508⟩⟩⟩
noncomputable def wholeBoxes13 := wholeStep12.proposed :: wholeBoxes12
theorem wholeAccepted12 : StepValid wholeStep12.shape wholeBoxes12 wholeStep12.proposed := by
  dsimp only [StepValid,wholeStep12]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep13 : Instruction 40 := ⟨.log 0,⟨⟨-174605413760,-170634182144⟩,⟨0,0⟩,⟨-1325003660638,-1210476100427⟩,⟨0,0⟩,⟨0,0⟩,⟨-3098044933919,1719221944365⟩⟩⟩
noncomputable def wholeBoxes14 := wholeStep13.proposed :: wholeBoxes13
theorem wholeAccepted13 : StepValid wholeStep13.shape wholeBoxes13 wholeStep13.proposed := by
  dsimp only [StepValid,wholeStep13]
  exact ⟨by decide,by decide,lc24,by decide⟩
noncomputable def wholeStep14 : Instruction 40 := ⟨.mul 1 0,⟨⟨-149506185263,-145579056186⟩,⟨0,0⟩,⟨-973685615320,-853217520694⟩,⟨0,0⟩,⟨0,0⟩,⟨-784037910190,4400055858380⟩⟩⟩
noncomputable def wholeBoxes15 := wholeStep14.proposed :: wholeBoxes14
theorem wholeAccepted14 : StepValid wholeStep14.shape wholeBoxes14 wholeStep14.proposed := by
  dsimp only [StepValid,wholeStep14]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep15 : Instruction 40 := ⟨.add 4 0,⟨⟨19398359919,27180189385⟩,⟨0,0⟩,⟨199206108114,435158156160⟩,⟨0,0⟩,⟨0,0⟩,⟨-3066553355842,7040263186822⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15
theorem wholeAccepted15 : StepValid wholeStep15.shape wholeBoxes15 wholeStep15.proposed := by
  dsimp only [StepValid,wholeStep15]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 0 15,⟨⟨9699179959,13590094693⟩,⟨0,0⟩,⟨99603054057,217579078080⟩,⟨0,0⟩,⟨0,0⟩,⟨-1533276677921,3520131593411⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16
theorem wholeAccepted16 : StepValid wholeStep16.shape wholeBoxes16 wholeStep16.proposed := by
  dsimp only [StepValid,wholeStep16]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨-13590094693,-9699179959⟩,⟨0,0⟩,⟨-217579078080,-99603054057⟩,⟨0,0⟩,⟨0,0⟩,⟨-3520131593411,1533276677921⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17
theorem wholeAccepted17 : StepValid wholeStep17.shape wholeBoxes17 wholeStep17.proposed := by
  dsimp only [StepValid,wholeStep17]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep18 : Instruction 40 := ⟨.add 10 0,⟨⟨748533288923,752424222921⟩,⟨0,0⟩,⟨-217579078080,-99603054057⟩,⟨0,0⟩,⟨0,0⟩,⟨-3520131593411,1533276677921⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18
theorem wholeAccepted18 : StepValid wholeStep18.shape wholeBoxes18 wholeStep18.proposed := by
  dsimp only [StepValid,wholeStep18]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep19 : Instruction 40 := ⟨.mul 12 12,⟨⟨22719834361,23706145024⟩,⟨0,0⟩,⟨297982210242,331978908874⟩,⟨0,0⟩,⟨0,0⟩,⟨1189452215013,2700653670915⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19
theorem wholeAccepted19 : StepValid wholeStep19.shape wholeBoxes19 wholeStep19.proposed := by
  dsimp only [StepValid,wholeStep19]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep20 : Instruction 40 := ⟨.neg 0,⟨⟨-23706145024,-22719834361⟩,⟨0,0⟩,⟨-331978908874,-297982210242⟩,⟨0,0⟩,⟨0,0⟩,⟨-2700653670915,-1189452215013⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20
theorem wholeAccepted20 : StepValid wholeStep20.shape wholeBoxes20 wholeStep20.proposed := by
  dsimp only [StepValid,wholeStep20]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep21 : Instruction 40 := ⟨.add 19 0,⟨⟨1075805482752,1076791793415⟩,⟨0,0⟩,⟨-331978908874,-297982210242⟩,⟨0,0⟩,⟨0,0⟩,⟨-2700653670915,-1189452215013⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21
theorem wholeAccepted21 : StepValid wholeStep21.shape wholeBoxes21 wholeStep21.proposed := by
  dsimp only [StepValid,wholeStep21]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep22 : Instruction 40 := ⟨.log 0,⟨⟨-23965438336,-22957855360⟩,⟨0,0⟩,⟨-339294302117,-304269504127⟩,⟨0,0⟩,⟨0,0⟩,⟨-2864866107661,-1298750091699⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22
theorem wholeAccepted22 : StepValid wholeStep22.shape wholeBoxes22 wholeStep22.proposed := by
  dsimp only [StepValid,wholeStep22]
  exact ⟨by decide,by decide,lc21,by decide⟩
noncomputable def wholeStep23 : Instruction 40 := ⟨.mul 0 22,⟨⟨-11982719168,-11478927680⟩,⟨0,0⟩,⟨-169647151059,-152134752063⟩,⟨0,0⟩,⟨0,0⟩,⟨-1432433053831,-649375045849⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23
theorem wholeAccepted23 : StepValid wholeStep23.shape wholeBoxes23 wholeStep23.proposed := by
  dsimp only [StepValid,wholeStep23]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep24 : Instruction 40 := ⟨.neg 0,⟨⟨11478927680,11982719168⟩,⟨0,0⟩,⟨152134752063,169647151059⟩,⟨0,0⟩,⟨0,0⟩,⟨649375045849,1432433053831⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24
theorem wholeAccepted24 : StepValid wholeStep24.shape wholeBoxes24 wholeStep24.proposed := by
  dsimp only [StepValid,wholeStep24]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep25 : Instruction 40 := ⟨.add 17 0,⟨⟨773602311296,774106122048⟩,⟨0,0⟩,⟨152134752063,169647151059⟩,⟨0,0⟩,⟨0,0⟩,⟨649375045849,1432433053831⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25
theorem wholeAccepted25 : StepValid wholeStep25.shape wholeBoxes25 wholeStep25.proposed := by
  dsimp only [StepValid,wholeStep25]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep26 : Instruction 40 := ⟨.add 24 26,⟨⟨1413971953319,1414521709134⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26
theorem wholeAccepted26 : StepValid wholeStep26.shape wholeBoxes26 wholeStep26.proposed := by
  dsimp only [StepValid,wholeStep26]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep27 : Instruction 40 := ⟨.neg 27,⟨⟨-315010081358,-314460325543⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27
theorem wholeAccepted27 : StepValid wholeStep27.shape wholeBoxes27 wholeStep27.proposed := by
  dsimp only [StepValid,wholeStep27]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep28 : Instruction 40 := ⟨.add 26 0,⟨⟨784501546418,785051302233⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28
theorem wholeAccepted28 : StepValid wholeStep28.shape wholeBoxes28 wholeStep28.proposed := by
  dsimp only [StepValid,wholeStep28]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep29 : Instruction 40 := ⟨.inv 0,⟨⟨1539932251785,1541011391418⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29
theorem wholeAccepted29 : StepValid wholeStep29.shape wholeBoxes29 wholeStep29.proposed := by
  dsimp only [StepValid,wholeStep29]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep30 : Instruction 40 := ⟨.mul 3 0,⟨⟨1980352875794,1982511155060⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30
theorem wholeAccepted30 : StepValid wholeStep30.shape wholeBoxes30 wholeStep30.proposed := by
  dsimp only [StepValid,wholeStep30]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨646962473984,648160121088⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31
theorem wholeAccepted31 : StepValid wholeStep31.shape wholeBoxes31 wholeStep31.proposed := by
  dsimp only [StepValid,wholeStep31]
  exact ⟨by decide,by decide,lc12,by decide⟩
noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 0 31,⟨⟨323481236992,324080060544⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32
theorem wholeAccepted32 : StepValid wholeStep32.shape wholeBoxes32 wholeStep32.proposed := by
  dsimp only [StepValid,wholeStep32]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep33 : Instruction 40 := ⟨.inv 20,⟨⟨1284098596758,1288744907945⟩,⟨0,0⟩,⟨1413691881651,1553045622728⟩,⟨0,0⟩,⟨0,0⟩,⟨-464379033602,5502789252592⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33
theorem wholeAccepted33 : StepValid wholeStep33.shape wholeBoxes33 wholeStep33.proposed := by
  dsimp only [StepValid,wholeStep33]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep34 : Instruction 40 := ⟨.mul 25 0,⟨⟨1468685565740,1477978188114⟩,⟨0,0⟩,⟨2827383763302,3106091245456⟩,⟨0,0⟩,⟨0,0⟩,⟨-919148940089,11005578505184⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34
theorem wholeAccepted34 : StepValid wholeStep34.shape wholeBoxes34 wholeStep34.proposed := by
  dsimp only [StepValid,wholeStep34]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨318310508864,325245389248⟩,⟨0,0⟩,⟨2103374291268,2325333291876⟩,⟨0,0⟩,⟨0,0⟩,⟨-5605905389158,4215406449050⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35
theorem wholeAccepted35 : StepValid wholeStep35.shape wholeBoxes35 wholeStep35.proposed := by
  dsimp only [StepValid,wholeStep35]
  exact ⟨by decide,by decide,lc27,by decide⟩
noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 0 35,⟨⟨159155254432,162622694624⟩,⟨0,0⟩,⟨1051687145634,1162666645938⟩,⟨0,0⟩,⟨0,0⟩,⟨-2802952694579,2107703224525⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36
theorem wholeAccepted36 : StepValid wholeStep36.shape wholeBoxes36 wholeStep36.proposed := by
  dsimp only [StepValid,wholeStep36]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep37 : Instruction 40 := ⟨.mul 40 11,⟨⟨1547204622592,1548212244096⟩,⟨0,0⟩,⟨304269504126,339294302118⟩,⟨0,0⟩,⟨0,0⟩,⟨1298750091698,2864866107662⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37
theorem wholeAccepted37 : StepValid wholeStep37.shape wholeBoxes37 wholeStep37.proposed := by
  dsimp only [StepValid,wholeStep37]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep38 : Instruction 40 := ⟨.add 0 17,⟨⟨1523498477568,1525492409735⟩,⟨0,0⟩,⟨-27709404748,41312091876⟩,⟨0,0⟩,⟨0,0⟩,⟨-1401903579217,1675413892649⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38
theorem wholeAccepted38 : StepValid wholeStep38.shape wholeBoxes38 wholeStep38.proposed := by
  dsimp only [StepValid,wholeStep38]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep39 : Instruction 40 := ⟨.mul 20 0,⟨⟨1037178050031,1043933881162⟩,⟨0,0⟩,⟨-320837406857,-109740433425⟩,⟨0,0⟩,⟨0,0⟩,⟨-5859635650220,3284805556104⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39
theorem wholeAccepted39 : StepValid wholeStep39.shape wholeBoxes39 wholeStep39.proposed := by
  dsimp only [StepValid,wholeStep39]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep40 : Instruction 40 := ⟨.mul 43 41,⟨⟨1478478522960,1478644884768⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40
theorem wholeAccepted40 : StepValid wholeStep40.shape wholeBoxes40 wholeStep40.proposed := by
  dsimp only [StepValid,wholeStep40]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 19 19,⟨⟨1052610456753,1054541431919⟩,⟨0,0⟩,⟨-650238079584,-583115062074⟩,⟨0,0⟩,⟨0,0⟩,⟨-5128182805634,-2127142976759⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41
theorem wholeAccepted41 : StepValid wholeStep41.shape wholeBoxes41 wholeStep41.proposed := by
  dsimp only [StepValid,wholeStep41]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep42 : Instruction 40 := ⟨.mul 1 0,⟨⟨1415412001144,1418168079984⟩,⟨0,0⟩,⟨-874452971638,-784096387806⟩,⟨0,0⟩,⟨0,0⟩,⟨-6896481203245,-2860301907643⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42
theorem wholeAccepted42 : StepValid wholeStep42.shape wholeBoxes42 wholeStep42.proposed := by
  dsimp only [StepValid,wholeStep42]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep43 : Instruction 40 := ⟨.mul 17 17,⟨⟨544296686750,545005867200⟩,⟨0,0⟩,⟨214080129488,238878598290⟩,⟨0,0⟩,⟨0,0⟩,⟨955884423367,2069346650857⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43
theorem wholeAccepted43 : StepValid wholeStep43.shape wholeBoxes43 wholeStep43.proposed := by
  dsimp only [StepValid,wholeStep43]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep44 : Instruction 40 := ⟨.mul 18 0,⟨⟨382960183651,383708882830⟩,⟨0,0⟩,⟨225936059415,252272073380⟩,⟨0,0⟩,⟨0,0⟩,⟨1053254109141,2240657047038⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44
theorem wholeAccepted44 : StepValid wholeStep44.shape wholeBoxes44 wholeStep44.proposed := by
  dsimp only [StepValid,wholeStep44]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 2 0,⟨⟨492988365203,494913992621⟩,⟨0,0⟩,⟨-14317959402,52283671963⟩,⟨0,0⟩,⟨0,0⟩,⟨-1452147189486,1571547966096⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45
theorem wholeAccepted45 : StepValid wholeStep45.shape wholeBoxes45 wholeStep45.proposed := by
  dsimp only [StepValid,wholeStep45]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep46 : Instruction 40 := ⟨.inv 0,⟨⟨2442698807548,2452240062739⟩,⟨0,0⟩,⟨-260071279699,71220897167⟩,⟨0,0⟩,⟨0,0⟩,⟨-7832355762468,7278485115009⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46
theorem wholeAccepted46 : StepValid wholeStep46.shape wholeBoxes46 wholeStep46.proposed := by
  dsimp only [StepValid,wholeStep46]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep47 : Instruction 40 := ⟨.mul 7 0,⟨⟨2304217183360,2328285050895⟩,⟨0,0⟩,⟨-962488741712,-176180872829⟩,⟨0,0⟩,⟨0,0⟩,⟨-20546754513090,14388451916632⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47
theorem wholeAccepted47 : StepValid wholeStep47.shape wholeBoxes47 wholeStep47.proposed := by
  dsimp only [StepValid,wholeStep47]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep48 : Instruction 40 := ⟨.neg 11,⟨⟨-162622694624,-159155254432⟩,⟨0,0⟩,⟨-1162666645938,-1051687145634⟩,⟨0,0⟩,⟨0,0⟩,⟨-2107703224525,2802952694579⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48
theorem wholeAccepted48 : StepValid wholeStep48.shape wholeBoxes48 wholeStep48.proposed := by
  dsimp only [StepValid,wholeStep48]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep49 : Instruction 40 := ⟨.mul 0 10,⟨⟨-225627160307,-220527715850⟩,⟨0,0⟩,⟨-1619225647240,-1453133870367⟩,⟨0,0⟩,⟨0,0⟩,⟨-3259456184804,4154842826612⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49
theorem wholeAccepted49 : StepValid wholeStep49.shape wholeBoxes49 wholeStep49.proposed := by
  dsimp only [StepValid,wholeStep49]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 53 43,⟨⟨316105818112,322894299136⟩,⟨0,0⟩,⟨2072944477824,2260892629310⟩,⟨0,0⟩,⟨0,0⟩,⟨-5207480375016,2561719883176⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50
theorem wholeAccepted50 : StepValid wholeStep50.shape wholeBoxes50 wholeStep50.proposed := by
  dsimp only [StepValid,wholeStep50]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep51 : Instruction 40 := ⟨.inv 29,⟨⟨1122710840672,1123740154700⟩,⟨0,0⟩,⟨310689457155,346770895294⟩,⟨0,0⟩,⟨0,0⟩,⟨1412130708867,3035004257920⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51
theorem wholeAccepted51 : StepValid wholeStep51.shape wholeBoxes51 wholeStep51.proposed := by
  dsimp only [StepValid,wholeStep51]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep52 : Instruction 40 := ⟨.mul 1 0,⟨⟨322775512171,330009506491⟩,⟨0,0⟩,⟨2206004848991,2412549454875⟩,⟨0,0⟩,⟨0,0⟩,⟨-3744742644045,4935569989370⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52
theorem wholeAccepted52 : StepValid wholeStep52.shape wholeBoxes52 wholeStep52.proposed := by
  dsimp only [StepValid,wholeStep52]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep53 : Instruction 40 := ⟨.neg 2,⟨⟨-322894299136,-316105818112⟩,⟨0,0⟩,⟨-2260892629310,-2072944477824⟩,⟨0,0⟩,⟨0,0⟩,⟨-2561719883176,5207480375016⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53
theorem wholeAccepted53 : StepValid wholeStep53.shape wholeBoxes53 wholeStep53.proposed := by
  dsimp only [StepValid,wholeStep53]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep54 : Instruction 40 := ⟨.add 1 0,⟨⟨-118786965,13903688379⟩,⟨0,0⟩,⟨-54887780319,339604977051⟩,⟨0,0⟩,⟨0,0⟩,⟨-6306462527221,10143050364386⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54
theorem wholeAccepted54 : StepValid wholeStep54.shape wholeBoxes54 wholeStep54.proposed := by
  dsimp only [StepValid,wholeStep54]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 36 0,⟨⟨-81288991,9514653288⟩,⟨0,0⟩,⟨-40312486048,232423969025⟩,⟨0,0⟩,⟨0,0⟩,⟨-4494595354836,6982263453102⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55
theorem wholeAccepted55 : StepValid wholeStep55.shape wholeBoxes55 wholeStep55.proposed := by
  dsimp only [StepValid,wholeStep55]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep56 : Instruction 40 := ⟨.add 6 0,⟨⟨-225708449298,-211013062562⟩,⟨0,0⟩,⟨-1659538133288,-1220709901342⟩,⟨0,0⟩,⟨0,0⟩,⟨-7754051539640,11137106279714⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56
theorem wholeAccepted56 : StepValid wholeStep56.shape wholeBoxes56 wholeStep56.proposed := by
  dsimp only [StepValid,wholeStep56]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep57 : Instruction 40 := ⟨.mul 0 10,⟨⟨-503397406526,-468791182627⟩,⟨0,0⟩,⟨-3715887082172,-2658567914406⟩,⟨0,0⟩,⟨0,0⟩,⟨-19002981400324,27231984393131⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57
theorem wholeAccepted57 : StepValid wholeStep57.shape wholeBoxes57 wholeStep57.proposed := by
  dsimp only [StepValid,wholeStep57]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 54 51,⟨⟨632211636224,645788598272⟩,⟨0,0⟩,⟨4145888955648,4521785258620⟩,⟨0,0⟩,⟨0,0⟩,⟨-10414960750032,5123439766352⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58
theorem wholeAccepted58 : StepValid wholeStep58.shape wholeBoxes58 wholeStep58.proposed := by
  dsimp only [StepValid,wholeStep58]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep59 : Instruction 40 := ⟨.mul 0 7,⟨⟨645551024342,660019012981⟩,⟨0,0⟩,⟨4412009697983,4825098909748⟩,⟨0,0⟩,⟨0,0⟩,⟨-7489485288089,9871139978739⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59
theorem wholeAccepted59 : StepValid wholeStep59.shape wholeBoxes59 wholeStep59.proposed := by
  dsimp only [StepValid,wholeStep59]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 57 53,⟨⟨474158727168,484341448704⟩,⟨0,0⟩,⟨3109416716736,3391338943965⟩,⟨0,0⟩,⟨0,0⟩,⟨-7811220562524,3842579824764⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60
theorem wholeAccepted60 : StepValid wholeStep60.shape wholeBoxes60 wholeStep60.proposed := by
  dsimp only [StepValid,wholeStep60]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 39 35,⟨⟨756922971015,758110326800⟩,⟨0,0⟩,⟨-84873595701,-43514834516⟩,⟨0,0⟩,⟨0,0⟩,⟨-1368452883713,483489452494⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61
theorem wholeAccepted61 : StepValid wholeStep61.shape wholeBoxes61 wholeStep61.proposed := by
  dsimp only [StepValid,wholeStep61]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep62 : Instruction 40 := ⟨.inv 0,⟨⟨1594656841989,1597158318493⟩,⟨0,0⟩,⟨91531834003,179088988689⟩,⟨0,0⟩,⟨0,0⟩,⟨-1009687539372,2927689929346⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62
theorem wholeAccepted62 : StepValid wholeStep62.shape wholeBoxes62 wholeStep62.proposed := by
  dsimp only [StepValid,wholeStep62]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep63 : Instruction 40 := ⟨.mul 2 0,⟨⟨687687550878,703557792612⟩,⟨0,0⟩,⟨4549159038873,5005172556969⟩,⟨0,0⟩,⟨0,0⟩,⟨-11273703598866,7976189260158⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63
theorem wholeAccepted63 : StepValid wholeStep63.shape wholeBoxes63 wholeStep63.proposed := by
  dsimp only [StepValid,wholeStep63]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep64 : Instruction 40 := ⟨.neg 0,⟨⟨-703557792612,-687687550878⟩,⟨0,0⟩,⟨-5005172556969,-4549159038873⟩,⟨0,0⟩,⟨0,0⟩,⟨-7976189260158,11273703598866⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64
theorem wholeAccepted64 : StepValid wholeStep64.shape wholeBoxes64 wholeStep64.proposed := by
  dsimp only [StepValid,wholeStep64]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep65 : Instruction 40 := ⟨.add 5 0,⟨⟨-58006768270,-27668537897⟩,⟨0,0⟩,⟨-593162858986,275939870875⟩,⟨0,0⟩,⟨0,0⟩,⟨-15465674548247,21144843577605⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65
theorem wholeAccepted65 : StepValid wholeStep65.shape wholeBoxes65 wholeStep65.proposed := by
  dsimp only [StepValid,wholeStep65]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 18 0,⟨⟨-122832981482,-57984216674⟩,⟨0,0⟩,⟨-1251626190577,635097910807⟩,⟨0,0⟩,⟨0,0⟩,⟨-33991731913373,46898002602162⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66
theorem wholeAccepted66 : StepValid wholeStep66.shape wholeBoxes66 wholeStep66.proposed := by
  dsimp only [StepValid,wholeStep66]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep67 : Instruction 40 := ⟨.add 9 0,⟨⟨-626230388008,-526775399301⟩,⟨0,0⟩,⟨-4967513272749,-2023470003599⟩,⟨0,0⟩,⟨0,0⟩,⟨-52994713313697,74129986995293⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67
theorem wholeAccepted67 : StepValid wholeStep67.shape wholeBoxes67 wholeStep67.proposed := by
  dsimp only [StepValid,wholeStep67]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 61 29,⟨⟨219000290891,223996177046⟩,⟨0,0⟩,⟨1432081511311,1574478112248⟩,⟨0,0⟩,⟨0,0⟩,⟨-3875327109888,2108058761375⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68
theorem wholeAccepted68 : StepValid wholeStep68.shape wholeBoxes68 wholeStep68.proposed := by
  dsimp only [StepValid,wholeStep68]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 27 25,⟨⟨521078967766,522715042827⟩,⟨0,0⟩,⟨-117361728889,-59553910600⟩,⟨0,0⟩,⟨0,0⟩,⟨-1909367437905,704629392065⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69
theorem wholeAccepted69 : StepValid wholeStep69.shape wholeBoxes69 wholeStep69.proposed := by
  dsimp only [StepValid,wholeStep69]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨2312781765522,2320043399176⟩,⟨0,0⟩,⟨263499588143,522539425440⟩,⟨0,0⟩,⟨0,0⟩,⟨-3077238270057,8736617409829⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70
theorem wholeAccepted70 : StepValid wholeStep70.shape wholeBoxes70 wholeStep70.proposed := by
  dsimp only [StepValid,wholeStep70]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 2 0,⟨⟨460658956778,472646981504⟩,⟨0,0⟩,⟨3064813875019,3428708064460⟩,⟨0,0⟩,⟨0,0⟩,⟨-8117704885500,7724529942429⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71
theorem wholeAccepted71 : StepValid wholeStep71.shape wholeBoxes71 wholeStep71.proposed := by
  dsimp only [StepValid,wholeStep71]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 65 39,⟨⟨46499872525,47586401713⟩,⟨0,0⟩,⟨304934766928,333198031599⟩,⟨0,0⟩,⟨0,0⟩,⟨-767450071734,377532312467⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72
theorem wholeAccepted72 : StepValid wholeStep72.shape wholeBoxes72 wholeStep72.proposed := by
  dsimp only [StepValid,wholeStep72]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep73 : Instruction 40 := ⟨.add 54 0,⟨⟨795033161448,800010624634⟩,⟨0,0⟩,⟨87355688848,233594977542⟩,⟨0,0⟩,⟨0,0⟩,⟨-4287581665145,1910808990388⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73
theorem wholeAccepted73 : StepValid wholeStep73.shape wholeBoxes73 wholeStep73.proposed := by
  dsimp only [StepValid,wholeStep73]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 0 0,⟨⟨574871344544,582092070115⟩,⟨0,0⟩,⟨126330031844,339929945576⟩,⟨0,0⟩,⟨0,0⟩,⟨-6225454616886,2879886064856⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74
theorem wholeAccepted74 : StepValid wholeStep74.shape wholeBoxes74 wholeStep74.proposed := by
  dsimp only [StepValid,wholeStep74]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep75 : Instruction 40 := ⟨.mul 7 0,⟨⟨-331532412861,-275420536189⟩,⟨0,0⟩,⟨-2823457676616,-1118480644964⟩,⟨0,0⟩,⟨0,0⟩,⟨-32767718565668,42325879247045⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75
theorem wholeAccepted75 : StepValid wholeStep75.shape wholeBoxes75 wholeStep75.proposed := by
  dsimp only [StepValid,wholeStep75]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep76 : Instruction 40 := ⟨.mul 79 28,⟨⟨4608434366720,4656570101790⟩,⟨0,0⟩,⟨-1924977483424,-352361745658⟩,⟨0,0⟩,⟨0,0⟩,⟨-41093509026180,28776903833264⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76
theorem wholeAccepted76 : StepValid wholeStep76.shape wholeBoxes76 wholeStep76.proposed := by
  dsimp only [StepValid,wholeStep76]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 0 3,⟨⟨3332259569923,3388145665472⟩,⟨0,0⟩,⟨-1034486085979,734518940342⟩,⟨0,0⟩,⟨0,0⟩,⟨-48876243963017,28974757896798⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77
theorem wholeAccepted77 : StepValid wholeStep77.shape wholeBoxes77 wholeStep77.proposed := by
  dsimp only [StepValid,wholeStep77]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep78 : Instruction 40 := ⟨.add 45 29,⟨⟨160858542368,164924806112⟩,⟨0,0⟩,⟨-1162666645938,-1051687145634⟩,⟨0,0⟩,⟨0,0⟩,⟨-2107703224525,2802952694579⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78
theorem wholeAccepted78 : StepValid wholeStep78.shape wholeBoxes78 wholeStep78.proposed := by
  dsimp only [StepValid,wholeStep78]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 1 0,⟨⟨487509548483,508215877706⟩,⟨0,0⟩,⟨-3737928976971,-3077142684361⟩,⟨0,0⟩,⟨0,0⟩,⟨-15379657223867,15171275014512⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79
theorem wholeAccepted79 : StepValid wholeStep79.shape wholeBoxes79 wholeStep79.proposed := by
  dsimp only [StepValid,wholeStep79]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep80 : Instruction 40 := ⟨.add 4 0,⟨⟨155977135622,232795341517⟩,⟨0,0⟩,⟨-6561386653587,-4195623329325⟩,⟨0,0⟩,⟨0,0⟩,⟨-48147375789535,57497154261557⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80
theorem wholeAccepted80 : StepValid wholeStep80.shape wholeBoxes80 wholeStep80.proposed := by
  dsimp only [StepValid,wholeStep80]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep81 : Instruction 40 := ⟨.mul 81 81,⟨⟨89935653105,90250388310⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81
theorem wholeAccepted81 : StepValid wholeStep81.shape wholeBoxes81 wholeStep81.proposed := by
  dsimp only [StepValid,wholeStep81]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep82 : Instruction 40 := ⟨.neg 0,⟨⟨-90250388310,-89935653105⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82
theorem wholeAccepted82 : StepValid wholeStep82.shape wholeBoxes82 wholeStep82.proposed := by
  dsimp only [StepValid,wholeStep82]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep83 : Instruction 40 := ⟨.add 81 0,⟨⟨1009261239466,1009575974671⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83
theorem wholeAccepted83 : StepValid wholeStep83.shape wholeBoxes83 wholeStep83.proposed := by
  dsimp only [StepValid,wholeStep83]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep84 : Instruction 40 := ⟨.inv 0,⟨⟨1197458982726,1197832406855⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes85 := wholeStep84.proposed :: wholeBoxes84
theorem wholeAccepted84 : StepValid wholeStep84.shape wholeBoxes84 wholeStep84.proposed := by
  dsimp only [StepValid,wholeStep84]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep85 : Instruction 40 := ⟨.mul 13 0,⟨⟨501695654535,514912127481⟩,⟨0,0⟩,⟨3337835464685,3735310777534⟩,⟨0,0⟩,⟨0,0⟩,⟨-8843608139739,8415274617404⟩⟩⟩
noncomputable def wholeBoxes86 := wholeStep85.proposed :: wholeBoxes85
theorem wholeAccepted85 : StepValid wholeStep85.shape wholeBoxes85 wholeStep85.proposed := by
  dsimp only [StepValid,wholeStep85]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep86 : Instruction 40 := ⟨.add 5 0,⟨⟨657672790157,747707468998⟩,⟨0,0⟩,⟨-3223551188902,-460312551791⟩,⟨0,0⟩,⟨0,0⟩,⟨-56990983929274,65912428878961⟩⟩⟩
noncomputable def wholeBoxes87 := wholeStep86.proposed :: wholeBoxes86
theorem wholeAccepted86 : StepValid wholeStep86.shape wholeBoxes86 wholeStep86.proposed := by
  dsimp only [StepValid,wholeStep86]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep87 : Instruction 40 := ⟨.mul 0 68,⟨⟨447735125500,511675544961⟩,⟨0,0⟩,⟨-2353920990695,-372952387619⟩,⟨0,0⟩,⟨0,0⟩,⟨-41310821333154,47424059717615⟩⟩⟩
noncomputable def wholeBoxes88 := wholeStep87.proposed :: wholeBoxes87
theorem wholeAccepted87 : StepValid wholeStep87.shape wholeBoxes87 wholeStep87.proposed := by
  dsimp only [StepValid,wholeStep87]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep88 : Instruction 40 := ⟨.mul 0 69,⟨⟨304812279916,350152799279⟩,⟨0,0⟩,⟨-1712102917364,-294460790632⟩,⟨0,0⟩,⟨0,0⟩,⟨-29840642580504,34098665654343⟩⟩⟩
noncomputable def wholeBoxes89 := wholeStep88.proposed :: wholeBoxes88
theorem wholeAccepted88 : StepValid wholeStep88.shape wholeBoxes88 wholeStep88.proposed := by
  dsimp only [StepValid,wholeStep88]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep89 : Instruction 40 := ⟨.mul 90 63,⟨⟨520119284630,520516576960⟩,⟨0,0⟩,⟨102285395551,114072414422⟩,⟨0,0⟩,⟨0,0⟩,⟨436597046534,963182086626⟩⟩⟩
noncomputable def wholeBoxes90 := wholeStep89.proposed :: wholeBoxes89
theorem wholeAccepted89 : StepValid wholeStep89.shape wholeBoxes89 wholeStep89.proposed := by
  dsimp only [StepValid,wholeStep89]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep90 : Instruction 40 := ⟨.inv 0,⟨⟨2322550084139,2324324160514⟩,⟨0,0⟩,⟨-509770117596,-456398440623⟩,⟨0,0⟩,⟨0,0⟩,⟨-4124924668529,-1724495038206⟩⟩⟩
noncomputable def wholeBoxes91 := wholeStep90.proposed :: wholeBoxes90
theorem wholeAccepted90 : StepValid wholeStep90.shape wholeBoxes90 wholeStep90.proposed := by
  dsimp only [StepValid,wholeStep90]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 2 0,⟨⟨643869303863,740209189859⟩,⟨0,0⟩,⟨-3781660425176,-748528494381⟩,⟨0,0⟩,⟨0,0⟩,⟨-64151115605720,73192734788266⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91
theorem wholeAccepted91 : StepValid wholeStep91.shape wholeBoxes91 wholeStep91.proposed := by
  dsimp only [StepValid,wholeStep91]
  exact ⟨by decide,by decide⟩
noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91]
theorem wholeAccepted : Accepted wholeProgram wholeInitial :=
  ⟨wholeAccepted0,⟨wholeAccepted1,⟨wholeAccepted2,⟨wholeAccepted3,⟨wholeAccepted4,⟨wholeAccepted5,⟨wholeAccepted6,⟨wholeAccepted7,⟨wholeAccepted8,⟨wholeAccepted9,⟨wholeAccepted10,⟨wholeAccepted11,⟨wholeAccepted12,⟨wholeAccepted13,⟨wholeAccepted14,⟨wholeAccepted15,⟨wholeAccepted16,⟨wholeAccepted17,⟨wholeAccepted18,⟨wholeAccepted19,⟨wholeAccepted20,⟨wholeAccepted21,⟨wholeAccepted22,⟨wholeAccepted23,⟨wholeAccepted24,⟨wholeAccepted25,⟨wholeAccepted26,⟨wholeAccepted27,⟨wholeAccepted28,⟨wholeAccepted29,⟨wholeAccepted30,⟨wholeAccepted31,⟨wholeAccepted32,⟨wholeAccepted33,⟨wholeAccepted34,⟨wholeAccepted35,⟨wholeAccepted36,⟨wholeAccepted37,⟨wholeAccepted38,⟨wholeAccepted39,⟨wholeAccepted40,⟨wholeAccepted41,⟨wholeAccepted42,⟨wholeAccepted43,⟨wholeAccepted44,⟨wholeAccepted45,⟨wholeAccepted46,⟨wholeAccepted47,⟨wholeAccepted48,⟨wholeAccepted49,⟨wholeAccepted50,⟨wholeAccepted51,⟨wholeAccepted52,⟨wholeAccepted53,⟨wholeAccepted54,⟨wholeAccepted55,⟨wholeAccepted56,⟨wholeAccepted57,⟨wholeAccepted58,⟨wholeAccepted59,⟨wholeAccepted60,⟨wholeAccepted61,⟨wholeAccepted62,⟨wholeAccepted63,⟨wholeAccepted64,⟨wholeAccepted65,⟨wholeAccepted66,⟨wholeAccepted67,⟨wholeAccepted68,⟨wholeAccepted69,⟨wholeAccepted70,⟨wholeAccepted71,⟨wholeAccepted72,⟨wholeAccepted73,⟨wholeAccepted74,⟨wholeAccepted75,⟨wholeAccepted76,⟨wholeAccepted77,⟨wholeAccepted78,⟨wholeAccepted79,⟨wholeAccepted80,⟨wholeAccepted81,⟨wholeAccepted82,⟨wholeAccepted83,⟨wholeAccepted84,⟨wholeAccepted85,⟨wholeAccepted86,⟨wholeAccepted87,⟨wholeAccepted88,⟨wholeAccepted89,⟨wholeAccepted90,⟨wholeAccepted91,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
noncomputable def whole_output : DyadicBivariateJetEnclosure 40 := ⟨⟨643869303863,740209189859⟩,⟨0,0⟩,⟨-3781660425176,-748528494381⟩,⟨0,0⟩,⟨0,0⟩,⟨-64151115605720,73192734788266⟩⟩
theorem whole_output_eq : (finalBoxes wholeProgram wholeInitial).getD 0 (zeroBox 40)=whole_output := rfl
open GeneralCK.Reflection GeneralCK.Reflection.SmallRatio GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed
theorem sameShape : shapes centerProgram=shapes wholeProgram := by decide
theorem scalar_program (a e r : ℝ) :
    (evalRealProgram wholeProgram [a,e,r,2]).getD 0 0=ReflectionMidpointKernel.scalarCore a e r := rfl
attribute [local irreducible] wholeProgram centerProgram
noncomputable def reflection_log_0_out : DyadicInterval 64 := ⟨-12786308645202662930,-12786308645202655416⟩
theorem reflection_log_0_checked : DyadicFastLog.check 1 2 1 16 reflection_log_0_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointFamily.Endpoints0422.sharedTwo_eq]
  decide
theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := DyadicFastLog.check_sound reflection_log_0_checked
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1):ℝ)=((1 / 2):ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [he]
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_0_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_1_out : DyadicInterval 64 := ⟨-4647202507667544845,-4647202507667544788⟩
theorem reflection_log_1_checked : DyadicFastLog.check 2000 2573 0 16 reflection_log_1_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointFamily.Endpoints0422.sharedTwo_eq]
  decide
theorem reflection_log_1 : Bounds (31490669 / 125000000) (251925353 / 1000000000) (Real.log (2573 / 2000)) := by
  have h := DyadicFastLog.check_sound reflection_log_1_checked
  have he : Real.log (2573 / 2000) = -Real.log (2000 / 2573) := by
    rw [show ((2573 / 2000):ℝ)=((2000 / 2573):ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [he]
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_1_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_2_out : DyadicInterval 64 := ⟨-6227119823812366091,-6227119823812366046⟩
theorem reflection_log_2_checked : DyadicFastLog.check 1427 2000 0 16 reflection_log_2_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointFamily.Endpoints0422.sharedTwo_eq]
  decide
theorem reflection_log_2 : Bounds (-337572843 / 1000000000) (-168786421 / 500000000) (Real.log (1427 / 2000)) := by
  have h := DyadicFastLog.check_sound reflection_log_2_checked
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_2_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_3_out : DyadicInterval 64 := ⟨-4640031761581636947,-4640031761581636896⟩
theorem reflection_log_3_checked : DyadicFastLog.check 500 643 0 16 reflection_log_3_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointFamily.Endpoints0422.sharedTwo_eq]
  decide
theorem reflection_log_3 : Bounds (2012293 / 8000000) (125768313 / 500000000) (Real.log (643 / 500)) := by
  have h := DyadicFastLog.check_sound reflection_log_3_checked
  have he : Real.log (643 / 500) = -Real.log (500 / 643) := by
    rw [show ((643 / 500):ℝ)=((500 / 643):ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [he]
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_3_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_4_out : DyadicInterval 64 := ⟨-6214197410622815977,-6214197410622815922⟩
theorem reflection_log_4_checked : DyadicFastLog.check 357 500 0 16 reflection_log_4_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointFamily.Endpoints0422.sharedTwo_eq]
  decide
theorem reflection_log_4 : Bounds (-336872317 / 1000000000) (-84218079 / 250000000) (Real.log (357 / 500)) := by
  have h := DyadicFastLog.check_sound reflection_log_4_checked
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_4_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_5_out : DyadicInterval 64 := ⟨-52774358549588705,-52774358549588660⟩
theorem reflection_log_5_checked : DyadicFastLog.check 200000 200573 0 16 reflection_log_5_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointFamily.Endpoints0422.sharedTwo_eq]
  decide
theorem reflection_log_5 : Bounds (2860903 / 1000000000) (357613 / 125000000) (Real.log (200573 / 200000)) := by
  have h := DyadicFastLog.check_sound reflection_log_5_checked
  have he : Real.log (200573 / 200000) = -Real.log (200000 / 200573) := by
    rw [show ((200573 / 200000):ℝ)=((200000 / 200573):ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [he]
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_5_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_6_out : DyadicInterval 64 := ⟨-52925774196890833,-52925774196890788⟩
theorem reflection_log_6_checked : DyadicFastLog.check 199427 200000 0 16 reflection_log_6_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointFamily.Endpoints0422.sharedTwo_eq]
  decide
theorem reflection_log_6 : Bounds (-358639 / 125000000) (-2869111 / 1000000000) (Real.log (199427 / 200000)) := by
  have h := DyadicFastLog.check_sound reflection_log_6_checked
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_6_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_7_out : DyadicInterval 64 := ⟨-5275014513956591,-5275014513956546⟩
theorem reflection_log_7_checked : DyadicFastLog.check 500000 500143 0 16 reflection_log_7_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointFamily.Endpoints0422.sharedTwo_eq]
  decide
theorem reflection_log_7 : Bounds (285959 / 1000000000) (7149 / 25000000) (Real.log (500143 / 500000)) := by
  have h := DyadicFastLog.check_sound reflection_log_7_checked
  have he : Real.log (500143 / 500000) = -Real.log (500000 / 500143) := by
    rw [show ((500143 / 500000):ℝ)=((500000 / 500143):ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [he]
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_7_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_8_out : DyadicInterval 64 := ⟨-5276523383896553,-5276523383896508⟩
theorem reflection_log_8_checked : DyadicFastLog.check 499857 500000 0 16 reflection_log_8_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointFamily.Endpoints0422.sharedTwo_eq]
  decide
theorem reflection_log_8 : Bounds (-286041 / 1000000000) (-7151 / 25000000) (Real.log (499857 / 500000)) := by
  have h := DyadicFastLog.check_sound reflection_log_8_checked
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_8_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
theorem entropy_bound {a z : ℝ} (ha : Bounds (143 / 500) (573 / 2000) a) (hz : Bounds (1 / 1000) (1 / 100) z) :
  Bounds (672334191659 / 1000000000000) (2689639377 / 4000000000) ((biasE a+biasE (a*z))/2) := by
  let x0 : ℝ := Real.log (2 / 1)
  have hx0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x0 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x1 : ℝ := (1 / 1)+(573 / 2000)
  have hx1 : Bounds (2573 / 2000) (2573 / 2000) x1 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((573 / 2000) : ℝ)) <;> norm_num
  let x2 : ℝ := (1 / 1)+(573 / 2000)
  have hx2 : Bounds (2573 / 2000) (2573 / 2000) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((573 / 2000) : ℝ)) <;> norm_num
  let x3 : ℝ := Real.log x2
  have hx3 : Bounds (31490669 / 125000000) (251925353 / 1000000000) x3 := by
    exact bounds_log hx2 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x4 : ℝ := x1*x3
  have hx4 : Bounds (81025491337 / 250000000000) (64820393327 / 200000000000) x4 := by
    apply bounds_mul hx1 hx3 <;> norm_num
  let x5 : ℝ := -(573 / 2000)
  have hx5 : Bounds (-573 / 2000) (-573 / 2000) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((573 / 2000) : ℝ))
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (1427 / 2000) (1427 / 2000) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-(573 / 2000)
  have hx7 : Bounds (1427 / 2000) (1427 / 2000) x7 := by
    exact hx6
  let x8 : ℝ := -(573 / 2000)
  have hx8 : Bounds (-573 / 2000) (-573 / 2000) x8 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((573 / 2000) : ℝ))
  let x9 : ℝ := (1 / 1)+x8
  have hx9 : Bounds (1427 / 2000) (1427 / 2000) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx8 <;> norm_num
  let x10 : ℝ := (1 / 1)-(573 / 2000)
  have hx10 : Bounds (1427 / 2000) (1427 / 2000) x10 := by
    exact hx9
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (-337572843 / 1000000000) (-168786421 / 500000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x12 : ℝ := x7*x11
  have hx12 : Bounds (-240858223481 / 1000000000000) (-240858222767 / 1000000000000) x12 := by
    apply bounds_mul hx7 hx11 <;> norm_num
  let x13 : ℝ := x4+x12
  have hx13 : Bounds (83243741867 / 1000000000000) (20810935967 / 250000000000) x13 := by
    apply bounds_add hx4 hx12 <;> norm_num
  let x14 : ℝ := (2 / 1)⁻¹
  have hx14 : Bounds (1 / 2) (1 / 2) x14 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x15 : ℝ := x13*x14
  have hx15 : Bounds (41621870933 / 1000000000000) (20810935967 / 500000000000) x15 := by
    apply bounds_mul hx13 hx14 <;> norm_num
  let x16 : ℝ := x13/(2 / 1)
  have hx16 : Bounds (41621870933 / 1000000000000) (20810935967 / 500000000000) x16 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx15
  let x17 : ℝ := -x16
  have hx17 : Bounds (-20810935967 / 500000000000) (-41621870933 / 1000000000000) x17 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx16
  let x18 : ℝ := x0+x17
  have hx18 : Bounds (325762654033 / 500000000000) (651525310067 / 1000000000000) x18 := by
    apply bounds_add hx0 hx17 <;> norm_num
  let x19 : ℝ := x0-x16
  have hx19 : Bounds (325762654033 / 500000000000) (651525310067 / 1000000000000) x19 := by
    exact hx18
  let x20 : ℝ := biasE (573 / 2000)
  have hx20 : Bounds (325762654033 / 500000000000) (651525310067 / 1000000000000) x20 := by
    simpa +zetaDelta only [biasE, div_one] using hx19
  let x21 : ℝ := Real.log (2 / 1)
  have hx21 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x21 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x22 : ℝ := (1 / 1)+(143 / 500)
  have hx22 : Bounds (643 / 500) (643 / 500) x22 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((143 / 500) : ℝ)) <;> norm_num
  let x23 : ℝ := (1 / 1)+(143 / 500)
  have hx23 : Bounds (643 / 500) (643 / 500) x23 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((143 / 500) : ℝ)) <;> norm_num
  let x24 : ℝ := Real.log x23
  have hx24 : Bounds (2012293 / 8000000) (125768313 / 500000000) x24 := by
    exact bounds_log hx23 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x25 : ℝ := x22*x24
  have hx25 : Bounds (1293904399 / 4000000000) (80869025259 / 250000000000) x25 := by
    apply bounds_mul hx22 hx24 <;> norm_num
  let x26 : ℝ := -(143 / 500)
  have hx26 : Bounds (-143 / 500) (-143 / 500) x26 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((143 / 500) : ℝ))
  let x27 : ℝ := (1 / 1)+x26
  have hx27 : Bounds (357 / 500) (357 / 500) x27 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx26 <;> norm_num
  let x28 : ℝ := (1 / 1)-(143 / 500)
  have hx28 : Bounds (357 / 500) (357 / 500) x28 := by
    exact hx27
  let x29 : ℝ := -(143 / 500)
  have hx29 : Bounds (-143 / 500) (-143 / 500) x29 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((143 / 500) : ℝ))
  let x30 : ℝ := (1 / 1)+x29
  have hx30 : Bounds (357 / 500) (357 / 500) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx29 <;> norm_num
  let x31 : ℝ := (1 / 1)-(143 / 500)
  have hx31 : Bounds (357 / 500) (357 / 500) x31 := by
    exact hx30
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (-336872317 / 1000000000) (-84218079 / 250000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x33 : ℝ := x28*x32
  have hx33 : Bounds (-120263417169 / 500000000000) (-30065854203 / 125000000000) x33 := by
    apply bounds_mul hx28 hx32 <;> norm_num
  let x34 : ℝ := x25+x33
  have hx34 : Bounds (20737316353 / 250000000000) (20737316853 / 250000000000) x34 := by
    apply bounds_add hx25 hx33 <;> norm_num
  let x35 : ℝ := (2 / 1)⁻¹
  have hx35 : Bounds (1 / 2) (1 / 2) x35 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x36 : ℝ := x34*x35
  have hx36 : Bounds (20737316353 / 500000000000) (20737316853 / 500000000000) x36 := by
    apply bounds_mul hx34 hx35 <;> norm_num
  let x37 : ℝ := x34/(2 / 1)
  have hx37 : Bounds (20737316353 / 500000000000) (20737316853 / 500000000000) x37 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx36
  let x38 : ℝ := -x37
  have hx38 : Bounds (-20737316853 / 500000000000) (-20737316353 / 500000000000) x38 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx37
  let x39 : ℝ := x21+x38
  have hx39 : Bounds (325836273147 / 500000000000) (325836274147 / 500000000000) x39 := by
    apply bounds_add hx21 hx38 <;> norm_num
  let x40 : ℝ := x21-x37
  have hx40 : Bounds (325836273147 / 500000000000) (325836274147 / 500000000000) x40 := by
    exact hx39
  let x41 : ℝ := biasE (143 / 500)
  have hx41 : Bounds (325836273147 / 500000000000) (325836274147 / 500000000000) x41 := by
    simpa +zetaDelta only [biasE, div_one] using hx40
  let x42 : ℝ := biasE a
  have hx42 : Bounds (325762654033 / 500000000000) (325836274147 / 500000000000) x42 := by
    exact bounds_biasE ha (by norm_num) (by norm_num) hx20.1 hx41.2
  let x43 : ℝ := a*z
  have hx43 : Bounds (143 / 500000) (573 / 200000) x43 := by
    apply bounds_mul ha hz <;> norm_num
  let x44 : ℝ := Real.log (2 / 1)
  have hx44 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x44 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x45 : ℝ := (1 / 1)+(573 / 200000)
  have hx45 : Bounds (200573 / 200000) (200573 / 200000) x45 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((573 / 200000) : ℝ)) <;> norm_num
  let x46 : ℝ := (1 / 1)+(573 / 200000)
  have hx46 : Bounds (200573 / 200000) (200573 / 200000) x46 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((573 / 200000) : ℝ)) <;> norm_num
  let x47 : ℝ := Real.log x46
  have hx47 : Bounds (2860903 / 1000000000) (357613 / 125000000) x47 := by
    exact bounds_log hx46 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x48 : ℝ := x45*x47
  have hx48 : Bounds (2869099487 / 1000000000000) (286910049 / 100000000000) x48 := by
    apply bounds_mul hx45 hx47 <;> norm_num
  let x49 : ℝ := -(573 / 200000)
  have hx49 : Bounds (-573 / 200000) (-573 / 200000) x49 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((573 / 200000) : ℝ))
  let x50 : ℝ := (1 / 1)+x49
  have hx50 : Bounds (199427 / 200000) (199427 / 200000) x50 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx49 <;> norm_num
  let x51 : ℝ := (1 / 1)-(573 / 200000)
  have hx51 : Bounds (199427 / 200000) (199427 / 200000) x51 := by
    exact hx50
  let x52 : ℝ := -(573 / 200000)
  have hx52 : Bounds (-573 / 200000) (-573 / 200000) x52 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((573 / 200000) : ℝ))
  let x53 : ℝ := (1 / 1)+x52
  have hx53 : Bounds (199427 / 200000) (199427 / 200000) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx52 <;> norm_num
  let x54 : ℝ := (1 / 1)-(573 / 200000)
  have hx54 : Bounds (199427 / 200000) (199427 / 200000) x54 := by
    exact hx53
  let x55 : ℝ := Real.log x54
  have hx55 : Bounds (-358639 / 125000000) (-2869111 / 1000000000) x55 := by
    exact bounds_log hx54 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x56 : ℝ := x51*x55
  have hx56 : Bounds (-572178399 / 200000000000) (-715222749 / 250000000000) x56 := by
    apply bounds_mul hx51 hx55 <;> norm_num
  let x57 : ℝ := x48+x56
  have hx57 : Bounds (2051873 / 250000000000) (4104747 / 500000000000) x57 := by
    apply bounds_add hx48 hx56 <;> norm_num
  let x58 : ℝ := (2 / 1)⁻¹
  have hx58 : Bounds (1 / 2) (1 / 2) x58 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x59 : ℝ := x57*x58
  have hx59 : Bounds (2051873 / 500000000000) (4104747 / 1000000000000) x59 := by
    apply bounds_mul hx57 hx58 <;> norm_num
  let x60 : ℝ := x57/(2 / 1)
  have hx60 : Bounds (2051873 / 500000000000) (4104747 / 1000000000000) x60 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx59
  let x61 : ℝ := -x60
  have hx61 : Bounds (-4104747 / 1000000000000) (-2051873 / 500000000000) x61 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx60
  let x62 : ℝ := x44+x61
  have hx62 : Bounds (693143075253 / 1000000000000) (346571538627 / 500000000000) x62 := by
    apply bounds_add hx44 hx61 <;> norm_num
  let x63 : ℝ := x44-x60
  have hx63 : Bounds (693143075253 / 1000000000000) (346571538627 / 500000000000) x63 := by
    exact hx62
  let x64 : ℝ := biasE (573 / 200000)
  have hx64 : Bounds (693143075253 / 1000000000000) (346571538627 / 500000000000) x64 := by
    simpa +zetaDelta only [biasE, div_one] using hx63
  let x65 : ℝ := Real.log (2 / 1)
  have hx65 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x65 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x66 : ℝ := (1 / 1)+(143 / 500000)
  have hx66 : Bounds (500143 / 500000) (500143 / 500000) x66 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((143 / 500000) : ℝ)) <;> norm_num
  let x67 : ℝ := (1 / 1)+(143 / 500000)
  have hx67 : Bounds (500143 / 500000) (500143 / 500000) x67 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((143 / 500000) : ℝ)) <;> norm_num
  let x68 : ℝ := Real.log x67
  have hx68 : Bounds (285959 / 1000000000) (7149 / 25000000) x68 := by
    exact bounds_log hx67 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x69 : ℝ := x66*x68
  have hx69 : Bounds (17877549 / 62500000000) (57208357 / 200000000000) x69 := by
    apply bounds_mul hx66 hx68 <;> norm_num
  let x70 : ℝ := -(143 / 500000)
  have hx70 : Bounds (-143 / 500000) (-143 / 500000) x70 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((143 / 500000) : ℝ))
  let x71 : ℝ := (1 / 1)+x70
  have hx71 : Bounds (499857 / 500000) (499857 / 500000) x71 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx70 <;> norm_num
  let x72 : ℝ := (1 / 1)-(143 / 500000)
  have hx72 : Bounds (499857 / 500000) (499857 / 500000) x72 := by
    exact hx71
  let x73 : ℝ := -(143 / 500000)
  have hx73 : Bounds (-143 / 500000) (-143 / 500000) x73 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((143 / 500000) : ℝ))
  let x74 : ℝ := (1 / 1)+x73
  have hx74 : Bounds (499857 / 500000) (499857 / 500000) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx73 <;> norm_num
  let x75 : ℝ := (1 / 1)-(143 / 500000)
  have hx75 : Bounds (499857 / 500000) (499857 / 500000) x75 := by
    exact hx74
  let x76 : ℝ := Real.log x75
  have hx76 : Bounds (-286041 / 1000000000) (-7151 / 25000000) x76 := by
    exact bounds_log hx75 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x77 : ℝ := x72*x76
  have hx77 : Bounds (-285959193 / 1000000000000) (-17872387 / 62500000000) x77 := by
    apply bounds_mul hx72 hx76 <;> norm_num
  let x78 : ℝ := x69+x77
  have hx78 : Bounds (81591 / 1000000000000) (83593 / 1000000000000) x78 := by
    apply bounds_add hx69 hx77 <;> norm_num
  let x79 : ℝ := (2 / 1)⁻¹
  have hx79 : Bounds (1 / 2) (1 / 2) x79 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x80 : ℝ := x78*x79
  have hx80 : Bounds (8159 / 200000000000) (41797 / 1000000000000) x80 := by
    apply bounds_mul hx78 hx79 <;> norm_num
  let x81 : ℝ := x78/(2 / 1)
  have hx81 : Bounds (8159 / 200000000000) (41797 / 1000000000000) x81 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx80
  let x82 : ℝ := -x81
  have hx82 : Bounds (-41797 / 1000000000000) (-8159 / 200000000000) x82 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx81
  let x83 : ℝ := x65+x82
  have hx83 : Bounds (693147138203 / 1000000000000) (138629428041 / 200000000000) x83 := by
    apply bounds_add hx65 hx82 <;> norm_num
  let x84 : ℝ := x65-x81
  have hx84 : Bounds (693147138203 / 1000000000000) (138629428041 / 200000000000) x84 := by
    exact hx83
  let x85 : ℝ := biasE (143 / 500000)
  have hx85 : Bounds (693147138203 / 1000000000000) (138629428041 / 200000000000) x85 := by
    simpa +zetaDelta only [biasE, div_one] using hx84
  let x86 : ℝ := biasE x43
  have hx86 : Bounds (693143075253 / 1000000000000) (138629428041 / 200000000000) x86 := by
    exact bounds_biasE hx43 (by norm_num) (by norm_num) hx64.1 hx85.2
  let x87 : ℝ := x42+x86
  have hx87 : Bounds (1344668383319 / 1000000000000) (1344819688499 / 1000000000000) x87 := by
    apply bounds_add hx42 hx86 <;> norm_num
  let x88 : ℝ := (2 / 1)⁻¹
  have hx88 : Bounds (1 / 2) (1 / 2) x88 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x89 : ℝ := x87*x88
  have hx89 : Bounds (672334191659 / 1000000000000) (2689639377 / 4000000000) x89 := by
    apply bounds_mul hx87 hx88 <;> norm_num
  let x90 : ℝ := x87/(2 / 1)
  have hx90 : Bounds (672334191659 / 1000000000000) (2689639377 / 4000000000) x90 := by
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

theorem center_inputs_eq : centerInitial=inputBoxes ⟨314460325543,315010081358⟩ ⟨739239261480,739322442384⟩ ⟨157230162771,157505040679⟩ := rfl
theorem whole_inputs_eq : wholeInitial=inputBoxes ⟨314460325543,315010081358⟩ ⟨739239261480,739322442384⟩ ⟨155655112365,159080091086⟩ := rfl
noncomputable def centerUpper : ℝ := (697153690975 / 1099511627776)
noncomputable def secondUpper : ℝ := (36596367394133 / 549755813888)


theorem center_inputs {a z : ℝ} (ha : Bounds (143/500) (573/2000) a)
    (hz : Bounds (1/1000) (1/100) z) :
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

theorem whole_inputs {a z s : ℝ} (ha : Bounds (143/500) (573/2000) a)
    (hz : Bounds (1/1000) (1/100) z) (hs : s∈Icc (a*(1-z)/2) (a*(1+z)/2)) :
    RegistersContain wholeInitial (inputJets a ((biasE a+biasE (a*z))/2)) s := by
  rw [whole_inputs_eq]
  apply inputs_contain
  · norm_num [DyadicInterval.Contains,DyadicInterval.scale]
    constructor <;> linarith [ha.1,ha.2]
  · have h := entropy_bound ha hz
    norm_num [DyadicInterval.Contains,DyadicInterval.scale]
    constructor <;> linarith [h.1,h.2]
  · have hb : a*z≤(573/2000:ℝ)*(1/100) :=
      mul_le_mul ha.2 hz.2 (by linarith [hz.1]) (by norm_num)
    norm_num [DyadicInterval.Contains,DyadicInterval.scale]
    constructor <;> nlinarith [ha.1,ha.2,hs.1,hs.2]

theorem curvature_pos {a z : ℝ} (ha : Bounds (143/500) (573/2000) a)
    (hz : Bounds (1/1000) (1/100) z) : 0<curvature a (a*z) := by
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
    have hb : a*z≤(573/200000:ℝ) := by
      have h := mul_le_mul ha.2 hz.2 hz0.le (by norm_num : (0:ℝ)≤573/2000)
      norm_num at h
      exact h
    have hb2 := mul_self_le_mul_self hb0 hb
    have hle : centerUpper+secondUpper*(a*z)^2/24 ≤
        centerUpper+secondUpper*(573/200000:ℝ)^2/24 := by
      unfold centerUpper secondUpper
      nlinarith
    apply hle.trans_lt
    exact lt_of_lt_of_le (by norm_num [centerUpper,secondUpper] :
      centerUpper+secondUpper*(573/200000:ℝ)^2/24 < 2*(143/500:ℝ)/(1-(143/500:ℝ)^2)^2)
      (LowRatioFamily.base_mono (by norm_num) ha.1 ha1)

#print axioms entropy_bound
#print axioms curvature_pos
end GeneralCK.Certificates.ReflectionMidpointFamily.Cell0422

end

-- ===== source module GeneralCK.Certificates.Generated.MidpointFamily.Cell0423 =====
section

namespace GeneralCK.Certificates.ReflectionMidpointFamily.Endpoints0423
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
noncomputable def out_w1 : DyadicInterval 40 := ⟨149283200128,149283200192⟩
theorem checked_w1 : DyadicFastLog.check 1099511627776 1259403739136 0 16 (lift40 out_w1.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w1 : out_w1.Contains (Real.log ((1259403739136:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w1
#print axioms endpoint_w1
noncomputable def out_w2 : DyadicInterval 40 := ⟨-172784252224,-172784252160⟩
theorem checked_w2 : DyadicFastLog.check 939619516416 1099511627776 0 16 (lift40 out_w2)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w2 : out_w2.Contains (Real.log ((939619516416:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w2
#print axioms endpoint_w2
noncomputable def out_w3 : DyadicInterval 40 := ⟨149538581056,149538581120⟩
theorem checked_w3 : DyadicFastLog.check 1099511627776 1259696291840 0 16 (lift40 out_w3.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w3 : out_w3.Contains (Real.log ((1259696291840:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w3
#print axioms endpoint_w3
noncomputable def out_w4 : DyadicInterval 40 := ⟨-173126640960,-173126640896⟩
theorem checked_w4 : DyadicFastLog.check 939326963712 1099511627776 0 16 (lift40 out_w4)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w4 : out_w4.Contains (Real.log ((939326963712:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w4
#print axioms endpoint_w4
noncomputable def out_w5 : DyadicInterval 40 := ⟨-23588059904,-23588059840⟩
theorem checked_w5 : DyadicFastLog.check 1076174788080 1099511627776 0 16 (lift40 out_w5)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w5 : out_w5.Contains (Real.log ((1076174788080:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w5
#print axioms endpoint_w5
noncomputable def out_w6 : DyadicInterval 40 := ⟨-23501052096,-23501052032⟩
theorem checked_w6 : DyadicFastLog.check 1076259952551 1099511627776 0 16 (lift40 out_w6)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w6 : out_w6.Contains (Real.log ((1076259952551:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w6
#print axioms endpoint_w6
noncomputable def out_w7 : DyadicInterval 40 := ⟨648160119616,648160121088⟩
theorem checked_w7 : DyadicFastLog.check 1099511627776 1982511155054 0 16 (lift40 out_w7.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w7 : out_w7.Contains (Real.log ((1982511155054:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w7
#print axioms endpoint_w7
noncomputable def out_w8 : DyadicInterval 40 := ⟨649358139136,649358140608⟩
theorem checked_w8 : DyadicFastLog.check 1099511627776 1984672461360 0 16 (lift40 out_w8.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w8 : out_w8.Contains (Real.log ((1984672461360:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w8
#print axioms endpoint_w8
noncomputable def out_w9 : DyadicInterval 40 := ⟨322067452288,322067452352⟩
theorem checked_w9 : DyadicFastLog.check 1099511627776 1473712530498 0 16 (lift40 out_w9.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w9 : out_w9.Contains (Real.log ((1473712530498:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w9
#print axioms endpoint_w9
noncomputable def out_w10 : DyadicInterval 40 := ⟨322665222016,322665222080⟩
theorem checked_w10 : DyadicFastLog.check 1099511627776 1474513959306 0 16 (lift40 out_w10.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w10 : out_w10.Contains (Real.log ((1474513959306:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w10
#print axioms endpoint_w10
noncomputable def out_w11 : DyadicInterval 40 := ⟨147925665088,147925665152⟩
theorem checked_w11 : DyadicFastLog.check 1099511627776 1257849749504 0 16 (lift40 out_w11.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w11 : out_w11.Contains (Real.log ((1257849749504:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w11
#print axioms endpoint_w11
noncomputable def out_w12 : DyadicInterval 40 := ⟨-170967327040,-170967326976⟩
theorem checked_w12 : DyadicFastLog.check 941173506048 1099511627776 0 16 (lift40 out_w12)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w12 : out_w12.Contains (Real.log ((941173506048:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w12
#print axioms endpoint_w12
noncomputable def out_w13 : DyadicInterval 40 := ⟨150893213248,150893213312⟩
theorem checked_w13 : DyadicFastLog.check 1099511627776 1261249232896 0 16 (lift40 out_w13.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w13 : out_w13.Contains (Real.log ((1261249232896:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w13
#print axioms endpoint_w13
noncomputable def out_w14 : DyadicInterval 40 := ⟨-174945911424,-174945911360⟩
theorem checked_w14 : DyadicFastLog.check 937774022656 1099511627776 0 16 (lift40 out_w14)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w14 : out_w14.Contains (Real.log ((937774022656:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w14
#print axioms endpoint_w14
noncomputable def out_w15 : DyadicInterval 40 := ⟨-24052698112,-24052698048⟩
theorem checked_w15 : DyadicFastLog.check 1075720107751 1099511627776 0 16 (lift40 out_w15)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w15 : out_w15.Contains (Real.log ((1075720107751:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w15
#print axioms endpoint_w15
noncomputable def out_w16 : DyadicInterval 40 := ⟨-23041661952,-23041661888⟩
theorem checked_w16 : DyadicFastLog.check 1076709721767 1099511627776 0 16 (lift40 out_w16)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w16 : out_w16.Contains (Real.log ((1076709721767:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w16
#print axioms endpoint_w16
noncomputable def out_w17 : DyadicInterval 40 := ⟨318892992128,318892992192⟩
theorem checked_w17 : DyadicFastLog.check 1099511627776 1469463830724 0 16 (lift40 out_w17.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w17 : out_w17.Contains (Real.log ((1469463830724:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w17
#print axioms endpoint_w17
noncomputable def out_w18 : DyadicInterval 40 := ⟨325839124608,325839124672⟩
theorem checked_w18 : DyadicFastLog.check 1099511627776 1478776510748 0 16 (lift40 out_w18.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w18 : out_w18.Contains (Real.log ((1478776510748:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w18
#print axioms endpoint_w18
end GeneralCK.Certificates.ReflectionMidpointFamily.Endpoints0423

namespace GeneralCK.Certificates.ReflectionMidpointFamily.Cell0423
open Set GeneralCK.Certificates.ReflectionMidpointFamily.Endpoints0423
open BivariateJetProgram (RegistersContain RegistersSound zeroBox zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
theorem lc0 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc1 : ProvedTranscendental.LogEncloses (⟨1259403739136,1259403739136⟩ : DyadicInterval 40) (⟨149283200128,149283200192⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w1
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w1
theorem lc2 : ProvedTranscendental.LogEncloses (⟨939619516416,939619516416⟩ : DyadicInterval 40) (⟨-172784252224,-172784252160⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w2
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w2
theorem lc3 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc4 : ProvedTranscendental.LogEncloses (⟨1259696291840,1259696291840⟩ : DyadicInterval 40) (⟨149538581056,149538581120⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w3
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w3
theorem lc5 : ProvedTranscendental.LogEncloses (⟨939326963712,939326963712⟩ : DyadicInterval 40) (⟨-173126640960,-173126640896⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w4
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w4
theorem lc6 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc7 : ProvedTranscendental.LogEncloses (⟨1076174788080,1076259952551⟩ : DyadicInterval 40) (⟨-23588059904,-23501052032⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w5
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w6
theorem lc8 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc9 : ProvedTranscendental.LogEncloses (⟨1259403739136,1259696291840⟩ : DyadicInterval 40) (⟨149283200128,149538581120⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w1
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w3
theorem lc10 : ProvedTranscendental.LogEncloses (⟨939326963712,939619516416⟩ : DyadicInterval 40) (⟨-173126640960,-172784252160⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w4
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w2
theorem lc11 : ProvedTranscendental.LogEncloses (⟨1076174788080,1076259952551⟩ : DyadicInterval 40) (⟨-23588059904,-23501052032⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w5
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w6
theorem lc12 : ProvedTranscendental.LogEncloses (⟨1982511155054,1984672461360⟩ : DyadicInterval 40) (⟨648160119616,649358140608⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w7
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
theorem lc13 : ProvedTranscendental.LogEncloses (⟨1473712530498,1474513959306⟩ : DyadicInterval 40) (⟨322067452288,322665222080⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w9
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w10
theorem lc14 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc15 : ProvedTranscendental.LogEncloses (⟨1257849749504,1257849749504⟩ : DyadicInterval 40) (⟨147925665088,147925665152⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w11
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w11
theorem lc16 : ProvedTranscendental.LogEncloses (⟨941173506048,941173506048⟩ : DyadicInterval 40) (⟨-170967327040,-170967326976⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w12
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w12
theorem lc17 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc18 : ProvedTranscendental.LogEncloses (⟨1261249232896,1261249232896⟩ : DyadicInterval 40) (⟨150893213248,150893213312⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w13
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w13
theorem lc19 : ProvedTranscendental.LogEncloses (⟨937774022656,937774022656⟩ : DyadicInterval 40) (⟨-174945911424,-174945911360⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w14
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w14
theorem lc20 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc21 : ProvedTranscendental.LogEncloses (⟨1075720107751,1076709721767⟩ : DyadicInterval 40) (⟨-24052698112,-23041661888⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w15
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w16
theorem lc22 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc23 : ProvedTranscendental.LogEncloses (⟨1257849749504,1261249232896⟩ : DyadicInterval 40) (⟨147925665088,150893213312⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w11
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w13
theorem lc24 : ProvedTranscendental.LogEncloses (⟨937774022656,941173506048⟩ : DyadicInterval 40) (⟨-174945911424,-170967326976⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w14
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w12
theorem lc25 : ProvedTranscendental.LogEncloses (⟨1075720107751,1076709721767⟩ : DyadicInterval 40) (⟨-24052698112,-23041661888⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w15
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w16
theorem lc26 : ProvedTranscendental.LogEncloses (⟨1982511155054,1984672461360⟩ : DyadicInterval 40) (⟨648160119616,649358140608⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w7
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
theorem lc27 : ProvedTranscendental.LogEncloses (⟨1469463830724,1478776510748⟩ : DyadicInterval 40) (⟨318892992128,325839124672⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w17
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w18
theorem ew3_ok (x : ℝ) (hx : (⟨159892111360,159892111360⟩ : DyadicInterval 40).Contains x) : (⟨750456219574,750456238903⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨159892111360,159892111360⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨149283200128,149283200192⟩ : DyadicInterval 40)) (minus:=(⟨-172784252224,-172784252160⟩ : DyadicInterval 40))
    (lc0 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc1 lc2 (by decide) hx
theorem ew6_ok (x : ℝ) (hx : (⟨160184664064,160184664064⟩ : DyadicInterval 40).Contains x) : (⟨750413332742,750413352072⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨160184664064,160184664064⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨149538581056,149538581120⟩ : DyadicInterval 40)) (minus:=(⟨-173126640960,-173126640896⟩ : DyadicInterval 40))
    (lc3 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc4 lc5 (by decide) hx
theorem ew17_ok (x : ℝ) (hx : (⟨158338121728,158338121728⟩ : DyadicInterval 40).Contains x) : (⟨750682694098,750682713428⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨158338121728,158338121728⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨147925665088,147925665152⟩ : DyadicInterval 40)) (minus:=(⟨-170967327040,-170967326976⟩ : DyadicInterval 40))
    (lc14 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc15 lc16 (by decide) hx
theorem ew20_ok (x : ℝ) (hx : (⟨161737605120,161737605120⟩ : DyadicInterval 40).Contains x) : (⟨750184347305,750184366634⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨161737605120,161737605120⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨150893213248,150893213312⟩ : DyadicInterval 40)) (minus:=(⟨-174945911424,-174945911360⟩ : DyadicInterval 40))
    (lc17 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc18 lc19 (by decide) hx
theorem bw9_ok (x : ℝ) (hx : (⟨159892111360,160184664064⟩ : DyadicInterval 40).Contains x) : (⟨773873909632,773917432832⟩ : DyadicInterval 40).Contains (Reflection.biasB x) := by
  exact ProvedTranscendental.denominator_encloses (c:=(⟨159892111360,160184664064⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (gapLog:=(⟨-23588059904,-23501052032⟩ : DyadicInterval 40))
    (lc6 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc7 (by decide) hx
theorem bw23_ok (x : ℝ) (hx : (⟨158338121728,161737605120⟩ : DyadicInterval 40).Contains x) : (⟨773644214560,774149751936⟩ : DyadicInterval 40).Contains (Reflection.biasB x) := by
  exact ProvedTranscendental.denominator_encloses (c:=(⟨158338121728,161737605120⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (gapLog:=(⟨-24052698112,-23041661888⟩ : DyadicInterval 40))
    (lc20 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc21 (by decide) hx
theorem brcenter6_contact (y : ℝ) (hy : (⟨5150927934880,5160499111409⟩ : DyadicInterval 40).Contains y) : (⟨159892111360,160184664064⟩ : DyadicInterval 40).Contains (Reflection.biasContact y) := by
  exact ProvedTranscendental.contact_bracket (Y:=(⟨5150927934880,5160499111409⟩ : DyadicInterval 40)) (c:=(⟨159892111360,160184664064⟩ : DyadicInterval 40)) (elo:=(⟨750456219574,750456238903⟩ : DyadicInterval 40)) (ehi:=(⟨750413332742,750413352072⟩ : DyadicInterval 40))
    (by decide) (by decide) (by decide) (by decide)
    (ew3_ok _ (DyadicContact.point_contains 40 159892111360)) (ew6_ok _ (DyadicContact.point_contains 40 160184664064))
    (by decide) (by decide) hy
theorem brcenter6_jet (y : ℝ) (hy : (⟨5150927934880,5160499111409⟩ : DyadicInterval 40).Contains y) : (⟨⟨159892111360,160184664064⟩,⟨-33156727837,-33033869235⟩,⟨13438208744,13516789415⟩⟩ : DyadicJetEnclosure 40).Contains reflectionContactJet y := by
  exact ProvedTranscendental.contact_jet (c:=(⟨159892111360,160184664064⟩ : DyadicInterval 40)) (B:=(⟨773873909632,773917432832⟩ : DyadicInterval 40)) (by decide) brcenter6_contact bw9_ok (by decide) (by decide) (by decide) hy
theorem brwhole6_contact (y : ℝ) (hy : (⟨5099928648391,5212717256322⟩ : DyadicInterval 40).Contains y) : (⟨158338121728,161737605120⟩ : DyadicInterval 40).Contains (Reflection.biasContact y) := by
  exact ProvedTranscendental.contact_bracket (Y:=(⟨5099928648391,5212717256322⟩ : DyadicInterval 40)) (c:=(⟨158338121728,161737605120⟩ : DyadicInterval 40)) (elo:=(⟨750682694098,750682713428⟩ : DyadicInterval 40)) (ehi:=(⟨750184347305,750184366634⟩ : DyadicInterval 40))
    (by decide) (by decide) (by decide) (by decide)
    (ew17_ok _ (DyadicContact.point_contains 40 158338121728)) (ew20_ok _ (DyadicContact.point_contains 40 161737605120))
    (by decide) (by decide) hy
theorem brwhole6_jet (y : ℝ) (hy : (⟨5099928648391,5212717256322⟩ : DyadicInterval 40).Contains y) : (⟨⟨158338121728,161737605120⟩,⟨-33812768735,-32385156398⟩,⟨13025384789,13938525549⟩⟩ : DyadicJetEnclosure 40).Contains reflectionContactJet y := by
  exact ProvedTranscendental.contact_jet (c:=(⟨158338121728,161737605120⟩ : DyadicInterval 40)) (B:=(⟨773644214560,774149751936⟩ : DyadicInterval 40)) (by decide) brwhole6_contact bw23_ok (by decide) (by decide) (by decide) hy
noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨315010081357,315559837172⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨739158158656,739241497705⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨157505040678,157779918586⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
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
noncomputable def centerStep4 : Instruction 40 := ⟨.inv 6,⟨⟨7662101935714,7675473841413⟩,⟨0,0⟩,⟨-53580969224837,-53394438576353⟩,⟨0,0⟩,⟨0,0⟩,⟨744173359948466,748076359164392⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4
theorem centerAccepted4 : StepValid centerStep4.shape centerBoxes4 centerStep4.proposed := by
  dsimp only [StepValid,centerStep4]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep5 : Instruction 40 := ⟨.mul 6 0,⟨⟨5150927934880,5160499111409⟩,⟨0,0⟩,⟨-36024426606904,-35894968187283⟩,⟨0,0⟩,⟨0,0⟩,⟨500278302261319,502958835701419⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5
theorem centerAccepted5 : StepValid centerStep5.shape centerBoxes5 centerStep5.proposed := by
  dsimp only [StepValid,centerStep5]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep6 : Instruction 40 := ⟨.contact 0,⟨⟨159892111360,160184664064⟩,⟨0,0⟩,⟨1078433056403,1086347864193⟩,⟨0,0⟩,⟨0,0⟩,⟨-844988725338,-520404619723⟩⟩⟩
noncomputable def centerBoxes7 := centerStep6.proposed :: centerBoxes6
theorem centerAccepted6 : StepValid centerStep6.shape centerBoxes6 centerStep6.proposed := by
  dsimp only [StepValid,centerStep6]
  exact ⟨by decide,by decide,(⟨⟨159892111360,160184664064⟩,⟨-33156727837,-33033869235⟩,⟨13438208744,13516789415⟩⟩ : DyadicJetEnclosure 40),brcenter6_jet,by decide⟩
noncomputable def centerStep7 : Instruction 40 := ⟨.log 10,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes8 := centerStep7.proposed :: centerBoxes7
theorem centerAccepted7 : StepValid centerStep7.shape centerBoxes7 centerStep7.proposed := by
  dsimp only [StepValid,centerStep7]
  exact ⟨by decide,by decide,lc0,by decide⟩
noncomputable def centerStep8 : Instruction 40 := ⟨.add 6 1,⟨⟨1259403739136,1259696291840⟩,⟨0,0⟩,⟨1078433056403,1086347864193⟩,⟨0,0⟩,⟨0,0⟩,⟨-844988725338,-520404619723⟩⟩⟩
noncomputable def centerBoxes9 := centerStep8.proposed :: centerBoxes8
theorem centerAccepted8 : StepValid centerStep8.shape centerBoxes8 centerStep8.proposed := by
  dsimp only [StepValid,centerStep8]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep9 : Instruction 40 := ⟨.log 0,⟨⟨149283200128,149538581120⟩,⟨0,0⟩,⟨941298067616,948426681114⟩,⟨0,0⟩,⟨0,0⟩,⟨-1555812617777,-1260079824684⟩⟩⟩
noncomputable def centerBoxes10 := centerStep9.proposed :: centerBoxes9
theorem centerAccepted9 : StepValid centerStep9.shape centerBoxes9 centerStep9.proposed := by
  dsimp only [StepValid,centerStep9]
  exact ⟨by decide,by decide,lc9,by decide⟩
noncomputable def centerStep10 : Instruction 40 := ⟨.mul 1 0,⟨⟨170992116574,171324423831⟩,⟨0,0⟩,⟨1224603914834,1234348466365⟩,⟨0,0⟩,⟨0,0⟩,⟨-50891591283,360165075958⟩⟩⟩
noncomputable def centerBoxes11 := centerStep10.proposed :: centerBoxes10
theorem centerAccepted10 : StepValid centerStep10.shape centerBoxes10 centerStep10.proposed := by
  dsimp only [StepValid,centerStep10]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep11 : Instruction 40 := ⟨.neg 4,⟨⟨-160184664064,-159892111360⟩,⟨0,0⟩,⟨-1086347864193,-1078433056403⟩,⟨0,0⟩,⟨0,0⟩,⟨520404619723,844988725338⟩⟩⟩
noncomputable def centerBoxes12 := centerStep11.proposed :: centerBoxes11
theorem centerAccepted11 : StepValid centerStep11.shape centerBoxes11 centerStep11.proposed := by
  dsimp only [StepValid,centerStep11]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep12 : Instruction 40 := ⟨.add 10 0,⟨⟨939326963712,939619516416⟩,⟨0,0⟩,⟨-1086347864193,-1078433056403⟩,⟨0,0⟩,⟨0,0⟩,⟨520404619723,844988725338⟩⟩⟩
noncomputable def centerBoxes13 := centerStep12.proposed :: centerBoxes12
theorem centerAccepted12 : StepValid centerStep12.shape centerBoxes12 centerStep12.proposed := by
  dsimp only [StepValid,centerStep12]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep13 : Instruction 40 := ⟨.log 0,⟨⟨-173126640960,-172784252160⟩,⟨0,0⟩,⟨-1271604196020,-1261946633265⟩,⟨0,0⟩,⟨0,0⟩,⟨-861671980203,-459293010228⟩⟩⟩
noncomputable def centerBoxes14 := centerStep13.proposed :: centerBoxes13
theorem centerAccepted13 : StepValid centerStep13.shape centerBoxes13 centerStep13.proposed := by
  dsimp only [StepValid,centerStep13]
  exact ⟨by decide,by decide,lc10,by decide⟩
noncomputable def centerStep14 : Instruction 40 := ⟨.mul 1 0,⟨⟨-147950386834,-147611814971⟩,⟨0,0⟩,⟨-917214375098,-907043379583⟩,⟨0,0⟩,⟨0,0⟩,⟨1606091300748,2038600517245⟩⟩⟩
noncomputable def centerBoxes15 := centerStep14.proposed :: centerBoxes14
theorem centerAccepted14 : StepValid centerStep14.shape centerBoxes14 centerStep14.proposed := by
  dsimp only [StepValid,centerStep14]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep15 : Instruction 40 := ⟨.add 4 0,⟨⟨23041729740,23712608860⟩,⟨0,0⟩,⟨307389539736,327305086782⟩,⟨0,0⟩,⟨0,0⟩,⟨1555199709465,2398765593203⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15
theorem centerAccepted15 : StepValid centerStep15.shape centerBoxes15 centerStep15.proposed := by
  dsimp only [StepValid,centerStep15]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep16 : Instruction 40 := ⟨.mul 0 15,⟨⟨11520864870,11856304430⟩,⟨0,0⟩,⟨153694769868,163652543391⟩,⟨0,0⟩,⟨0,0⟩,⟨777599854732,1199382796602⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16
theorem centerAccepted16 : StepValid centerStep16.shape centerBoxes16 centerStep16.proposed := by
  dsimp only [StepValid,centerStep16]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨-11856304430,-11520864870⟩,⟨0,0⟩,⟨-163652543391,-153694769868⟩,⟨0,0⟩,⟨0,0⟩,⟨-1199382796602,-777599854732⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17
theorem centerAccepted17 : StepValid centerStep17.shape centerBoxes17 centerStep17.proposed := by
  dsimp only [StepValid,centerStep17]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep18 : Instruction 40 := ⟨.add 10 0,⟨⟨750267079186,750602538010⟩,⟨0,0⟩,⟨-163652543391,-153694769868⟩,⟨0,0⟩,⟨0,0⟩,⟨-1199382796602,-777599854732⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18
theorem centerAccepted18 : StepValid centerStep18.shape centerBoxes18 centerStep18.proposed := by
  dsimp only [StepValid,centerStep18]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep19 : Instruction 40 := ⟨.mul 12 12,⟨⟨23251675225,23336839696⟩,⟨0,0⟩,⟨313653687678,316533746960⟩,⟨0,0⟩,⟨0,0⟩,⟨1869309238893,1995327854508⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19
theorem centerAccepted19 : StepValid centerStep19.shape centerBoxes19 centerStep19.proposed := by
  dsimp only [StepValid,centerStep19]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep20 : Instruction 40 := ⟨.neg 0,⟨⟨-23336839696,-23251675225⟩,⟨0,0⟩,⟨-316533746960,-313653687678⟩,⟨0,0⟩,⟨0,0⟩,⟨-1995327854508,-1869309238893⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20
theorem centerAccepted20 : StepValid centerStep20.shape centerBoxes20 centerStep20.proposed := by
  dsimp only [StepValid,centerStep20]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep21 : Instruction 40 := ⟨.add 19 0,⟨⟨1076174788080,1076259952551⟩,⟨0,0⟩,⟨-316533746960,-313653687678⟩,⟨0,0⟩,⟨0,0⟩,⟨-1995327854508,-1869309238893⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21
theorem centerAccepted21 : StepValid centerStep21.shape centerBoxes21 centerStep21.proposed := by
  dsimp only [StepValid,centerStep21]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep22 : Instruction 40 := ⟨.log 0,⟨⟨-23588059904,-23501052032⟩,⟨0,0⟩,⟨-323397778151,-320429907179⟩,⟨0,0⟩,⟨0,0⟩,⟨-2133717044081,-2003076729733⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22
theorem centerAccepted22 : StepValid centerStep22.shape centerBoxes22 centerStep22.proposed := by
  dsimp only [StepValid,centerStep22]
  exact ⟨by decide,by decide,lc7,by decide⟩
noncomputable def centerStep23 : Instruction 40 := ⟨.mul 0 22,⟨⟨-11794029952,-11750526016⟩,⟨0,0⟩,⟨-161698889076,-160214953589⟩,⟨0,0⟩,⟨0,0⟩,⟨-1066858522041,-1001538364866⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23
theorem centerAccepted23 : StepValid centerStep23.shape centerBoxes23 centerStep23.proposed := by
  dsimp only [StepValid,centerStep23]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep24 : Instruction 40 := ⟨.neg 0,⟨⟨11750526016,11794029952⟩,⟨0,0⟩,⟨160214953589,161698889076⟩,⟨0,0⟩,⟨0,0⟩,⟨1001538364866,1066858522041⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24
theorem centerAccepted24 : StepValid centerStep24.shape centerBoxes24 centerStep24.proposed := by
  dsimp only [StepValid,centerStep24]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep25 : Instruction 40 := ⟨.add 17 0,⟨⟨773873909632,773917432832⟩,⟨0,0⟩,⟨160214953589,161698889076⟩,⟨0,0⟩,⟨0,0⟩,⟨1001538364866,1066858522041⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25
theorem centerAccepted25 : StepValid centerStep25.shape centerBoxes25 centerStep25.proposed := by
  dsimp only [StepValid,centerStep25]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep26 : Instruction 40 := ⟨.add 24 26,⟨⟨1414521709133,1415071464948⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26
theorem centerAccepted26 : StepValid centerStep26.shape centerBoxes26 centerStep26.proposed := by
  dsimp only [StepValid,centerStep26]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep27 : Instruction 40 := ⟨.neg 27,⟨⟨-315559837172,-315010081357⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27
theorem centerAccepted27 : StepValid centerStep27.shape centerBoxes27 centerStep27.proposed := by
  dsimp only [StepValid,centerStep27]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep28 : Instruction 40 := ⟨.add 26 0,⟨⟨783951790604,784501546419⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28
theorem centerAccepted28 : StepValid centerStep28.shape centerBoxes28 centerStep28.proposed := by
  dsimp only [StepValid,centerStep28]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep29 : Instruction 40 := ⟨.inv 0,⟨⟨1541011391415,1542092044568⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29
theorem centerAccepted29 : StepValid centerStep29.shape centerBoxes29 centerStep29.proposed := by
  dsimp only [StepValid,centerStep29]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep30 : Instruction 40 := ⟨.mul 3 0,⟨⟨1982511155054,1984672461360⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30
theorem centerAccepted30 : StepValid centerStep30.shape centerBoxes30 centerStep30.proposed := by
  dsimp only [StepValid,centerStep30]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨648160119616,649358140608⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31
theorem centerAccepted31 : StepValid centerStep31.shape centerBoxes31 centerStep31.proposed := by
  dsimp only [StepValid,centerStep31]
  exact ⟨by decide,by decide,lc12,by decide⟩
noncomputable def centerStep32 : Instruction 40 := ⟨.mul 0 31,⟨⟨324080059808,324679070304⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32
theorem centerAccepted32 : StepValid centerStep32.shape centerBoxes32 centerStep32.proposed := by
  dsimp only [StepValid,centerStep32]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep33 : Instruction 40 := ⟨.inv 20,⟨⟨1286612079137,1287012793541⟩,⟨0,0⟩,⟨1476688140961,1488452534066⟩,⟨0,0⟩,⟨0,0⟩,⟨2231933851162,2730257046454⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33
theorem centerAccepted33 : StepValid centerStep33.shape centerBoxes33 centerStep33.proposed := by
  dsimp only [StepValid,centerStep33]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep34 : Instruction 40 := ⟨.mul 25 0,⟨⟨1473712530498,1474513959306⟩,⟨0,0⟩,⟨2953376281922,2976905068132⟩,⟨0,0⟩,⟨0,0⟩,⟨4464175752373,5460324491729⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34
theorem centerAccepted34 : StepValid centerStep34.shape centerBoxes34 centerStep34.proposed := by
  dsimp only [StepValid,centerStep34]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨322067452288,322665222080⟩,⟨0,0⟩,⟨2202265731479,2221017782956⟩,⟨0,0⟩,⟨0,0⟩,⟨-1157629954976,-337171581404⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35
theorem centerAccepted35 : StepValid centerStep35.shape centerBoxes35 centerStep35.proposed := by
  dsimp only [StepValid,centerStep35]
  exact ⟨by decide,by decide,lc13,by decide⟩
noncomputable def centerStep36 : Instruction 40 := ⟨.mul 0 35,⟨⟨161033726144,161332611040⟩,⟨0,0⟩,⟨1101132865739,1110508891478⟩,⟨0,0⟩,⟨0,0⟩,⟨-578814977488,-168585790702⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36
theorem centerAccepted36 : StepValid centerStep36.shape centerBoxes36 centerStep36.proposed := by
  dsimp only [StepValid,centerStep36]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep37 : Instruction 40 := ⟨.mul 40 11,⟨⟨1547747819264,1547834865664⟩,⟨0,0⟩,⟨320429907178,323397778152⟩,⟨0,0⟩,⟨0,0⟩,⟨2003076729732,2133717044082⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37
theorem centerAccepted37 : StepValid centerStep37.shape centerBoxes37 centerStep37.proposed := by
  dsimp only [StepValid,centerStep37]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep38 : Instruction 40 := ⟨.add 0 17,⟨⟨1524410979568,1524583190439⟩,⟨0,0⟩,⟨3896160218,9744090474⟩,⟨0,0⟩,⟨0,0⟩,⟨7748875224,264407805189⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38
theorem centerAccepted38 : StepValid centerStep38.shape centerBoxes38 centerStep38.proposed := by
  dsimp only [StepValid,centerStep38]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep39 : Instruction 40 := ⟨.mul 20 0,⟨⟨1040203072188,1040785729994⟩,⟨0,0⟩,⟨-224262072134,-206437158019⟩,⟨0,0⟩,⟨0,0⟩,⟨-1660677676227,-898684652851⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39
theorem centerAccepted39 : StepValid centerStep39.shape centerBoxes39 centerStep39.proposed := by
  dsimp only [StepValid,centerStep39]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep40 : Instruction 40 := ⟨.mul 43 41,⟨⟨1478316317312,1478482995410⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40
theorem centerAccepted40 : StepValid centerStep40.shape centerBoxes40 centerStep40.proposed := by
  dsimp only [StepValid,centerStep40]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep41 : Instruction 40 := ⟨.mul 19 19,⟨⟨1053333266553,1053499986907⟩,⟨0,0⟩,⟨-619679841264,-613992944394⟩,⟨0,0⟩,⟨0,0⟩,⟨-3727314517570,-3477016182034⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41
theorem centerAccepted41 : StepValid centerStep41.shape centerBoxes41 centerStep41.proposed := by
  dsimp only [StepValid,centerStep41]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep42 : Instruction 40 := ⟨.mul 1 0,⟨⟨1416228547452,1416612409509⟩,⟨0,0⟩,⟨-833266410980,-825526320488⟩,⟨0,0⟩,⟨0,0⟩,⟨-5012017147940,-4674920780834⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42
theorem centerAccepted42 : StepValid centerStep42.shape centerBoxes42 centerStep42.proposed := by
  dsimp only [StepValid,centerStep42]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep43 : Instruction 40 := ⟨.mul 17 17,⟨⟨544678940067,544740208026⟩,⟨0,0⟩,⟨225529533990,227631224564⟩,⟨0,0⟩,⟨0,0⟩,⟨1456525281207,1549427796457⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43
theorem centerAccepted43 : StepValid centerStep43.shape centerBoxes43 centerStep43.proposed := by
  dsimp only [StepValid,centerStep43]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep44 : Instruction 40 := ⟨.mul 18 0,⟨⟨383363677286,383428362835⟩,⟨0,0⟩,⟨238103105684,240335484178⟩,⟨0,0⟩,⟨0,0⟩,⟨1587022940382,1686117091674⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44
theorem centerAccepted44 : StepValid centerStep44.shape centerBoxes44 centerStep44.proposed := by
  dsimp only [StepValid,centerStep44]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep45 : Instruction 40 := ⟨.mul 2 0,⟨⟨493792489422,494009670502⟩,⟨0,0⟩,⟨16107551108,21814615515⟩,⟨0,0⟩,⟨0,0⟩,⟨-67929530425,184862813446⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45
theorem centerAccepted45 : StepValid centerStep45.shape centerBoxes45 centerStep45.proposed := by
  dsimp only [StepValid,centerStep45]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep46 : Instruction 40 := ⟨.inv 0,⟨⟨2447170352730,2448246673476⟩,⟨0,0⟩,⟨-108157902382,-79791801416⟩,⟨0,0⟩,⟨0,0⟩,⟨-911355289395,346354180489⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46
theorem centerAccepted46 : StepValid centerStep46.shape centerBoxes46 centerStep46.proposed := by
  dsimp only [StepValid,centerStep46]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep47 : Instruction 40 := ⟨.mul 7 0,⟨⟨2315167984376,2317483632632⟩,⟨0,0⟩,⟨-601738132423,-534952568863⟩,⟨0,0⟩,⟨0,0⟩,⟨-4530493416734,-1628216086574⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47
theorem centerAccepted47 : StepValid centerStep47.shape centerBoxes47 centerStep47.proposed := by
  dsimp only [StepValid,centerStep47]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep48 : Instruction 40 := ⟨.neg 11,⟨⟨-161332611040,-161033726144⟩,⟨0,0⟩,⟨-1110508891478,-1101132865739⟩,⟨0,0⟩,⟨0,0⟩,⟨168585790702,578814977488⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48
theorem centerAccepted48 : StepValid centerStep48.shape centerBoxes48 centerStep48.proposed := by
  dsimp only [StepValid,centerStep48]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep49 : Instruction 40 := ⟨.mul 0 10,⟨⟨-223703852372,-223264196588⟩,⟨0,0⟩,⟨-1541261761613,-1527229363721⟩,⟨0,0⟩,⟨0,0⟩,⟨175254745529,793646335907⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49
theorem centerAccepted49 : StepValid centerStep49.shape centerBoxes49 centerStep49.proposed := by
  dsimp only [StepValid,centerStep49]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep50 : Instruction 40 := ⟨.mul 53 43,⟨⟨319784222720,320369328128⟩,⟨0,0⟩,⟨2156866112806,2172695728386⟩,⟨0,0⟩,⟨0,0⟩,⟨-1689977450676,-1040809239446⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50
theorem centerAccepted50 : StepValid centerStep50.shape centerBoxes50 centerStep50.proposed := by
  dsimp only [StepValid,centerStep50]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep51 : Instruction 40 := ⟨.inv 29,⟨⟨1123265635545,1123354526612⟩,⟨0,0⟩,⟨327352521103,330410655790⟩,⟨0,0⟩,⟨0,0⟩,⟨2141751605286,2277169889509⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51
theorem centerAccepted51 : StepValid centerStep51.shape centerBoxes51 centerStep51.proposed := by
  dsimp only [StepValid,centerStep51]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep52 : Instruction 40 := ⟨.mul 1 0,⟨⟨326692887184,327316533859⟩,⟨0,0⟩,⟨2298671239716,2316083756556⟩,⟨0,0⟩,⟨0,0⟩,⟨180594427258,906032961763⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52
theorem centerAccepted52 : StepValid centerStep52.shape centerBoxes52 centerStep52.proposed := by
  dsimp only [StepValid,centerStep52]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep53 : Instruction 40 := ⟨.neg 2,⟨⟨-320369328128,-319784222720⟩,⟨0,0⟩,⟨-2172695728386,-2156866112806⟩,⟨0,0⟩,⟨0,0⟩,⟨1040809239446,1689977450676⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53
theorem centerAccepted53 : StepValid centerStep53.shape centerBoxes53 centerStep53.proposed := by
  dsimp only [StepValid,centerStep53]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep54 : Instruction 40 := ⟨.add 1 0,⟨⟨6323559056,7532311139⟩,⟨0,0⟩,⟨125975511330,159217643750⟩,⟨0,0⟩,⟨0,0⟩,⟨1221403666704,2596010412439⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54
theorem centerAccepted54 : StepValid centerStep54.shape centerBoxes54 centerStep54.proposed := by
  dsimp only [StepValid,centerStep54]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep55 : Instruction 40 := ⟨.mul 36 0,⟨⟨4314968630,5142075550⟩,⟨0,0⟩,⟨84840027792,107809018611⟩,⟨0,0⟩,⟨0,0⟩,⟨777829056843,1732524880235⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55
theorem centerAccepted55 : StepValid centerStep55.shape centerBoxes55 centerStep55.proposed := by
  dsimp only [StepValid,centerStep55]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep56 : Instruction 40 := ⟨.add 6 0,⟨⟨-219388883742,-218122121038⟩,⟨0,0⟩,⟨-1456421733821,-1419420345110⟩,⟨0,0⟩,⟨0,0⟩,⟨953083802372,2526171216142⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56
theorem centerAccepted56 : StepValid centerStep56.shape centerBoxes56 centerStep56.proposed := by
  dsimp only [StepValid,centerStep56]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep57 : Instruction 40 := ⟨.mul 0 10,⟨⟨-488506070560,-485471889877⟩,⟨0,0⟩,⟨-3227137593094,-3137606422699⟩,⟨0,0⟩,⟨0,0⟩,⟨2258173827067,6093322131721⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57
theorem centerAccepted57 : StepValid centerStep57.shape centerBoxes57 centerStep57.proposed := by
  dsimp only [StepValid,centerStep57]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep58 : Instruction 40 := ⟨.mul 54 51,⟨⟨639568445440,640738656256⟩,⟨0,0⟩,⟨4313732225612,4345391456772⟩,⟨0,0⟩,⟨0,0⟩,⟨-3379954901352,-2081618478892⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58
theorem centerAccepted58 : StepValid centerStep58.shape centerBoxes58 centerStep58.proposed := by
  dsimp only [StepValid,centerStep58]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep59 : Instruction 40 := ⟨.mul 0 7,⟨⟨653385774368,654633067717⟩,⟨0,0⟩,⟨4597342479433,4632167513110⟩,⟨0,0⟩,⟨0,0⟩,⟨361188854518,1812065923523⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59
theorem centerAccepted59 : StepValid centerStep59.shape centerBoxes59 centerStep59.proposed := by
  dsimp only [StepValid,centerStep59]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep60 : Instruction 40 := ⟨.mul 57 53,⟨⟨479676334080,480553992192⟩,⟨0,0⟩,⟨3235299169209,3259043592579⟩,⟨0,0⟩,⟨0,0⟩,⟨-2534966176014,-1561213859169⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60
theorem centerAccepted60 : StepValid centerStep60.shape centerBoxes60 centerStep60.proposed := by
  dsimp only [StepValid,centerStep60]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep61 : Instruction 40 := ⟨.mul 39 35,⟨⟨757448643252,757551187725⟩,⟨0,0⟩,⟨-65985378684,-62480800688⟩,⟨0,0⟩,⟨0,0⟩,⟨-517279644312,-362794315815⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61
theorem centerAccepted61 : StepValid centerStep61.shape centerBoxes61 centerStep61.proposed := by
  dsimp only [StepValid,centerStep61]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep62 : Instruction 40 := ⟨.inv 0,⟨⟨1595833838298,1596049884550⟩,⟨0,0⟩,⟨131620117026,139040391674⟩,⟨0,0⟩,⟨0,0⟩,⟨785962606571,1114205418279⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62
theorem centerAccepted62 : StepValid centerStep62.shape centerBoxes62 centerStep62.proposed := by
  dsimp only [StepValid,centerStep62]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep63 : Instruction 40 := ⟨.mul 2 0,⟨⟨696203392504,697571653071⟩,⟨0,0⟩,⟨4753142044562,4791593314599⟩,⟨0,0⟩,⟨0,0⟩,⟨-2562286590722,-954719005871⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63
theorem centerAccepted63 : StepValid centerStep63.shape centerBoxes63 centerStep63.proposed := by
  dsimp only [StepValid,centerStep63]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep64 : Instruction 40 := ⟨.neg 0,⟨⟨-697571653071,-696203392504⟩,⟨0,0⟩,⟨-4791593314599,-4753142044562⟩,⟨0,0⟩,⟨0,0⟩,⟨954719005871,2562286590722⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64
theorem centerAccepted64 : StepValid centerStep64.shape centerBoxes64 centerStep64.proposed := by
  dsimp only [StepValid,centerStep64]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep65 : Instruction 40 := ⟨.add 5 0,⟨⟨-44185878703,-41570324787⟩,⟨0,0⟩,⟨-194250835166,-120974531452⟩,⟨0,0⟩,⟨0,0⟩,⟨1315907860389,4374352514245⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65
theorem centerAccepted65 : StepValid centerStep65.shape centerBoxes65 centerStep65.proposed := by
  dsimp only [StepValid,centerStep65]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep66 : Instruction 40 := ⟨.mul 18 0,⟨⟨-93132303562,-87531848336⟩,⟨0,0⟩,⟨-389204596186,-230546023896⟩,⟨0,0⟩,⟨0,0⟩,⟨2950095670745,9614678180925⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66
theorem centerAccepted66 : StepValid centerStep66.shape centerBoxes66 centerStep66.proposed := by
  dsimp only [StepValid,centerStep66]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep67 : Instruction 40 := ⟨.add 9 0,⟨⟨-581638374122,-573003738213⟩,⟨0,0⟩,⟨-3616342189280,-3368152446595⟩,⟨0,0⟩,⟨0,0⟩,⟨5208269497812,15708000312646⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67
theorem centerAccepted67 : StepValid centerStep67.shape centerBoxes67 centerStep67.proposed := by
  dsimp only [StepValid,centerStep67]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep68 : Instruction 40 := ⟨.mul 61 29,⟨⟨221681411952,222112108712⟩,⟨0,0⟩,⟨1495753310512,1507749899773⟩,⟨0,0⟩,⟨0,0⟩,⟨-1162891864441,-663736042881⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68
theorem centerAccepted68 : StepValid centerStep68.shape centerBoxes68 centerStep68.proposed := by
  dsimp only [StepValid,centerStep68]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep69 : Instruction 40 := ⟨.mul 27 25,⟨⟨521802982951,521944277374⟩,⟨0,0⟩,⟨-90955622817,-86055964914⟩,⟨0,0⟩,⟨0,0⟩,⟨-707885661195,-489746899428⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69
theorem centerAccepted69 : StepValid centerStep69.shape centerBoxes69 centerStep69.proposed := by
  dsimp only [StepValid,centerStep69]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨2316197096166,2316824278731⟩,⟨0,0⟩,⟨381884780966,403846283205⟩,⟨0,0⟩,⟨0,0⟩,⟨2299244047606,3283827273572⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70
theorem centerAccepted70 : StepValid centerStep70.shape centerBoxes70 centerStep70.proposed := by
  dsimp only [StepValid,centerStep70]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep71 : Instruction 40 := ⟨.mul 2 0,⟨⟨466987187462,468021176916⟩,⟨0,0⟩,⟨3227902408830,3258620130152⟩,⟨0,0⟩,⟨0,0⟩,⟨-947789510477,372740661342⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71
theorem centerAccepted71 : StepValid centerStep71.shape centerBoxes71 centerStep71.proposed := by
  dsimp only [StepValid,centerStep71]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep72 : Instruction 40 := ⟨.mul 65 39,⟨⟨47128055496,47301553246⟩,⟨0,0⟩,⟨317867169922,320791891294⟩,⟨0,0⟩,⟨0,0⟩,⟨-249520011276,-153388791917⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72
theorem centerAccepted72 : StepValid centerStep72.shape centerBoxes72 centerStep72.proposed := by
  dsimp only [StepValid,centerStep72]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep73 : Instruction 40 := ⟨.add 54 0,⟨⟨797395134682,797904091256⟩,⟨0,0⟩,⟨154214626531,167097121426⟩,⟨0,0⟩,⟨0,0⟩,⟨-1448902807878,-930988646649⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73
theorem centerAccepted73 : StepValid centerStep73.shape centerBoxes73 centerStep73.proposed := by
  dsimp only [StepValid,centerStep73]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep74 : Instruction 40 := ⟨.mul 0 0,⟨⟨578292202421,579030655757⟩,⟨0,0⟩,⟨223681114024,242521267544⟩,⟨0,0⟩,⟨0,0⟩,⟨-2059647753782,-1299566737166⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74
theorem centerAccepted74 : StepValid centerStep74.shape centerBoxes74 centerStep74.proposed := by
  dsimp only [StepValid,centerStep74]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep75 : Instruction 40 := ⟨.mul 7 0,⟨⟨-306305491160,-301373432891⟩,⟨0,0⟩,⟨-2032750367149,-1888062261908⟩,⟨0,0⟩,⟨0,0⟩,⟨1821243544245,7991365882411⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75
theorem centerAccepted75 : StepValid centerStep75.shape centerBoxes75 centerStep75.proposed := by
  dsimp only [StepValid,centerStep75]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep76 : Instruction 40 := ⟨.mul 79 28,⟨⟨4630335968752,4634967265264⟩,⟨0,0⟩,⟨-1203476264846,-1069905137726⟩,⟨0,0⟩,⟨0,0⟩,⟨-9060986833468,-3256432173148⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76
theorem centerAccepted76 : StepValid centerStep76.shape centerBoxes76 centerStep76.proposed := by
  dsimp only [StepValid,centerStep76]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep77 : Instruction 40 := ⟨.mul 0 3,⟨⟨3358043043977,3363547278961⟩,⟨0,0⟩,⟨-223911323080,-71529451328⟩,⟨0,0⟩,⟨0,0⟩,⟨-13049075632286,-6582416454733⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77
theorem centerAccepted77 : StepValid centerStep77.shape centerBoxes77 centerStep77.proposed := by
  dsimp only [StepValid,centerStep77]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep78 : Instruction 40 := ⟨.add 45 29,⟨⟨162747448768,163645344160⟩,⟨0,0⟩,⟨-1110508891478,-1101132865739⟩,⟨0,0⟩,⟨0,0⟩,⟨168585790702,578814977488⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78
theorem centerAccepted78 : StepValid centerStep78.shape centerBoxes78 centerStep78.proposed := by
  dsimp only [StepValid,centerStep78]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep79 : Instruction 40 := ⟨.mul 1 0,⟨⟨497050621798,500612124656⟩,⟨0,0⟩,⟨-3430515067267,-3373582145290⟩,⟨0,0⟩,⟨0,0⟩,⟨-1284002129601,1248655360708⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79
theorem centerAccepted79 : StepValid centerStep79.shape centerBoxes79 centerStep79.proposed := by
  dsimp only [StepValid,centerStep79]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep80 : Instruction 40 := ⟨.add 4 0,⟨⟨190745130638,199238691765⟩,⟨0,0⟩,⟨-5463265434416,-5261644407198⟩,⟨0,0⟩,⟨0,0⟩,⟨537241414644,9240021243119⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80
theorem centerAccepted80 : StepValid centerStep80.shape centerBoxes80 centerStep80.proposed := by
  dsimp only [StepValid,centerStep80]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep81 : Instruction 40 := ⟨.mul 81 81,⟨⟨90250388308,90565673269⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81
theorem centerAccepted81 : StepValid centerStep81.shape centerBoxes81 centerStep81.proposed := by
  dsimp only [StepValid,centerStep81]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep82 : Instruction 40 := ⟨.neg 0,⟨⟨-90565673269,-90250388308⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82
theorem centerAccepted82 : StepValid centerStep82.shape centerBoxes82 centerStep82.proposed := by
  dsimp only [StepValid,centerStep82]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep83 : Instruction 40 := ⟨.add 81 0,⟨⟨1008945954507,1009261239468⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83
theorem centerAccepted83 : StepValid centerStep83.shape centerBoxes83 centerStep83.proposed := by
  dsimp only [StepValid,centerStep83]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep84 : Instruction 40 := ⟨.inv 0,⟨⟨1197832406852,1198206716836⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes85 := centerStep84.proposed :: centerBoxes84
theorem centerAccepted84 : StepValid centerStep84.shape centerBoxes84 centerStep84.proposed := by
  dsimp only [StepValid,centerStep84]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep85 : Instruction 40 := ⟨.mul 13 0,⟨⟨508746222045,510032002969⟩,⟨0,0⟩,⟨3516548632844,3551122542891⟩,⟨0,0⟩,⟨0,0⟩,⟨-1032865618618,406198854815⟩⟩⟩
noncomputable def centerBoxes86 := centerStep85.proposed :: centerBoxes85
theorem centerAccepted85 : StepValid centerStep85.shape centerBoxes85 centerStep85.proposed := by
  dsimp only [StepValid,centerStep85]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep86 : Instruction 40 := ⟨.add 5 0,⟨⟨699491352683,709270694734⟩,⟨0,0⟩,⟨-1946716801572,-1710521864307⟩,⟨0,0⟩,⟨0,0⟩,⟨-495624203974,9646220097934⟩⟩⟩
noncomputable def centerBoxes87 := centerStep86.proposed :: centerBoxes86
theorem centerAccepted86 : StepValid centerStep86.shape centerBoxes86 centerStep86.proposed := by
  dsimp only [StepValid,centerStep86]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep87 : Instruction 40 := ⟨.mul 0 68,⟨⟨477307670820,484197138216⟩,⟨0,0⟩,⟨-1434531918853,-1264976531721⟩,⟨0,0⟩,⟨0,0⟩,⟨-633833520827,6669982417552⟩⟩⟩
noncomputable def centerBoxes88 := centerStep87.proposed :: centerBoxes87
theorem centerAccepted87 : StepValid centerStep87.shape centerBoxes87 centerStep87.proposed := by
  dsimp only [StepValid,centerStep87]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep88 : Instruction 40 := ⟨.mul 0 69,⟨⟨325697539719,330546391381⟩,⟨0,0⟩,⟨-1051378960547,-929894613651⟩,⟨0,0⟩,⟨0,0⟩,⟨-607227969602,4642862177023⟩⟩⟩
noncomputable def centerBoxes89 := centerStep88.proposed :: centerBoxes88
theorem centerAccepted88 : StepValid centerStep88.shape centerBoxes88 centerStep88.proposed := by
  dsimp only [StepValid,centerStep88]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep89 : Instruction 40 := ⟨.mul 90 63,⟨⟨520244806535,520332725634⟩,⟨0,0⟩,⟨107706173443,108716020748⟩,⟨0,0⟩,⟨0,0⟩,⟨673294610894,717287631845⟩⟩⟩
noncomputable def centerBoxes90 := centerStep89.proposed :: centerBoxes89
theorem centerAccepted89 : StepValid centerStep89.shape centerBoxes89 centerStep89.proposed := by
  dsimp only [StepValid,centerStep89]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep90 : Instruction 40 := ⟨.inv 0,⟨⟨2323370720420,2323763359920⟩,⟨0,0⟩,⟨-485598899744,-480925679777⟩,⟨0,0⟩,⟨0,0⟩,⟨-3004790961772,-2803418485559⟩⟩⟩
noncomputable def centerBoxes91 := centerStep90.proposed :: centerBoxes90
theorem centerAccepted90 : StepValid centerStep90.shape centerBoxes90 centerStep90.proposed := by
  dsimp only [StepValid,centerStep90]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep91 : Instruction 40 := ⟨.mul 2 0,⟨⟨688229308703,698593424245⟩,⟨0,0⟩,⟨-2368023042327,-2107414028726⟩,⟨0,0⟩,⟨0,0⟩,⟨-1373206503347,9910712325553⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91
theorem centerAccepted91 : StepValid centerStep91.shape centerBoxes91 centerStep91.proposed := by
  dsimp only [StepValid,centerStep91]
  exact ⟨by decide,by decide⟩
noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91]
theorem centerAccepted : Accepted centerProgram centerInitial :=
  ⟨centerAccepted0,⟨centerAccepted1,⟨centerAccepted2,⟨centerAccepted3,⟨centerAccepted4,⟨centerAccepted5,⟨centerAccepted6,⟨centerAccepted7,⟨centerAccepted8,⟨centerAccepted9,⟨centerAccepted10,⟨centerAccepted11,⟨centerAccepted12,⟨centerAccepted13,⟨centerAccepted14,⟨centerAccepted15,⟨centerAccepted16,⟨centerAccepted17,⟨centerAccepted18,⟨centerAccepted19,⟨centerAccepted20,⟨centerAccepted21,⟨centerAccepted22,⟨centerAccepted23,⟨centerAccepted24,⟨centerAccepted25,⟨centerAccepted26,⟨centerAccepted27,⟨centerAccepted28,⟨centerAccepted29,⟨centerAccepted30,⟨centerAccepted31,⟨centerAccepted32,⟨centerAccepted33,⟨centerAccepted34,⟨centerAccepted35,⟨centerAccepted36,⟨centerAccepted37,⟨centerAccepted38,⟨centerAccepted39,⟨centerAccepted40,⟨centerAccepted41,⟨centerAccepted42,⟨centerAccepted43,⟨centerAccepted44,⟨centerAccepted45,⟨centerAccepted46,⟨centerAccepted47,⟨centerAccepted48,⟨centerAccepted49,⟨centerAccepted50,⟨centerAccepted51,⟨centerAccepted52,⟨centerAccepted53,⟨centerAccepted54,⟨centerAccepted55,⟨centerAccepted56,⟨centerAccepted57,⟨centerAccepted58,⟨centerAccepted59,⟨centerAccepted60,⟨centerAccepted61,⟨centerAccepted62,⟨centerAccepted63,⟨centerAccepted64,⟨centerAccepted65,⟨centerAccepted66,⟨centerAccepted67,⟨centerAccepted68,⟨centerAccepted69,⟨centerAccepted70,⟨centerAccepted71,⟨centerAccepted72,⟨centerAccepted73,⟨centerAccepted74,⟨centerAccepted75,⟨centerAccepted76,⟨centerAccepted77,⟨centerAccepted78,⟨centerAccepted79,⟨centerAccepted80,⟨centerAccepted81,⟨centerAccepted82,⟨centerAccepted83,⟨centerAccepted84,⟨centerAccepted85,⟨centerAccepted86,⟨centerAccepted87,⟨centerAccepted88,⟨centerAccepted89,⟨centerAccepted90,⟨centerAccepted91,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
noncomputable def center_output : DyadicBivariateJetEnclosure 40 := ⟨⟨688229308703,698593424245⟩,⟨0,0⟩,⟨-2368023042327,-2107414028726⟩,⟨0,0⟩,⟨0,0⟩,⟨-1373206503347,9910712325553⟩⟩
theorem center_output_eq : (finalBoxes centerProgram centerInitial).getD 0 (zeroBox 40)=center_output := rfl
noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨315010081357,315559837172⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨739158158656,739241497705⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨155927241493,159357717772⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
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
noncomputable def wholeStep4 : Instruction 40 := ⟨.inv 6,⟨⟨7586239540304,7753140554782⟩,⟨0,0⟩,⟨-54670807423650,-52342357196604⟩,⟨0,0⟩,⟨0,0⟩,⟨722287331514222,771015864664110⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4
theorem wholeAccepted4 : StepValid wholeStep4.shape wholeBoxes4 wholeStep4.proposed := by
  dsimp only [StepValid,wholeStep4]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep5 : Instruction 40 := ⟨.mul 6 0,⟨⟨5099928648391,5212717256322⟩,⟨0,0⟩,⟨-36757164307893,-35187695507517⟩,⟨0,0⟩,⟨0,0⟩,⟨485565191395479,518381896243784⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5
theorem wholeAccepted5 : StepValid wholeStep5.shape wholeBoxes5 wholeStep5.proposed := by
  dsimp only [StepValid,wholeStep5]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep6 : Instruction 40 := ⟨.contact 0,⟨⟨158338121728,161737605120⟩,⟨0,0⟩,⟨1036422893135,1130375945738⟩,⟨0,0⟩,⟨0,0⟩,⟨-2601043014784,1275723354639⟩⟩⟩
noncomputable def wholeBoxes7 := wholeStep6.proposed :: wholeBoxes6
theorem wholeAccepted6 : StepValid wholeStep6.shape wholeBoxes6 wholeStep6.proposed := by
  dsimp only [StepValid,wholeStep6]
  exact ⟨by decide,by decide,(⟨⟨158338121728,161737605120⟩,⟨-33812768735,-32385156398⟩,⟨13025384789,13938525549⟩⟩ : DyadicJetEnclosure 40),brwhole6_jet,by decide⟩
noncomputable def wholeStep7 : Instruction 40 := ⟨.log 10,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes8 := wholeStep7.proposed :: wholeBoxes7
theorem wholeAccepted7 : StepValid wholeStep7.shape wholeBoxes7 wholeStep7.proposed := by
  dsimp only [StepValid,wholeStep7]
  exact ⟨by decide,by decide,lc0,by decide⟩
noncomputable def wholeStep8 : Instruction 40 := ⟨.add 6 1,⟨⟨1257849749504,1261249232896⟩,⟨0,0⟩,⟨1036422893135,1130375945738⟩,⟨0,0⟩,⟨0,0⟩,⟨-2601043014784,1275723354639⟩⟩⟩
noncomputable def wholeBoxes9 := wholeStep8.proposed :: wholeBoxes8
theorem wholeAccepted8 : StepValid wholeStep8.shape wholeBoxes8 wholeStep8.proposed := by
  dsimp only [StepValid,wholeStep8]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep9 : Instruction 40 := ⟨.log 0,⟨⟨147925665088,150893213312⟩,⟨0,0⟩,⟨903516127163,988084225949⟩,⟨0,0⟩,⟨0,0⟩,⟨-3161572900140,372677132663⟩⟩⟩
noncomputable def wholeBoxes10 := wholeStep9.proposed :: wholeBoxes9
theorem wholeAccepted9 : StepValid wholeStep9.shape wholeBoxes9 wholeStep9.proposed := by
  dsimp only [StepValid,wholeStep9]
  exact ⟨by decide,by decide,lc23,by decide⟩
noncomputable def wholeStep10 : Instruction 40 := ⟨.mul 1 0,⟨⟨169228097344,173089528780⟩,⟨0,0⟩,⟨1173067248604,1288559843232⟩,⟨0,0⟩,⟨0,0⟩,⟨-2280250133930,2634215003783⟩⟩⟩
noncomputable def wholeBoxes11 := wholeStep10.proposed :: wholeBoxes10
theorem wholeAccepted10 : StepValid wholeStep10.shape wholeBoxes10 wholeStep10.proposed := by
  dsimp only [StepValid,wholeStep10]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep11 : Instruction 40 := ⟨.neg 4,⟨⟨-161737605120,-158338121728⟩,⟨0,0⟩,⟨-1130375945738,-1036422893135⟩,⟨0,0⟩,⟨0,0⟩,⟨-1275723354639,2601043014784⟩⟩⟩
noncomputable def wholeBoxes12 := wholeStep11.proposed :: wholeBoxes11
theorem wholeAccepted11 : StepValid wholeStep11.shape wholeBoxes11 wholeStep11.proposed := by
  dsimp only [StepValid,wholeStep11]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep12 : Instruction 40 := ⟨.add 10 0,⟨⟨937774022656,941173506048⟩,⟨0,0⟩,⟨-1130375945738,-1036422893135⟩,⟨0,0⟩,⟨0,0⟩,⟨-1275723354639,2601043014784⟩⟩⟩
noncomputable def wholeBoxes13 := wholeStep12.proposed :: wholeBoxes12
theorem wholeAccepted12 : StepValid wholeStep12.shape wholeBoxes12 wholeStep12.proposed := by
  dsimp only [StepValid,wholeStep12]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep13 : Instruction 40 := ⟨.log 0,⟨⟨-174945911424,-170967326976⟩,⟨0,0⟩,⟨-1325331546909,-1210785274948⟩,⟨0,0⟩,⟨0,0⟩,⟨-3093277797130,1716323999403⟩⟩⟩
noncomputable def wholeBoxes14 := wholeStep13.proposed :: wholeBoxes13
theorem wholeAccepted13 : StepValid wholeStep13.shape wholeBoxes13 wholeStep13.proposed := by
  dsimp only [StepValid,wholeStep13]
  exact ⟨by decide,by decide,lc24,by decide⟩
noncomputable def wholeStep14 : Instruction 40 := ⟨.mul 1 0,⟨⟨-149752356105,-145818119527⟩,⟨0,0⟩,⟨-973316206933,-852822566031⟩,⟨0,0⟩,⟨0,0⟩,⟨-779056604304,4397213217584⟩⟩⟩
noncomputable def wholeBoxes15 := wholeStep14.proposed :: wholeBoxes14
theorem wholeAccepted14 : StepValid wholeStep14.shape wholeBoxes14 wholeStep14.proposed := by
  dsimp only [StepValid,wholeStep14]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep15 : Instruction 40 := ⟨.add 4 0,⟨⟨19475741239,27271409253⟩,⟨0,0⟩,⟨199751041671,435737277201⟩,⟨0,0⟩,⟨0,0⟩,⟨-3059306738234,7031428221367⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15
theorem wholeAccepted15 : StepValid wholeStep15.shape wholeBoxes15 wholeStep15.proposed := by
  dsimp only [StepValid,wholeStep15]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 0 15,⟨⟨9737870619,13635704627⟩,⟨0,0⟩,⟨99875520835,217868638601⟩,⟨0,0⟩,⟨0,0⟩,⟨-1529653369117,3515714110684⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16
theorem wholeAccepted16 : StepValid wholeStep16.shape wholeBoxes16 wholeStep16.proposed := by
  dsimp only [StepValid,wholeStep16]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨-13635704627,-9737870619⟩,⟨0,0⟩,⟨-217868638601,-99875520835⟩,⟨0,0⟩,⟨0,0⟩,⟨-3515714110684,1529653369117⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17
theorem wholeAccepted17 : StepValid wholeStep17.shape wholeBoxes17 wholeStep17.proposed := by
  dsimp only [StepValid,wholeStep17]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep18 : Instruction 40 := ⟨.add 10 0,⟨⟨748487678989,752385532261⟩,⟨0,0⟩,⟨-217868638601,-99875520835⟩,⟨0,0⟩,⟨0,0⟩,⟨-3515714110684,1529653369117⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18
theorem wholeAccepted18 : StepValid wholeStep18.shape wholeBoxes18 wholeStep18.proposed := by
  dsimp only [StepValid,wholeStep18]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep19 : Instruction 40 := ⟨.mul 12 12,⟨⟨22801906009,23791520025⟩,⟨0,0⟩,⟨298505718482,332555461408⟩,⟨0,0⟩,⟨0,0⟩,⟨1188684010027,2699529830132⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19
theorem wholeAccepted19 : StepValid wholeStep19.shape wholeBoxes19 wholeStep19.proposed := by
  dsimp only [StepValid,wholeStep19]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep20 : Instruction 40 := ⟨.neg 0,⟨⟨-23791520025,-22801906009⟩,⟨0,0⟩,⟨-332555461408,-298505718482⟩,⟨0,0⟩,⟨0,0⟩,⟨-2699529830132,-1188684010027⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20
theorem wholeAccepted20 : StepValid wholeStep20.shape wholeBoxes20 wholeStep20.proposed := by
  dsimp only [StepValid,wholeStep20]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep21 : Instruction 40 := ⟨.add 19 0,⟨⟨1075720107751,1076709721767⟩,⟨0,0⟩,⟨-332555461408,-298505718482⟩,⟨0,0⟩,⟨0,0⟩,⟨-2699529830132,-1188684010027⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21
theorem wholeAccepted21 : StepValid wholeStep21.shape wholeBoxes21 wholeStep21.proposed := by
  dsimp only [StepValid,wholeStep21]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep22 : Instruction 40 := ⟨.log 0,⟨⟨-24052698112,-23041661888⟩,⟨0,0⟩,⟨-339910534408,-304827291695⟩,⟨0,0⟩,⟨0,0⟩,⟨-2864317139903,-1298367194271⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22
theorem wholeAccepted22 : StepValid wholeStep22.shape wholeBoxes22 wholeStep22.proposed := by
  dsimp only [StepValid,wholeStep22]
  exact ⟨by decide,by decide,lc21,by decide⟩
noncomputable def wholeStep23 : Instruction 40 := ⟨.mul 0 22,⟨⟨-12026349056,-11520830944⟩,⟨0,0⟩,⟨-169955267204,-152413645847⟩,⟨0,0⟩,⟨0,0⟩,⟨-1432158569952,-649183597135⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23
theorem wholeAccepted23 : StepValid wholeStep23.shape wholeBoxes23 wholeStep23.proposed := by
  dsimp only [StepValid,wholeStep23]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep24 : Instruction 40 := ⟨.neg 0,⟨⟨11520830944,12026349056⟩,⟨0,0⟩,⟨152413645847,169955267204⟩,⟨0,0⟩,⟨0,0⟩,⟨649183597135,1432158569952⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24
theorem wholeAccepted24 : StepValid wholeStep24.shape wholeBoxes24 wholeStep24.proposed := by
  dsimp only [StepValid,wholeStep24]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep25 : Instruction 40 := ⟨.add 17 0,⟨⟨773644214560,774149751936⟩,⟨0,0⟩,⟨152413645847,169955267204⟩,⟨0,0⟩,⟨0,0⟩,⟨649183597135,1432158569952⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25
theorem wholeAccepted25 : StepValid wholeStep25.shape wholeBoxes25 wholeStep25.proposed := by
  dsimp only [StepValid,wholeStep25]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep26 : Instruction 40 := ⟨.add 24 26,⟨⟨1414521709133,1415071464948⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26
theorem wholeAccepted26 : StepValid wholeStep26.shape wholeBoxes26 wholeStep26.proposed := by
  dsimp only [StepValid,wholeStep26]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep27 : Instruction 40 := ⟨.neg 27,⟨⟨-315559837172,-315010081357⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27
theorem wholeAccepted27 : StepValid wholeStep27.shape wholeBoxes27 wholeStep27.proposed := by
  dsimp only [StepValid,wholeStep27]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep28 : Instruction 40 := ⟨.add 26 0,⟨⟨783951790604,784501546419⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28
theorem wholeAccepted28 : StepValid wholeStep28.shape wholeBoxes28 wholeStep28.proposed := by
  dsimp only [StepValid,wholeStep28]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep29 : Instruction 40 := ⟨.inv 0,⟨⟨1541011391415,1542092044568⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29
theorem wholeAccepted29 : StepValid wholeStep29.shape wholeBoxes29 wholeStep29.proposed := by
  dsimp only [StepValid,wholeStep29]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep30 : Instruction 40 := ⟨.mul 3 0,⟨⟨1982511155054,1984672461360⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30
theorem wholeAccepted30 : StepValid wholeStep30.shape wholeBoxes30 wholeStep30.proposed := by
  dsimp only [StepValid,wholeStep30]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨648160119616,649358140608⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31
theorem wholeAccepted31 : StepValid wholeStep31.shape wholeBoxes31 wholeStep31.proposed := by
  dsimp only [StepValid,wholeStep31]
  exact ⟨by decide,by decide,lc12,by decide⟩
noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 0 31,⟨⟨324080059808,324679070304⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32
theorem wholeAccepted32 : StepValid wholeStep32.shape wholeBoxes32 wholeStep32.proposed := by
  dsimp only [StepValid,wholeStep32]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep33 : Instruction 40 := ⟨.inv 20,⟨⟨1284487729250,1289144069262⟩,⟨0,0⟩,⟨1414481474445,1553911082287⟩,⟨0,0⟩,⟨0,0⟩,⟨-460353435912,5499830972620⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33
theorem wholeAccepted33 : StepValid wholeStep33.shape wholeBoxes33 wholeStep33.proposed := by
  dsimp only [StepValid,wholeStep33]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep34 : Instruction 40 := ⟨.mul 25 0,⟨⟨1469463830724,1478776510748⟩,⟨0,0⟩,⟨2828962948891,3107822164573⟩,⟨0,0⟩,⟨0,0⟩,⟨-911075067279,10999661945238⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34
theorem wholeAccepted34 : StepValid wholeStep34.shape wholeBoxes34 wholeStep34.proposed := by
  dsimp only [StepValid,wholeStep34]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨318892992128,325839124672⟩,⟨0,0⟩,⟨2103412945934,2325396879844⟩,⟨0,0⟩,⟨0,0⟩,⟨-5599768720279,4206467871789⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35
theorem wholeAccepted35 : StepValid wholeStep35.shape wholeBoxes35 wholeStep35.proposed := by
  dsimp only [StepValid,wholeStep35]
  exact ⟨by decide,by decide,lc27,by decide⟩
noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 0 35,⟨⟨159446496064,162919562336⟩,⟨0,0⟩,⟨1051706472967,1162698439922⟩,⟨0,0⟩,⟨0,0⟩,⟨-2799884360140,2103233935895⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36
theorem wholeAccepted36 : StepValid wholeStep36.shape wholeBoxes36 wholeStep36.proposed := by
  dsimp only [StepValid,wholeStep36]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep37 : Instruction 40 := ⟨.mul 40 11,⟨⟨1547288429120,1548299503872⟩,⟨0,0⟩,⟨304827291694,339910534408⟩,⟨0,0⟩,⟨0,0⟩,⟨1298367194270,2864317139904⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37
theorem wholeAccepted37 : StepValid wholeStep37.shape wholeBoxes37 wholeStep37.proposed := by
  dsimp only [StepValid,wholeStep37]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep38 : Instruction 40 := ⟨.add 0 17,⟨⟨1523496909095,1525497597863⟩,⟨0,0⟩,⟨-27728169714,41404815926⟩,⟨0,0⟩,⟨0,0⟩,⟨-1401162635862,1675633129877⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38
theorem wholeAccepted38 : StepValid wholeStep38.shape wholeBoxes38 wholeStep38.proposed := by
  dsimp only [StepValid,wholeStep38]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep39 : Instruction 40 := ⟨.mul 20 0,⟨⟨1037113784546,1043883750873⟩,⟨0,0⟩,⟨-321252044674,-110055828206⟩,⟨0,0⟩,⟨0,0⟩,⟨-5853025457277,3279898793718⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39
theorem wholeAccepted39 : StepValid wholeStep39.shape wholeBoxes39 wholeStep39.proposed := by
  dsimp only [StepValid,wholeStep39]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep40 : Instruction 40 := ⟨.mul 43 41,⟨⟨1478316317312,1478482995410⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40
theorem wholeAccepted40 : StepValid wholeStep40.shape wholeBoxes40 wholeStep40.proposed := by
  dsimp only [StepValid,wholeStep40]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 19 19,⟨⟨1052443394855,1054380686535⟩,⟨0,0⟩,⟨-651317711026,-584093147426⟩,⟨0,0⟩,⟨0,0⟩,⟨-5125010554070,-2124758168857⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41
theorem wholeAccepted41 : StepValid wholeStep41.shape wholeBoxes41 wholeStep41.proposed := by
  dsimp only [StepValid,wholeStep41]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep42 : Instruction 40 := ⟨.mul 1 0,⟨⟨1415032096393,1417796662037⟩,⟨0,0⟩,⟨-875808982857,-785325419810⟩,⟨0,0⟩,⟨0,0⟩,⟨-6891460503075,-2856781676531⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42
theorem wholeAccepted42 : StepValid wholeStep42.shape wholeBoxes42 wholeStep42.proposed := by
  dsimp only [StepValid,wholeStep42]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep43 : Instruction 40 := ⟨.mul 17 17,⟨⟨544355653548,545067303777⟩,⟨0,0⟩,⟨214484198894,239325941850⟩,⟨0,0⟩,⟨0,0⟩,⟨955819002321,2069264145599⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43
theorem wholeAccepted43 : StepValid wholeStep43.shape wholeBoxes43 wholeStep43.proposed := by
  dsimp only [StepValid,wholeStep43]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep44 : Instruction 40 := ⟨.mul 18 0,⟨⟨383022417764,383773765869⟩,⟨0,0⟩,⟨226374767756,252758743749⟩,⟨0,0⟩,⟨0,0⟩,⟨1053405176264,2240897214600⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44
theorem wholeAccepted44 : StepValid wholeStep44.shape wholeBoxes44 wholeStep44.proposed := by
  dsimp only [StepValid,wholeStep44]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 2 0,⟨⟨492936137356,494868040029⟩,⟨0,0⟩,⟨-14356327797,52353481953⟩,⟨0,0⟩,⟨0,0⟩,⟨-1452368788911,1571033360065⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45
theorem wholeAccepted45 : StepValid wholeStep45.shape wholeBoxes45 wholeStep45.proposed := by
  dsimp only [StepValid,wholeStep45]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep46 : Instruction 40 := ⟨.inv 0,⟨⟨2442925632343,2452499883858⟩,⟨0,0⟩,⟨-260473717951,71426883904⟩,⟨0,0⟩,⟨0,0⟩,⟨-7831517579456,7281283367782⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46
theorem wholeAccepted46 : StepValid wholeStep46.shape wholeBoxes46 wholeStep46.proposed := by
  dsimp only [StepValid,wholeStep46]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep47 : Instruction 40 := ⟨.mul 7 0,⟨⟨2304288362141,2328419921267⟩,⟨0,0⟩,⟨-963859642026,-176711946760⟩,⟨0,0⟩,⟨0,0⟩,⟨-20532416115256,14381039575475⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47
theorem wholeAccepted47 : StepValid wholeStep47.shape wholeBoxes47 wholeStep47.proposed := by
  dsimp only [StepValid,wholeStep47]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep48 : Instruction 40 := ⟨.neg 11,⟨⟨-162919562336,-159446496064⟩,⟨0,0⟩,⟨-1162698439922,-1051706472967⟩,⟨0,0⟩,⟨0,0⟩,⟨-2103233935895,2799884360140⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48
theorem wholeAccepted48 : StepValid wholeStep48.shape wholeBoxes48 wholeStep48.proposed := by
  dsimp only [StepValid,wholeStep48]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep49 : Instruction 40 := ⟨.mul 0 10,⟨⟨-226039811413,-220931036819⟩,⟨0,0⟩,⟨-1619300138946,-1453148888290⟩,⟨0,0⟩,⟨0,0⟩,⟨-3253948637278,4150908960967⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49
theorem wholeAccepted49 : StepValid wholeStep49.shape wholeBoxes49 wholeStep49.proposed := by
  dsimp only [StepValid,wholeStep49]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 53 43,⟨⟨316676243456,323475210240⟩,⟨0,0⟩,⟨2072845786270,2260751891476⟩,⟨0,0⟩,⟨0,0⟩,⟨-5202086029568,2551446709278⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50
theorem wholeAccepted50 : StepValid wholeStep50.shape wholeBoxes50 wholeStep50.proposed := by
  dsimp only [StepValid,wholeStep50]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep51 : Instruction 40 := ⟨.inv 29,⟨⟨1122796418732,1123829340834⟩,⟨0,0⟩,⟨311282739355,347428278316⟩,⟨0,0⟩,⟨0,0⟩,⟨1412162883129,3035073109485⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51
theorem wholeAccepted51 : StepValid wholeStep51.shape wholeBoxes51 wholeStep51.proposed := by
  dsimp only [StepValid,wholeStep51]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep52 : Instruction 40 := ⟨.mul 1 0,⟨⟨323382621036,330629456858⟩,⟨0,0⟩,⟨2206397470180,2412965607946⟩,⟨0,0⟩,⟨0,0⟩,⟨-3736728328818,4929515726287⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52
theorem wholeAccepted52 : StepValid wholeStep52.shape wholeBoxes52 wholeStep52.proposed := by
  dsimp only [StepValid,wholeStep52]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep53 : Instruction 40 := ⟨.neg 2,⟨⟨-323475210240,-316676243456⟩,⟨0,0⟩,⟨-2260751891476,-2072845786270⟩,⟨0,0⟩,⟨0,0⟩,⟨-2551446709278,5202086029568⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53
theorem wholeAccepted53 : StepValid wholeStep53.shape wholeBoxes53 wholeStep53.proposed := by
  dsimp only [StepValid,wholeStep53]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep54 : Instruction 40 := ⟨.add 1 0,⟨⟨-92589204,13953213402⟩,⟨0,0⟩,⟨-54354421296,340119821676⟩,⟨0,0⟩,⟨0,0⟩,⟨-6288175038096,10131601755855⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54
theorem wholeAccepted54 : StepValid wholeStep54.shape wholeBoxes54 wholeStep54.proposed := by
  dsimp only [StepValid,wholeStep54]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 36 0,⟨⟨-63357928,9548053543⟩,⟨0,0⟩,⟨-39959057001,232759162236⟩,⟨0,0⟩,⟨0,0⟩,⟨-4482344881813,6973912975052⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55
theorem wholeAccepted55 : StepValid wholeStep55.shape wholeBoxes55 wholeStep55.proposed := by
  dsimp only [StepValid,wholeStep55]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep56 : Instruction 40 := ⟨.add 6 0,⟨⟨-226103169341,-211382983276⟩,⟨0,0⟩,⟨-1659259195947,-1220389726054⟩,⟨0,0⟩,⟨0,0⟩,⟨-7736293519091,11124821936019⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56
theorem wholeAccepted56 : StepValid wholeStep56.shape wholeBoxes56 wholeStep56.proposed := by
  dsimp only [StepValid,wholeStep56]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep57 : Instruction 40 := ⟨.mul 0 10,⟨⟨-504331179899,-469656613937⟩,⟨0,0⟩,⟨-3715724988231,-2657932245771⟩,⟨0,0⟩,⟨0,0⟩,⟨-18968977775603,27210937582931⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57
theorem wholeAccepted57 : StepValid wholeStep57.shape wholeBoxes57 wholeStep57.proposed := by
  dsimp only [StepValid,wholeStep57]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 54 51,⟨⟨633352486912,646950420480⟩,⟨0,0⟩,⟨4145691572540,4521503782952⟩,⟨0,0⟩,⟨0,0⟩,⟨-10404172059136,5102893418556⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58
theorem wholeAccepted58 : StepValid wholeStep58.shape wholeBoxes58 wholeStep58.proposed := by
  dsimp only [StepValid,wholeStep58]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep59 : Instruction 40 := ⟨.mul 0 7,⟨⟨646765242072,661258913716⟩,⟨0,0⟩,⟨4412794940360,4825931215890⟩,⟨0,0⟩,⟨0,0⟩,⟨-7473456657633,9859031452573⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59
theorem wholeAccepted59 : StepValid wholeStep59.shape wholeBoxes59 wholeStep59.proposed := by
  dsimp only [StepValid,wholeStep59]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 57 53,⟨⟨475014365184,485212815360⟩,⟨0,0⟩,⟨3109268679405,3391127837214⟩,⟨0,0⟩,⟨0,0⟩,⟨-7803129044352,3827170063917⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60
theorem wholeAccepted60 : StepValid wholeStep60.shape wholeBoxes60 wholeStep60.proposed := by
  dsimp only [StepValid,wholeStep60]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 39 35,⟨⟨756903898807,758095269715⟩,⟨0,0⟩,⟨-85031665023,-43605481234⟩,⟨0,0⟩,⟨0,0⟩,⟨-1368370798344,483312631662⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61
theorem wholeAccepted61 : StepValid wholeStep61.shape wholeBoxes61 wholeStep61.proposed := by
  dsimp only [StepValid,wholeStep61]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep62 : Instruction 40 := ⟨.inv 0,⟨⟨1594688514636,1597198563147⟩,⟨0,0⟩,⟨91726149571,179431567748⟩,⟨0,0⟩,⟨0,0⟩,⟨-1009321378538,2927815019038⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62
theorem wholeAccepted62 : StepValid wholeStep62.shape wholeBoxes62 wholeStep62.proposed := by
  dsimp only [StepValid,wholeStep62]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep63 : Instruction 40 := ⟨.mul 2 0,⟨⟨688942193342,704841305846⟩,⟨0,0⟩,⟨4549189080237,5005283133140⟩,⟨0,0⟩,⟨0,0⟩,⟨-11261799661486,7958364825553⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63
theorem wholeAccepted63 : StepValid wholeStep63.shape wholeBoxes63 wholeStep63.proposed := by
  dsimp only [StepValid,wholeStep63]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep64 : Instruction 40 := ⟨.neg 0,⟨⟨-704841305846,-688942193342⟩,⟨0,0⟩,⟨-5005283133140,-4549189080237⟩,⟨0,0⟩,⟨0,0⟩,⟨-7958364825553,11261799661486⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64
theorem wholeAccepted64 : StepValid wholeStep64.shape wholeBoxes64 wholeStep64.proposed := by
  dsimp only [StepValid,wholeStep64]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep65 : Instruction 40 := ⟨.add 5 0,⟨⟨-58076063774,-27683279626⟩,⟨0,0⟩,⟨-592488192780,276742135653⟩,⟨0,0⟩,⟨0,0⟩,⟨-15431821483186,21120831114059⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65
theorem wholeAccepted65 : StepValid wholeStep65.shape wholeBoxes65 wholeStep65.proposed := by
  dsimp only [StepValid,wholeStep65]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 18 0,⟨⟨-122986842908,-58016902647⟩,⟨0,0⟩,⟨-1250254485922,636963773786⟩,⟨0,0⟩,⟨0,0⟩,⟨-33924548812154,46850579330778⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66
theorem wholeAccepted66 : StepValid wholeStep66.shape wholeBoxes66 wholeStep66.proposed := by
  dsimp only [StepValid,wholeStep66]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep67 : Instruction 40 := ⟨.add 9 0,⟨⟨-627318022807,-527673516584⟩,⟨0,0⟩,⟨-4965979474153,-2020968471985⟩,⟨0,0⟩,⟨0,0⟩,⟨-52893526587757,74061516913709⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67
theorem wholeAccepted67 : StepValid wholeStep67.shape wholeBoxes67 wholeStep67.proposed := by
  dsimp only [StepValid,wholeStep67]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 61 29,⟨⟨219395259632,224399926169⟩,⟨0,0⟩,⟨1432001578397,1574410367243⟩,⟨0,0⟩,⟨0,0⟩,⟨-3871893634122,2101598346097⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68
theorem wholeAccepted68 : StepValid wholeStep68.shape wholeBoxes68 wholeStep68.proposed := by
  dsimp only [StepValid,wholeStep68]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 27 25,⟨⟨521052708817,522694279393⟩,⟨0,0⟩,⟨-117579029598,-59675363559⟩,⟨0,0⟩,⟨0,0⟩,⟨-1909288346848,704504170436⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69
theorem wholeAccepted69 : StepValid wholeStep69.shape wholeBoxes69 wholeStep69.proposed := by
  dsimp only [StepValid,wholeStep69]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨2312873638139,2320160319979⟩,⟨0,0⟩,⟨264057941062,523559698125⟩,⟨0,0⟩,⟨0,0⟩,⟨-3076744568309,8738030274476⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70
theorem wholeAccepted70 : StepValid wholeStep70.shape wholeBoxes70 wholeStep70.proposed := by
  dsimp only [StepValid,wholeStep70]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 2 0,⟨⟨461508090971,473522781707⟩,⟨0,0⟩,⟨3064971461740,3429132647440⟩,⟨0,0⟩,⟨0,0⟩,⟨-8110484896190,7717475521350⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71
theorem wholeAccepted71 : StepValid wholeStep71.shape wholeBoxes71 wholeStep71.proposed := by
  dsimp only [StepValid,wholeStep71]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 65 39,⟨⟨46670018454,47760127258⟩,⟨0,0⟩,⟨305484712219,333793114948⟩,⟨0,0⟩,⟨0,0⟩,⟨-768072120865,376713317337⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72
theorem wholeAccepted72 : StepValid wholeStep72.shape wholeBoxes72 wholeStep72.proposed := by
  dsimp only [StepValid,wholeStep72]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep73 : Instruction 40 := ⟨.add 54 0,⟨⟨795157697443,800145659519⟩,⟨0,0⟩,⟨87616073618,233917594113⟩,⟨0,0⟩,⟨0,0⟩,⟨-4283786231549,1906366686454⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73
theorem wholeAccepted73 : StepValid wholeStep73.shape wholeBoxes73 wholeStep73.proposed := by
  dsimp only [StepValid,wholeStep73]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 0 0,⟨⟨575051457238,582288590929⟩,⟨0,0⟩,⟨126726436714,340456877194⟩,⟨0,0⟩,⟨0,0⟩,⟨-6220900801283,2874164184422⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74
theorem wholeAccepted74 : StepValid wholeStep74.shape wholeBoxes74 wholeStep74.proposed := by
  dsimp only [StepValid,wholeStep74]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep75 : Instruction 40 := ⟨.mul 7 0,⟨⟨-332220340683,-275976549035⟩,⟨0,0⟩,⟨-2824170156273,-1117797227699⟩,⟨0,0⟩,⟨0,0⟩,⟨-32726998858749,42305545548659⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75
theorem wholeAccepted75 : StepValid wholeStep75.shape wholeBoxes75 wholeStep75.proposed := by
  dsimp only [StepValid,wholeStep75]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep76 : Instruction 40 := ⟨.mul 79 28,⟨⟨4608576724282,4656839842534⟩,⟨0,0⟩,⟨-1927719284052,-353423893520⟩,⟨0,0⟩,⟨0,0⟩,⟨-41064832230512,28762079150950⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76
theorem wholeAccepted76 : StepValid wholeStep76.shape wholeBoxes76 wholeStep76.proposed := by
  dsimp only [StepValid,wholeStep76]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 0 3,⟨⟨3332884495257,3388913853159⟩,⟨0,0⟩,⟨-1035615078179,735134601877⟩,⟨0,0⟩,⟨0,0⟩,⟨-48847694945107,28948821549046⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77
theorem wholeAccepted77 : StepValid wholeStep77.shape wholeBoxes77 wholeStep77.proposed := by
  dsimp only [StepValid,wholeStep77]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep78 : Instruction 40 := ⟨.add 45 29,⟨⟨161160497472,165232574240⟩,⟨0,0⟩,⟨-1162698439922,-1051706472967⟩,⟨0,0⟩,⟨0,0⟩,⟨-2103233935895,2799884360140⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78
theorem wholeAccepted78 : StepValid wholeStep78.shape wholeBoxes78 wholeStep78.proposed := by
  dsimp only [StepValid,wholeStep78]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 1 0,⟨⟨488516273683,509279707181⟩,⟨0,0⟩,⟨-3739298513564,-3077500891441⟩,⟨0,0⟩,⟨0,0⟩,⟨-15378089949745,15170436447628⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79
theorem wholeAccepted79 : StepValid wholeStep79.shape wholeBoxes79 wholeStep79.proposed := by
  dsimp only [StepValid,wholeStep79]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep80 : Instruction 40 := ⟨.add 4 0,⟨⟨156295933000,233303158146⟩,⟨0,0⟩,⟨-6563468669837,-4195298119140⟩,⟨0,0⟩,⟨0,0⟩,⟨-48105088808494,57475981996287⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80
theorem wholeAccepted80 : StepValid wholeStep80.shape wholeBoxes80 wholeStep80.proposed := by
  dsimp only [StepValid,wholeStep80]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep81 : Instruction 40 := ⟨.mul 81 81,⟨⟨90250388308,90565673269⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81
theorem wholeAccepted81 : StepValid wholeStep81.shape wholeBoxes81 wholeStep81.proposed := by
  dsimp only [StepValid,wholeStep81]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep82 : Instruction 40 := ⟨.neg 0,⟨⟨-90565673269,-90250388308⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82
theorem wholeAccepted82 : StepValid wholeStep82.shape wholeBoxes82 wholeStep82.proposed := by
  dsimp only [StepValid,wholeStep82]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep83 : Instruction 40 := ⟨.add 81 0,⟨⟨1008945954507,1009261239468⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83
theorem wholeAccepted83 : StepValid wholeStep83.shape wholeBoxes83 wholeStep83.proposed := by
  dsimp only [StepValid,wholeStep83]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep84 : Instruction 40 := ⟨.inv 0,⟨⟨1197832406852,1198206716836⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes85 := wholeStep84.proposed :: wholeBoxes84
theorem wholeAccepted84 : StepValid wholeStep84.shape wholeBoxes84 wholeStep84.proposed := by
  dsimp only [StepValid,wholeStep84]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep85 : Instruction 40 := ⟨.mul 13 0,⟨⟨502777172541,516027446444⟩,⟨0,0⟩,⟨3339048037513,3736940717394⟩,⟨0,0⟩,⟨0,0⟩,⟨-8838503599156,8410216657193⟩⟩⟩
noncomputable def wholeBoxes86 := wholeStep85.proposed :: wholeBoxes85
theorem wholeAccepted85 : StepValid wholeStep85.shape wholeBoxes85 wholeStep85.proposed := by
  dsimp only [StepValid,wholeStep85]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep86 : Instruction 40 := ⟨.add 5 0,⟨⟨659073105541,749330604590⟩,⟨0,0⟩,⟨-3224420632324,-458357401746⟩,⟨0,0⟩,⟨0,0⟩,⟨-56943592407650,65886198653480⟩⟩⟩
noncomputable def wholeBoxes87 := wholeStep86.proposed :: wholeBoxes86
theorem wholeAccepted86 : StepValid wholeStep86.shape wholeBoxes86 wholeStep86.proposed := by
  dsimp only [StepValid,wholeStep86]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep87 : Instruction 40 := ⟨.mul 0 68,⟨⟨448661102428,512759930438⟩,⟨0,0⟩,⟨-2354921045816,-371892508577⟩,⟨0,0⟩,⟨0,0⟩,⟨-41278699331228,47405627804738⟩⟩⟩
noncomputable def wholeBoxes88 := wholeStep87.proposed :: wholeBoxes87
theorem wholeAccepted87 : StepValid wholeStep87.shape wholeBoxes87 wholeStep87.proposed := by
  dsimp only [StepValid,wholeStep87]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep88 : Instruction 40 := ⟨.mul 0 69,⟨⟨305424061670,350876828802⟩,⟨0,0⟩,⟨-1713054036794,-293918876069⟩,⟨0,0⟩,⟨0,0⟩,⟨-29818627421471,34085842660451⟩⟩⟩
noncomputable def wholeBoxes89 := wholeStep88.proposed :: wholeBoxes88
theorem wholeAccepted88 : StepValid wholeStep88.shape wholeBoxes88 wholeStep88.proposed := by
  dsimp only [StepValid,wholeStep88]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep89 : Instruction 40 := ⟨.mul 90 63,⟨⟨520090391627,520488922184⟩,⟨0,0⟩,⟨102461662953,114267082855⟩,⟨0,0⟩,⟨0,0⟩,⟨436420443555,962892087230⟩⟩⟩
noncomputable def wholeBoxes90 := wholeStep89.proposed :: wholeBoxes89
theorem wholeAccepted89 : StepValid wholeStep89.shape wholeBoxes89 wholeStep89.proposed := by
  dsimp only [StepValid,wholeStep89]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep90 : Instruction 40 := ⟨.inv 0,⟨⟨2322673486578,2324453285578⟩,⟨0,0⟩,⟨-510696795119,-457233531374⟩,⟨0,0⟩,⟨0,0⟩,⟨-4123459378201,-1723112742976⟩⟩⟩
noncomputable def wholeBoxes91 := wholeStep90.proposed :: wholeBoxes90
theorem wholeAccepted90 : StepValid wholeStep90.shape wholeBoxes90 wholeStep90.proposed := by
  dsimp only [StepValid,wholeStep90]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 2 0,⟨⟨645195878136,741780966148⟩,⟨0,0⟩,⟨-3784503638735,-747902688939⟩,⟨0,0⟩,⟨0,0⟩,⟨-64110330368110,73172824417288⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91
theorem wholeAccepted91 : StepValid wholeStep91.shape wholeBoxes91 wholeStep91.proposed := by
  dsimp only [StepValid,wholeStep91]
  exact ⟨by decide,by decide⟩
noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91]
theorem wholeAccepted : Accepted wholeProgram wholeInitial :=
  ⟨wholeAccepted0,⟨wholeAccepted1,⟨wholeAccepted2,⟨wholeAccepted3,⟨wholeAccepted4,⟨wholeAccepted5,⟨wholeAccepted6,⟨wholeAccepted7,⟨wholeAccepted8,⟨wholeAccepted9,⟨wholeAccepted10,⟨wholeAccepted11,⟨wholeAccepted12,⟨wholeAccepted13,⟨wholeAccepted14,⟨wholeAccepted15,⟨wholeAccepted16,⟨wholeAccepted17,⟨wholeAccepted18,⟨wholeAccepted19,⟨wholeAccepted20,⟨wholeAccepted21,⟨wholeAccepted22,⟨wholeAccepted23,⟨wholeAccepted24,⟨wholeAccepted25,⟨wholeAccepted26,⟨wholeAccepted27,⟨wholeAccepted28,⟨wholeAccepted29,⟨wholeAccepted30,⟨wholeAccepted31,⟨wholeAccepted32,⟨wholeAccepted33,⟨wholeAccepted34,⟨wholeAccepted35,⟨wholeAccepted36,⟨wholeAccepted37,⟨wholeAccepted38,⟨wholeAccepted39,⟨wholeAccepted40,⟨wholeAccepted41,⟨wholeAccepted42,⟨wholeAccepted43,⟨wholeAccepted44,⟨wholeAccepted45,⟨wholeAccepted46,⟨wholeAccepted47,⟨wholeAccepted48,⟨wholeAccepted49,⟨wholeAccepted50,⟨wholeAccepted51,⟨wholeAccepted52,⟨wholeAccepted53,⟨wholeAccepted54,⟨wholeAccepted55,⟨wholeAccepted56,⟨wholeAccepted57,⟨wholeAccepted58,⟨wholeAccepted59,⟨wholeAccepted60,⟨wholeAccepted61,⟨wholeAccepted62,⟨wholeAccepted63,⟨wholeAccepted64,⟨wholeAccepted65,⟨wholeAccepted66,⟨wholeAccepted67,⟨wholeAccepted68,⟨wholeAccepted69,⟨wholeAccepted70,⟨wholeAccepted71,⟨wholeAccepted72,⟨wholeAccepted73,⟨wholeAccepted74,⟨wholeAccepted75,⟨wholeAccepted76,⟨wholeAccepted77,⟨wholeAccepted78,⟨wholeAccepted79,⟨wholeAccepted80,⟨wholeAccepted81,⟨wholeAccepted82,⟨wholeAccepted83,⟨wholeAccepted84,⟨wholeAccepted85,⟨wholeAccepted86,⟨wholeAccepted87,⟨wholeAccepted88,⟨wholeAccepted89,⟨wholeAccepted90,⟨wholeAccepted91,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
noncomputable def whole_output : DyadicBivariateJetEnclosure 40 := ⟨⟨645195878136,741780966148⟩,⟨0,0⟩,⟨-3784503638735,-747902688939⟩,⟨0,0⟩,⟨0,0⟩,⟨-64110330368110,73172824417288⟩⟩
theorem whole_output_eq : (finalBoxes wholeProgram wholeInitial).getD 0 (zeroBox 40)=whole_output := rfl
open GeneralCK.Reflection GeneralCK.Reflection.SmallRatio GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed
theorem sameShape : shapes centerProgram=shapes wholeProgram := by decide
theorem scalar_program (a e r : ℝ) :
    (evalRealProgram wholeProgram [a,e,r,2]).getD 0 0=ReflectionMidpointKernel.scalarCore a e r := rfl
attribute [local irreducible] wholeProgram centerProgram
noncomputable def reflection_log_0_out : DyadicInterval 64 := ⟨-12786308645202662930,-12786308645202655416⟩
theorem reflection_log_0_checked : DyadicFastLog.check 1 2 1 16 reflection_log_0_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointFamily.Endpoints0423.sharedTwo_eq]
  decide
theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := DyadicFastLog.check_sound reflection_log_0_checked
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1):ℝ)=((1 / 2):ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [he]
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_0_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_1_out : DyadicInterval 64 := ⟨-4654370467374487743,-4654370467374487698⟩
theorem reflection_log_1_checked : DyadicFastLog.check 1000 1287 0 16 reflection_log_1_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointFamily.Endpoints0423.sharedTwo_eq]
  decide
theorem reflection_log_1 : Bounds (31539241 / 125000000) (252313929 / 1000000000) (Real.log (1287 / 1000)) := by
  have h := DyadicFastLog.check_sound reflection_log_1_checked
  have he : Real.log (1287 / 1000) = -Real.log (1000 / 1287) := by
    rw [show ((1287 / 1000):ℝ)=((1000 / 1287):ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [he]
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_1_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_2_out : DyadicInterval 64 := ⟨-6240051295827186155,-6240051295827186108⟩
theorem reflection_log_2_checked : DyadicFastLog.check 713 1000 0 16 reflection_log_2_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointFamily.Endpoints0423.sharedTwo_eq]
  decide
theorem reflection_log_2 : Bounds (-338273859 / 1000000000) (-169136929 / 500000000) (Real.log (713 / 1000)) := by
  have h := DyadicFastLog.check_sound reflection_log_2_checked
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_2_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_3_out : DyadicInterval 64 := ⟨-4647202507667544845,-4647202507667544788⟩
theorem reflection_log_3_checked : DyadicFastLog.check 2000 2573 0 16 reflection_log_3_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointFamily.Endpoints0423.sharedTwo_eq]
  decide
theorem reflection_log_3 : Bounds (31490669 / 125000000) (251925353 / 1000000000) (Real.log (2573 / 2000)) := by
  have h := DyadicFastLog.check_sound reflection_log_3_checked
  have he : Real.log (2573 / 2000) = -Real.log (2000 / 2573) := by
    rw [show ((2573 / 2000):ℝ)=((2000 / 2573):ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [he]
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_3_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_4_out : DyadicInterval 64 := ⟨-6227119823812366091,-6227119823812366046⟩
theorem reflection_log_4_checked : DyadicFastLog.check 1427 2000 0 16 reflection_log_4_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointFamily.Endpoints0423.sharedTwo_eq]
  decide
theorem reflection_log_4 : Bounds (-337572843 / 1000000000) (-168786421 / 500000000) (Real.log (1427 / 2000)) := by
  have h := DyadicFastLog.check_sound reflection_log_4_checked
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_4_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_5_out : DyadicInterval 64 := ⟨-52866328545992757,-52866328545992712⟩
theorem reflection_log_5_checked : DyadicFastLog.check 100000 100287 0 16 reflection_log_5_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointFamily.Endpoints0423.sharedTwo_eq]
  decide
theorem reflection_log_5 : Bounds (2865889 / 1000000000) (286589 / 100000000) (Real.log (100287 / 100000)) := by
  have h := DyadicFastLog.check_sound reflection_log_5_checked
  have he : Real.log (100287 / 100000) = -Real.log (100000 / 100287) := by
    rw [show ((100287 / 100000):ℝ)=((100000 / 100287):ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [he]
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_5_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_6_out : DyadicInterval 64 := ⟨-53018273158030641,-53018273158030596⟩
theorem reflection_log_6_checked : DyadicFastLog.check 99713 100000 0 16 reflection_log_6_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointFamily.Endpoints0423.sharedTwo_eq]
  decide
theorem reflection_log_6 : Bounds (-2874127 / 1000000000) (-1437063 / 500000000) (Real.log (99713 / 100000)) := by
  have h := DyadicFastLog.check_sound reflection_log_6_checked
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_6_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_7_out : DyadicInterval 64 := ⟨-5284235246558737,-5284235246558692⟩
theorem reflection_log_7_checked : DyadicFastLog.check 2000000 2000573 0 16 reflection_log_7_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointFamily.Endpoints0423.sharedTwo_eq]
  decide
theorem reflection_log_7 : Bounds (143229 / 500000000) (286459 / 1000000000) (Real.log (2000573 / 2000000)) := by
  have h := DyadicFastLog.check_sound reflection_log_7_checked
  have he : Real.log (2000573 / 2000000) = -Real.log (2000000 / 2000573) := by
    rw [show ((2000573 / 2000000):ℝ)=((2000000 / 2000573):ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [he]
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_7_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_8_out : DyadicInterval 64 := ⟨-5285749396879625,-5285749396879580⟩
theorem reflection_log_8_checked : DyadicFastLog.check 1999427 2000000 0 16 reflection_log_8_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointFamily.Endpoints0423.sharedTwo_eq]
  decide
theorem reflection_log_8 : Bounds (-143271 / 500000000) (-286541 / 1000000000) (Real.log (1999427 / 2000000)) := by
  have h := DyadicFastLog.check_sound reflection_log_8_checked
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_8_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
theorem entropy_bound {a z : ℝ} (ha : Bounds (573 / 2000) (287 / 1000) a) (hz : Bounds (1 / 1000) (1 / 100) z) :
  Bounds (67226042907 / 100000000000) (672336225493 / 1000000000000) ((biasE a+biasE (a*z))/2) := by
  let x0 : ℝ := Real.log (2 / 1)
  have hx0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x0 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x1 : ℝ := (1 / 1)+(287 / 1000)
  have hx1 : Bounds (1287 / 1000) (1287 / 1000) x1 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((287 / 1000) : ℝ)) <;> norm_num
  let x2 : ℝ := (1 / 1)+(287 / 1000)
  have hx2 : Bounds (1287 / 1000) (1287 / 1000) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((287 / 1000) : ℝ)) <;> norm_num
  let x3 : ℝ := Real.log x2
  have hx3 : Bounds (31539241 / 125000000) (252313929 / 1000000000) x3 := by
    exact bounds_log hx2 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x4 : ℝ := x1*x3
  have hx4 : Bounds (40591003167 / 125000000000) (324728026623 / 1000000000000) x4 := by
    apply bounds_mul hx1 hx3 <;> norm_num
  let x5 : ℝ := -(287 / 1000)
  have hx5 : Bounds (-287 / 1000) (-287 / 1000) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((287 / 1000) : ℝ))
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (713 / 1000) (713 / 1000) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-(287 / 1000)
  have hx7 : Bounds (713 / 1000) (713 / 1000) x7 := by
    exact hx6
  let x8 : ℝ := -(287 / 1000)
  have hx8 : Bounds (-287 / 1000) (-287 / 1000) x8 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((287 / 1000) : ℝ))
  let x9 : ℝ := (1 / 1)+x8
  have hx9 : Bounds (713 / 1000) (713 / 1000) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx8 <;> norm_num
  let x10 : ℝ := (1 / 1)-(287 / 1000)
  have hx10 : Bounds (713 / 1000) (713 / 1000) x10 := by
    exact hx9
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (-338273859 / 1000000000) (-169136929 / 500000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x12 : ℝ := x7*x11
  have hx12 : Bounds (-241189261467 / 1000000000000) (-120594630377 / 500000000000) x12 := by
    apply bounds_mul hx7 hx11 <;> norm_num
  let x13 : ℝ := x4+x12
  have hx13 : Bounds (83538763869 / 1000000000000) (83538765869 / 1000000000000) x13 := by
    apply bounds_add hx4 hx12 <;> norm_num
  let x14 : ℝ := (2 / 1)⁻¹
  have hx14 : Bounds (1 / 2) (1 / 2) x14 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x15 : ℝ := x13*x14
  have hx15 : Bounds (20884690967 / 500000000000) (8353876587 / 200000000000) x15 := by
    apply bounds_mul hx13 hx14 <;> norm_num
  let x16 : ℝ := x13/(2 / 1)
  have hx16 : Bounds (20884690967 / 500000000000) (8353876587 / 200000000000) x16 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx15
  let x17 : ℝ := -x16
  have hx17 : Bounds (-8353876587 / 200000000000) (-20884690967 / 500000000000) x17 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx16
  let x18 : ℝ := x0+x17
  have hx18 : Bounds (130275559413 / 200000000000) (325688899533 / 500000000000) x18 := by
    apply bounds_add hx0 hx17 <;> norm_num
  let x19 : ℝ := x0-x16
  have hx19 : Bounds (130275559413 / 200000000000) (325688899533 / 500000000000) x19 := by
    exact hx18
  let x20 : ℝ := biasE (287 / 1000)
  have hx20 : Bounds (130275559413 / 200000000000) (325688899533 / 500000000000) x20 := by
    simpa +zetaDelta only [biasE, div_one] using hx19
  let x21 : ℝ := Real.log (2 / 1)
  have hx21 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x21 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x22 : ℝ := (1 / 1)+(573 / 2000)
  have hx22 : Bounds (2573 / 2000) (2573 / 2000) x22 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((573 / 2000) : ℝ)) <;> norm_num
  let x23 : ℝ := (1 / 1)+(573 / 2000)
  have hx23 : Bounds (2573 / 2000) (2573 / 2000) x23 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((573 / 2000) : ℝ)) <;> norm_num
  let x24 : ℝ := Real.log x23
  have hx24 : Bounds (31490669 / 125000000) (251925353 / 1000000000) x24 := by
    exact bounds_log hx23 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x25 : ℝ := x22*x24
  have hx25 : Bounds (81025491337 / 250000000000) (64820393327 / 200000000000) x25 := by
    apply bounds_mul hx22 hx24 <;> norm_num
  let x26 : ℝ := -(573 / 2000)
  have hx26 : Bounds (-573 / 2000) (-573 / 2000) x26 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((573 / 2000) : ℝ))
  let x27 : ℝ := (1 / 1)+x26
  have hx27 : Bounds (1427 / 2000) (1427 / 2000) x27 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx26 <;> norm_num
  let x28 : ℝ := (1 / 1)-(573 / 2000)
  have hx28 : Bounds (1427 / 2000) (1427 / 2000) x28 := by
    exact hx27
  let x29 : ℝ := -(573 / 2000)
  have hx29 : Bounds (-573 / 2000) (-573 / 2000) x29 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((573 / 2000) : ℝ))
  let x30 : ℝ := (1 / 1)+x29
  have hx30 : Bounds (1427 / 2000) (1427 / 2000) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx29 <;> norm_num
  let x31 : ℝ := (1 / 1)-(573 / 2000)
  have hx31 : Bounds (1427 / 2000) (1427 / 2000) x31 := by
    exact hx30
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (-337572843 / 1000000000) (-168786421 / 500000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x33 : ℝ := x28*x32
  have hx33 : Bounds (-240858223481 / 1000000000000) (-240858222767 / 1000000000000) x33 := by
    apply bounds_mul hx28 hx32 <;> norm_num
  let x34 : ℝ := x25+x33
  have hx34 : Bounds (83243741867 / 1000000000000) (20810935967 / 250000000000) x34 := by
    apply bounds_add hx25 hx33 <;> norm_num
  let x35 : ℝ := (2 / 1)⁻¹
  have hx35 : Bounds (1 / 2) (1 / 2) x35 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x36 : ℝ := x34*x35
  have hx36 : Bounds (41621870933 / 1000000000000) (20810935967 / 500000000000) x36 := by
    apply bounds_mul hx34 hx35 <;> norm_num
  let x37 : ℝ := x34/(2 / 1)
  have hx37 : Bounds (41621870933 / 1000000000000) (20810935967 / 500000000000) x37 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx36
  let x38 : ℝ := -x37
  have hx38 : Bounds (-20810935967 / 500000000000) (-41621870933 / 1000000000000) x38 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx37
  let x39 : ℝ := x21+x38
  have hx39 : Bounds (325762654033 / 500000000000) (651525310067 / 1000000000000) x39 := by
    apply bounds_add hx21 hx38 <;> norm_num
  let x40 : ℝ := x21-x37
  have hx40 : Bounds (325762654033 / 500000000000) (651525310067 / 1000000000000) x40 := by
    exact hx39
  let x41 : ℝ := biasE (573 / 2000)
  have hx41 : Bounds (325762654033 / 500000000000) (651525310067 / 1000000000000) x41 := by
    simpa +zetaDelta only [biasE, div_one] using hx40
  let x42 : ℝ := biasE a
  have hx42 : Bounds (130275559413 / 200000000000) (651525310067 / 1000000000000) x42 := by
    exact bounds_biasE ha (by norm_num) (by norm_num) hx20.1 hx41.2
  let x43 : ℝ := a*z
  have hx43 : Bounds (573 / 2000000) (287 / 100000) x43 := by
    apply bounds_mul ha hz <;> norm_num
  let x44 : ℝ := Real.log (2 / 1)
  have hx44 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x44 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x45 : ℝ := (1 / 1)+(287 / 100000)
  have hx45 : Bounds (100287 / 100000) (100287 / 100000) x45 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((287 / 100000) : ℝ)) <;> norm_num
  let x46 : ℝ := (1 / 1)+(287 / 100000)
  have hx46 : Bounds (100287 / 100000) (100287 / 100000) x46 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((287 / 100000) : ℝ)) <;> norm_num
  let x47 : ℝ := Real.log x46
  have hx47 : Bounds (2865889 / 1000000000) (286589 / 100000000) x47 := by
    exact bounds_log hx46 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x48 : ℝ := x45*x47
  have hx48 : Bounds (2874114101 / 1000000000000) (574823021 / 200000000000) x48 := by
    apply bounds_mul hx45 hx47 <;> norm_num
  let x49 : ℝ := -(287 / 100000)
  have hx49 : Bounds (-287 / 100000) (-287 / 100000) x49 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((287 / 100000) : ℝ))
  let x50 : ℝ := (1 / 1)+x49
  have hx50 : Bounds (99713 / 100000) (99713 / 100000) x50 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx49 <;> norm_num
  let x51 : ℝ := (1 / 1)-(287 / 100000)
  have hx51 : Bounds (99713 / 100000) (99713 / 100000) x51 := by
    exact hx50
  let x52 : ℝ := -(287 / 100000)
  have hx52 : Bounds (-287 / 100000) (-287 / 100000) x52 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((287 / 100000) : ℝ))
  let x53 : ℝ := (1 / 1)+x52
  have hx53 : Bounds (99713 / 100000) (99713 / 100000) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx52 <;> norm_num
  let x54 : ℝ := (1 / 1)-(287 / 100000)
  have hx54 : Bounds (99713 / 100000) (99713 / 100000) x54 := by
    exact hx53
  let x55 : ℝ := Real.log x54
  have hx55 : Bounds (-2874127 / 1000000000) (-1437063 / 500000000) x55 := by
    exact bounds_log hx54 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x56 : ℝ := x51*x55
  have hx56 : Bounds (-179117391 / 62500000000) (-1432938629 / 500000000000) x56 := by
    apply bounds_mul hx51 hx55 <;> norm_num
  let x57 : ℝ := x48+x56
  have hx57 : Bounds (1647169 / 200000000000) (8237847 / 1000000000000) x57 := by
    apply bounds_add hx48 hx56 <;> norm_num
  let x58 : ℝ := (2 / 1)⁻¹
  have hx58 : Bounds (1 / 2) (1 / 2) x58 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x59 : ℝ := x57*x58
  have hx59 : Bounds (2058961 / 500000000000) (1029731 / 250000000000) x59 := by
    apply bounds_mul hx57 hx58 <;> norm_num
  let x60 : ℝ := x57/(2 / 1)
  have hx60 : Bounds (2058961 / 500000000000) (1029731 / 250000000000) x60 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx59
  let x61 : ℝ := -x60
  have hx61 : Bounds (-1029731 / 250000000000) (-2058961 / 500000000000) x61 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx60
  let x62 : ℝ := x44+x61
  have hx62 : Bounds (173285765269 / 250000000000) (346571531539 / 500000000000) x62 := by
    apply bounds_add hx44 hx61 <;> norm_num
  let x63 : ℝ := x44-x60
  have hx63 : Bounds (173285765269 / 250000000000) (346571531539 / 500000000000) x63 := by
    exact hx62
  let x64 : ℝ := biasE (287 / 100000)
  have hx64 : Bounds (173285765269 / 250000000000) (346571531539 / 500000000000) x64 := by
    simpa +zetaDelta only [biasE, div_one] using hx63
  let x65 : ℝ := Real.log (2 / 1)
  have hx65 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x65 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x66 : ℝ := (1 / 1)+(573 / 2000000)
  have hx66 : Bounds (2000573 / 2000000) (2000573 / 2000000) x66 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((573 / 2000000) : ℝ)) <;> norm_num
  let x67 : ℝ := (1 / 1)+(573 / 2000000)
  have hx67 : Bounds (2000573 / 2000000) (2000573 / 2000000) x67 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((573 / 2000000) : ℝ)) <;> norm_num
  let x68 : ℝ := Real.log x67
  have hx68 : Bounds (143229 / 500000000) (286459 / 1000000000) x68 := by
    exact bounds_log hx67 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x69 : ℝ := x66*x68
  have hx69 : Bounds (28654007 / 100000000000) (286541071 / 1000000000000) x69 := by
    apply bounds_mul hx66 hx68 <;> norm_num
  let x70 : ℝ := -(573 / 2000000)
  have hx70 : Bounds (-573 / 2000000) (-573 / 2000000) x70 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((573 / 2000000) : ℝ))
  let x71 : ℝ := (1 / 1)+x70
  have hx71 : Bounds (1999427 / 2000000) (1999427 / 2000000) x71 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx70 <;> norm_num
  let x72 : ℝ := (1 / 1)-(573 / 2000000)
  have hx72 : Bounds (1999427 / 2000000) (1999427 / 2000000) x72 := by
    exact hx71
  let x73 : ℝ := -(573 / 2000000)
  have hx73 : Bounds (-573 / 2000000) (-573 / 2000000) x73 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((573 / 2000000) : ℝ))
  let x74 : ℝ := (1 / 1)+x73
  have hx74 : Bounds (1999427 / 2000000) (1999427 / 2000000) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx73 <;> norm_num
  let x75 : ℝ := (1 / 1)-(573 / 2000000)
  have hx75 : Bounds (1999427 / 2000000) (1999427 / 2000000) x75 := by
    exact hx74
  let x76 : ℝ := Real.log x75
  have hx76 : Bounds (-143271 / 500000000) (-286541 / 1000000000) x76 := by
    exact bounds_log hx75 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x77 : ℝ := x72*x76
  have hx77 : Bounds (-143229953 / 500000000000) (-143229453 / 500000000000) x77 := by
    apply bounds_mul hx72 hx76 <;> norm_num
  let x78 : ℝ := x69+x77
  have hx78 : Bounds (20041 / 250000000000) (16433 / 200000000000) x78 := by
    apply bounds_add hx69 hx77 <;> norm_num
  let x79 : ℝ := (2 / 1)⁻¹
  have hx79 : Bounds (1 / 2) (1 / 2) x79 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x80 : ℝ := x78*x79
  have hx80 : Bounds (20041 / 500000000000) (41083 / 1000000000000) x80 := by
    apply bounds_mul hx78 hx79 <;> norm_num
  let x81 : ℝ := x78/(2 / 1)
  have hx81 : Bounds (20041 / 500000000000) (41083 / 1000000000000) x81 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx80
  let x82 : ℝ := -x81
  have hx82 : Bounds (-41083 / 1000000000000) (-20041 / 500000000000) x82 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx81
  let x83 : ℝ := x65+x82
  have hx83 : Bounds (693147138917 / 1000000000000) (346573570459 / 500000000000) x83 := by
    apply bounds_add hx65 hx82 <;> norm_num
  let x84 : ℝ := x65-x81
  have hx84 : Bounds (693147138917 / 1000000000000) (346573570459 / 500000000000) x84 := by
    exact hx83
  let x85 : ℝ := biasE (573 / 2000000)
  have hx85 : Bounds (693147138917 / 1000000000000) (346573570459 / 500000000000) x85 := by
    simpa +zetaDelta only [biasE, div_one] using hx84
  let x86 : ℝ := biasE x43
  have hx86 : Bounds (173285765269 / 250000000000) (346573570459 / 500000000000) x86 := by
    exact bounds_biasE hx43 (by norm_num) (by norm_num) hx64.1 hx85.2
  let x87 : ℝ := x42+x86
  have hx87 : Bounds (1344520858141 / 1000000000000) (268934490197 / 200000000000) x87 := by
    apply bounds_add hx42 hx86 <;> norm_num
  let x88 : ℝ := (2 / 1)⁻¹
  have hx88 : Bounds (1 / 2) (1 / 2) x88 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x89 : ℝ := x87*x88
  have hx89 : Bounds (67226042907 / 100000000000) (672336225493 / 1000000000000) x89 := by
    apply bounds_mul hx87 hx88 <;> norm_num
  let x90 : ℝ := x87/(2 / 1)
  have hx90 : Bounds (67226042907 / 100000000000) (672336225493 / 1000000000000) x90 := by
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

theorem center_inputs_eq : centerInitial=inputBoxes ⟨315010081357,315559837172⟩ ⟨739158158656,739241497705⟩ ⟨157505040678,157779918586⟩ := rfl
theorem whole_inputs_eq : wholeInitial=inputBoxes ⟨315010081357,315559837172⟩ ⟨739158158656,739241497705⟩ ⟨155927241493,159357717772⟩ := rfl
noncomputable def centerUpper : ℝ := (698593424245 / 1099511627776)
noncomputable def secondUpper : ℝ := (9146603052161 / 137438953472)


theorem center_inputs {a z : ℝ} (ha : Bounds (573/2000) (287/1000) a)
    (hz : Bounds (1/1000) (1/100) z) :
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

theorem whole_inputs {a z s : ℝ} (ha : Bounds (573/2000) (287/1000) a)
    (hz : Bounds (1/1000) (1/100) z) (hs : s∈Icc (a*(1-z)/2) (a*(1+z)/2)) :
    RegistersContain wholeInitial (inputJets a ((biasE a+biasE (a*z))/2)) s := by
  rw [whole_inputs_eq]
  apply inputs_contain
  · norm_num [DyadicInterval.Contains,DyadicInterval.scale]
    constructor <;> linarith [ha.1,ha.2]
  · have h := entropy_bound ha hz
    norm_num [DyadicInterval.Contains,DyadicInterval.scale]
    constructor <;> linarith [h.1,h.2]
  · have hb : a*z≤(287/1000:ℝ)*(1/100) :=
      mul_le_mul ha.2 hz.2 (by linarith [hz.1]) (by norm_num)
    norm_num [DyadicInterval.Contains,DyadicInterval.scale]
    constructor <;> nlinarith [ha.1,ha.2,hs.1,hs.2]

theorem curvature_pos {a z : ℝ} (ha : Bounds (573/2000) (287/1000) a)
    (hz : Bounds (1/1000) (1/100) z) : 0<curvature a (a*z) := by
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
    have hb : a*z≤(287/100000:ℝ) := by
      have h := mul_le_mul ha.2 hz.2 hz0.le (by norm_num : (0:ℝ)≤287/1000)
      norm_num at h
      exact h
    have hb2 := mul_self_le_mul_self hb0 hb
    have hle : centerUpper+secondUpper*(a*z)^2/24 ≤
        centerUpper+secondUpper*(287/100000:ℝ)^2/24 := by
      unfold centerUpper secondUpper
      nlinarith
    apply hle.trans_lt
    exact lt_of_lt_of_le (by norm_num [centerUpper,secondUpper] :
      centerUpper+secondUpper*(287/100000:ℝ)^2/24 < 2*(573/2000:ℝ)/(1-(573/2000:ℝ)^2)^2)
      (LowRatioFamily.base_mono (by norm_num) ha.1 ha1)

#print axioms entropy_bound
#print axioms curvature_pos
end GeneralCK.Certificates.ReflectionMidpointFamily.Cell0423

end


