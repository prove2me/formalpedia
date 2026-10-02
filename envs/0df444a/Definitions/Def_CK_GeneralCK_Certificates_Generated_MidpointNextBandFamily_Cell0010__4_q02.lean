-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Cell0010__4_q02
-- name    : CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Cell0010__4_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T12:31:16.085778+00:00
-- url     : https://prove2.me/theorems/b13e8be9-2465-4fa9-a513-cdf9852e7886
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0010 (+3 modules: GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0011, GeneralCK.Cert…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0010 (+3 modules: GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0011, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0012, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0013) (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0010 (+3 modules: GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0011, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0012, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0013) (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0010 (+3 modules: GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0011, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0012, GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0013) (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointNextBandFamily/Cell0010 (+3 modules: GeneralCK/Certificates/Generated/MidpointNextBandFamily/Cell0011, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Cell0012, GeneralCK/Certificates/Generated/MidpointNextBandFamily/Cell0013) (piece 3 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextBandFamily_Cell0010__4_q01

-- ===== source module GeneralCK.Certificates.Generated.MidpointNextBandFamily.Cell0012 =====
section

namespace GeneralCK.Certificates.ReflectionMidpointNextBandFamily.Endpoints0012
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
noncomputable def out_w1 : DyadicInterval 40 := ⟨80453217600,80453217664⟩
theorem checked_w1 : DyadicFastLog.check 1099511627776 1182981423104 0 16 (lift40 out_w1.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w1 : out_w1.Contains (Real.log ((1182981423104:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w1
#print axioms endpoint_w1
noncomputable def out_w2 : DyadicInterval 40 := ⟨-86808185216,-86808185152⟩
theorem checked_w2 : DyadicFastLog.check 1016041832448 1099511627776 0 16 (lift40 out_w2)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w2 : out_w2.Contains (Real.log ((1016041832448:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w2
#print axioms endpoint_w2
noncomputable def out_w3 : DyadicInterval 40 := ⟨80510716928,80510716992⟩
theorem checked_w3 : DyadicFastLog.check 1099511627776 1183043289088 0 16 (lift40 out_w3.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w3 : out_w3.Contains (Real.log ((1183043289088:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w3
#print axioms endpoint_w3
noncomputable def out_w4 : DyadicInterval 40 := ⟨-86875135616,-86875135552⟩
theorem checked_w4 : DyadicFastLog.check 1015979966464 1099511627776 0 16 (lift40 out_w4)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w4 : out_w4.Contains (Real.log ((1015979966464:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w4
#print axioms endpoint_w4
noncomputable def out_w5 : DyadicInterval 40 := ⟨-6364418688,-6364418624⟩
theorem checked_w5 : DyadicFastLog.check 1093165593532 1099511627776 0 16 (lift40 out_w5)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w5 : out_w5.Contains (Real.log ((1093165593532:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w5
#print axioms endpoint_w5
noncomputable def out_w6 : DyadicInterval 40 := ⟨-6354967552,-6354967488⟩
theorem checked_w6 : DyadicFastLog.check 1093174990167 1099511627776 0 16 (lift40 out_w6)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w6 : out_w6.Contains (Real.log ((1093174990167:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w6
#print axioms endpoint_w6
noncomputable def out_w7 : DyadicInterval 40 := ⟨335061400192,335061400256⟩
theorem checked_w7 : DyadicFastLog.check 1099511627776 1491232075746 0 16 (lift40 out_w7.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w7 : out_w7.Contains (Real.log ((1491232075746:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w7
#print axioms endpoint_w7
noncomputable def out_w8 : DyadicInterval 40 := ⟨335286450880,335286450944⟩
theorem checked_w8 : DyadicFastLog.check 1099511627776 1491537335996 0 16 (lift40 out_w8.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w8 : out_w8.Contains (Real.log ((1491537335996:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w8
#print axioms endpoint_w8
noncomputable def out_w9 : DyadicInterval 40 := ⟨167261402816,167261402880⟩
theorem checked_w9 : DyadicFastLog.check 1099511627776 1280165627640 0 16 (lift40 out_w9.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w9 : out_w9.Contains (Real.log ((1280165627640:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w9
#print axioms endpoint_w9
noncomputable def out_w10 : DyadicInterval 40 := ⟨167385852544,167385852608⟩
theorem checked_w10 : DyadicFastLog.check 1099511627776 1280310533132 0 16 (lift40 out_w10.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w10 : out_w10.Contains (Real.log ((1280310533132:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w10
#print axioms endpoint_w10
noncomputable def out_w11 : DyadicInterval 40 := ⟨73883411328,73883411392⟩
theorem checked_w11 : DyadicFastLog.check 1099511627776 1175933943808 0 16 (lift40 out_w11.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w11 : out_w11.Contains (Real.log ((1175933943808:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w11
#print axioms endpoint_w11
noncomputable def out_w12 : DyadicInterval 40 := ⟨-79208069568,-79208069504⟩
theorem checked_w12 : DyadicFastLog.check 1023089311744 1099511627776 0 16 (lift40 out_w12)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w12 : out_w12.Contains (Real.log ((1023089311744:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w12
#print axioms endpoint_w12
noncomputable def out_w13 : DyadicInterval 40 := ⟨87027596992,87027597056⟩
theorem checked_w13 : DyadicFastLog.check 1099511627776 1190076088320 0 16 (lift40 out_w13.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w13 : out_w13.Contains (Real.log ((1190076088320:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w13
#print axioms endpoint_w13
noncomputable def out_w14 : DyadicInterval 40 := ⟨-94512620928,-94512620864⟩
theorem checked_w14 : DyadicFastLog.check 1008947167232 1099511627776 0 16 (lift40 out_w14)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w14 : out_w14.Contains (Real.log ((1008947167232:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w14
#print axioms endpoint_w14
noncomputable def out_w15 : DyadicInterval 40 := ⟨-7485023936,-7485023872⟩
theorem checked_w15 : DyadicFastLog.check 1092052023615 1099511627776 0 16 (lift40 out_w15)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w15 : out_w15.Contains (Real.log ((1092052023615:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w15
#print axioms endpoint_w15
noncomputable def out_w16 : DyadicInterval 40 := ⟨-5324658176,-5324658112⟩
theorem checked_w16 : DyadicFastLog.check 1094199841852 1099511627776 0 16 (lift40 out_w16)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w16 : out_w16.Contains (Real.log ((1094199841852:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w16
#print axioms endpoint_w16
noncomputable def out_w17 : DyadicInterval 40 := ⟨153091480832,153091480896⟩
theorem checked_w17 : DyadicFastLog.check 1099511627776 1263773387006 0 16 (lift40 out_w17.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w17 : out_w17.Contains (Real.log ((1263773387006:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w17
#print axioms endpoint_w17
noncomputable def out_w18 : DyadicInterval 40 := ⟨181540217920,181540217984⟩
theorem checked_w18 : DyadicFastLog.check 1099511627776 1296898925478 0 16 (lift40 out_w18.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w18 : out_w18.Contains (Real.log ((1296898925478:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w18
#print axioms endpoint_w18
end GeneralCK.Certificates.ReflectionMidpointNextBandFamily.Endpoints0012

namespace GeneralCK.Certificates.ReflectionMidpointNextBandFamily.Cell0012
open Set GeneralCK.Certificates.ReflectionMidpointNextBandFamily.Endpoints0012
open BivariateJetProgram (RegistersContain RegistersSound zeroBox zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
theorem lc0 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc1 : ProvedTranscendental.LogEncloses (⟨1182981423104,1182981423104⟩ : DyadicInterval 40) (⟨80453217600,80453217664⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w1
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w1
theorem lc2 : ProvedTranscendental.LogEncloses (⟨1016041832448,1016041832448⟩ : DyadicInterval 40) (⟨-86808185216,-86808185152⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w2
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w2
theorem lc3 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc4 : ProvedTranscendental.LogEncloses (⟨1183043289088,1183043289088⟩ : DyadicInterval 40) (⟨80510716928,80510716992⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w3
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w3
theorem lc5 : ProvedTranscendental.LogEncloses (⟨1015979966464,1015979966464⟩ : DyadicInterval 40) (⟨-86875135616,-86875135552⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w4
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w4
theorem lc6 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc7 : ProvedTranscendental.LogEncloses (⟨1093165593532,1093174990167⟩ : DyadicInterval 40) (⟨-6364418688,-6354967488⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w5
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w6
theorem lc8 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc9 : ProvedTranscendental.LogEncloses (⟨1182981423104,1183043289088⟩ : DyadicInterval 40) (⟨80453217600,80510716992⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w1
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w3
theorem lc10 : ProvedTranscendental.LogEncloses (⟨1015979966464,1016041832448⟩ : DyadicInterval 40) (⟨-86875135616,-86808185152⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w4
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w2
theorem lc11 : ProvedTranscendental.LogEncloses (⟨1093165593532,1093174990167⟩ : DyadicInterval 40) (⟨-6364418688,-6354967488⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w5
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w6
theorem lc12 : ProvedTranscendental.LogEncloses (⟨1491232075746,1491537335996⟩ : DyadicInterval 40) (⟨335061400192,335286450944⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w7
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
theorem lc13 : ProvedTranscendental.LogEncloses (⟨1280165627640,1280310533132⟩ : DyadicInterval 40) (⟨167261402816,167385852608⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w9
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w10
theorem lc14 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc15 : ProvedTranscendental.LogEncloses (⟨1175933943808,1175933943808⟩ : DyadicInterval 40) (⟨73883411328,73883411392⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w11
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w11
theorem lc16 : ProvedTranscendental.LogEncloses (⟨1023089311744,1023089311744⟩ : DyadicInterval 40) (⟨-79208069568,-79208069504⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w12
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w12
theorem lc17 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc18 : ProvedTranscendental.LogEncloses (⟨1190076088320,1190076088320⟩ : DyadicInterval 40) (⟨87027596992,87027597056⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w13
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w13
theorem lc19 : ProvedTranscendental.LogEncloses (⟨1008947167232,1008947167232⟩ : DyadicInterval 40) (⟨-94512620928,-94512620864⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w14
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w14
theorem lc20 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc21 : ProvedTranscendental.LogEncloses (⟨1092052023615,1094199841852⟩ : DyadicInterval 40) (⟨-7485023936,-5324658112⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w15
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w16
theorem lc22 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc23 : ProvedTranscendental.LogEncloses (⟨1175933943808,1190076088320⟩ : DyadicInterval 40) (⟨73883411328,87027597056⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w11
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w13
theorem lc24 : ProvedTranscendental.LogEncloses (⟨1008947167232,1023089311744⟩ : DyadicInterval 40) (⟨-94512620928,-79208069504⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w14
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w12
theorem lc25 : ProvedTranscendental.LogEncloses (⟨1092052023615,1094199841852⟩ : DyadicInterval 40) (⟨-7485023936,-5324658112⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w15
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w16
theorem lc26 : ProvedTranscendental.LogEncloses (⟨1491232075746,1491537335996⟩ : DyadicInterval 40) (⟨335061400192,335286450944⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w7
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
theorem lc27 : ProvedTranscendental.LogEncloses (⟨1263773387006,1296898925478⟩ : DyadicInterval 40) (⟨153091480832,181540217984⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w17
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w18
theorem ew3_ok (x : ℝ) (hx : (⟨83469795328,83469795328⟩ : DyadicInterval 40).Contains x) : (⟨758952014511,758952033840⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨83469795328,83469795328⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨80453217600,80453217664⟩ : DyadicInterval 40)) (minus:=(⟨-86808185216,-86808185152⟩ : DyadicInterval 40))
    (lc0 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc1 lc2 (by decide) hx
theorem ew6_ok (x : ℝ) (hx : (⟨83531661312,83531661312⟩ : DyadicInterval 40).Contains x) : (⟨758947307094,758947326423⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨83531661312,83531661312⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨80510716928,80510716992⟩ : DyadicInterval 40)) (minus:=(⟨-86875135616,-86875135552⟩ : DyadicInterval 40))
    (lc3 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc4 lc5 (by decide) hx
theorem ew17_ok (x : ℝ) (hx : (⟨76422316032,76422316032⟩ : DyadicInterval 40).Contains x) : (⟨759465348048,759465367378⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨76422316032,76422316032⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨73883411328,73883411392⟩ : DyadicInterval 40)) (minus:=(⟨-79208069568,-79208069504⟩ : DyadicInterval 40))
    (lc14 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc15 lc16 (by decide) hx
theorem ew20_ok (x : ℝ) (hx : (⟨90564460544,90564460544⟩ : DyadicInterval 40).Contains x) : (⟨758389352531,758389371860⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨90564460544,90564460544⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨87027596992,87027597056⟩ : DyadicInterval 40)) (minus:=(⟨-94512620928,-94512620864⟩ : DyadicInterval 40))
    (lc17 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc18 lc19 (by decide) hx
theorem bw9_ok (x : ℝ) (hx : (⟨83469795328,83531661312⟩ : DyadicInterval 40).Contains x) : (⟨765300867360,765305612224⟩ : DyadicInterval 40).Contains (Reflection.biasB x) := by
  exact ProvedTranscendental.denominator_encloses (c:=(⟨83469795328,83531661312⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (gapLog:=(⟨-6364418688,-6354967488⟩ : DyadicInterval 40))
    (lc6 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc7 (by decide) hx
theorem bw23_ok (x : ℝ) (hx : (⟨76422316032,90564460544⟩ : DyadicInterval 40).Contains x) : (⟨764785712672,765865914848⟩ : DyadicInterval 40).Contains (Reflection.biasB x) := by
  exact ProvedTranscendental.denominator_encloses (c:=(⟨76422316032,90564460544⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (gapLog:=(⟨-7485023936,-5324658112⟩ : DyadicInterval 40))
    (lc20 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc21 (by decide) hx
theorem brcenter6_contact (y : ℝ) (hy : (⟨9990234897702,9997004679960⟩ : DyadicInterval 40).Contains y) : (⟨83469795328,83531661312⟩ : DyadicInterval 40).Contains (Reflection.biasContact y) := by
  exact ProvedTranscendental.contact_bracket (Y:=(⟨9990234897702,9997004679960⟩ : DyadicInterval 40)) (c:=(⟨83469795328,83531661312⟩ : DyadicInterval 40)) (elo:=(⟨758952014511,758952033840⟩ : DyadicInterval 40)) (ehi:=(⟨758947307094,758947326423⟩ : DyadicInterval 40))
    (by decide) (by decide) (by decide) (by decide)
    (ew3_ok _ (DyadicContact.point_contains 40 83469795328)) (ew6_ok _ (DyadicContact.point_contains 40 83531661312))
    (by decide) (by decide) hy
theorem brcenter6_jet (y : ℝ) (hy : (⟨9990234897702,9997004679960⟩ : DyadicInterval 40).Contains y) : (⟨⟨83469795328,83531661312⟩,⟨-9117379503,-9103822866⟩,⟨1977558341,1982032840⟩⟩ : DyadicJetEnclosure 40).Contains reflectionContactJet y := by
  exact ProvedTranscendental.contact_jet (c:=(⟨83469795328,83531661312⟩ : DyadicInterval 40)) (B:=(⟨765300867360,765305612224⟩ : DyadicInterval 40)) (by decide) brcenter6_contact bw9_ok (by decide) (by decide) (by decide) hy
theorem brwhole6_contact (y : ℝ) (hy : (⟨9207589767526,10926359482297⟩ : DyadicInterval 40).Contains y) : (⟨76422316032,90564460544⟩ : DyadicInterval 40).Contains (Reflection.biasContact y) := by
  exact ProvedTranscendental.contact_bracket (Y:=(⟨9207589767526,10926359482297⟩ : DyadicInterval 40)) (c:=(⟨76422316032,90564460544⟩ : DyadicInterval 40)) (elo:=(⟨759465348048,759465367378⟩ : DyadicInterval 40)) (ehi:=(⟨758389352531,758389371860⟩ : DyadicInterval 40))
    (by decide) (by decide) (by decide) (by decide)
    (ew17_ok _ (DyadicContact.point_contains 40 76422316032)) (ew20_ok _ (DyadicContact.point_contains 40 90564460544))
    (by decide) (by decide) hy
theorem brwhole6_jet (y : ℝ) (hy : (⟨9207589767526,10926359482297⟩ : DyadicInterval 40).Contains y) : (⟨⟨76422316032,90564460544⟩,⟨-10724470107,-7625839294⟩,⟨1509424700,2534639161⟩⟩ : DyadicJetEnclosure 40).Contains reflectionContactJet y := by
  exact ProvedTranscendental.contact_jet (c:=(⟨76422316032,90564460544⟩ : DyadicInterval 40)) (B:=(⟨764785712672,765865914848⟩ : DyadicInterval 40)) (by decide) brwhole6_contact bw23_ok (by decide) (by decide) (by decide) hy
noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨166246158119,166356109283⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨755761270018,755773553797⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨83123079059,83178054642⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
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
noncomputable def centerStep4 : Instruction 40 := ⟨.inv 6,⟨⟨14534192039208,14543804600364⟩,⟨0,0⟩,⟨-192378367731698,-192124151210534⟩,⟨0,0⟩,⟨0,0⟩,⟨5079290183973602,5089374807770196⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4
theorem centerAccepted4 : StepValid centerStep4.shape centerBoxes4 centerStep4.proposed := by
  dsimp only [StepValid,centerStep4]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep5 : Instruction 40 := ⟨.mul 6 0,⟨⟨9990234897702,9997004679960⟩,⟨0,0⟩,⟨-132235511641058,-132058623894411⟩,⟨0,0⟩,⟨0,0⟩,⟨3491305324341601,3498293958794789⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5
theorem centerAccepted5 : StepValid centerStep5.shape centerBoxes5 centerStep5.proposed := by
  dsimp only [StepValid,centerStep5]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep6 : Instruction 40 := ⟨.contact 0,⟨⟨83469795328,83531661312⟩,⟨0,0⟩,⟨1093429382183,1096524414066⟩,⟨0,0⟩,⟨0,0⟩,⟨-481117038406,-238924551600⟩⟩⟩
noncomputable def centerBoxes7 := centerStep6.proposed :: centerBoxes6
theorem centerAccepted6 : StepValid centerStep6.shape centerBoxes6 centerStep6.proposed := by
  dsimp only [StepValid,centerStep6]
  exact ⟨by decide,by decide,(⟨⟨83469795328,83531661312⟩,⟨-9117379503,-9103822866⟩,⟨1977558341,1982032840⟩⟩ : DyadicJetEnclosure 40),brcenter6_jet,by decide⟩
noncomputable def centerStep7 : Instruction 40 := ⟨.log 10,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes8 := centerStep7.proposed :: centerBoxes7
theorem centerAccepted7 : StepValid centerStep7.shape centerBoxes7 centerStep7.proposed := by
  dsimp only [StepValid,centerStep7]
  exact ⟨by decide,by decide,lc0,by decide⟩
noncomputable def centerStep8 : Instruction 40 := ⟨.add 6 1,⟨⟨1182981423104,1183043289088⟩,⟨0,0⟩,⟨1093429382183,1096524414066⟩,⟨0,0⟩,⟨0,0⟩,⟨-481117038406,-238924551600⟩⟩⟩
noncomputable def centerBoxes9 := centerStep8.proposed :: centerBoxes8
theorem centerAccepted8 : StepValid centerStep8.shape centerBoxes8 centerStep8.proposed := by
  dsimp only [StepValid,centerStep8]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep9 : Instruction 40 := ⟨.log 0,⟨⟨80453217600,80510716992⟩,⟨0,0⟩,⟨1016225129672,1019154924888⟩,⟨0,0⟩,⟨0,0⟩,⟨-1391840989850,-1161302169592⟩⟩⟩
noncomputable def centerBoxes10 := centerStep9.proposed :: centerBoxes9
theorem centerAccepted9 : StepValid centerStep9.shape centerBoxes9 centerStep9.proposed := by
  dsimp only [StepValid,centerStep9]
  exact ⟨by decide,by decide,lc9,by decide⟩
noncomputable def centerStep10 : Instruction 40 := ⟨.mul 1 0,⟨⟨86560850695,86627245253⟩,⟨0,0⟩,⟨1173380371354,1176873739684⟩,⟨0,0⟩,⟨0,0⟩,⟨488396482207,765826709116⟩⟩⟩
noncomputable def centerBoxes11 := centerStep10.proposed :: centerBoxes10
theorem centerAccepted10 : StepValid centerStep10.shape centerBoxes10 centerStep10.proposed := by
  dsimp only [StepValid,centerStep10]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep11 : Instruction 40 := ⟨.neg 4,⟨⟨-83531661312,-83469795328⟩,⟨0,0⟩,⟨-1096524414066,-1093429382183⟩,⟨0,0⟩,⟨0,0⟩,⟨238924551600,481117038406⟩⟩⟩
noncomputable def centerBoxes12 := centerStep11.proposed :: centerBoxes11
theorem centerAccepted11 : StepValid centerStep11.shape centerBoxes11 centerStep11.proposed := by
  dsimp only [StepValid,centerStep11]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep12 : Instruction 40 := ⟨.add 10 0,⟨⟨1015979966464,1016041832448⟩,⟨0,0⟩,⟨-1096524414066,-1093429382183⟩,⟨0,0⟩,⟨0,0⟩,⟨238924551600,481117038406⟩⟩⟩
noncomputable def centerBoxes13 := centerStep12.proposed :: centerBoxes12
theorem centerAccepted12 : StepValid centerStep12.shape centerBoxes12 centerStep12.proposed := by
  dsimp only [StepValid,centerStep12]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep13 : Instruction 40 := ⟨.log 0,⟨⟨-86875135616,-86808185152⟩,⟨0,0⟩,⟨-1186678264536,-1183256713913⟩,⟨0,0⟩,⟨0,0⟩,⟨-1022202598434,-752706870139⟩⟩⟩
noncomputable def centerBoxes14 := centerStep13.proposed :: centerBoxes13
theorem centerAccepted13 : StepValid centerStep13.shape centerBoxes13 centerStep13.proposed := by
  dsimp only [StepValid,centerStep13]
  exact ⟨by decide,by decide,lc10,by decide⟩
noncomputable def centerStep14 : Instruction 40 := ⟨.mul 1 0,⟨⟨-80279980453,-80213228138⟩,⟨0,0⟩,⟨-1010263202413,-1006723695664⟩,⟨0,0⟩,⟨0,0⟩,⟨1370806427175,1652522469174⟩⟩⟩
noncomputable def centerBoxes15 := centerStep14.proposed :: centerBoxes14
theorem centerAccepted14 : StepValid centerStep14.shape centerBoxes14 centerStep14.proposed := by
  dsimp only [StepValid,centerStep14]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep15 : Instruction 40 := ⟨.add 4 0,⟨⟨6280870242,6414017115⟩,⟨0,0⟩,⟨163117168941,170150044020⟩,⟨0,0⟩,⟨0,0⟩,⟨1859202909382,2418349178290⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15
theorem centerAccepted15 : StepValid centerStep15.shape centerBoxes15 centerStep15.proposed := by
  dsimp only [StepValid,centerStep15]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep16 : Instruction 40 := ⟨.mul 0 15,⟨⟨3140435121,3207008558⟩,⟨0,0⟩,⟨81558584470,85075022010⟩,⟨0,0⟩,⟨0,0⟩,⟨929601454691,1209174589145⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16
theorem centerAccepted16 : StepValid centerStep16.shape centerBoxes16 centerStep16.proposed := by
  dsimp only [StepValid,centerStep16]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨-3207008558,-3140435121⟩,⟨0,0⟩,⟨-85075022010,-81558584470⟩,⟨0,0⟩,⟨0,0⟩,⟨-1209174589145,-929601454691⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17
theorem centerAccepted17 : StepValid centerStep17.shape centerBoxes17 centerStep17.proposed := by
  dsimp only [StepValid,centerStep17]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep18 : Instruction 40 := ⟨.add 10 0,⟨⟨758916375058,758982967759⟩,⟨0,0⟩,⟨-85075022010,-81558584470⟩,⟨0,0⟩,⟨0,0⟩,⟨-1209174589145,-929601454691⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18
theorem centerAccepted18 : StepValid centerStep18.shape centerBoxes18 centerStep18.proposed := by
  dsimp only [StepValid,centerStep18]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep19 : Instruction 40 := ⟨.mul 12 12,⟨⟨6336637609,6346034244⟩,⟨0,0⟩,⟨166016119212,166609435794⟩,⟨0,0⟩,⟨0,0⟩,⟨2101659098693,2150814556850⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19
theorem centerAccepted19 : StepValid centerStep19.shape centerBoxes19 centerStep19.proposed := by
  dsimp only [StepValid,centerStep19]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep20 : Instruction 40 := ⟨.neg 0,⟨⟨-6346034244,-6336637609⟩,⟨0,0⟩,⟨-166609435794,-166016119212⟩,⟨0,0⟩,⟨0,0⟩,⟨-2150814556850,-2101659098693⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20
theorem centerAccepted20 : StepValid centerStep20.shape centerBoxes20 centerStep20.proposed := by
  dsimp only [StepValid,centerStep20]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep21 : Instruction 40 := ⟨.add 19 0,⟨⟨1093165593532,1093174990167⟩,⟨0,0⟩,⟨-166609435794,-166016119212⟩,⟨0,0⟩,⟨0,0⟩,⟨-2150814556850,-2101659098693⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21
theorem centerAccepted21 : StepValid centerStep21.shape centerBoxes21 centerStep21.proposed := by
  dsimp only [StepValid,centerStep21]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep22 : Instruction 40 := ⟨.log 0,⟨⟨-6364418688,-6354967488⟩,⟨0,0⟩,⟨-167576635267,-166978439054⟩,⟨0,0⟩,⟨0,0⟩,⟨-2188840809902,-2139199808000⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22
theorem centerAccepted22 : StepValid centerStep22.shape centerBoxes22 centerStep22.proposed := by
  dsimp only [StepValid,centerStep22]
  exact ⟨by decide,by decide,lc7,by decide⟩
noncomputable def centerStep23 : Instruction 40 := ⟨.mul 0 22,⟨⟨-3182209344,-3177483744⟩,⟨0,0⟩,⟨-83788317634,-83489219527⟩,⟨0,0⟩,⟨0,0⟩,⟨-1094420404951,-1069599904000⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23
theorem centerAccepted23 : StepValid centerStep23.shape centerBoxes23 centerStep23.proposed := by
  dsimp only [StepValid,centerStep23]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep24 : Instruction 40 := ⟨.neg 0,⟨⟨3177483744,3182209344⟩,⟨0,0⟩,⟨83489219527,83788317634⟩,⟨0,0⟩,⟨0,0⟩,⟨1069599904000,1094420404951⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24
theorem centerAccepted24 : StepValid centerStep24.shape centerBoxes24 centerStep24.proposed := by
  dsimp only [StepValid,centerStep24]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep25 : Instruction 40 := ⟨.add 17 0,⟨⟨765300867360,765305612224⟩,⟨0,0⟩,⟨83489219527,83788317634⟩,⟨0,0⟩,⟨0,0⟩,⟨1069599904000,1094420404951⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25
theorem centerAccepted25 : StepValid centerStep25.shape centerBoxes25 centerStep25.proposed := by
  dsimp only [StepValid,centerStep25]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep26 : Instruction 40 := ⟨.add 24 26,⟨⟨1265757785895,1265867737059⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26
theorem centerAccepted26 : StepValid centerStep26.shape centerBoxes26 centerStep26.proposed := by
  dsimp only [StepValid,centerStep26]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep27 : Instruction 40 := ⟨.neg 27,⟨⟨-166356109283,-166246158119⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27
theorem centerAccepted27 : StepValid centerStep27.shape centerBoxes27 centerStep27.proposed := by
  dsimp only [StepValid,centerStep27]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep28 : Instruction 40 := ⟨.add 26 0,⟨⟨933155518493,933265469657⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28
theorem centerAccepted28 : StepValid centerStep28.shape centerBoxes28 centerStep28.proposed := by
  dsimp only [StepValid,centerStep28]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep29 : Instruction 40 := ⟨.inv 0,⟨⟨1295371851761,1295524481886⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29
theorem centerAccepted29 : StepValid centerStep29.shape centerBoxes29 centerStep29.proposed := by
  dsimp only [StepValid,centerStep29]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep30 : Instruction 40 := ⟨.mul 3 0,⟨⟨1491232075746,1491537335996⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30
theorem centerAccepted30 : StepValid centerStep30.shape centerBoxes30 centerStep30.proposed := by
  dsimp only [StepValid,centerStep30]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨335061400192,335286450944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31
theorem centerAccepted31 : StepValid centerStep31.shape centerBoxes31 centerStep31.proposed := by
  dsimp only [StepValid,centerStep31]
  exact ⟨by decide,by decide,lc12,by decide⟩
noncomputable def centerStep32 : Instruction 40 := ⟨.mul 0 31,⟨⟨167530700096,167643225472⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32
theorem centerAccepted32 : StepValid centerStep32.shape centerBoxes32 centerStep32.proposed := by
  dsimp only [StepValid,centerStep32]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep33 : Instruction 40 := ⟨.inv 20,⟨⟨1189838627708,1189911080454⟩,⟨0,0⟩,⟨1280463534120,1284244368349⟩,⟨0,0⟩,⟨0,0⟩,⟨2192499831727,2492319080799⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33
theorem centerAccepted33 : StepValid centerStep33.shape centerBoxes33 centerStep33.proposed := by
  dsimp only [StepValid,centerStep33]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep34 : Instruction 40 := ⟨.mul 25 0,⟨⟨1280165627640,1280310533132⟩,⟨0,0⟩,⟨2560927068241,2568488736698⟩,⟨0,0⟩,⟨0,0⟩,⟨4385031368780,4984622418531⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34
theorem centerAccepted34 : StepValid centerStep34.shape centerBoxes34 centerStep34.proposed := by
  dsimp only [StepValid,centerStep34]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨167261402816,167385852608⟩,⟨0,0⟩,⟨2199286045493,2206029572143⟩,⟨0,0⟩,⟨0,0⟩,⟨-660316757101,-117893652797⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35
theorem centerAccepted35 : StepValid centerStep35.shape centerBoxes35 centerStep35.proposed := by
  dsimp only [StepValid,centerStep35]
  exact ⟨by decide,by decide,lc13,by decide⟩
noncomputable def centerStep36 : Instruction 40 := ⟨.mul 0 35,⟨⟨83630701408,83692926304⟩,⟨0,0⟩,⟨1099643022746,1103014786072⟩,⟨0,0⟩,⟨0,0⟩,⟨-330158378551,-58946826398⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36
theorem centerAccepted36 : StepValid centerStep36.shape centerBoxes36 centerStep36.proposed := by
  dsimp only [StepValid,centerStep36]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep37 : Instruction 40 := ⟨.mul 40 11,⟨⟨1530601734720,1530611224448⟩,⟨0,0⟩,⟨166978439054,167576635268⟩,⟨0,0⟩,⟨0,0⟩,⟨2139199808000,2188840809902⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37
theorem centerAccepted37 : StepValid centerStep37.shape centerBoxes37 centerStep37.proposed := by
  dsimp only [StepValid,centerStep37]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep38 : Instruction 40 := ⟨.add 0 17,⟨⟨1524255700476,1524274586839⟩,⟨0,0⟩,⟨369003260,1560516056⟩,⟨0,0⟩,⟨0,0⟩,⟨-11614748850,87181711209⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38
theorem centerAccepted38 : StepValid centerStep38.shape centerBoxes38 centerStep38.proposed := by
  dsimp only [StepValid,centerStep38]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep39 : Instruction 40 := ⟨.mul 20 0,⟨⟨1052087655686,1052193010400⟩,⟨0,0⟩,⟨-117686478379,-111987658050⟩,⟨0,0⟩,⟨0,0⟩,⟨-1684561553443,-1228582799141⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39
theorem centerAccepted39 : StepValid centerStep39.shape centerBoxes39 centerStep39.proposed := by
  dsimp only [StepValid,centerStep39]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep40 : Instruction 40 := ⟨.mul 43 41,⟨⟨1511522540036,1511547107594⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40
theorem centerAccepted40 : StepValid centerStep40.shape centerBoxes40 centerStep40.proposed := by
  dsimp only [StepValid,centerStep40]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep41 : Instruction 40 := ⟨.mul 19 19,⟨⟨1086856186595,1086874871478⟩,⟨0,0⟩,⟨-331298485138,-330115853092⟩,⟨0,0⟩,⟨0,0⟩,⟨-4226704423123,-4128565182197⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41
theorem centerAccepted41 : StepValid centerStep41.shape centerBoxes41 centerStep41.proposed := by
  dsimp only [StepValid,centerStep41]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep42 : Instruction 40 := ⟨.mul 1 0,⟨⟨1494124829892,1494174801610⟩,⟨0,0⟩,⟨-455450633091,-453817440549⟩,⟨0,0⟩,⟨0,0⟩,⟨-5810636908270,-5675628318293⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42
theorem centerAccepted42 : StepValid centerStep42.shape centerBoxes42 centerStep42.proposed := by
  dsimp only [StepValid,centerStep42]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep43 : Instruction 40 := ⟨.mul 17 17,⟨⟨532677784196,532684389420⟩,⟨0,0⟩,⟨116223185830,116640275746⟩,⟨0,0⟩,⟨0,0⟩,⟨1501641571004,1536294003407⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43
theorem centerAccepted43 : StepValid centerStep43.shape centerBoxes43 centerStep43.proposed := by
  dsimp only [StepValid,centerStep43]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep44 : Instruction 40 := ⟨.mul 18 0,⟨⟨370763491690,370770387933⟩,⟨0,0⟩,⟨121343471058,121779691162⟩,⟨0,0⟩,⟨0,0⟩,⟨1581035093971,1617319206127⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44
theorem centerAccepted44 : StepValid centerStep44.shape centerBoxes44 centerStep44.proposed := by
  dsimp only [StepValid,centerStep44]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep45 : Instruction 40 := ⟨.mul 2 0,⟨⟨503829995933,503856218377⟩,⟨0,0⟩,⟨11309280250,12461175207⟩,⟨0,0⟩,⟨0,0⟩,⟨88150423234,183814576491⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45
theorem centerAccepted45 : StepValid centerStep45.shape centerBoxes45 centerStep45.proposed := by
  dsimp only [StepValid,centerStep45]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep46 : Instruction 40 := ⟨.inv 0,⟨⟨2399346828563,2399471705483⟩,⟨0,0⟩,⟨-59345885652,-53854422574⟩,⟨0,0⟩,⟨0,0⟩,⟨-872992542675,-416833840342⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46
theorem centerAccepted46 : StepValid centerStep46.shape centerBoxes46 centerStep46.proposed := by
  dsimp only [StepValid,centerStep46]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep47 : Instruction 40 := ⟨.mul 7 0,⟨⟨2295858557809,2296207964866⟩,⟨0,0⟩,⟨-313619876641,-295910290673⟩,⟨0,0⟩,⟨0,0⟩,⟨-4500682165460,-3067155888914⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47
theorem centerAccepted47 : StepValid centerStep47.shape centerBoxes47 centerStep47.proposed := by
  dsimp only [StepValid,centerStep47]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep48 : Instruction 40 := ⟨.neg 11,⟨⟨-83692926304,-83630701408⟩,⟨0,0⟩,⟨-1103014786072,-1099643022746⟩,⟨0,0⟩,⟨0,0⟩,⟨58946826398,330158378551⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48
theorem centerAccepted48 : StepValid centerStep48.shape centerBoxes48 centerStep48.proposed := by
  dsimp only [StepValid,centerStep48]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep49 : Instruction 40 := ⟨.mul 0 10,⟨⟨-116025149204,-115937449078⟩,⟨0,0⟩,⟨-1529249867848,-1524465920656⟩,⟨0,0⟩,⟨0,0⟩,⟨71951034499,457851051267⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49
theorem centerAccepted49 : StepValid centerStep49.shape centerBoxes49 centerStep49.proposed := by
  dsimp only [StepValid,centerStep49]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep50 : Instruction 40 := ⟨.mul 53 43,⟨⟨166939590656,167063322624⟩,⟨0,0⟩,⟨2186858764366,2193048828132⟩,⟨0,0⟩,⟨0,0⟩,⟨-962234076812,-477849103200⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50
theorem centerAccepted50 : StepValid centerStep50.shape centerBoxes50 centerStep50.proposed := by
  dsimp only [StepValid,centerStep50]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep51 : Instruction 40 := ⟨.inv 29,⟨⟨1105884995987,1105894501957⟩,⟨0,0⟩,⟨167946337027,168549449516⟩,⟨0,0⟩,⟨0,0⟩,⟨2177105114503,2227236079266⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51
theorem centerAccepted51 : StepValid centerStep51.shape centerBoxes51 centerStep51.proposed := by
  dsimp only [StepValid,centerStep51]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep52 : Instruction 40 := ⟨.mul 1 0,⟨⟨167907263442,168033156996⟩,⟨0,0⟩,⟨2225034394187,2231389837669⟩,⟨0,0⟩,⟨0,0⟩,⟨30800492484,530160515685⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52
theorem centerAccepted52 : StepValid centerStep52.shape centerBoxes52 centerStep52.proposed := by
  dsimp only [StepValid,centerStep52]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep53 : Instruction 40 := ⟨.neg 2,⟨⟨-167063322624,-166939590656⟩,⟨0,0⟩,⟨-2193048828132,-2186858764366⟩,⟨0,0⟩,⟨0,0⟩,⟨477849103200,962234076812⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53
theorem centerAccepted53 : StepValid centerStep53.shape centerBoxes53 centerStep53.proposed := by
  dsimp only [StepValid,centerStep53]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep54 : Instruction 40 := ⟨.add 1 0,⟨⟨843940818,1093566340⟩,⟨0,0⟩,⟨31985566055,44531073303⟩,⟨0,0⟩,⟨0,0⟩,⟨508649595684,1492394592497⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54
theorem centerAccepted54 : StepValid centerStep54.shape centerBoxes54 centerStep54.proposed := by
  dsimp only [StepValid,centerStep54]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep55 : Instruction 40 := ⟨.mul 36 0,⟨⟨582513627,754878990⟩,⟨0,0⟩,⟨21992795758,30676797502⟩,⟨0,0⟩,⟨0,0⟩,⟨342991580162,1024727819902⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55
theorem centerAccepted55 : StepValid centerStep55.shape centerBoxes55 centerStep55.proposed := by
  dsimp only [StepValid,centerStep55]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep56 : Instruction 40 := ⟨.add 6 0,⟨⟨-115442635577,-115182570088⟩,⟨0,0⟩,⟨-1507257072090,-1493789123154⟩,⟨0,0⟩,⟨0,0⟩,⟨414942614661,1482578871169⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56
theorem centerAccepted56 : StepValid centerStep56.shape centerBoxes56 centerStep56.proposed := by
  dsimp only [StepValid,centerStep56]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep57 : Instruction 40 := ⟨.mul 0 10,⟨⟨-251931248998,-251350624463⟩,⟨0,0⟩,⟨-3283655684361,-3253505519506⟩,⟨0,0⟩,⟨0,0⟩,⟨1095484131747,3489809045442⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57
theorem centerAccepted57 : StepValid centerStep57.shape centerBoxes57 centerStep57.proposed := by
  dsimp only [StepValid,centerStep57]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep58 : Instruction 40 := ⟨.mul 54 51,⟨⟨333879181312,334126645248⟩,⟨0,0⟩,⟨4373717528732,4386097656264⟩,⟨0,0⟩,⟨0,0⟩,⟨-1924468153624,-955698206400⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58
theorem centerAccepted58 : StepValid centerStep58.shape centerBoxes58 centerStep58.proposed := by
  dsimp only [StepValid,centerStep58]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep59 : Instruction 40 := ⟨.mul 0 7,⟨⟨335814526884,336066313992⟩,⟨0,0⟩,⟨4450068788374,4462779675337⟩,⟨0,0⟩,⟨0,0⟩,⟨61600984970,1060321031370⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59
theorem centerAccepted59 : StepValid centerStep59.shape centerBoxes59 centerStep59.proposed := by
  dsimp only [StepValid,centerStep59]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep60 : Instruction 40 := ⟨.mul 57 53,⟨⟨250409385984,250594983936⟩,⟨0,0⟩,⟨3280288146549,3289573242198⟩,⟨0,0⟩,⟨0,0⟩,⟨-1443351115218,-716773654800⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60
theorem centerAccepted60 : StepValid centerStep60.shape centerBoxes60 centerStep60.proposed := by
  dsimp only [StepValid,centerStep60]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep61 : Instruction 40 := ⟨.mul 39 35,⟨⟨760883792189,760895050115⟩,⟨0,0⟩,⟨-32959718780,-32247941565⟩,⟨0,0⟩,⟨0,0⟩,⟨-459022417970,-399931767011⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61
theorem centerAccepted61 : StepValid centerStep61.shape centerBoxes61 centerStep61.proposed := by
  dsimp only [StepValid,centerStep61]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep62 : Instruction 40 := ⟨.inv 0,⟨⟨1588820717695,1588844225656⟩,⟨0,0⟩,⟨67336747234,68825041880⟩,⟨0,0⟩,⟨0,0⟩,⟨840802972728,964473200538⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62
theorem centerAccepted62 : StepValid centerStep62.shape centerBoxes62 centerStep62.proposed := by
  dsimp only [StepValid,centerStep62]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep63 : Instruction 40 := ⟨.mul 2 0,⟨⟨361847578784,362121130098⟩,⟨0,0⟩,⟨4755430855561,4769268944987⟩,⟨0,0⟩,⟨0,0⟩,⟨-1492432840057,-404109099804⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63
theorem centerAccepted63 : StepValid centerStep63.shape centerBoxes63 centerStep63.proposed := by
  dsimp only [StepValid,centerStep63]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep64 : Instruction 40 := ⟨.neg 0,⟨⟨-362121130098,-361847578784⟩,⟨0,0⟩,⟨-4769268944987,-4755430855561⟩,⟨0,0⟩,⟨0,0⟩,⟨404109099804,1492432840057⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64
theorem centerAccepted64 : StepValid centerStep64.shape centerBoxes64 centerStep64.proposed := by
  dsimp only [StepValid,centerStep64]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep65 : Instruction 40 := ⟨.add 5 0,⟨⟨-26306603214,-25781264792⟩,⟨0,0⟩,⟨-319200156613,-292651180224⟩,⟨0,0⟩,⟨0,0⟩,⟨465710084774,2552753871427⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65
theorem centerAccepted65 : StepValid centerStep65.shape centerBoxes65 centerStep65.proposed := by
  dsimp only [StepValid,centerStep65]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep66 : Instruction 40 := ⟨.mul 18 0,⟨⟨-54938420207,-53833116366⟩,⟨0,0⟩,⟨-659675606988,-603572919239⟩,⟨0,0⟩,⟨0,0⟩,⟨1201875996527,5620919600292⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66
theorem centerAccepted66 : StepValid centerStep66.shape centerBoxes66 centerStep66.proposed := by
  dsimp only [StepValid,centerStep66]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep67 : Instruction 40 := ⟨.add 9 0,⟨⟨-306869669205,-305183740829⟩,⟨0,0⟩,⟨-3943331291349,-3857078438745⟩,⟨0,0⟩,⟨0,0⟩,⟨2297360128274,9110728645734⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67
theorem centerAccepted67 : StepValid centerStep67.shape centerBoxes67 centerStep67.proposed := by
  dsimp only [StepValid,centerStep67]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep68 : Instruction 40 := ⟨.mul 61 29,⟨⟨115714384579,115801584375⟩,⟨0,0⟩,⟨1515851881309,1520251908649⟩,⟨0,0⟩,⟨0,0⟩,⟨-667130476535,-321485812198⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68
theorem centerAccepted68 : StepValid centerStep68.shape centerBoxes68 centerStep68.proposed := by
  dsimp only [StepValid,centerStep68]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep69 : Instruction 40 := ⟨.mul 27 25,⟨⟨526546632695,526562214227⟩,⟨0,0⟩,⟨-45619929304,-44630720768⟩,⟨0,0⟩,⟨0,0⟩,⟨-633659989689,-551308255976⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69
theorem centerAccepted69 : StepValid centerStep69.shape centerBoxes69 centerStep69.proposed := by
  dsimp only [StepValid,centerStep69]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨2295884108185,2295952047832⟩,⟨0,0⟩,⟨194596117570,198920976043⟩,⟨0,0⟩,⟨0,0⟩,⟨2436767696028,2797477718443⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70
theorem centerAccepted70 : StepValid centerStep70.shape centerBoxes70 centerStep70.proposed := by
  dsimp only [StepValid,centerStep70]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep71 : Instruction 40 := ⟨.mul 2 0,⟨⟨241622562173,241811799050⟩,⟨0,0⟩,⟨3185721484119,3195474025302⟩,⟨0,0⟩,⟨0,0⟩,⟨-600059800161,173420787012⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71
theorem centerAccepted71 : StepValid centerStep71.shape centerBoxes71 centerStep71.proposed := by
  dsimp only [StepValid,centerStep71]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep72 : Instruction 40 := ⟨.mul 65 39,⟨⟨12718149490,12736124638⟩,⟨0,0⟩,⟨166603958771,167187763130⟩,⟨0,0⟩,⟨0,0⟩,⟨-73356215715,-36404523961⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72
theorem centerAccepted72 : StepValid centerStep72.shape centerBoxes72 centerStep72.proposed := by
  dsimp only [StepValid,centerStep72]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep73 : Instruction 40 := ⟨.add 54 0,⟨⟨771634524548,771719092397⟩,⟨0,0⟩,⟨81528936761,85629178660⟩,⟨0,0⟩,⟨0,0⟩,⟨-1282530804860,-966005978652⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73
theorem centerAccepted73 : StepValid centerStep73.shape centerBoxes73 centerStep73.proposed := by
  dsimp only [StepValid,centerStep73]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep74 : Instruction 40 := ⟨.mul 0 0,⟨⟨541531189332,541649894849⟩,⟨0,0⟩,⟨114433609914,120201861208⟩,⟨0,0⟩,⟨0,0⟩,⟨-1788260380943,-1342543706068⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74
theorem centerAccepted74 : StepValid centerStep74.shape centerBoxes74 centerStep74.proposed := by
  dsimp only [StepValid,centerStep74]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep75 : Instruction 40 := ⟨.mul 7 0,⟨⟨-151172502281,-150309018987⟩,⟨0,0⟩,⟨-1976142161495,-1931449834437⟩,⟨0,0⟩,⟨0,0⟩,⟨641942417016,4184429840807⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75
theorem centerAccepted75 : StepValid centerStep75.shape centerBoxes75 centerStep75.proposed := by
  dsimp only [StepValid,centerStep75]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep76 : Instruction 40 := ⟨.mul 79 28,⟨⟨4591717115618,4592415929732⟩,⟨0,0⟩,⟨-627239753282,-591820581346⟩,⟨0,0⟩,⟨0,0⟩,⟨-9001364330920,-6134311777828⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76
theorem centerAccepted76 : StepValid centerStep76.shape centerBoxes76 centerStep76.proposed := by
  dsimp only [StepValid,centerStep76]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep77 : Instruction 40 := ⟨.mul 0 3,⟨⟨3222455646545,3223299293680⟩,⟨0,0⟩,⟨-99767092957,-57684145554⟩,⟨0,0⟩,⟨0,0⟩,⟨-11772371781442,-8426990410570⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77
theorem centerAccepted77 : StepValid centerStep77.shape centerBoxes77 centerStep77.proposed := by
  dsimp only [StepValid,centerStep77]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep78 : Instruction 40 := ⟨.add 45 29,⟨⟨83837773792,84012524064⟩,⟨0,0⟩,⟨-1103014786072,-1099643022746⟩,⟨0,0⟩,⟨0,0⟩,⟨58946826398,330158378551⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78
theorem centerAccepted78 : StepValid centerStep78.shape centerBoxes78 centerStep78.proposed := by
  dsimp only [StepValid,centerStep78]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep79 : Instruction 40 := ⟨.mul 1 0,⟨⟨245712278728,246288900122⟩,⟨0,0⟩,⟨-3241192158533,-3227239156492⟩,⟨0,0⟩,⟨0,0⟩,⟨-611370703742,525495406681⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79
theorem centerAccepted79 : StepValid centerStep79.shape centerBoxes79 centerStep79.proposed := by
  dsimp only [StepValid,centerStep79]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep80 : Instruction 40 := ⟨.add 4 0,⟨⟨94539776447,95979881135⟩,⟨0,0⟩,⟨-5217334320028,-5158688990929⟩,⟨0,0⟩,⟨0,0⟩,⟨30571713274,4709925247488⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80
theorem centerAccepted80 : StepValid centerStep80.shape centerBoxes80 centerStep80.proposed := by
  dsimp only [StepValid,centerStep80]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep81 : Instruction 40 := ⟨.mul 81 81,⟨⟨25136419107,25169679335⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81
theorem centerAccepted81 : StepValid centerStep81.shape centerBoxes81 centerStep81.proposed := by
  dsimp only [StepValid,centerStep81]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep82 : Instruction 40 := ⟨.neg 0,⟨⟨-25169679335,-25136419107⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82
theorem centerAccepted82 : StepValid centerStep82.shape centerBoxes82 centerStep82.proposed := by
  dsimp only [StepValid,centerStep82]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep83 : Instruction 40 := ⟨.add 81 0,⟨⟨1074341948441,1074375208669⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83
theorem centerAccepted83 : StepValid centerStep83.shape centerBoxes83 centerStep83.proposed := by
  dsimp only [StepValid,centerStep83]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep84 : Instruction 40 := ⟨.inv 0,⟨⟨1125236146422,1125270982269⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes85 := centerStep84.proposed :: centerBoxes84
theorem centerAccepted84 : StepValid centerStep84.shape centerBoxes84 centerStep84.proposed := by
  dsimp only [StepValid,centerStep84]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep85 : Instruction 40 := ⟨.mul 13 0,⟨⟨247275639365,247476965016⟩,⟨0,0⟩,⟨3260255622411,3270337579367⟩,⟨0,0⟩,⟨0,0⟩,⟨-614117999019,177483688592⟩⟩⟩
noncomputable def centerBoxes86 := centerStep85.proposed :: centerBoxes85
theorem centerAccepted85 : StepValid centerStep85.shape centerBoxes85 centerStep85.proposed := by
  dsimp only [StepValid,centerStep85]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep86 : Instruction 40 := ⟨.add 5 0,⟨⟨341815415812,343456846151⟩,⟨0,0⟩,⟨-1957078697617,-1888351411562⟩,⟨0,0⟩,⟨0,0⟩,⟨-583546285745,4887408936080⟩⟩⟩
noncomputable def centerBoxes87 := centerStep86.proposed :: centerBoxes86
theorem centerAccepted86 : StepValid centerStep86.shape centerBoxes86 centerStep86.proposed := by
  dsimp only [StepValid,centerStep86]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep87 : Instruction 40 := ⟨.mul 0 68,⟨⟨235931398771,237085165635⟩,⟨0,0⟩,⟨-1377528857849,-1328752468508⟩,⟨0,0⟩,⟨0,0⟩,⟨-500384382028,3387599515677⟩⟩⟩
noncomputable def centerBoxes88 := centerStep87.proposed :: centerBoxes87
theorem centerAccepted87 : StepValid centerStep87.shape centerBoxes87 centerStep87.proposed := by
  dsimp only [StepValid,centerStep87]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep88 : Instruction 40 := ⟨.mul 0 69,⟨⟨162847028984,163657753206⟩,⟨0,0⟩,⟨-969240287658,-934646084410⟩,⟨0,0⟩,⟨0,0⟩,⟨-409016356715,2352130430415⟩⟩⟩
noncomputable def centerBoxes89 := centerStep88.proposed :: centerBoxes88
theorem centerAccepted88 : StepValid centerStep88.shape centerBoxes88 centerStep88.proposed := by
  dsimp only [StepValid,centerStep88]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep89 : Instruction 40 := ⟨.mul 90 63,⟨⟨526037870678,526049682132⟩,⟨0,0⟩,⟨57387222643,57593747065⟩,⟨0,0⟩,⟨0,0⟩,⟨735201121513,752273989563⟩⟩⟩
noncomputable def centerBoxes90 := centerStep89.proposed :: centerBoxes89
theorem centerAccepted89 : StepValid centerStep89.shape centerBoxes89 centerStep89.proposed := by
  dsimp only [StepValid,centerStep89]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep90 : Instruction 40 := ⟨.inv 0,⟨⟨2298120996319,2298172597453⟩,⟨0,0⟩,⟨-251617571030,-250704041378⟩,⟨0,0⟩,⟨0,0⟩,⟨-3231861795796,-3156730898252⟩⟩⟩
noncomputable def centerBoxes91 := centerStep90.proposed :: centerBoxes90
theorem centerAccepted90 : StepValid centerStep90.shape centerBoxes90 centerStep90.proposed := by
  dsimp only [StepValid,centerStep90]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep91 : Instruction 40 := ⟨.mul 2 0,⟨⟨340371276703,342073475421⟩,⟨0,0⟩,⟨-2063334828368,-1990662166464⟩,⟨0,0⟩,⟨0,0⟩,⟨-909740558061,4892438688862⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91
theorem centerAccepted91 : StepValid centerStep91.shape centerBoxes91 centerStep91.proposed := by
  dsimp only [StepValid,centerStep91]
  exact ⟨by decide,by decide⟩
noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91]
theorem centerAccepted : Accepted centerProgram centerInitial :=
  ⟨centerAccepted0,⟨centerAccepted1,⟨centerAccepted2,⟨centerAccepted3,⟨centerAccepted4,⟨centerAccepted5,⟨centerAccepted6,⟨centerAccepted7,⟨centerAccepted8,⟨centerAccepted9,⟨centerAccepted10,⟨centerAccepted11,⟨centerAccepted12,⟨centerAccepted13,⟨centerAccepted14,⟨centerAccepted15,⟨centerAccepted16,⟨centerAccepted17,⟨centerAccepted18,⟨centerAccepted19,⟨centerAccepted20,⟨centerAccepted21,⟨centerAccepted22,⟨centerAccepted23,⟨centerAccepted24,⟨centerAccepted25,⟨centerAccepted26,⟨centerAccepted27,⟨centerAccepted28,⟨centerAccepted29,⟨centerAccepted30,⟨centerAccepted31,⟨centerAccepted32,⟨centerAccepted33,⟨centerAccepted34,⟨centerAccepted35,⟨centerAccepted36,⟨centerAccepted37,⟨centerAccepted38,⟨centerAccepted39,⟨centerAccepted40,⟨centerAccepted41,⟨centerAccepted42,⟨centerAccepted43,⟨centerAccepted44,⟨centerAccepted45,⟨centerAccepted46,⟨centerAccepted47,⟨centerAccepted48,⟨centerAccepted49,⟨centerAccepted50,⟨centerAccepted51,⟨centerAccepted52,⟨centerAccepted53,⟨centerAccepted54,⟨centerAccepted55,⟨centerAccepted56,⟨centerAccepted57,⟨centerAccepted58,⟨centerAccepted59,⟨centerAccepted60,⟨centerAccepted61,⟨centerAccepted62,⟨centerAccepted63,⟨centerAccepted64,⟨centerAccepted65,⟨centerAccepted66,⟨centerAccepted67,⟨centerAccepted68,⟨centerAccepted69,⟨centerAccepted70,⟨centerAccepted71,⟨centerAccepted72,⟨centerAccepted73,⟨centerAccepted74,⟨centerAccepted75,⟨centerAccepted76,⟨centerAccepted77,⟨centerAccepted78,⟨centerAccepted79,⟨centerAccepted80,⟨centerAccepted81,⟨centerAccepted82,⟨centerAccepted83,⟨centerAccepted84,⟨centerAccepted85,⟨centerAccepted86,⟨centerAccepted87,⟨centerAccepted88,⟨centerAccepted89,⟨centerAccepted90,⟨centerAccepted91,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
noncomputable def center_output : DyadicBivariateJetEnclosure 40 := ⟨⟨340371276703,342073475421⟩,⟨0,0⟩,⟨-2063334828368,-1990662166464⟩,⟨0,0⟩,⟨0,0⟩,⟨-909740558061,4892438688862⟩⟩
theorem center_output_eq : (finalBoxes centerProgram centerInitial).getD 0 (zeroBox 40)=center_output := rfl
noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨166246158119,166356109283⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨755761270018,755773553797⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨76052944415,90248189286⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
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
noncomputable def wholeStep4 : Instruction 40 := ⟨.inv 6,⟨⟨13395568699816,15895845044708⟩,⟨0,0⟩,⟨-229809201924007,-163200875969314⟩,⟨0,0⟩,⟨0,0⟩,⟨3976617419388450,6644789143378198⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4
theorem wholeAccepted4 : StepValid wholeStep4.shape wholeBoxes4 wholeStep4.proposed := by
  dsimp only [StepValid,wholeStep4]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep5 : Instruction 40 := ⟨.mul 6 0,⟨⟨9207589767526,10926359482297⟩,⟨0,0⟩,⟨-157964420607968,-112177896235715⟩,⟨0,0⟩,⟨0,0⟩,⟨2733371212573471,4567442288246334⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5
theorem wholeAccepted5 : StepValid wholeStep5.shape wholeBoxes5 wholeStep5.proposed := by
  dsimp only [StepValid,wholeStep5]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep6 : Instruction 40 := ⟨.contact 0,⟨⟨76422316032,90564460544⟩,⟨0,0⟩,⟨778027796543,1540761065171⟩,⟨0,0⟩,⟨0,0⟩,⟨-28838325324954,33358327362598⟩⟩⟩
noncomputable def wholeBoxes7 := wholeStep6.proposed :: wholeBoxes6
theorem wholeAccepted6 : StepValid wholeStep6.shape wholeBoxes6 wholeStep6.proposed := by
  dsimp only [StepValid,wholeStep6]
  exact ⟨by decide,by decide,(⟨⟨76422316032,90564460544⟩,⟨-10724470107,-7625839294⟩,⟨1509424700,2534639161⟩⟩ : DyadicJetEnclosure 40),brwhole6_jet,by decide⟩
noncomputable def wholeStep7 : Instruction 40 := ⟨.log 10,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes8 := wholeStep7.proposed :: wholeBoxes7
theorem wholeAccepted7 : StepValid wholeStep7.shape wholeBoxes7 wholeStep7.proposed := by
  dsimp only [StepValid,wholeStep7]
  exact ⟨by decide,by decide,lc0,by decide⟩
noncomputable def wholeStep8 : Instruction 40 := ⟨.add 6 1,⟨⟨1175933943808,1190076088320⟩,⟨0,0⟩,⟨778027796543,1540761065171⟩,⟨0,0⟩,⟨0,0⟩,⟨-28838325324954,33358327362598⟩⟩⟩
noncomputable def wholeBoxes9 := wholeStep8.proposed :: wholeBoxes8
theorem wholeAccepted8 : StepValid wholeStep8.shape wholeBoxes8 wholeStep8.proposed := by
  dsimp only [StepValid,wholeStep8]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep9 : Instruction 40 := ⟨.log 0,⟨⟨73883411328,87027597056⟩,⟨0,0⟩,⟨718820096821,1440629140525⟩,⟨0,0⟩,⟨0,0⟩,⟨-28851739069299,30720477901098⟩⟩⟩
noncomputable def wholeBoxes10 := wholeStep9.proposed :: wholeBoxes9
theorem wholeAccepted9 : StepValid wholeStep9.shape wholeBoxes9 wholeStep9.proposed := by
  dsimp only [StepValid,wholeStep9]
  exact ⟨by decide,by decide,lc23,by decide⟩
noncomputable def wholeStep10 : Instruction 40 := ⟨.mul 1 0,⟨⟨79018728924,94195877210⟩,⟨0,0⟩,⟨821062984922,1681243725594⟩,⟨0,0⟩,⟨0,0⟩,⟨-32493490741118,39928756288808⟩⟩⟩
noncomputable def wholeBoxes11 := wholeStep10.proposed :: wholeBoxes10
theorem wholeAccepted10 : StepValid wholeStep10.shape wholeBoxes10 wholeStep10.proposed := by
  dsimp only [StepValid,wholeStep10]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep11 : Instruction 40 := ⟨.neg 4,⟨⟨-90564460544,-76422316032⟩,⟨0,0⟩,⟨-1540761065171,-778027796543⟩,⟨0,0⟩,⟨0,0⟩,⟨-33358327362598,28838325324954⟩⟩⟩
noncomputable def wholeBoxes12 := wholeStep11.proposed :: wholeBoxes11
theorem wholeAccepted11 : StepValid wholeStep11.shape wholeBoxes11 wholeStep11.proposed := by
  dsimp only [StepValid,wholeStep11]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep12 : Instruction 40 := ⟨.add 10 0,⟨⟨1008947167232,1023089311744⟩,⟨0,0⟩,⟨-1540761065171,-778027796543⟩,⟨0,0⟩,⟨0,0⟩,⟨-33358327362598,28838325324954⟩⟩⟩
noncomputable def wholeBoxes13 := wholeStep12.proposed :: wholeBoxes12
theorem wholeAccepted12 : StepValid wholeStep12.shape wholeBoxes12 wholeStep12.proposed := by
  dsimp only [StepValid,wholeStep12]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep13 : Instruction 40 := ⟨.log 0,⟨⟨-94512620928,-79208069504⟩,⟨0,0⟩,⟨-1679061859531,-836144605570⟩,⟨0,0⟩,⟨0,0⟩,⟨-38916707665931,30791030232670⟩⟩⟩
noncomputable def wholeBoxes14 := wholeStep13.proposed :: wholeBoxes13
theorem wholeAccepted13 : StepValid wholeStep13.shape wholeBoxes13 wholeStep13.proposed := by
  dsimp only [StepValid,wholeStep13]
  exact ⟨by decide,by decide,lc24,by decide⟩
noncomputable def wholeStep14 : Instruction 40 := ⟨.mul 1 0,⟨⟨-87943455853,-72683867390⟩,⟨0,0⟩,⟨-1506308910811,-634831271502⟩,⟨0,0⟩,⟨0,0⟩,⟨-37507348570935,36224103638054⟩⟩⟩
noncomputable def wholeBoxes15 := wholeStep14.proposed :: wholeBoxes14
theorem wholeAccepted14 : StepValid wholeStep14.shape wholeBoxes14 wholeStep14.proposed := by
  dsimp only [StepValid,wholeStep14]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep15 : Instruction 40 := ⟨.add 4 0,⟨⟨-8924726929,21512009820⟩,⟨0,0⟩,⟨-685245925889,1046412454092⟩,⟨0,0⟩,⟨0,0⟩,⟨-70000839312053,76152859926862⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15
theorem wholeAccepted15 : StepValid wholeStep15.shape wholeBoxes15 wholeStep15.proposed := by
  dsimp only [StepValid,wholeStep15]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 0 15,⟨⟨-4462363465,10756004910⟩,⟨0,0⟩,⟨-342622962945,523206227046⟩,⟨0,0⟩,⟨0,0⟩,⟨-35000419656027,38076429963431⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16
theorem wholeAccepted16 : StepValid wholeStep16.shape wholeBoxes16 wholeStep16.proposed := by
  dsimp only [StepValid,wholeStep16]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨-10756004910,4462363465⟩,⟨0,0⟩,⟨-523206227046,342622962945⟩,⟨0,0⟩,⟨0,0⟩,⟨-38076429963431,35000419656027⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17
theorem wholeAccepted17 : StepValid wholeStep17.shape wholeBoxes17 wholeStep17.proposed := by
  dsimp only [StepValid,wholeStep17]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep18 : Instruction 40 := ⟨.add 10 0,⟨⟨751367378706,766585766345⟩,⟨0,0⟩,⟨-523206227046,342622962945⟩,⟨0,0⟩,⟨0,0⟩,⟨-38076429963431,35000419656027⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18
theorem wholeAccepted18 : StepValid wholeStep18.shape wholeBoxes18 wholeStep18.proposed := by
  dsimp only [StepValid,wholeStep18]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep19 : Instruction 40 := ⟨.mul 12 12,⟨⟨5311785924,7459604161⟩,⟨0,0⟩,⟨108154720052,253818497540⟩,⟨0,0⟩,⟨0,0⟩,⟨-3649620564563,9813490727886⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19
theorem wholeAccepted19 : StepValid wholeStep19.shape wholeBoxes19 wholeStep19.proposed := by
  dsimp only [StepValid,wholeStep19]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep20 : Instruction 40 := ⟨.neg 0,⟨⟨-7459604161,-5311785924⟩,⟨0,0⟩,⟨-253818497540,-108154720052⟩,⟨0,0⟩,⟨0,0⟩,⟨-9813490727886,3649620564563⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20
theorem wholeAccepted20 : StepValid wholeStep20.shape wholeBoxes20 wholeStep20.proposed := by
  dsimp only [StepValid,wholeStep20]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep21 : Instruction 40 := ⟨.add 19 0,⟨⟨1092052023615,1094199841852⟩,⟨0,0⟩,⟨-253818497540,-108154720052⟩,⟨0,0⟩,⟨0,0⟩,⟨-9813490727886,3649620564563⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21
theorem wholeAccepted21 : StepValid wholeStep21.shape wholeBoxes21 wholeStep21.proposed := by
  dsimp only [StepValid,wholeStep21]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep22 : Instruction 40 := ⟨.log 0,⟨⟨-7485023936,-5324658112⟩,⟨0,0⟩,⟨-255552284466,-108679756427⟩,⟨0,0⟩,⟨0,0⟩,⟨-9939921200217,3663808138326⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22
theorem wholeAccepted22 : StepValid wholeStep22.shape wholeBoxes22 wholeStep22.proposed := by
  dsimp only [StepValid,wholeStep22]
  exact ⟨by decide,by decide,lc21,by decide⟩
noncomputable def wholeStep23 : Instruction 40 := ⟨.mul 0 22,⟨⟨-3742511968,-2662329056⟩,⟨0,0⟩,⟨-127776142233,-54339878213⟩,⟨0,0⟩,⟨0,0⟩,⟨-4969960600109,1831904069163⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23
theorem wholeAccepted23 : StepValid wholeStep23.shape wholeBoxes23 wholeStep23.proposed := by
  dsimp only [StepValid,wholeStep23]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep24 : Instruction 40 := ⟨.neg 0,⟨⟨2662329056,3742511968⟩,⟨0,0⟩,⟨54339878213,127776142233⟩,⟨0,0⟩,⟨0,0⟩,⟨-1831904069163,4969960600109⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24
theorem wholeAccepted24 : StepValid wholeStep24.shape wholeBoxes24 wholeStep24.proposed := by
  dsimp only [StepValid,wholeStep24]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep25 : Instruction 40 := ⟨.add 17 0,⟨⟨764785712672,765865914848⟩,⟨0,0⟩,⟨54339878213,127776142233⟩,⟨0,0⟩,⟨0,0⟩,⟨-1831904069163,4969960600109⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25
theorem wholeAccepted25 : StepValid wholeStep25.shape wholeBoxes25 wholeStep25.proposed := by
  dsimp only [StepValid,wholeStep25]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep26 : Instruction 40 := ⟨.add 24 26,⟨⟨1265757785895,1265867737059⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26
theorem wholeAccepted26 : StepValid wholeStep26.shape wholeBoxes26 wholeStep26.proposed := by
  dsimp only [StepValid,wholeStep26]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep27 : Instruction 40 := ⟨.neg 27,⟨⟨-166356109283,-166246158119⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27
theorem wholeAccepted27 : StepValid wholeStep27.shape wholeBoxes27 wholeStep27.proposed := by
  dsimp only [StepValid,wholeStep27]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep28 : Instruction 40 := ⟨.add 26 0,⟨⟨933155518493,933265469657⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28
theorem wholeAccepted28 : StepValid wholeStep28.shape wholeBoxes28 wholeStep28.proposed := by
  dsimp only [StepValid,wholeStep28]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep29 : Instruction 40 := ⟨.inv 0,⟨⟨1295371851761,1295524481886⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29
theorem wholeAccepted29 : StepValid wholeStep29.shape wholeBoxes29 wholeStep29.proposed := by
  dsimp only [StepValid,wholeStep29]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep30 : Instruction 40 := ⟨.mul 3 0,⟨⟨1491232075746,1491537335996⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30
theorem wholeAccepted30 : StepValid wholeStep30.shape wholeBoxes30 wholeStep30.proposed := by
  dsimp only [StepValid,wholeStep30]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨335061400192,335286450944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31
theorem wholeAccepted31 : StepValid wholeStep31.shape wholeBoxes31 wholeStep31.proposed := by
  dsimp only [StepValid,wholeStep31]
  exact ⟨by decide,by decide,lc12,by decide⟩
noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 0 31,⟨⟨167530700096,167643225472⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32
theorem wholeAccepted32 : StepValid wholeStep32.shape wholeBoxes32 wholeStep32.proposed := by
  dsimp only [StepValid,wholeStep32]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep33 : Instruction 40 := ⟨.inv 20,⟨⟨1181642507391,1198205276627⟩,⟨0,0⟩,⟨898602600743,1829776720001⟩,⟨0,0⟩,⟨0,0⟩,⟨-32881093664481,45204172034851⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33
theorem wholeAccepted33 : StepValid wholeStep33.shape wholeBoxes33 wholeStep33.proposed := by
  dsimp only [StepValid,wholeStep33]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep34 : Instruction 40 := ⟨.mul 25 0,⟨⟨1263773387006,1296898925478⟩,⟨0,0⟩,⟨1797205201486,3659553440000⟩,⟨0,0⟩,⟨0,0⟩,⟨-65744608308259,90408344069660⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34
theorem wholeAccepted34 : StepValid wholeStep34.shape wholeBoxes34 wholeStep34.proposed := by
  dsimp only [StepValid,wholeStep34]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨153091480832,181540217984⟩,⟨0,0⟩,⟨1523671565850,3183894835198⟩,⟨0,0⟩,⟨0,0⟩,⟨-66419023741379,76545858094320⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35
theorem wholeAccepted35 : StepValid wholeStep35.shape wholeBoxes35 wholeStep35.proposed := by
  dsimp only [StepValid,wholeStep35]
  exact ⟨by decide,by decide,lc27,by decide⟩
noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 0 35,⟨⟨76545740416,90770108992⟩,⟨0,0⟩,⟨761835782925,1591947417599⟩,⟨0,0⟩,⟨0,0⟩,⟨-33209511870690,38272929047160⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36
theorem wholeAccepted36 : StepValid wholeStep36.shape wholeBoxes36 wholeStep36.proposed := by
  dsimp only [StepValid,wholeStep36]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep37 : Instruction 40 := ⟨.mul 40 11,⟨⟨1529571425344,1531731829696⟩,⟨0,0⟩,⟨108679756426,255552284466⟩,⟨0,0⟩,⟨0,0⟩,⟨-3663808138326,9939921200218⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37
theorem wholeAccepted37 : StepValid wholeStep37.shape wholeBoxes37 wholeStep37.proposed := by
  dsimp only [StepValid,wholeStep37]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep38 : Instruction 40 := ⟨.add 0 17,⟨⟨1522111821183,1526420043772⟩,⟨0,0⟩,⟨-145138741114,147397564414⟩,⟨0,0⟩,⟨0,0⟩,⟨-13477298866212,13589541764781⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38
theorem wholeAccepted38 : StepValid wholeStep38.shape wholeBoxes38 wholeStep38.proposed := by
  dsimp only [StepValid,wholeStep38]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep39 : Instruction 40 := ⟨.mul 20 0,⟨⟨1040157411971,1064228744344⟩,⟨0,0⟩,⟨-827543558511,578419924723⟩,⟨0,0⟩,⟨0,0⟩,⟨-62397130039413,58202900961713⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39
theorem wholeAccepted39 : StepValid wholeStep39.shape wholeBoxes39 wholeStep39.proposed := by
  dsimp only [StepValid,wholeStep39]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep40 : Instruction 40 := ⟨.mul 43 41,⟨⟨1511522540036,1511547107594⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40
theorem wholeAccepted40 : StepValid wholeStep40.shape wholeBoxes40 wholeStep40.proposed := by
  dsimp only [StepValid,wholeStep40]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 19 19,⟨⟨1084643028918,1088913717385⟩,⟨0,0⟩,⟨-505184579866,-214841895096⟩,⟨0,0⟩,⟨0,0⟩,⟨-19510885174897,7381164458383⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41
theorem wholeAccepted41 : StepValid wholeStep41.shape wholeBoxes41 wholeStep41.proposed := by
  dsimp only [StepValid,wholeStep41]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep42 : Instruction 40 := ⟨.mul 1 0,⟨⟨1491082353916,1496977692962⟩,⟨0,0⟩,⟨-694499513427,-295347824232⟩,⟨0,0⟩,⟨0,0⟩,⟨-26822474003634,10147212185752⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42
theorem wholeAccepted42 : StepValid wholeStep42.shape wholeBoxes42 wholeStep42.proposed := by
  dsimp only [StepValid,wholeStep42]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep43 : Instruction 40 := ⟨.mul 17 17,⟨⟨531960892028,533464662591⟩,⟨0,0⟩,⟨75594220990,178005197208⟩,⟨0,0⟩,⟨0,0⟩,⟨-2546658040009,6953360142298⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43
theorem wholeAccepted43 : StepValid wholeStep43.shape wholeBoxes43 wholeStep43.proposed := by
  dsimp only [StepValid,wholeStep43]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep44 : Instruction 40 := ⟨.mul 18 0,⟨⟨370015268275,371585339831⟩,⟨0,0⟩,⟨78871444438,185984544998⟩,⟨0,0⟩,⟨0,0⟩,⟨-2655214406558,7296084291804⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44
theorem wholeAccepted44 : StepValid wholeStep44.shape wholeBoxes44 wholeStep44.proposed := by
  dsimp only [StepValid,wholeStep44]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 2 0,⟨⟨501789361082,505910943283⟩,⟨0,0⟩,⟨-127749461791,153824212867⟩,⟨0,0⟩,⟨0,0⟩,⟨-12914794939580,13320497328245⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45
theorem wholeAccepted45 : StepValid wholeStep45.shape wholeBoxes45 wholeStep45.proposed := by
  dsimp only [StepValid,wholeStep45]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep46 : Instruction 40 := ⟨.inv 0,⟨⟨2389602035033,2409229675592⟩,⟨0,0⟩,⟨-738552642218,613360541811⟩,⟨0,0⟩,⟨0,0⟩,⟨-64331449340327,62460315445416⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46
theorem wholeAccepted46 : StepValid wholeStep46.shape wholeBoxes46 wholeStep46.proposed := by
  dsimp only [StepValid,wholeStep46]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep47 : Instruction 40 := ⟨.mul 7 0,⟨⟨2260605714037,2331918469729⟩,⟨0,0⟩,⟨-2528151026190,1861101160866⟩,⟨0,0⟩,⟨0,0⟩,⟨-199913811272250,189100854407739⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47
theorem wholeAccepted47 : StepValid wholeStep47.shape wholeBoxes47 wholeStep47.proposed := by
  dsimp only [StepValid,wholeStep47]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep48 : Instruction 40 := ⟨.neg 11,⟨⟨-90770108992,-76545740416⟩,⟨0,0⟩,⟨-1591947417599,-761835782925⟩,⟨0,0⟩,⟨0,0⟩,⟨-38272929047160,33209511870690⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48
theorem wholeAccepted48 : StepValid wholeStep48.shape wholeBoxes48 wholeStep48.proposed := by
  dsimp only [StepValid,wholeStep48]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep49 : Instruction 40 := ⟨.mul 0 10,⟨⟨-126013504761,-105966297586⟩,⟨0,0⟩,⟨-2222222737912,-1042667455876⟩,⟨0,0⟩,⟨0,0⟩,⟨-54681903350366,47636701254787⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49
theorem wholeAccepted49 : StepValid wholeStep49.shape wholeBoxes49 wholeStep49.proposed := by
  dsimp only [StepValid,wholeStep49]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 53 43,⟨⟨152844632064,181128921088⟩,⟨0,0⟩,⟨1556055593086,3081522130342⟩,⟨0,0⟩,⟨0,0⟩,⟨-57676650649908,66716654725196⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50
theorem wholeAccepted50 : StepValid wholeStep50.shape wholeBoxes50 wholeStep50.proposed := by
  dsimp only [StepValid,wholeStep50]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep51 : Instruction 40 := ⟨.inv 29,⟨⟨1104849199729,1107022187105⟩,⟨0,0⟩,⟨109207341589,257297914567⟩,⟨0,0⟩,⟨0,0⟩,⟨-3678061706555,10067621020953⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51
theorem wholeAccepted51 : StepValid wholeStep51.shape wholeBoxes51 wholeStep51.proposed := by
  dsimp only [StepValid,wholeStep51]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep52 : Instruction 40 := ⟨.mul 1 0,⟨⟨153586615323,182366179043⟩,⟨0,0⟩,⟨1578790518304,3144957610865⟩,⟨0,0⟩,⟨0,0⟩,⟨-58367431762768,70273102027680⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52
theorem wholeAccepted52 : StepValid wholeStep52.shape wholeBoxes52 wholeStep52.proposed := by
  dsimp only [StepValid,wholeStep52]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep53 : Instruction 40 := ⟨.neg 2,⟨⟨-181128921088,-152844632064⟩,⟨0,0⟩,⟨-3081522130342,-1556055593086⟩,⟨0,0⟩,⟨0,0⟩,⟨-66716654725196,57676650649908⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53
theorem wholeAccepted53 : StepValid wholeStep53.shape wholeBoxes53 wholeStep53.proposed := by
  dsimp only [StepValid,wholeStep53]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep54 : Instruction 40 := ⟨.add 1 0,⟨⟨-27542305765,29521546979⟩,⟨0,0⟩,⟨-1502731612038,1588902017779⟩,⟨0,0⟩,⟨0,0⟩,⟨-125084086487964,127949752677588⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54
theorem wholeAccepted54 : StepValid wholeStep54.shape wholeBoxes54 wholeStep54.proposed := by
  dsimp only [StepValid,wholeStep54]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 36 0,⟨⟨-19202652377,20582590619⟩,⟨0,0⟩,⟨-1061760960181,1120897629180⟩,⟨0,0⟩,⟨0,0⟩,⟨-89743846068482,91591254168170⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55
theorem wholeAccepted55 : StepValid wholeStep55.shape wholeBoxes55 wholeStep55.proposed := by
  dsimp only [StepValid,wholeStep55]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep56 : Instruction 40 := ⟨.add 6 0,⟨⟨-145216157138,-85383706967⟩,⟨0,0⟩,⟨-3283983698093,78230173304⟩,⟨0,0⟩,⟨0,0⟩,⟨-144425749418848,139227955422957⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56
theorem wholeAccepted56 : StepValid wholeStep56.shape wholeBoxes56 wholeStep56.proposed := by
  dsimp only [StepValid,wholeStep56]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep57 : Instruction 40 := ⟨.mul 0 10,⟨⟨-318194975219,-185567005180⟩,⟨0,0⟩,⟨-7276813303569,268959621825⟩,⟨0,0⟩,⟨0,0⟩,⟨-328376318468906,317981973610371⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57
theorem wholeAccepted57 : StepValid wholeStep57.shape wholeBoxes57 wholeStep57.proposed := by
  dsimp only [StepValid,wholeStep57]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 54 51,⟨⟨305689264128,362257842176⟩,⟨0,0⟩,⟨3112111186172,6163044260684⟩,⟨0,0⟩,⟨0,0⟩,⟨-115353301299816,133433309450392⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58
theorem wholeAccepted58 : StepValid wholeStep58.shape wholeBoxes58 wholeStep58.proposed := by
  dsimp only [StepValid,wholeStep58]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep59 : Instruction 40 := ⟨.mul 0 7,⟨⟨307173230646,364732358086⟩,⟨0,0⟩,⟨3157581036609,6289915221729⟩,⟨0,0⟩,⟨0,0⟩,⟨-116734863525535,140546204055359⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59
theorem wholeAccepted59 : StepValid wholeStep59.shape wholeBoxes59 wholeStep59.proposed := by
  dsimp only [StepValid,wholeStep59]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 57 53,⟨⟨229266948096,271693381632⟩,⟨0,0⟩,⟨2334083389629,4622283195513⟩,⟨0,0⟩,⟨0,0⟩,⟨-86514975974862,100074982087794⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60
theorem wholeAccepted60 : StepValid wholeStep60.shape wholeBoxes60 wholeStep60.proposed := by
  dsimp only [StepValid,wholeStep60]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 39 35,⟨⟨759597046594,762165985095⟩,⟨0,0⟩,⟨-122826315291,51929828234⟩,⟨0,0⟩,⟨0,0⟩,⟨-8717644135522,7477406931272⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61
theorem wholeAccepted61 : StepValid wholeStep61.shape wholeBoxes61 wholeStep61.proposed := by
  dsimp only [StepValid,wholeStep61]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep62 : Instruction 40 := ⟨.inv 0,⟨⟨1586171310785,1591535703089⟩,⟨0,0⟩,⟨-108805288357,257350218700⟩,⟨0,0⟩,⟨0,0⟩,⟨-15702125826371,18348755710963⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62
theorem wholeAccepted62 : StepValid wholeStep62.shape wholeBoxes62 wholeStep62.proposed := by
  dsimp only [StepValid,wholeStep62]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep63 : Instruction 40 := ⟨.mul 2 0,⟨⟨330743801515,393274346753⟩,⟨0,0⟩,⟨3340296127931,6754316097277⟩,⟨0,0⟩,⟨0,0⟩,⟨-130024722686694,151555681121941⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63
theorem wholeAccepted63 : StepValid wholeStep63.shape wholeBoxes63 wholeStep63.proposed := by
  dsimp only [StepValid,wholeStep63]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep64 : Instruction 40 := ⟨.neg 0,⟨⟨-393274346753,-330743801515⟩,⟨0,0⟩,⟨-6754316097277,-3340296127931⟩,⟨0,0⟩,⟨0,0⟩,⟨-151555681121941,130024722686694⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64
theorem wholeAccepted64 : StepValid wholeStep64.shape wholeBoxes64 wholeStep64.proposed := by
  dsimp only [StepValid,wholeStep64]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep65 : Instruction 40 := ⟨.add 5 0,⟨⟨-86101116107,33988556571⟩,⟨0,0⟩,⟨-3596735060668,2949619093798⟩,⟨0,0⟩,⟨0,0⟩,⟨-268290544647476,270570926742053⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65
theorem wholeAccepted65 : StepValid wholeStep65.shape wholeBoxes65 wholeStep65.proposed := by
  dsimp only [StepValid,wholeStep65]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 18 0,⟨⟨-182609058279,72085224772⟩,⟨0,0⟩,⟨-7773938528620,6453726990490⟩,⟨0,0⟩,⟨0,0⟩,⟨-597381254934688,606040268927567⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66
theorem wholeAccepted66 : StepValid wholeStep66.shape wholeBoxes66 wholeStep66.proposed := by
  dsimp only [StepValid,wholeStep66]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep67 : Instruction 40 := ⟨.add 9 0,⟨⟨-500804033498,-113481780408⟩,⟨0,0⟩,⟨-15050751832189,6722686612315⟩,⟨0,0⟩,⟨0,0⟩,⟨-925757573403594,924022242537938⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67
theorem wholeAccepted67 : StepValid wholeStep67.shape wholeBoxes67 wholeStep67.proposed := by
  dsimp only [StepValid,wholeStep67]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 61 29,⟨⟨105795434714,125728008996⟩,⟨0,0⟩,⟨1065110058819,2151134643507⟩,⟨0,0⟩,⟨0,0⟩,⟨-41552275751156,47842839093071⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68
theorem wholeAccepted68 : StepValid wholeStep68.shape wholeBoxes68 wholeStep68.proposed := by
  dsimp only [StepValid,wholeStep68]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 27 25,⟨⟨524767231759,528322733622⟩,⟨0,0⟩,⟨-170535146592,72345587657⟩,⟨0,0⟩,⟨0,0⟩,⟨-12152040300375,10438014248208⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69
theorem wholeAccepted69 : StepValid wholeStep69.shape wholeBoxes69 wholeStep69.proposed := by
  dsimp only [StepValid,wholeStep69]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨2288233578984,2303737250443⟩,⟨0,0⟩,⟨-317598384778,748652251775⟩,⟨0,0⟩,⟨0,0⟩,⟨-46029485372990,53834251153955⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70
theorem wholeAccepted70 : StepValid wholeStep70.shape wholeBoxes70 wholeStep70.proposed := by
  dsimp only [StepValid,wholeStep70]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 2 0,⟨⟨220174721303,263429954201⟩,⟨0,0⟩,⟨2180322180105,4592744122431⟩,⟨0,0⟩,⟨0,0⟩,⟨-93568009848341,109327363487412⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71
theorem wholeAccepted71 : StepValid wholeStep71.shape wholeBoxes71 wholeStep71.proposed := by
  dsimp only [StepValid,wholeStep71]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 65 39,⟨⟨11644337162,13808419935⟩,⟨0,0⟩,⟨118546760358,234920803130⟩,⟨0,0⟩,⟨0,0⟩,⟨-4396997496485,5086165033770⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72
theorem wholeAccepted72 : StepValid wholeStep72.shape wholeBoxes72 wholeStep72.proposed := by
  dsimp only [StepValid,wholeStep72]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep73 : Instruction 40 := ⟨.add 54 0,⟨⟨763011715868,780394186280⟩,⟨0,0⟩,⟨-404659466688,577543766075⟩,⟨0,0⟩,⟨0,0⟩,⟨-42473427459916,40086584689797⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73
theorem wholeAccepted73 : StepValid wholeStep73.shape wholeBoxes73 wholeStep73.proposed := by
  dsimp only [StepValid,wholeStep73]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 0 0,⟨⟨529495881484,553895993999⟩,⟨0,0⟩,⟨-574425749122,819839983466⟩,⟨0,0⟩,⟨0,0⟩,⟨-60717365001390,57510795962064⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74
theorem wholeAccepted74 : StepValid wholeStep74.shape wholeBoxes74 wholeStep74.proposed := by
  dsimp only [StepValid,wholeStep74]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep75 : Instruction 40 := ⟨.mul 7 0,⟨⟨-252287780253,-54649840739⟩,⟨0,0⟩,⟨-7955468679089,3648296038207⟩,⟨0,0⟩,⟨0,0⟩,⟨-515004527348060,508872106907723⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75
theorem wholeAccepted75 : StepValid wholeStep75.shape wholeBoxes75 wholeStep75.proposed := by
  dsimp only [StepValid,wholeStep75]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep76 : Instruction 40 := ⟨.mul 79 28,⟨⟨4521211428074,4663836939458⟩,⟨0,0⟩,⟨-5056302052380,3722202321732⟩,⟨0,0⟩,⟨0,0⟩,⟨-399827622544500,378201708815478⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76
theorem wholeAccepted76 : StepValid wholeStep76.shape wholeBoxes76 wholeStep76.proposed := by
  dsimp only [StepValid,wholeStep76]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 0 3,⟨⟨3137517787342,3310225323104⟩,⟨0,0⟩,⟨-5305241297169,5091674213339⟩,⟨0,0⟩,⟨0,0⟩,⟨-469256304805020,442381113996563⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77
theorem wholeAccepted77 : StepValid wholeStep77.shape wholeBoxes77 wholeStep77.proposed := by
  dsimp only [StepValid,wholeStep77]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep78 : Instruction 40 := ⟨.add 45 29,⟨⟨76760591104,91097485056⟩,⟨0,0⟩,⟨-1591947417599,-761835782925⟩,⟨0,0⟩,⟨0,0⟩,⟨-38272929047160,33209511870690⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78
theorem wholeAccepted78 : StepValid wholeStep78.shape wholeBoxes78 wholeStep78.proposed := by
  dsimp only [StepValid,wholeStep78]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 1 0,⟨⟨219040630286,274261039434⟩,⟨0,0⟩,⟨-5232321922972,-1752082066014⟩,⟨0,0⟩,⟨0,0⟩,⟨-168849004117914,151996668545668⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79
theorem wholeAccepted79 : StepValid wholeStep79.shape wholeBoxes79 wholeStep79.proposed := by
  dsimp only [StepValid,wholeStep79]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep80 : Instruction 40 := ⟨.add 4 0,⟨⟨-33247149967,219611198695⟩,⟨0,0⟩,⟨-13187790602061,1896213972193⟩,⟨0,0⟩,⟨0,0⟩,⟨-683853531465974,660868775453391⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80
theorem wholeAccepted80 : StepValid wholeStep80.shape wholeBoxes80 wholeStep80.proposed := by
  dsimp only [StepValid,wholeStep80]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep81 : Instruction 40 := ⟨.mul 81 81,⟨⟨25136419107,25169679335⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81
theorem wholeAccepted81 : StepValid wholeStep81.shape wholeBoxes81 wholeStep81.proposed := by
  dsimp only [StepValid,wholeStep81]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep82 : Instruction 40 := ⟨.neg 0,⟨⟨-25169679335,-25136419107⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82
theorem wholeAccepted82 : StepValid wholeStep82.shape wholeBoxes82 wholeStep82.proposed := by
  dsimp only [StepValid,wholeStep82]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep83 : Instruction 40 := ⟨.add 81 0,⟨⟨1074341948441,1074375208669⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83
theorem wholeAccepted83 : StepValid wholeStep83.shape wholeBoxes83 wholeStep83.proposed := by
  dsimp only [StepValid,wholeStep83]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep84 : Instruction 40 := ⟨.inv 0,⟨⟨1125236146422,1125270982269⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes85 := wholeStep84.proposed :: wholeBoxes84
theorem wholeAccepted84 : StepValid wholeStep84.shape wholeBoxes84 wholeStep84.proposed := by
  dsimp only [StepValid,wholeStep84]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep85 : Instruction 40 := ⟨.mul 13 0,⟨⟨225325998088,269601590229⟩,⟨0,0⟩,⟨2231333681174,4700342915347⟩,⟨0,0⟩,⟨0,0⟩,⟨-95760120849262,111888684569167⟩⟩⟩
noncomputable def wholeBoxes86 := wholeStep85.proposed :: wholeBoxes85
theorem wholeAccepted85 : StepValid wholeStep85.shape wholeBoxes85 wholeStep85.proposed := by
  dsimp only [StepValid,wholeStep85]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep86 : Instruction 40 := ⟨.add 5 0,⟨⟨192078848121,489212788924⟩,⟨0,0⟩,⟨-10956456920887,6596556887540⟩,⟨0,0⟩,⟨0,0⟩,⟨-779613652315236,772757460022558⟩⟩⟩
noncomputable def wholeBoxes87 := wholeStep86.proposed :: wholeBoxes86
theorem wholeAccepted86 : StepValid wholeStep86.shape wholeBoxes86 wholeStep86.proposed := by
  dsimp only [StepValid,wholeStep86]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep87 : Instruction 40 := ⟨.mul 0 68,⟨⟨131259894822,341081941500⟩,⟨0,0⟩,⟨-7871697655574,4751602457078⟩,⟨0,0⟩,⟨0,0⟩,⟨-567321033554442,564771194675253⟩⟩⟩
noncomputable def wholeBoxes88 := wholeStep87.proposed :: wholeBoxes87
theorem wholeAccepted87 : StepValid wholeStep87.shape wholeBoxes87 wholeStep87.proposed := by
  dsimp only [StepValid,wholeStep87]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep88 : Instruction 40 := ⟨.mul 0 69,⟨⟨89698372086,237804271375⟩,⟨0,0⟩,⟨-5650497383123,3419130113189⟩,⟨0,0⟩,⟨0,0⟩,⟨-412257086897267,412110796451946⟩⟩⟩
noncomputable def wholeBoxes89 := wholeStep88.proposed :: wholeBoxes88
theorem wholeAccepted88 : StepValid wholeStep88.shape wholeBoxes88 wholeStep88.proposed := by
  dsimp only [StepValid,wholeStep88]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep89 : Instruction 40 := ⟨.mul 90 63,⟨⟨525683773503,526434818491⟩,⟨0,0⟩,⟨37351106012,87829747923⟩,⟨0,0⟩,⟨0,0⟩,⟨-1259199642452,3416211970922⟩⟩⟩
noncomputable def wholeBoxes90 := wholeStep89.proposed :: wholeBoxes89
theorem wholeAccepted89 : StepValid wholeStep89.shape wholeBoxes89 wholeStep89.proposed := by
  dsimp only [StepValid,wholeStep89]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep90 : Instruction 40 := ⟨.inv 0,⟨⟨2296439705640,2299720631586⟩,⟨0,0⟩,⟨-384230774368,-162934820955⟩,⟨0,0⟩,⟨0,0⟩,⟨-14921858577348,5637041374515⟩⟩⟩
noncomputable def wholeBoxes91 := wholeStep90.proposed :: wholeBoxes90
theorem wholeAccepted90 : StepValid wholeStep90.shape wholeBoxes90 wholeStep90.proposed := by
  dsimp only [StepValid,wholeStep90]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 2 0,⟨⟨187343997085,497387544929⟩,⟨0,0⟩,⟨-11901590487496,7138104661120⟩,⟨0,0⟩,⟨0,0⟩,⟨-867887210901106,867132624613825⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91
theorem wholeAccepted91 : StepValid wholeStep91.shape wholeBoxes91 wholeStep91.proposed := by
  dsimp only [StepValid,wholeStep91]
  exact ⟨by decide,by decide⟩
noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91]
theorem wholeAccepted : Accepted wholeProgram wholeInitial :=
  ⟨wholeAccepted0,⟨wholeAccepted1,⟨wholeAccepted2,⟨wholeAccepted3,⟨wholeAccepted4,⟨wholeAccepted5,⟨wholeAccepted6,⟨wholeAccepted7,⟨wholeAccepted8,⟨wholeAccepted9,⟨wholeAccepted10,⟨wholeAccepted11,⟨wholeAccepted12,⟨wholeAccepted13,⟨wholeAccepted14,⟨wholeAccepted15,⟨wholeAccepted16,⟨wholeAccepted17,⟨wholeAccepted18,⟨wholeAccepted19,⟨wholeAccepted20,⟨wholeAccepted21,⟨wholeAccepted22,⟨wholeAccepted23,⟨wholeAccepted24,⟨wholeAccepted25,⟨wholeAccepted26,⟨wholeAccepted27,⟨wholeAccepted28,⟨wholeAccepted29,⟨wholeAccepted30,⟨wholeAccepted31,⟨wholeAccepted32,⟨wholeAccepted33,⟨wholeAccepted34,⟨wholeAccepted35,⟨wholeAccepted36,⟨wholeAccepted37,⟨wholeAccepted38,⟨wholeAccepted39,⟨wholeAccepted40,⟨wholeAccepted41,⟨wholeAccepted42,⟨wholeAccepted43,⟨wholeAccepted44,⟨wholeAccepted45,⟨wholeAccepted46,⟨wholeAccepted47,⟨wholeAccepted48,⟨wholeAccepted49,⟨wholeAccepted50,⟨wholeAccepted51,⟨wholeAccepted52,⟨wholeAccepted53,⟨wholeAccepted54,⟨wholeAccepted55,⟨wholeAccepted56,⟨wholeAccepted57,⟨wholeAccepted58,⟨wholeAccepted59,⟨wholeAccepted60,⟨wholeAccepted61,⟨wholeAccepted62,⟨wholeAccepted63,⟨wholeAccepted64,⟨wholeAccepted65,⟨wholeAccepted66,⟨wholeAccepted67,⟨wholeAccepted68,⟨wholeAccepted69,⟨wholeAccepted70,⟨wholeAccepted71,⟨wholeAccepted72,⟨wholeAccepted73,⟨wholeAccepted74,⟨wholeAccepted75,⟨wholeAccepted76,⟨wholeAccepted77,⟨wholeAccepted78,⟨wholeAccepted79,⟨wholeAccepted80,⟨wholeAccepted81,⟨wholeAccepted82,⟨wholeAccepted83,⟨wholeAccepted84,⟨wholeAccepted85,⟨wholeAccepted86,⟨wholeAccepted87,⟨wholeAccepted88,⟨wholeAccepted89,⟨wholeAccepted90,⟨wholeAccepted91,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
noncomputable def whole_output : DyadicBivariateJetEnclosure 40 := ⟨⟨187343997085,497387544929⟩,⟨0,0⟩,⟨-11901590487496,7138104661120⟩,⟨0,0⟩,⟨0,0⟩,⟨-867887210901106,867132624613825⟩⟩
theorem whole_output_eq : (finalBoxes wholeProgram wholeInitial).getD 0 (zeroBox 40)=whole_output := rfl
open GeneralCK.Reflection GeneralCK.Reflection.SmallRatio GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed
theorem sameShape : shapes centerProgram=shapes wholeProgram := by decide
theorem scalar_program (a e r : ℝ) :
    (evalRealProgram wholeProgram [a,e,r,2]).getD 0 0=ReflectionMidpointKernel.scalarCore a e r := rfl
attribute [local irreducible] wholeProgram centerProgram
noncomputable def reflection_log_0_out : DyadicInterval 64 := ⟨-12786308645202662930,-12786308645202655416⟩
theorem reflection_log_0_checked : DyadicFastLog.check 1 2 1 16 reflection_log_0_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointNextBandFamily.Endpoints0012.sharedTwo_eq]
  decide
theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := DyadicFastLog.check_sound reflection_log_0_checked
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1):ℝ)=((1 / 2):ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [he]
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_0_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_1_out : DyadicInterval 64 := ⟨-2598993845852405361,-2598993845852405314⟩
theorem reflection_log_1_checked : DyadicFastLog.check 10000 11513 0 16 reflection_log_1_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointNextBandFamily.Endpoints0012.sharedTwo_eq]
  decide
theorem reflection_log_1 : Bounds (70445869 / 500000000) (140891739 / 1000000000) (Real.log (11513 / 10000)) := by
  have h := DyadicFastLog.check_sound reflection_log_1_checked
  have he : Real.log (11513 / 10000) = -Real.log (10000 / 11513) := by
    rw [show ((11513 / 10000):ℝ)=((10000 / 11513):ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [he]
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_1_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_2_out : DyadicInterval 64 := ⟨-3026179363400955913,-3026179363400955866⟩
theorem reflection_log_2_checked : DyadicFastLog.check 8487 10000 0 16 reflection_log_2_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointNextBandFamily.Endpoints0012.sharedTwo_eq]
  decide
theorem reflection_log_2 : Bounds (-164049513 / 1000000000) (-20506189 / 125000000) (Real.log (8487 / 10000)) := by
  have h := DyadicFastLog.check_sound reflection_log_2_checked
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_2_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_3_out : DyadicInterval 64 := ⟨-2597391522804821605,-2597391522804821560⟩
theorem reflection_log_3_checked : DyadicFastLog.check 1250 1439 0 16 reflection_log_3_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointNextBandFamily.Endpoints0012.sharedTwo_eq]
  decide
theorem reflection_log_3 : Bounds (35201219 / 250000000) (140804877 / 1000000000) (Real.log (1439 / 1250)) := by
  have h := DyadicFastLog.check_sound reflection_log_3_checked
  have he : Real.log (1439 / 1250) = -Real.log (1250 / 1439) := by
    rw [show ((1439 / 1250):ℝ)=((1250 / 1439):ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [he]
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_3_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_4_out : DyadicInterval 64 := ⟨-3024005962034823511,-3024005962034823464⟩
theorem reflection_log_4_checked : DyadicFastLog.check 1061 1250 0 16 reflection_log_4_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointNextBandFamily.Endpoints0012.sharedTwo_eq]
  decide
theorem reflection_log_4 : Bounds (-40982923 / 250000000) (-163931691 / 1000000000) (Real.log (1061 / 1250)) := by
  have h := DyadicFastLog.check_sound reflection_log_4_checked
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_4_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_5_out : DyadicInterval 64 := ⟨-235721830024356753,-235721830024356710⟩
theorem reflection_log_5_checked : DyadicFastLog.check 2000000 2025721 0 16 reflection_log_5_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointNextBandFamily.Endpoints0012.sharedTwo_eq]
  decide
theorem reflection_log_5 : Bounds (6389253 / 500000000) (12778507 / 1000000000) (Real.log (2025721 / 2000000)) := by
  have h := DyadicFastLog.check_sound reflection_log_5_checked
  have he : Real.log (2025721 / 2000000) = -Real.log (2000000 / 2025721) := by
    rw [show ((2025721 / 2000000):ℝ)=((2000000 / 2025721):ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [he]
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_5_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_6_out : DyadicInterval 64 := ⟨-238773034740393007,-238773034740392960⟩
theorem reflection_log_6_checked : DyadicFastLog.check 1974279 2000000 0 16 reflection_log_6_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointNextBandFamily.Endpoints0012.sharedTwo_eq]
  decide
theorem reflection_log_6 : Bounds (-12943913 / 1000000000) (-1617989 / 125000000) (Real.log (1974279 / 2000000)) := by
  have h := DyadicFastLog.check_sound reflection_log_6_checked
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_6_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_7_out : DyadicInterval 64 := ⟨-225441986863277609,-225441986863277566⟩
theorem reflection_log_7_checked : DyadicFastLog.check 6250000000 6326851369 0 16 reflection_log_7_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointNextBandFamily.Endpoints0012.sharedTwo_eq]
  decide
theorem reflection_log_7 : Bounds (6110617 / 500000000) (2444247 / 200000000) (Real.log (6326851369 / 6250000000)) := by
  have h := DyadicFastLog.check_sound reflection_log_7_checked
  have he : Real.log (6326851369 / 6250000000) = -Real.log (6250000000 / 6326851369) := by
    rw [show ((6326851369 / 6250000000):ℝ)=((6250000000 / 6326851369):ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [he]
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_7_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_8_out : DyadicInterval 64 := ⟨-228231290148883569,-228231290148883522⟩
theorem reflection_log_8_checked : DyadicFastLog.check 6173148631 6250000000 0 16 reflection_log_8_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointNextBandFamily.Endpoints0012.sharedTwo_eq]
  decide
theorem reflection_log_8 : Bounds (-3093111 / 250000000) (-12372443 / 1000000000) (Real.log (6173148631 / 6250000000)) := by
  have h := DyadicFastLog.check_sound reflection_log_8_checked
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_8_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
theorem entropy_bound {a z : ℝ} (ha : Bounds (189 / 1250) (1513 / 10000) a) (hz : Bounds (406621 / 5000000) (17 / 200) z) :
  Bounds (687360870887 / 1000000000000) (343686021459 / 500000000000) ((biasE a+biasE (a*z))/2) := by
  let x0 : ℝ := Real.log (2 / 1)
  have hx0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x0 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x1 : ℝ := (1 / 1)+(1513 / 10000)
  have hx1 : Bounds (11513 / 10000) (11513 / 10000) x1 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1513 / 10000) : ℝ)) <;> norm_num
  let x2 : ℝ := (1 / 1)+(1513 / 10000)
  have hx2 : Bounds (11513 / 10000) (11513 / 10000) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1513 / 10000) : ℝ)) <;> norm_num
  let x3 : ℝ := Real.log x2
  have hx3 : Bounds (70445869 / 500000000) (140891739 / 1000000000) x3 := by
    exact bounds_log hx2 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x4 : ℝ := x1*x3
  have hx4 : Bounds (162208657959 / 1000000000000) (162208659111 / 1000000000000) x4 := by
    apply bounds_mul hx1 hx3 <;> norm_num
  let x5 : ℝ := -(1513 / 10000)
  have hx5 : Bounds (-1513 / 10000) (-1513 / 10000) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1513 / 10000) : ℝ))
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (8487 / 10000) (8487 / 10000) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-(1513 / 10000)
  have hx7 : Bounds (8487 / 10000) (8487 / 10000) x7 := by
    exact hx6
  let x8 : ℝ := -(1513 / 10000)
  have hx8 : Bounds (-1513 / 10000) (-1513 / 10000) x8 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1513 / 10000) : ℝ))
  let x9 : ℝ := (1 / 1)+x8
  have hx9 : Bounds (8487 / 10000) (8487 / 10000) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx8 <;> norm_num
  let x10 : ℝ := (1 / 1)-(1513 / 10000)
  have hx10 : Bounds (8487 / 10000) (8487 / 10000) x10 := by
    exact hx9
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (-164049513 / 1000000000) (-20506189 / 125000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x12 : ℝ := x7*x11
  have hx12 : Bounds (-34807205421 / 250000000000) (-69614410417 / 500000000000) x12 := by
    apply bounds_mul hx7 hx11 <;> norm_num
  let x13 : ℝ := x4+x12
  have hx13 : Bounds (919193451 / 40000000000) (22979838277 / 1000000000000) x13 := by
    apply bounds_add hx4 hx12 <;> norm_num
  let x14 : ℝ := (2 / 1)⁻¹
  have hx14 : Bounds (1 / 2) (1 / 2) x14 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x15 : ℝ := x13*x14
  have hx15 : Bounds (11489918137 / 1000000000000) (11489919139 / 1000000000000) x15 := by
    apply bounds_mul hx13 hx14 <;> norm_num
  let x16 : ℝ := x13/(2 / 1)
  have hx16 : Bounds (11489918137 / 1000000000000) (11489919139 / 1000000000000) x16 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx15
  let x17 : ℝ := -x16
  have hx17 : Bounds (-11489919139 / 1000000000000) (-11489918137 / 1000000000000) x17 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx16
  let x18 : ℝ := x0+x17
  have hx18 : Bounds (681657260861 / 1000000000000) (681657262863 / 1000000000000) x18 := by
    apply bounds_add hx0 hx17 <;> norm_num
  let x19 : ℝ := x0-x16
  have hx19 : Bounds (681657260861 / 1000000000000) (681657262863 / 1000000000000) x19 := by
    exact hx18
  let x20 : ℝ := biasE (1513 / 10000)
  have hx20 : Bounds (681657260861 / 1000000000000) (681657262863 / 1000000000000) x20 := by
    simpa +zetaDelta only [biasE, div_one] using hx19
  let x21 : ℝ := Real.log (2 / 1)
  have hx21 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x21 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x22 : ℝ := (1 / 1)+(189 / 1250)
  have hx22 : Bounds (1439 / 1250) (1439 / 1250) x22 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((189 / 1250) : ℝ)) <;> norm_num
  let x23 : ℝ := (1 / 1)+(189 / 1250)
  have hx23 : Bounds (1439 / 1250) (1439 / 1250) x23 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((189 / 1250) : ℝ)) <;> norm_num
  let x24 : ℝ := Real.log x23
  have hx24 : Bounds (35201219 / 250000000) (140804877 / 1000000000) x24 := by
    exact bounds_log hx23 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x25 : ℝ := x22*x24
  have hx25 : Bounds (162094573251 / 1000000000000) (162094574403 / 1000000000000) x25 := by
    apply bounds_mul hx22 hx24 <;> norm_num
  let x26 : ℝ := -(189 / 1250)
  have hx26 : Bounds (-189 / 1250) (-189 / 1250) x26 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((189 / 1250) : ℝ))
  let x27 : ℝ := (1 / 1)+x26
  have hx27 : Bounds (1061 / 1250) (1061 / 1250) x27 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx26 <;> norm_num
  let x28 : ℝ := (1 / 1)-(189 / 1250)
  have hx28 : Bounds (1061 / 1250) (1061 / 1250) x28 := by
    exact hx27
  let x29 : ℝ := -(189 / 1250)
  have hx29 : Bounds (-189 / 1250) (-189 / 1250) x29 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((189 / 1250) : ℝ))
  let x30 : ℝ := (1 / 1)+x29
  have hx30 : Bounds (1061 / 1250) (1061 / 1250) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx29 <;> norm_num
  let x31 : ℝ := (1 / 1)-(189 / 1250)
  have hx31 : Bounds (1061 / 1250) (1061 / 1250) x31 := by
    exact hx30
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (-40982923 / 250000000) (-163931691 / 1000000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x33 : ℝ := x28*x32
  have hx33 : Bounds (-13914522017 / 100000000000) (-3478630483 / 25000000000) x33 := by
    apply bounds_mul hx28 hx32 <;> norm_num
  let x34 : ℝ := x25+x33
  have hx34 : Bounds (22949353081 / 1000000000000) (22949355083 / 1000000000000) x34 := by
    apply bounds_add hx25 hx33 <;> norm_num
  let x35 : ℝ := (2 / 1)⁻¹
  have hx35 : Bounds (1 / 2) (1 / 2) x35 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x36 : ℝ := x34*x35
  have hx36 : Bounds (573733827 / 50000000000) (5737338771 / 500000000000) x36 := by
    apply bounds_mul hx34 hx35 <;> norm_num
  let x37 : ℝ := x34/(2 / 1)
  have hx37 : Bounds (573733827 / 50000000000) (5737338771 / 500000000000) x37 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx36
  let x38 : ℝ := -x37
  have hx38 : Bounds (-5737338771 / 500000000000) (-573733827 / 50000000000) x38 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx37
  let x39 : ℝ := x21+x38
  have hx39 : Bounds (340836251229 / 500000000000) (34083625223 / 50000000000) x39 := by
    apply bounds_add hx21 hx38 <;> norm_num
  let x40 : ℝ := x21-x37
  have hx40 : Bounds (340836251229 / 500000000000) (34083625223 / 50000000000) x40 := by
    exact hx39
  let x41 : ℝ := biasE (189 / 1250)
  have hx41 : Bounds (340836251229 / 500000000000) (34083625223 / 50000000000) x41 := by
    simpa +zetaDelta only [biasE, div_one] using hx40
  let x42 : ℝ := biasE a
  have hx42 : Bounds (681657260861 / 1000000000000) (34083625223 / 50000000000) x42 := by
    exact bounds_biasE ha (by norm_num) (by norm_num) hx20.1 hx41.2
  let x43 : ℝ := a*z
  have hx43 : Bounds (76851369 / 6250000000) (25721 / 2000000) x43 := by
    apply bounds_mul ha hz <;> norm_num
  let x44 : ℝ := Real.log (2 / 1)
  have hx44 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x44 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x45 : ℝ := (1 / 1)+(25721 / 2000000)
  have hx45 : Bounds (2025721 / 2000000) (2025721 / 2000000) x45 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((25721 / 2000000) : ℝ)) <;> norm_num
  let x46 : ℝ := (1 / 1)+(25721 / 2000000)
  have hx46 : Bounds (2025721 / 2000000) (2025721 / 2000000) x46 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((25721 / 2000000) : ℝ)) <;> norm_num
  let x47 : ℝ := Real.log x46
  have hx47 : Bounds (6389253 / 500000000) (12778507 / 1000000000) x47 := by
    exact bounds_log hx46 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x48 : ℝ := x45*x47
  have hx48 : Bounds (1617855497 / 125000000000) (1294284499 / 100000000000) x48 := by
    apply bounds_mul hx45 hx47 <;> norm_num
  let x49 : ℝ := -(25721 / 2000000)
  have hx49 : Bounds (-25721 / 2000000) (-25721 / 2000000) x49 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((25721 / 2000000) : ℝ))
  let x50 : ℝ := (1 / 1)+x49
  have hx50 : Bounds (1974279 / 2000000) (1974279 / 2000000) x50 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx49 <;> norm_num
  let x51 : ℝ := (1 / 1)-(25721 / 2000000)
  have hx51 : Bounds (1974279 / 2000000) (1974279 / 2000000) x51 := by
    exact hx50
  let x52 : ℝ := -(25721 / 2000000)
  have hx52 : Bounds (-25721 / 2000000) (-25721 / 2000000) x52 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((25721 / 2000000) : ℝ))
  let x53 : ℝ := (1 / 1)+x52
  have hx53 : Bounds (1974279 / 2000000) (1974279 / 2000000) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx52 <;> norm_num
  let x54 : ℝ := (1 / 1)-(25721 / 2000000)
  have hx54 : Bounds (1974279 / 2000000) (1974279 / 2000000) x54 := by
    exact hx53
  let x55 : ℝ := Real.log x54
  have hx55 : Bounds (-12943913 / 1000000000) (-1617989 / 125000000) x55 := by
    exact bounds_log hx54 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x56 : ℝ := x51*x55
  have hx56 : Bounds (-12777447807 / 1000000000000) (-12777446819 / 1000000000000) x56 := by
    apply bounds_mul hx51 hx55 <;> norm_num
  let x57 : ℝ := x48+x56
  have hx57 : Bounds (165396169 / 1000000000000) (165398171 / 1000000000000) x57 := by
    apply bounds_add hx48 hx56 <;> norm_num
  let x58 : ℝ := (2 / 1)⁻¹
  have hx58 : Bounds (1 / 2) (1 / 2) x58 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x59 : ℝ := x57*x58
  have hx59 : Bounds (20674521 / 250000000000) (41349543 / 500000000000) x59 := by
    apply bounds_mul hx57 hx58 <;> norm_num
  let x60 : ℝ := x57/(2 / 1)
  have hx60 : Bounds (20674521 / 250000000000) (41349543 / 500000000000) x60 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx59
  let x61 : ℝ := -x60
  have hx61 : Bounds (-41349543 / 500000000000) (-20674521 / 250000000000) x61 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx60
  let x62 : ℝ := x44+x61
  have hx62 : Bounds (346532240457 / 500000000000) (173266120729 / 250000000000) x62 := by
    apply bounds_add hx44 hx61 <;> norm_num
  let x63 : ℝ := x44-x60
  have hx63 : Bounds (346532240457 / 500000000000) (173266120729 / 250000000000) x63 := by
    exact hx62
  let x64 : ℝ := biasE (25721 / 2000000)
  have hx64 : Bounds (346532240457 / 500000000000) (173266120729 / 250000000000) x64 := by
    simpa +zetaDelta only [biasE, div_one] using hx63
  let x65 : ℝ := Real.log (2 / 1)
  have hx65 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x65 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x66 : ℝ := (1 / 1)+(76851369 / 6250000000)
  have hx66 : Bounds (6326851369 / 6250000000) (6326851369 / 6250000000) x66 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((76851369 / 6250000000) : ℝ)) <;> norm_num
  let x67 : ℝ := (1 / 1)+(76851369 / 6250000000)
  have hx67 : Bounds (6326851369 / 6250000000) (6326851369 / 6250000000) x67 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((76851369 / 6250000000) : ℝ)) <;> norm_num
  let x68 : ℝ := Real.log x67
  have hx68 : Bounds (6110617 / 500000000) (2444247 / 200000000) x68 := by
    exact bounds_log hx67 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x69 : ℝ := x66*x68
  have hx69 : Bounds (1237150897 / 100000000000) (12371509983 / 1000000000000) x69 := by
    apply bounds_mul hx66 hx68 <;> norm_num
  let x70 : ℝ := -(76851369 / 6250000000)
  have hx70 : Bounds (-76851369 / 6250000000) (-76851369 / 6250000000) x70 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((76851369 / 6250000000) : ℝ))
  let x71 : ℝ := (1 / 1)+x70
  have hx71 : Bounds (6173148631 / 6250000000) (6173148631 / 6250000000) x71 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx70 <;> norm_num
  let x72 : ℝ := (1 / 1)-(76851369 / 6250000000)
  have hx72 : Bounds (6173148631 / 6250000000) (6173148631 / 6250000000) x72 := by
    exact hx71
  let x73 : ℝ := -(76851369 / 6250000000)
  have hx73 : Bounds (-76851369 / 6250000000) (-76851369 / 6250000000) x73 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((76851369 / 6250000000) : ℝ))
  let x74 : ℝ := (1 / 1)+x73
  have hx74 : Bounds (6173148631 / 6250000000) (6173148631 / 6250000000) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx73 <;> norm_num
  let x75 : ℝ := (1 / 1)-(76851369 / 6250000000)
  have hx75 : Bounds (6173148631 / 6250000000) (6173148631 / 6250000000) x75 := by
    exact hx74
  let x76 : ℝ := Real.log x75
  have hx76 : Bounds (-3093111 / 250000000) (-12372443 / 1000000000) x76 := by
    exact bounds_log hx75 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x77 : ℝ := x72*x76
  have hx77 : Bounds (-12220309719 / 1000000000000) (-1222030873 / 100000000000) x77 := by
    apply bounds_mul hx72 hx76 <;> norm_num
  let x78 : ℝ := x69+x77
  have hx78 : Bounds (151199251 / 1000000000000) (151201253 / 1000000000000) x78 := by
    apply bounds_add hx69 hx77 <;> norm_num
  let x79 : ℝ := (2 / 1)⁻¹
  have hx79 : Bounds (1 / 2) (1 / 2) x79 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x80 : ℝ := x78*x79
  have hx80 : Bounds (604797 / 8000000000) (75600627 / 1000000000000) x80 := by
    apply bounds_mul hx78 hx79 <;> norm_num
  let x81 : ℝ := x78/(2 / 1)
  have hx81 : Bounds (604797 / 8000000000) (75600627 / 1000000000000) x81 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx80
  let x82 : ℝ := -x81
  have hx82 : Bounds (-75600627 / 1000000000000) (-604797 / 8000000000) x82 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx81
  let x83 : ℝ := x65+x82
  have hx83 : Bounds (693071579373 / 1000000000000) (5544572651 / 8000000000) x83 := by
    apply bounds_add hx65 hx82 <;> norm_num
  let x84 : ℝ := x65-x81
  have hx84 : Bounds (693071579373 / 1000000000000) (5544572651 / 8000000000) x84 := by
    exact hx83
  let x85 : ℝ := biasE (76851369 / 6250000000)
  have hx85 : Bounds (693071579373 / 1000000000000) (5544572651 / 8000000000) x85 := by
    simpa +zetaDelta only [biasE, div_one] using hx84
  let x86 : ℝ := biasE x43
  have hx86 : Bounds (346532240457 / 500000000000) (5544572651 / 8000000000) x86 := by
    exact bounds_biasE hx43 (by norm_num) (by norm_num) hx64.1 hx85.2
  let x87 : ℝ := x42+x86
  have hx87 : Bounds (54988869671 / 40000000000) (274948817167 / 200000000000) x87 := by
    apply bounds_add hx42 hx86 <;> norm_num
  let x88 : ℝ := (2 / 1)⁻¹
  have hx88 : Bounds (1 / 2) (1 / 2) x88 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x89 : ℝ := x87*x88
  have hx89 : Bounds (687360870887 / 1000000000000) (343686021459 / 500000000000) x89 := by
    apply bounds_mul hx87 hx88 <;> norm_num
  let x90 : ℝ := x87/(2 / 1)
  have hx90 : Bounds (687360870887 / 1000000000000) (343686021459 / 500000000000) x90 := by
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

theorem center_inputs_eq : centerInitial=inputBoxes ⟨166246158119,166356109283⟩ ⟨755761270018,755773553797⟩ ⟨83123079059,83178054642⟩ := rfl
theorem whole_inputs_eq : wholeInitial=inputBoxes ⟨166246158119,166356109283⟩ ⟨755761270018,755773553797⟩ ⟨76052944415,90248189286⟩ := rfl
noncomputable def centerUpper : ℝ := (342073475421 / 1099511627776)
noncomputable def secondUpper : ℝ := (867132624613825 / 1099511627776)


theorem center_inputs {a z : ℝ} (ha : Bounds (189/1250) (1513/10000) a)
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

theorem whole_inputs {a z s : ℝ} (ha : Bounds (189/1250) (1513/10000) a)
    (hz : Bounds (406621/5000000) (17/200) z) (hs : s∈Icc (a*(1-z)/2) (a*(1+z)/2)) :
    RegistersContain wholeInitial (inputJets a ((biasE a+biasE (a*z))/2)) s := by
  rw [whole_inputs_eq]
  apply inputs_contain
  · norm_num [DyadicInterval.Contains,DyadicInterval.scale]
    constructor <;> linarith [ha.1,ha.2]
  · have h := entropy_bound ha hz
    norm_num [DyadicInterval.Contains,DyadicInterval.scale]
    constructor <;> linarith [h.1,h.2]
  · have hb : a*z≤(1513/10000:ℝ)*(17/200) :=
      mul_le_mul ha.2 hz.2 (by linarith [hz.1]) (by norm_num)
    norm_num [DyadicInterval.Contains,DyadicInterval.scale]
    constructor <;> nlinarith [ha.1,ha.2,hs.1,hs.2]

theorem curvature_pos {a z : ℝ} (ha : Bounds (189/1250) (1513/10000) a)
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
    have hb : a*z≤(25721/2000000:ℝ) := by
      have h := mul_le_mul ha.2 hz.2 hz0.le (by norm_num : (0:ℝ)≤1513/10000)
      norm_num at h
      exact h
    have hb2 := mul_self_le_mul_self hb0 hb
    have hle : centerUpper+secondUpper*(a*z)^2/24 ≤
        centerUpper+secondUpper*(25721/2000000:ℝ)^2/24 := by
      unfold centerUpper secondUpper
      nlinarith
    apply hle.trans_lt
    exact lt_of_lt_of_le (by norm_num [centerUpper,secondUpper] :
      centerUpper+secondUpper*(25721/2000000:ℝ)^2/24 < 2*(189/1250:ℝ)/(1-(189/1250:ℝ)^2)^2)
      (LowRatioFamily.base_mono (by norm_num) ha.1 ha1)

#print axioms entropy_bound
#print axioms curvature_pos
end GeneralCK.Certificates.ReflectionMidpointNextBandFamily.Cell0012

end


