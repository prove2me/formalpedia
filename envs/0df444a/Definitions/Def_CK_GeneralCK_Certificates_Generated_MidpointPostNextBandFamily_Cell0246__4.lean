-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Cell0246__4
-- name    : CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Cell0246__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T14:58:32.602861+00:00
-- url     : https://prove2.me/theorems/fbd2dcd0-3835-4916-8196-4dbe36ff8b32
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0246 (+3 modules: GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0247, Genera…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0246 (+3 modules: GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0247, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0248, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0249)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0246 (+3 modules: GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0247, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0248, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0249)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0246 (+3 modules: GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0247, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0248, GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0249) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Cell0246 (+3 modules: GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Cell0247, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Cell0248, GeneralCK/Certificates/Generated/MidpointPostNextBandFamily/Cell0249).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointPostNextBandFamily_Cell0246__4_q02

-- ===== source module GeneralCK.Certificates.Generated.MidpointPostNextBandFamily.Cell0249 =====
section

namespace GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily.Endpoints0249
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
noncomputable def out_w1 : DyadicInterval 40 := ⟨100112240064,100112240128⟩
theorem checked_w1 : DyadicFastLog.check 1099511627776 1204323090432 0 16 (lift40 out_w1.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w1 : out_w1.Contains (Real.log ((1204323090432:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w1
#print axioms endpoint_w1
noncomputable def out_w2 : DyadicInterval 40 := ⟨-110149113728,-110149113664⟩
theorem checked_w2 : DyadicFastLog.check 994700165120 1099511627776 0 16 (lift40 out_w2)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w2 : out_w2.Contains (Real.log ((994700165120:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w2
#print axioms endpoint_w2
noncomputable def out_w3 : DyadicInterval 40 := ⟨100321872960,100321873024⟩
theorem checked_w3 : DyadicFastLog.check 1099511627776 1204552728576 0 16 (lift40 out_w3.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w3 : out_w3.Contains (Real.log ((1204552728576:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w3
#print axioms endpoint_w3
noncomputable def out_w4 : DyadicInterval 40 := ⟨-110402978112,-110402978048⟩
theorem checked_w4 : DyadicFastLog.check 994470526976 1099511627776 0 16 (lift40 out_w4)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w4 : out_w4.Contains (Real.log ((994470526976:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w4
#print axioms endpoint_w4
noncomputable def out_w5 : DyadicInterval 40 := ⟨-10081105088,-10081105024⟩
theorem checked_w5 : DyadicFastLog.check 1089476597151 1099511627776 0 16 (lift40 out_w5)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w5 : out_w5.Contains (Real.log ((1089476597151:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w5
#print axioms endpoint_w5
noncomputable def out_w6 : DyadicInterval 40 := ⟨-10036873600,-10036873536⟩
theorem checked_w6 : DyadicFastLog.check 1089520425840 1099511627776 0 16 (lift40 out_w6)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w6 : out_w6.Contains (Real.log ((1089520425840:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w6
#print axioms endpoint_w6
noncomputable def out_w7 : DyadicInterval 40 := ⟨421585241024,421585241088⟩
theorem checked_w7 : DyadicFastLog.check 1099511627776 1613322390912 0 16 (lift40 out_w7.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w7 : out_w7.Contains (Real.log ((1613322390912:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w7
#print axioms endpoint_w7
noncomputable def out_w8 : DyadicInterval 40 := ⟨422497649728,422497649792⟩
theorem checked_w8 : DyadicFastLog.check 1099511627776 1614661731336 0 16 (lift40 out_w8.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w8 : out_w8.Contains (Real.log ((1614661731336:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w8
#print axioms endpoint_w8
noncomputable def out_w9 : DyadicInterval 40 := ⟨210261353728,210261353792⟩
theorem checked_w9 : DyadicFastLog.check 1099511627776 1331222500972 0 16 (lift40 out_w9.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w9 : out_w9.Contains (Real.log ((1331222500972:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w9
#print axioms endpoint_w9
noncomputable def out_w10 : DyadicInterval 40 := ⟨210724851072,210724851136⟩
theorem checked_w10 : DyadicFastLog.check 1099511627776 1331783793902 0 16 (lift40 out_w10.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w10 : out_w10.Contains (Real.log ((1331783793902:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w10
#print axioms endpoint_w10
noncomputable def out_w11 : DyadicInterval 40 := ⟨91929336128,91929336192⟩
theorem checked_w11 : DyadicFastLog.check 1099511627776 1195393417216 0 16 (lift40 out_w11.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w11 : out_w11.Contains (Real.log ((1195393417216:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w11
#print axioms endpoint_w11
noncomputable def out_w12 : DyadicInterval 40 := ⟨-100322563648,-100322563584⟩
theorem checked_w12 : DyadicFastLog.check 1003629838336 1099511627776 0 16 (lift40 out_w12)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w12 : out_w12.Contains (Real.log ((1003629838336:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w12
#print axioms endpoint_w12
noncomputable def out_w13 : DyadicInterval 40 := ⟨108415231040,108415231104⟩
theorem checked_w13 : DyadicFastLog.check 1099511627776 1213451993088 0 16 (lift40 out_w13.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w13 : out_w13.Contains (Real.log ((1213451993088:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w13
#print axioms endpoint_w13
noncomputable def out_w14 : DyadicInterval 40 := ⟨-120286517696,-120286517632⟩
theorem checked_w14 : DyadicFastLog.check 985571262464 1099511627776 0 16 (lift40 out_w14)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w14 : out_w14.Contains (Real.log ((985571262464:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w14
#print axioms endpoint_w14
noncomputable def out_w15 : DyadicInterval 40 := ⟨-11871286656,-11871286592⟩
theorem checked_w15 : DyadicFastLog.check 1087704197532 1099511627776 0 16 (lift40 out_w15)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w15 : out_w15.Contains (Real.log ((1087704197532:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w15
#print axioms endpoint_w15
noncomputable def out_w16 : DyadicInterval 40 := ⟨-8393227520,-8393227456⟩
theorem checked_w16 : DyadicFastLog.check 1091150354176 1099511627776 0 16 (lift40 out_w16)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w16 : out_w16.Contains (Real.log ((1091150354176:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w16
#print axioms endpoint_w16
noncomputable def out_w17 : DyadicInterval 40 := ⟨192251899776,192251899840⟩
theorem checked_w17 : DyadicFastLog.check 1099511627776 1309595342616 0 16 (lift40 out_w17.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w17 : out_w17.Contains (Real.log ((1309595342616:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w17
#print axioms endpoint_w17
noncomputable def out_w18 : DyadicInterval 40 := ⟨228701748672,228701748736⟩
theorem checked_w18 : DyadicFastLog.check 1099511627776 1353737296290 0 16 (lift40 out_w18.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w18 : out_w18.Contains (Real.log ((1353737296290:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w18
#print axioms endpoint_w18
end GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily.Endpoints0249

namespace GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily.Cell0249
open Set GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily.Endpoints0249
open BivariateJetProgram (RegistersContain RegistersSound zeroBox zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
theorem lc0 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc1 : ProvedTranscendental.LogEncloses (⟨1204323090432,1204323090432⟩ : DyadicInterval 40) (⟨100112240064,100112240128⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w1
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w1
theorem lc2 : ProvedTranscendental.LogEncloses (⟨994700165120,994700165120⟩ : DyadicInterval 40) (⟨-110149113728,-110149113664⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w2
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w2
theorem lc3 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc4 : ProvedTranscendental.LogEncloses (⟨1204552728576,1204552728576⟩ : DyadicInterval 40) (⟨100321872960,100321873024⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w3
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w3
theorem lc5 : ProvedTranscendental.LogEncloses (⟨994470526976,994470526976⟩ : DyadicInterval 40) (⟨-110402978112,-110402978048⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w4
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w4
theorem lc6 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc7 : ProvedTranscendental.LogEncloses (⟨1089476597151,1089520425840⟩ : DyadicInterval 40) (⟨-10081105088,-10036873536⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w5
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w6
theorem lc8 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc9 : ProvedTranscendental.LogEncloses (⟨1204323090432,1204552728576⟩ : DyadicInterval 40) (⟨100112240064,100321873024⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w1
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w3
theorem lc10 : ProvedTranscendental.LogEncloses (⟨994470526976,994700165120⟩ : DyadicInterval 40) (⟨-110402978112,-110149113664⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w4
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w2
theorem lc11 : ProvedTranscendental.LogEncloses (⟨1089476597151,1089520425840⟩ : DyadicInterval 40) (⟨-10081105088,-10036873536⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w5
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w6
theorem lc12 : ProvedTranscendental.LogEncloses (⟨1613322390912,1614661731336⟩ : DyadicInterval 40) (⟨421585241024,422497649792⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w7
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
theorem lc13 : ProvedTranscendental.LogEncloses (⟨1331222500972,1331783793902⟩ : DyadicInterval 40) (⟨210261353728,210724851136⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w9
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w10
theorem lc14 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc15 : ProvedTranscendental.LogEncloses (⟨1195393417216,1195393417216⟩ : DyadicInterval 40) (⟨91929336128,91929336192⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w11
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w11
theorem lc16 : ProvedTranscendental.LogEncloses (⟨1003629838336,1003629838336⟩ : DyadicInterval 40) (⟨-100322563648,-100322563584⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w12
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w12
theorem lc17 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc18 : ProvedTranscendental.LogEncloses (⟨1213451993088,1213451993088⟩ : DyadicInterval 40) (⟨108415231040,108415231104⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w13
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w13
theorem lc19 : ProvedTranscendental.LogEncloses (⟨985571262464,985571262464⟩ : DyadicInterval 40) (⟨-120286517696,-120286517632⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w14
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w14
theorem lc20 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc21 : ProvedTranscendental.LogEncloses (⟨1087704197532,1091150354176⟩ : DyadicInterval 40) (⟨-11871286656,-8393227456⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w15
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w16
theorem lc22 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc23 : ProvedTranscendental.LogEncloses (⟨1195393417216,1213451993088⟩ : DyadicInterval 40) (⟨91929336128,108415231104⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w11
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w13
theorem lc24 : ProvedTranscendental.LogEncloses (⟨985571262464,1003629838336⟩ : DyadicInterval 40) (⟨-120286517696,-100322563584⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w14
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w12
theorem lc25 : ProvedTranscendental.LogEncloses (⟨1087704197532,1091150354176⟩ : DyadicInterval 40) (⟨-11871286656,-8393227456⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w15
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w16
theorem lc26 : ProvedTranscendental.LogEncloses (⟨1613322390912,1614661731336⟩ : DyadicInterval 40) (⟨421585241024,422497649792⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w7
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
theorem lc27 : ProvedTranscendental.LogEncloses (⟨1309595342616,1353737296290⟩ : DyadicInterval 40) (⟨192251899776,228701748736⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w17
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w18
theorem ew3_ok (x : ℝ) (hx : (⟨104811462656,104811462656⟩ : DyadicInterval 40).Contains x) : (⟨757120189200,757120208530⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨104811462656,104811462656⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨100112240064,100112240128⟩ : DyadicInterval 40)) (minus:=(⟨-110149113728,-110149113664⟩ : DyadicInterval 40))
    (lc0 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc1 lc2 (by decide) hx
theorem ew6_ok (x : ℝ) (hx : (⟨105041100800,105041100800⟩ : DyadicInterval 40).Contains x) : (⟨757098207961,757098227290⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨105041100800,105041100800⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨100321872960,100321873024⟩ : DyadicInterval 40)) (minus:=(⟨-110402978112,-110402978048⟩ : DyadicInterval 40))
    (lc3 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc4 lc5 (by decide) hx
theorem ew17_ok (x : ℝ) (hx : (⟨95881789440,95881789440⟩ : DyadicInterval 40).Contains x) : (⟨757937431948,757937451278⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨95881789440,95881789440⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨91929336128,91929336192⟩ : DyadicInterval 40)) (minus:=(⟨-100322563648,-100322563584⟩ : DyadicInterval 40))
    (lc14 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc15 lc16 (by decide) hx
theorem ew20_ok (x : ℝ) (hx : (⟨113940365312,113940365312⟩ : DyadicInterval 40).Contains x) : (⟨756209056338,756209075667⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨113940365312,113940365312⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨108415231040,108415231104⟩ : DyadicInterval 40)) (minus:=(⟨-120286517696,-120286517632⟩ : DyadicInterval 40))
    (lc17 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc18 lc19 (by decide) hx
theorem bw9_ok (x : ℝ) (hx : (⟨104811462656,105041100800⟩ : DyadicInterval 40).Contains x) : (⟨767141820384,767163955424⟩ : DyadicInterval 40).Contains (Reflection.biasB x) := by
  exact ProvedTranscendental.denominator_encloses (c:=(⟨104811462656,105041100800⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (gapLog:=(⟨-10081105088,-10036873536⟩ : DyadicInterval 40))
    (lc6 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc7 (by decide) hx
theorem bw23_ok (x : ℝ) (hx : (⟨95881789440,113940365312⟩ : DyadicInterval 40).Contains x) : (⟨766319997344,768059046208⟩ : DyadicInterval 40).Contains (Reflection.biasB x) := by
  exact ProvedTranscendental.denominator_encloses (c:=(⟨95881789440,113940365312⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (gapLog:=(⟨-11871286656,-8393227456⟩ : DyadicInterval 40))
    (lc20 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc21 (by decide) hx
theorem brcenter6_contact (y : ℝ) (hy : (⟨7925053787108,7942257709861⟩ : DyadicInterval 40).Contains y) : (⟨104811462656,105041100800⟩ : DyadicInterval 40).Contains (Reflection.biasContact y) := by
  exact ProvedTranscendental.contact_bracket (Y:=(⟨7925053787108,7942257709861⟩ : DyadicInterval 40)) (c:=(⟨104811462656,105041100800⟩ : DyadicInterval 40)) (elo:=(⟨757120189200,757120208530⟩ : DyadicInterval 40)) (ehi:=(⟨757098207961,757098227290⟩ : DyadicInterval 40))
    (by decide) (by decide) (by decide) (by decide)
    (ew3_ok _ (DyadicContact.point_contains 40 104811462656)) (ew6_ok _ (DyadicContact.point_contains 40 105041100800))
    (by decide) (by decide) hy
theorem brcenter6_jet (y : ℝ) (hy : (⟨7925053787108,7942257709861⟩ : DyadicInterval 40).Contains y) : (⟨⟨104811462656,105041100800⟩,⟨-14382781077,-14319550112⟩,⟨3886732036,3913019887⟩⟩ : DyadicJetEnclosure 40).Contains reflectionContactJet y := by
  exact ProvedTranscendental.contact_jet (c:=(⟨104811462656,105041100800⟩ : DyadicInterval 40)) (B:=(⟨767141820384,767163955424⟩ : DyadicInterval 40)) (by decide) brcenter6_contact bw9_ok (by decide) (by decide) (by decide) hy
theorem brwhole6_contact (y : ℝ) (hy : (⟨7297471258842,8691286953160⟩ : DyadicInterval 40).Contains y) : (⟨95881789440,113940365312⟩ : DyadicInterval 40).Contains (Reflection.biasContact y) := by
  exact ProvedTranscendental.contact_bracket (Y:=(⟨7297471258842,8691286953160⟩ : DyadicInterval 40)) (c:=(⟨95881789440,113940365312⟩ : DyadicInterval 40)) (elo:=(⟨757937431948,757937451278⟩ : DyadicInterval 40)) (ehi:=(⟨756209056338,756209075667⟩ : DyadicInterval 40))
    (by decide) (by decide) (by decide) (by decide)
    (ew17_ok _ (DyadicContact.point_contains 40 95881789440)) (ew20_ok _ (DyadicContact.point_contains 40 113940365312))
    (by decide) (by decide) hy
theorem brwhole6_jet (y : ℝ) (hy : (⟨7297471258842,8691286953160⟩ : DyadicInterval 40).Contains y) : (⟨⟨95881789440,113940365312⟩,⟨-16941234592,-11969545299⟩,⟨2949239280,5021427061⟩⟩ : DyadicJetEnclosure 40).Contains reflectionContactJet y := by
  exact ProvedTranscendental.contact_jet (c:=(⟨95881789440,113940365312⟩ : DyadicInterval 40)) (B:=(⟨766319997344,768059046208⟩ : DyadicInterval 40)) (by decide) brwhole6_contact bw23_ok (by decide) (by decide) (by decide) hy
noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨208247502300,208687306952⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨752087604397,752131805121⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨104123751150,104343653476⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
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
noncomputable def centerStep4 : Instruction 40 := ⟨.inv 6,⟨⟨11586002400162,11610471254278⟩,⟨0,0⟩,⟨-122602653160735,-122086432035357⟩,⟨0,0⟩,⟨0,0⟩,⟨2572949041839566,2589285177638758⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4
theorem centerAccepted4 : StepValid centerStep4.shape centerBoxes4 centerStep4.proposed := by
  dsimp only [StepValid,centerStep4]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep5 : Instruction 40 := ⟨.mul 6 0,⟨⟨7925053787108,7942257709861⟩,⟨0,0⟩,⟨-83867557654601,-83509523573274⟩,⟨0,0⟩,⟨0,0⟩,⟨1759947809762412,1771226138435385⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5
theorem centerAccepted5 : StepValid centerStep5.shape centerBoxes5 centerStep5.proposed := by
  dsimp only [StepValid,centerStep5]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep6 : Instruction 40 := ⟨.contact 0,⟨⟨104811462656,105041100800⟩,⟨0,0⟩,⟨1087590869826,1097076820960⟩,⟨0,0⟩,⟨0,0⟩,⟨-748418802580,-154060826737⟩⟩⟩
noncomputable def centerBoxes7 := centerStep6.proposed :: centerBoxes6
theorem centerAccepted6 : StepValid centerStep6.shape centerBoxes6 centerStep6.proposed := by
  dsimp only [StepValid,centerStep6]
  exact ⟨by decide,by decide,(⟨⟨104811462656,105041100800⟩,⟨-14382781077,-14319550112⟩,⟨3886732036,3913019887⟩⟩ : DyadicJetEnclosure 40),brcenter6_jet,by decide⟩
noncomputable def centerStep7 : Instruction 40 := ⟨.log 10,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes8 := centerStep7.proposed :: centerBoxes7
theorem centerAccepted7 : StepValid centerStep7.shape centerBoxes7 centerStep7.proposed := by
  dsimp only [StepValid,centerStep7]
  exact ⟨by decide,by decide,lc0,by decide⟩
noncomputable def centerStep8 : Instruction 40 := ⟨.add 6 1,⟨⟨1204323090432,1204552728576⟩,⟨0,0⟩,⟨1087590869826,1097076820960⟩,⟨0,0⟩,⟨0,0⟩,⟨-748418802580,-154060826737⟩⟩⟩
noncomputable def centerBoxes9 := centerStep8.proposed :: centerBoxes8
theorem centerAccepted8 : StepValid centerStep8.shape centerBoxes8 centerStep8.proposed := by
  dsimp only [StepValid,centerStep8]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep9 : Instruction 40 := ⟨.log 0,⟨⟨100112240064,100321873024⟩,⟨0,0⟩,⟨992749241495,1001598932042⟩,⟨0,0⟩,⟨0,0⟩,⟨-1595689863788,-1036979662097⟩⟩⟩
noncomputable def centerBoxes10 := centerStep9.proposed :: centerBoxes9
theorem centerAccepted9 : StepValid centerStep9.shape centerBoxes9 centerStep9.proposed := by
  dsimp only [StepValid,centerStep9]
  exact ⟨by decide,by decide,lc9,by decide⟩
noncomputable def centerStep10 : Instruction 40 := ⟨.mul 1 0,⟨⟨109655486397,109906055411⟩,⟨0,0⟩,⟨1186410366055,1197385725446⟩,⟨0,0⟩,⟨0,0⟩,⟨147551569792,848904181696⟩⟩⟩
noncomputable def centerBoxes11 := centerStep10.proposed :: centerBoxes10
theorem centerAccepted10 : StepValid centerStep10.shape centerBoxes10 centerStep10.proposed := by
  dsimp only [StepValid,centerStep10]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep11 : Instruction 40 := ⟨.neg 4,⟨⟨-105041100800,-104811462656⟩,⟨0,0⟩,⟨-1097076820960,-1087590869826⟩,⟨0,0⟩,⟨0,0⟩,⟨154060826737,748418802580⟩⟩⟩
noncomputable def centerBoxes12 := centerStep11.proposed :: centerBoxes11
theorem centerAccepted11 : StepValid centerStep11.shape centerBoxes11 centerStep11.proposed := by
  dsimp only [StepValid,centerStep11]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep12 : Instruction 40 := ⟨.add 10 0,⟨⟨994470526976,994700165120⟩,⟨0,0⟩,⟨-1097076820960,-1087590869826⟩,⟨0,0⟩,⟨0,0⟩,⟨154060826737,748418802580⟩⟩⟩
noncomputable def centerBoxes13 := centerStep12.proposed :: centerBoxes12
theorem centerAccepted12 : StepValid centerStep12.shape centerBoxes12 centerStep12.proposed := by
  dsimp only [StepValid,centerStep12]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep13 : Instruction 40 := ⟨.log 0,⟨⟨-110402978112,-110149113664⟩,⟨0,0⟩,⟨-1212955727183,-1202190217282⟩,⟨0,0⟩,⟨0,0⟩,⟨-1167810425049,-486986859343⟩⟩⟩
noncomputable def centerBoxes14 := centerStep13.proposed :: centerBoxes13
theorem centerAccepted13 : StepValid centerStep13.shape centerBoxes13 centerStep13.proposed := by
  dsimp only [StepValid,centerStep13]
  exact ⟨by decide,by decide,lc10,by decide⟩
noncomputable def centerStep14 : Instruction 40 := ⟨.mul 1 0,⟨⟨-99878762338,-99626092479⟩,⟨0,0⟩,⟨-988375260725,-977181289866⟩,⟨0,0⟩,⟨0,0⟩,⟨1246674692914,1964642691865⟩⟩⟩
noncomputable def centerBoxes15 := centerStep14.proposed :: centerBoxes14
theorem centerAccepted14 : StepValid centerStep14.shape centerBoxes14 centerStep14.proposed := by
  dsimp only [StepValid,centerStep14]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep15 : Instruction 40 := ⟨.add 4 0,⟨⟨9776724059,10279962932⟩,⟨0,0⟩,⟨198035105330,220204435580⟩,⟨0,0⟩,⟨0,0⟩,⟨1394226262706,2813546873561⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15
theorem centerAccepted15 : StepValid centerStep15.shape centerBoxes15 centerStep15.proposed := by
  dsimp only [StepValid,centerStep15]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep16 : Instruction 40 := ⟨.mul 0 15,⟨⟨4888362029,5139981466⟩,⟨0,0⟩,⟨99017552665,110102217790⟩,⟨0,0⟩,⟨0,0⟩,⟨697113131353,1406773436781⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16
theorem centerAccepted16 : StepValid centerStep16.shape centerBoxes16 centerStep16.proposed := by
  dsimp only [StepValid,centerStep16]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨-5139981466,-4888362029⟩,⟨0,0⟩,⟨-110102217790,-99017552665⟩,⟨0,0⟩,⟨0,0⟩,⟨-1406773436781,-697113131353⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17
theorem centerAccepted17 : StepValid centerStep17.shape centerBoxes17 centerStep17.proposed := by
  dsimp only [StepValid,centerStep17]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep18 : Instruction 40 := ⟨.add 10 0,⟨⟨756983402150,757235040851⟩,⟨0,0⟩,⟨-110102217790,-99017552665⟩,⟨0,0⟩,⟨0,0⟩,⟨-1406773436781,-697113131353⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18
theorem centerAccepted18 : StepValid centerStep18.shape centerBoxes18 centerStep18.proposed := by
  dsimp only [StepValid,centerStep18]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep19 : Instruction 40 := ⟨.mul 12 12,⟨⟨9991201936,10035030625⟩,⟨0,0⟩,⟨207350221604,209616986352⟩,⟨0,0⟩,⟨0,0⟩,⟨2008599340563,2159922970351⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19
theorem centerAccepted19 : StepValid centerStep19.shape centerBoxes19 centerStep19.proposed := by
  dsimp only [StepValid,centerStep19]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep20 : Instruction 40 := ⟨.neg 0,⟨⟨-10035030625,-9991201936⟩,⟨0,0⟩,⟨-209616986352,-207350221604⟩,⟨0,0⟩,⟨0,0⟩,⟨-2159922970351,-2008599340563⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20
theorem centerAccepted20 : StepValid centerStep20.shape centerBoxes20 centerStep20.proposed := by
  dsimp only [StepValid,centerStep20]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep21 : Instruction 40 := ⟨.add 19 0,⟨⟨1089476597151,1089520425840⟩,⟨0,0⟩,⟨-209616986352,-207350221604⟩,⟨0,0⟩,⟨0,0⟩,⟨-2159922970351,-2008599340563⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21
theorem centerAccepted21 : StepValid centerStep21.shape centerBoxes21 centerStep21.proposed := by
  dsimp only [StepValid,centerStep21]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep22 : Instruction 40 := ⟨.log 0,⟨⟨-10081105088,-10036873536⟩,⟨0,0⟩,⟨-211547741803,-209251680159⟩,⟨0,0⟩,⟨0,0⟩,⟨-2220519860120,-2066842125521⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22
theorem centerAccepted22 : StepValid centerStep22.shape centerBoxes22 centerStep22.proposed := by
  dsimp only [StepValid,centerStep22]
  exact ⟨by decide,by decide,lc7,by decide⟩
noncomputable def centerStep23 : Instruction 40 := ⟨.mul 0 22,⟨⟨-5040552544,-5018436768⟩,⟨0,0⟩,⟨-105773870902,-104625840079⟩,⟨0,0⟩,⟨0,0⟩,⟨-1110259930060,-1033421062760⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23
theorem centerAccepted23 : StepValid centerStep23.shape centerBoxes23 centerStep23.proposed := by
  dsimp only [StepValid,centerStep23]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep24 : Instruction 40 := ⟨.neg 0,⟨⟨5018436768,5040552544⟩,⟨0,0⟩,⟨104625840079,105773870902⟩,⟨0,0⟩,⟨0,0⟩,⟨1033421062760,1110259930060⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24
theorem centerAccepted24 : StepValid centerStep24.shape centerBoxes24 centerStep24.proposed := by
  dsimp only [StepValid,centerStep24]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep25 : Instruction 40 := ⟨.add 17 0,⟨⟨767141820384,767163955424⟩,⟨0,0⟩,⟨104625840079,105773870902⟩,⟨0,0⟩,⟨0,0⟩,⟨1033421062760,1110259930060⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25
theorem centerAccepted25 : StepValid centerStep25.shape centerBoxes25 centerStep25.proposed := by
  dsimp only [StepValid,centerStep25]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep26 : Instruction 40 := ⟨.add 24 26,⟨⟨1307759130076,1308198934728⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26
theorem centerAccepted26 : StepValid centerStep26.shape centerBoxes26 centerStep26.proposed := by
  dsimp only [StepValid,centerStep26]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep27 : Instruction 40 := ⟨.neg 27,⟨⟨-208687306952,-208247502300⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27
theorem centerAccepted27 : StepValid centerStep27.shape centerBoxes27 centerStep27.proposed := by
  dsimp only [StepValid,centerStep27]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep28 : Instruction 40 := ⟨.add 26 0,⟨⟨890824320824,891264125476⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28
theorem centerAccepted28 : StepValid centerStep28.shape centerBoxes28 centerStep28.proposed := by
  dsimp only [StepValid,centerStep28]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep29 : Instruction 40 := ⟨.inv 0,⟨⟨1356417009344,1357086679556⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29
theorem centerAccepted29 : StepValid centerStep29.shape centerBoxes29 centerStep29.proposed := by
  dsimp only [StepValid,centerStep29]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep30 : Instruction 40 := ⟨.mul 3 0,⟨⟨1613322390912,1614661731336⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30
theorem centerAccepted30 : StepValid centerStep30.shape centerBoxes30 centerStep30.proposed := by
  dsimp only [StepValid,centerStep30]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨421585241024,422497649792⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31
theorem centerAccepted31 : StepValid centerStep31.shape centerBoxes31 centerStep31.proposed := by
  dsimp only [StepValid,centerStep31]
  exact ⟨by decide,by decide,lc12,by decide⟩
noncomputable def centerStep32 : Instruction 40 := ⟨.mul 0 31,⟨⟨210792620512,211248824896⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32
theorem centerAccepted32 : StepValid centerStep32.shape centerBoxes32 centerStep32.proposed := by
  dsimp only [StepValid,centerStep32]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep33 : Instruction 40 := ⟨.inv 20,⟨⟨1215367064374,1215647710839⟩,⟨0,0⟩,⟨1328864887179,1341074360515⟩,⟨0,0⟩,⟨0,0⟩,⟨1991051185879,2770646177430⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33
theorem centerAccepted33 : StepValid centerStep33.shape centerBoxes33 centerStep33.proposed := by
  dsimp only [StepValid,centerStep33]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep34 : Instruction 40 := ⟨.mul 25 0,⟨⟨1331222500972,1331783793902⟩,⟨0,0⟩,⟨2657729774358,2682148721030⟩,⟨0,0⟩,⟨0,0⟩,⟨3982293447130,5541253040452⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34
theorem centerAccepted34 : StepValid centerStep34.shape centerBoxes34 centerStep34.proposed := by
  dsimp only [StepValid,centerStep34]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨210261353728,210724851136⟩,⟨0,0⟩,⟨2194203596537,2215297370684⟩,⟨0,0⟩,⟨0,0⟩,⟨-1175629506929,197960674519⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35
theorem centerAccepted35 : StepValid centerStep35.shape centerBoxes35 centerStep35.proposed := by
  dsimp only [StepValid,centerStep35]
  exact ⟨by decide,by decide,lc13,by decide⟩
noncomputable def centerStep36 : Instruction 40 := ⟨.mul 0 35,⟨⟨105130676864,105362425568⟩,⟨0,0⟩,⟨1097101798268,1107648685342⟩,⟨0,0⟩,⟨0,0⟩,⟨-587814753465,98980337260⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36
theorem centerAccepted36 : StepValid centerStep36.shape centerBoxes36 centerStep36.proposed := by
  dsimp only [StepValid,centerStep36]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep37 : Instruction 40 := ⟨.mul 40 11,⟨⟨1534283640768,1534327910848⟩,⟨0,0⟩,⟨209251680158,211547741804⟩,⟨0,0⟩,⟨0,0⟩,⟨2066842125520,2220519860120⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37
theorem centerAccepted37 : StepValid centerStep37.shape centerBoxes37 centerStep37.proposed := by
  dsimp only [StepValid,centerStep37]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep38 : Instruction 40 := ⟨.add 0 17,⟨⟨1524248610143,1524336708912⟩,⟨0,0⟩,⟨-365306194,4197520200⟩,⟨0,0⟩,⟨0,0⟩,⟨-93080844831,211920519557⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38
theorem centerAccepted38 : StepValid centerStep38.shape centerBoxes38 centerStep38.proposed := by
  dsimp only [StepValid,centerStep38]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep39 : Instruction 40 := ⟨.mul 20 0,⟨⟨1049403089044,1049812608511⟩,⟨0,0⟩,⟨-152894676796,-134376803224⟩,⟨0,0⟩,⟨0,0⟩,⟨-2015262708222,-820382080062⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39
theorem centerAccepted39 : StepValid centerStep39.shape centerBoxes39 centerStep39.proposed := by
  dsimp only [StepValid,centerStep39]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep40 : Instruction 40 := ⟨.mul 43 41,⟨⟨1504175208794,1504263610242⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40
theorem centerAccepted40 : StepValid centerStep40.shape centerBoxes40 centerStep40.proposed := by
  dsimp only [StepValid,centerStep40]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep41 : Instruction 40 := ⟨.mul 19 19,⟨⟨1079533154315,1079620013409⟩,⟨0,0⟩,⟨-415424416558,-410915552222⟩,⟨0,0⟩,⟨0,0⟩,⟨-4202385898751,-3900609396857⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41
theorem centerAccepted41 : StepValid centerStep41.shape centerBoxes41 centerStep41.proposed := by
  dsimp only [StepValid,centerStep41]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep42 : Instruction 40 := ⟨.mul 1 0,⟨⟨1476843870288,1477049499100⟩,⟨0,0⟩,⟨-568350362878,-562148658500⟩,⟨0,0⟩,⟨0,0⟩,⟨-5749367286340,-5336187272351⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42
theorem centerAccepted42 : StepValid centerStep42.shape centerBoxes42 centerStep42.proposed := by
  dsimp only [StepValid,centerStep42]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep43 : Instruction 40 := ⟨.mul 17 17,⟨⟨535243609721,535274497908⟩,⟨0,0⟩,⟨145997287140,147603534392⟩,⟨0,0⟩,⟨0,0⟩,⟨1461971044993,1569677826884⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43
theorem centerAccepted43 : StepValid centerStep43.shape centerBoxes43 centerStep43.proposed := by
  dsimp only [StepValid,centerStep43]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep44 : Instruction 40 := ⟨.mul 18 0,⟨⟨373445579598,373477906626⟩,⟨0,0⟩,⟨152795962041,154481464887⟩,⟨0,0⟩,⟨0,0⟩,⟨1550889761737,1664119983078⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44
theorem centerAccepted44 : StepValid centerStep44.shape centerBoxes44 centerStep44.proposed := by
  dsimp only [StepValid,centerStep44]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep45 : Instruction 40 := ⟨.mul 2 0,⟨⟨501605259264,501718527546⟩,⟨0,0⟩,⟨12177657651,16593584168⟩,⟨0,0⟩,⟨0,0⟩,⟨-29502929162,266867526545⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45
theorem centerAccepted45 : StepValid centerStep45.shape centerBoxes45 centerStep45.proposed := by
  dsimp only [StepValid,centerStep45]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep46 : Instruction 40 := ⟨.inv 0,⟨⟨2409569815026,2410113923823⟩,⟨0,0⟩,⟨-79728885435,-58484817048⟩,⟨0,0⟩,⟨0,0⟩,⟨-1279406535534,147030747679⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46
theorem centerAccepted46 : StepValid centerStep46.shape centerBoxes46 centerStep46.proposed := by
  dsimp only [StepValid,centerStep46]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep47 : Instruction 40 := ⟨.mul 7 0,⟨⟨2299757404357,2301174377115⟩,⟨0,0⟩,⟨-411268027726,-350305014362⟩,⟨0,0⟩,⟨0,0⟩,⟨-5624707973911,-1635301414183⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47
theorem centerAccepted47 : StepValid centerStep47.shape centerBoxes47 centerStep47.proposed := by
  dsimp only [StepValid,centerStep47]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep48 : Instruction 40 := ⟨.neg 11,⟨⟨-105362425568,-105130676864⟩,⟨0,0⟩,⟨-1107648685342,-1097101798268⟩,⟨0,0⟩,⟨0,0⟩,⟨-98980337260,587814753465⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48
theorem centerAccepted48 : StepValid centerStep48.shape centerBoxes48 centerStep48.proposed := by
  dsimp only [StepValid,centerStep48]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep49 : Instruction 40 := ⟨.mul 0 10,⟨⟨-146071955018,-145742240504⟩,⟨0,0⟩,⟨-1536019965493,-1520872867011⟩,⟨0,0⟩,⟨0,0⟩,⟨-165988764800,824587998235⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49
theorem centerAccepted49 : StepValid centerStep49.shape centerBoxes49 centerStep49.proposed := by
  dsimp only [StepValid,centerStep49]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep50 : Instruction 40 := ⟨.mul 53 43,⟨⟨209622925312,210082201600⟩,⟨0,0⟩,⟨2175181739652,2194153641920⟩,⟨0,0⟩,⟨0,0⟩,⟨-1496837605160,-308121653474⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50
theorem centerAccepted50 : StepValid centerStep50.shape centerBoxes50 centerStep50.proposed := by
  dsimp only [StepValid,centerStep50]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep51 : Instruction 40 := ⟨.inv 29,⟨⟨1109594451781,1109639089795⟩,⟨0,0⟩,⟨211170575613,213496281196⟩,⟨0,0⟩,⟨0,0⟩,⟨2125984204152,2282049802149⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51
theorem centerAccepted51 : StepValid centerStep51.shape centerBoxes51 centerStep51.proposed := by
  dsimp only [StepValid,centerStep51]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep52 : Instruction 40 := ⟨.mul 1 0,⟨⟨211545225185,212017242089⟩,⟨0,0⟩,⟨2235388623132,2255156158643⟩,⟨0,0⟩,⟨0,0⟩,⟨-269779529544,977174982176⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52
theorem centerAccepted52 : StepValid centerStep52.shape centerBoxes52 centerStep52.proposed := by
  dsimp only [StepValid,centerStep52]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep53 : Instruction 40 := ⟨.neg 2,⟨⟨-210082201600,-209622925312⟩,⟨0,0⟩,⟨-2194153641920,-2175181739652⟩,⟨0,0⟩,⟨0,0⟩,⟨308121653474,1496837605160⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53
theorem centerAccepted53 : StepValid centerStep53.shape centerBoxes53 centerStep53.proposed := by
  dsimp only [StepValid,centerStep53]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep54 : Instruction 40 := ⟨.add 1 0,⟨⟨1463023585,2394316777⟩,⟨0,0⟩,⟨41234981212,79974418991⟩,⟨0,0⟩,⟨0,0⟩,⟨38342123930,2474012587336⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54
theorem centerAccepted54 : StepValid centerStep54.shape centerBoxes54 centerStep54.proposed := by
  dsimp only [StepValid,centerStep54]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep55 : Instruction 40 := ⟨.mul 36 0,⟨⟨1007251349,1648968976⟩,⟨0,0⟩,⟨28149385596,54946728976⟩,⟨0,0⟩,⟨0,0⟩,⟨7317219917,1695501083158⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55
theorem centerAccepted55 : StepValid centerStep55.shape centerBoxes55 centerStep55.proposed := by
  dsimp only [StepValid,centerStep55]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep56 : Instruction 40 := ⟨.add 6 0,⟨⟨-145064703669,-144093271528⟩,⟨0,0⟩,⟨-1507870579897,-1465926138035⟩,⟨0,0⟩,⟨0,0⟩,⟨-158671544883,2520089081393⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56
theorem centerAccepted56 : StepValid centerStep56.shape centerBoxes56 centerStep56.proposed := by
  dsimp only [StepValid,centerStep56]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep57 : Instruction 40 := ⟨.mul 0 10,⟨⟨-317979776963,-315779104878⟩,⟨0,0⟩,⟨-3297566410138,-3202044832621⟩,⟨0,0⟩,⟨0,0⟩,⟨-211254362060,5911479270909⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57
theorem centerAccepted57 : StepValid centerStep57.shape centerBoxes57 centerStep57.proposed := by
  dsimp only [StepValid,centerStep57]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep58 : Instruction 40 := ⟨.mul 54 51,⟨⟨419245850624,420164403200⟩,⟨0,0⟩,⟨4350363479304,4388307283840⟩,⟨0,0⟩,⟨0,0⟩,⟨-2993675210320,-616243306948⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58
theorem centerAccepted58 : StepValid centerStep58.shape centerBoxes58 centerStep58.proposed := by
  dsimp only [StepValid,centerStep58]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep59 : Instruction 40 := ⟨.mul 0 7,⟨⟨423090450371,424034484178⟩,⟨0,0⟩,⟨4470777246266,4510312317285⟩,⟨0,0⟩,⟨0,0⟩,⟨-539559059088,1954349964352⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59
theorem centerAccepted59 : StepValid centerStep59.shape centerBoxes59 centerStep59.proposed := by
  dsimp only [StepValid,centerStep59]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep60 : Instruction 40 := ⟨.mul 57 53,⟨⟨314434387968,315123302400⟩,⟨0,0⟩,⟨3262772609478,3291230462880⟩,⟨0,0⟩,⟨0,0⟩,⟨-2245256407740,-462182480211⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60
theorem centerAccepted60 : StepValid centerStep60.shape centerBoxes60 centerStep60.proposed := by
  dsimp only [StepValid,centerStep60]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep61 : Instruction 40 := ⟨.mul 39 35,⟨⟨760140264905,760192778583⟩,⟨0,0⟩,⟨-42585445182,-39857908259⟩,⟨0,0⟩,⟨0,0⟩,⟨-523387813313,-340713145306⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61
theorem centerAccepted61 : StepValid centerStep61.shape centerBoxes61 centerStep61.proposed := by
  dsimp only [StepValid,centerStep61]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep62 : Instruction 40 := ⟨.inv 0,⟨⟨1590288481650,1590398345450⟩,⟨0,0⟩,⟨83380918883,89099110631⟩,⟨0,0⟩,⟨0,0⟩,⟨721499840579,1105037848522⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62
theorem centerAccepted62 : StepValid centerStep62.shape centerBoxes62 centerStep62.proposed := by
  dsimp only [StepValid,centerStep62]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep63 : Instruction 40 := ⟨.mul 2 0,⟨⟨454784990706,455812895553⟩,⟨0,0⟩,⟨4742985335990,4786165562694⟩,⟨0,0⟩,⟨0,0⟩,⟨-2546477625058,181636201572⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63
theorem centerAccepted63 : StepValid centerStep63.shape centerBoxes63 centerStep63.proposed := by
  dsimp only [StepValid,centerStep63]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep64 : Instruction 40 := ⟨.neg 0,⟨⟨-455812895553,-454784990706⟩,⟨0,0⟩,⟨-4786165562694,-4742985335990⟩,⟨0,0⟩,⟨0,0⟩,⟨-181636201572,2546477625058⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64
theorem centerAccepted64 : StepValid centerStep64.shape centerBoxes64 centerStep64.proposed := by
  dsimp only [StepValid,centerStep64]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep65 : Instruction 40 := ⟨.add 5 0,⟨⟨-32722445182,-30750506528⟩,⟨0,0⟩,⟨-315388316428,-232673018705⟩,⟨0,0⟩,⟨0,0⟩,⟨-721195260660,4500827589410⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65
theorem centerAccepted65 : StepValid centerStep65.shape centerBoxes65 centerStep65.proposed := by
  dsimp only [StepValid,centerStep65]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep66 : Instruction 40 := ⟨.mul 18 0,⟨⟨-68484998710,-64318287582⟩,⟨0,0⟩,⟨-650280941022,-474423179246⟩,⟨0,0⟩,⟨0,0⟩,⟨-1315399147277,9823144486868⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66
theorem centerAccepted66 : StepValid centerStep66.shape centerBoxes66 centerStep66.proposed := by
  dsimp only [StepValid,centerStep66]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep67 : Instruction 40 := ⟨.add 9 0,⟨⟨-386464775673,-380097392460⟩,⟨0,0⟩,⟨-3947847351160,-3676468011867⟩,⟨0,0⟩,⟨0,0⟩,⟨-1526653509337,15734623757777⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67
theorem centerAccepted67 : StepValid centerStep67.shape centerBoxes67 centerStep67.proposed := by
  dsimp only [StepValid,centerStep67]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep68 : Instruction 40 := ⟨.mul 61 29,⟨⟨145299715114,145626478020⟩,⟨0,0⟩,⟨1507688011380,1521362158045⟩,⟨0,0⟩,⟨0,0⟩,⟨-1047211396084,-184951779501⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68
theorem centerAccepted68 : StepValid centerStep68.shape centerBoxes68 centerStep68.proposed := by
  dsimp only [StepValid,centerStep68]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep69 : Instruction 40 := ⟨.mul 27 25,⟨⟨525518064322,525590676816⟩,⟨0,0⟩,⟨-58896315827,-55101003164⟩,⟨0,0⟩,⟨0,0⟩,⟨-721975095590,-466666978274⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69
theorem centerAccepted69 : StepValid centerStep69.shape centerBoxes69 centerStep69.proposed := by
  dsimp only [StepValid,centerStep69]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨2300127975896,2300445791858⟩,⟨0,0⟩,⟨241136999699,257817553951⟩,⟨0,0⟩,⟨0,0⟩,⟨2092821661116,3218221586400⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70
theorem centerAccepted70 : StepValid centerStep70.shape centerBoxes70 centerStep70.proposed := by
  dsimp only [StepValid,centerStep70]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep71 : Instruction 40 := ⟨.mul 2 0,⟨⟨303960350377,304686017030⟩,⟨0,0⟩,⟨3185880369762,3217206755582⟩,⟨0,0⟩,⟨0,0⟩,⟨-1253145393158,752800818570⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71
theorem centerAccepted71 : StepValid centerStep71.shape centerBoxes71 centerStep71.proposed := by
  dsimp only [StepValid,centerStep71]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep72 : Instruction 40 := ⟨.mul 65 39,⟨⟨20093905616,20181513819⟩,⟨0,0⟩,⟨208507235125,210781026225⟩,⟨0,0⟩,⟨0,0⟩,⟨-143793470284,-29535736199⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72
theorem centerAccepted72 : StepValid centerStep72.shape centerBoxes72 centerStep72.proposed := by
  dsimp only [StepValid,centerStep72]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep73 : Instruction 40 := ⟨.add 54 0,⟨⟨777077307766,777416554670⟩,⟨0,0⟩,⟨98405017335,111763473560⟩,⟨0,0⟩,⟨0,0⟩,⟨-1550566907065,-726648867552⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73
theorem centerAccepted73 : StepValid centerStep73.shape centerBoxes73 centerStep73.proposed := by
  dsimp only [StepValid,centerStep73]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep74 : Instruction 40 := ⟨.mul 0 0,⟨⟨549197595541,549677224149⟩,⟨0,0⟩,⟨139095038214,158046122222⟩,⟨0,0⟩,⟨0,0⟩,⟨-2175061736560,-1004393692102⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74
theorem centerAccepted74 : StepValid centerStep74.shape centerBoxes74 centerStep74.proposed := by
  dsimp only [StepValid,centerStep74]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep75 : Instruction 40 := ⟨.mul 7 0,⟨⟨-193204764513,-189855722065⟩,⟨0,0⟩,⟨-2029192758092,-1884452152380⟩,⟨0,0⟩,⟨0,0⟩,⟨-1550946007984,7700502591519⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75
theorem centerAccepted75 : StepValid centerStep75.shape centerBoxes75 centerStep75.proposed := by
  dsimp only [StepValid,centerStep75]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep76 : Instruction 40 := ⟨.mul 79 28,⟨⟨4599514808714,4602348754230⟩,⟨0,0⟩,⟨-822536055452,-700610028724⟩,⟨0,0⟩,⟨0,0⟩,⟨-11249415947822,-3270602828366⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76
theorem centerAccepted76 : StepValid centerStep76.shape centerBoxes76 centerStep76.proposed := by
  dsimp only [StepValid,centerStep76]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep77 : Instruction 40 := ⟨.mul 0 3,⟨⟨3250696485870,3254119394027⟩,⟨0,0⟩,⟨-169927999958,-27333655094⟩,⟨0,0⟩,⟨0,0⟩,⟨-14611569744974,-5476641082825⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77
theorem centerAccepted77 : StepValid centerStep77.shape centerBoxes77 centerStep77.proposed := by
  dsimp only [StepValid,centerStep77]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep78 : Instruction 40 := ⟨.add 45 29,⟨⟨105430194944,106118148032⟩,⟨0,0⟩,⟨-1107648685342,-1097101798268⟩,⟨0,0⟩,⟨0,0⟩,⟨-98980337260,587814753465⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78
theorem centerAccepted78 : StepValid centerStep78.shape centerBoxes78 centerStep78.proposed := by
  dsimp only [StepValid,centerStep78]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep79 : Instruction 40 := ⟨.mul 1 0,⟨⟨311703446831,314067732297⟩,⟨0,0⟩,⟨-3294602277852,-3246192821148⟩,⟨0,0⟩,⟨0,0⟩,⟨-1648614626875,1556924966152⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79
theorem centerAccepted79 : StepValid centerStep79.shape centerBoxes79 centerStep79.proposed := by
  dsimp only [StepValid,centerStep79]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep80 : Instruction 40 := ⟨.add 4 0,⟨⟨118498682318,124212010232⟩,⟨0,0⟩,⟨-5323795035944,-5130644973528⟩,⟨0,0⟩,⟨0,0⟩,⟨-3199560634859,9257427557671⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80
theorem centerAccepted80 : StepValid centerStep80.shape centerBoxes80 centerStep80.proposed := by
  dsimp only [StepValid,centerStep80]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep81 : Instruction 40 := ⟨.mul 81 81,⟨⟨39442076935,39608850860⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81
theorem centerAccepted81 : StepValid centerStep81.shape centerBoxes81 centerStep81.proposed := by
  dsimp only [StepValid,centerStep81]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep82 : Instruction 40 := ⟨.neg 0,⟨⟨-39608850860,-39442076935⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82
theorem centerAccepted82 : StepValid centerStep82.shape centerBoxes82 centerStep82.proposed := by
  dsimp only [StepValid,centerStep82]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep83 : Instruction 40 := ⟨.add 81 0,⟨⟨1059902776916,1060069550841⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83
theorem centerAccepted83 : StepValid centerStep83.shape centerBoxes83 centerStep83.proposed := by
  dsimp only [StepValid,centerStep83]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep84 : Instruction 40 := ⟨.inv 0,⟨⟨1140421228640,1140600672010⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes85 := centerStep84.proposed :: centerBoxes84
theorem centerAccepted84 : StepValid centerStep84.shape centerBoxes84 centerStep84.proposed := by
  dsimp only [StepValid,centerStep84]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep85 : Instruction 40 := ⟨.mul 13 0,⟨⟨315269822963,316072215152⟩,⟨0,0⟩,⟨3304417628518,3337434634352⟩,⟨0,0⟩,⟨0,0⟩,⟨-1299975772384,780933186935⟩⟩⟩
noncomputable def centerBoxes86 := centerStep85.proposed :: centerBoxes85
theorem centerAccepted85 : StepValid centerStep85.shape centerBoxes85 centerStep85.proposed := by
  dsimp only [StepValid,centerStep85]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep86 : Instruction 40 := ⟨.add 5 0,⟨⟨433768505281,440284225384⟩,⟨0,0⟩,⟨-2019377407426,-1793210339176⟩,⟨0,0⟩,⟨0,0⟩,⟨-4499536407243,10038360744606⟩⟩⟩
noncomputable def centerBoxes87 := centerStep86.proposed :: centerBoxes86
theorem centerAccepted86 : StepValid centerStep86.shape centerBoxes86 centerStep86.proposed := by
  dsimp only [StepValid,centerStep86]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep87 : Instruction 40 := ⟨.mul 0 68,⟨⟨298637641092,303224299746⟩,⟨0,0⟩,⟨-1434836670596,-1273639244696⟩,⟨0,0⟩,⟨0,0⟩,⟨-3339180866221,7042843799124⟩⟩⟩
noncomputable def centerBoxes88 := centerStep87.proposed :: centerBoxes87
theorem centerAccepted87 : StepValid centerStep87.shape centerBoxes87 centerStep87.proposed := by
  dsimp only [StepValid,centerStep87]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep88 : Instruction 40 := ⟨.mul 0 69,⟨⟨205603771577,208830956586⟩,⟨0,0⟩,⟨-1018537907624,-903759552707⟩,⟨0,0⟩,⟨0,0⟩,⟨-2458261740627,4948434516350⟩⟩⟩
noncomputable def centerBoxes89 := centerStep88.proposed :: centerBoxes88
theorem centerAccepted88 : StepValid centerStep88.shape centerBoxes88 centerStep88.proposed := by
  dsimp only [StepValid,centerStep88]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep89 : Instruction 40 := ⟨.mul 90 63,⟨⟨524740111291,524786092335⟩,⟨0,0⟩,⟨71566134850,72355662684⟩,⟨0,0⟩,⟨0,0⟩,⟨706880356505,759484287619⟩⟩⟩
noncomputable def centerBoxes90 := centerStep89.proposed :: centerBoxes89
theorem centerAccepted89 : StepValid centerStep89.shape centerBoxes89 centerStep89.proposed := by
  dsimp only [StepValid,centerStep89]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep90 : Instruction 40 := ⟨.inv 0,⟨⟨2303654455162,2303856315921⟩,⟨0,0⟩,⟨-317675449009,-314153991109⟩,⟨0,0⟩,⟨0,0⟩,⟨-3248810224780,-3015386349006⟩⟩⟩
noncomputable def centerBoxes91 := centerStep90.proposed :: centerBoxes90
theorem centerAccepted90 : StepValid centerStep90.shape centerBoxes90 centerStep90.proposed := by
  dsimp only [StepValid,centerStep90]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep91 : Instruction 40 := ⟨.mul 2 0,⟨⟨430773110921,437572924321⟩,⟨0,0⟩,⟨-2194524731191,-1952267635184⟩,⟨0,0⟩,⟨0,0⟩,⟨-5251508485679,10393374652788⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91
theorem centerAccepted91 : StepValid centerStep91.shape centerBoxes91 centerStep91.proposed := by
  dsimp only [StepValid,centerStep91]
  exact ⟨by decide,by decide⟩
noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91]
theorem centerAccepted : Accepted centerProgram centerInitial :=
  ⟨centerAccepted0,⟨centerAccepted1,⟨centerAccepted2,⟨centerAccepted3,⟨centerAccepted4,⟨centerAccepted5,⟨centerAccepted6,⟨centerAccepted7,⟨centerAccepted8,⟨centerAccepted9,⟨centerAccepted10,⟨centerAccepted11,⟨centerAccepted12,⟨centerAccepted13,⟨centerAccepted14,⟨centerAccepted15,⟨centerAccepted16,⟨centerAccepted17,⟨centerAccepted18,⟨centerAccepted19,⟨centerAccepted20,⟨centerAccepted21,⟨centerAccepted22,⟨centerAccepted23,⟨centerAccepted24,⟨centerAccepted25,⟨centerAccepted26,⟨centerAccepted27,⟨centerAccepted28,⟨centerAccepted29,⟨centerAccepted30,⟨centerAccepted31,⟨centerAccepted32,⟨centerAccepted33,⟨centerAccepted34,⟨centerAccepted35,⟨centerAccepted36,⟨centerAccepted37,⟨centerAccepted38,⟨centerAccepted39,⟨centerAccepted40,⟨centerAccepted41,⟨centerAccepted42,⟨centerAccepted43,⟨centerAccepted44,⟨centerAccepted45,⟨centerAccepted46,⟨centerAccepted47,⟨centerAccepted48,⟨centerAccepted49,⟨centerAccepted50,⟨centerAccepted51,⟨centerAccepted52,⟨centerAccepted53,⟨centerAccepted54,⟨centerAccepted55,⟨centerAccepted56,⟨centerAccepted57,⟨centerAccepted58,⟨centerAccepted59,⟨centerAccepted60,⟨centerAccepted61,⟨centerAccepted62,⟨centerAccepted63,⟨centerAccepted64,⟨centerAccepted65,⟨centerAccepted66,⟨centerAccepted67,⟨centerAccepted68,⟨centerAccepted69,⟨centerAccepted70,⟨centerAccepted71,⟨centerAccepted72,⟨centerAccepted73,⟨centerAccepted74,⟨centerAccepted75,⟨centerAccepted76,⟨centerAccepted77,⟨centerAccepted78,⟨centerAccepted79,⟨centerAccepted80,⟨centerAccepted81,⟨centerAccepted82,⟨centerAccepted83,⟨centerAccepted84,⟨centerAccepted85,⟨centerAccepted86,⟨centerAccepted87,⟨centerAccepted88,⟨centerAccepted89,⟨centerAccepted90,⟨centerAccepted91,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
noncomputable def center_output : DyadicBivariateJetEnclosure 40 := ⟨⟨430773110921,437572924321⟩,⟨0,0⟩,⟨-2194524731191,-1952267635184⟩,⟨0,0⟩,⟨0,0⟩,⟨-5251508485679,10393374652788⟩⟩
theorem center_output_eq : (finalBoxes centerProgram centerInitial).getD 0 (zeroBox 40)=center_output := rfl
noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨208247502300,208687306952⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨752087604397,752131805121⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨95150196951,113317207675⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
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
noncomputable def wholeStep4 : Instruction 40 := ⟨.inv 6,⟨⟨10668510497380,12705447370091⟩,⟨0,0⟩,⟨-146818268034761,-103516064184720⟩,⟨0,0⟩,⟨0,0⟩,⟨2008823171130910,3393127876704184⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4
theorem wholeAccepted4 : StepValid wholeStep4.shape wholeBoxes4 wholeStep4.proposed := by
  dsimp only [StepValid,wholeStep4]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep5 : Instruction 40 := ⟨.mul 6 0,⟨⟨7297471258842,8691286953160⟩,⟨0,0⟩,⟨-100432488545015,-70807026285630⟩,⟨0,0⟩,⟨0,0⟩,⟨1374074605731066,2321102688176238⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5
theorem wholeAccepted5 : StepValid wholeStep5.shape wholeBoxes5 wholeStep5.proposed := by
  dsimp only [StepValid,wholeStep5]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep6 : Instruction 40 := ⟨.contact 0,⟨⟨95881789440,113940365312⟩,⟨0,0⟩,⟨770822142488,1547460077836⟩,⟨0,0⟩,⟨0,0⟩,⟨-23532433563604,26937824040302⟩⟩⟩
noncomputable def wholeBoxes7 := wholeStep6.proposed :: wholeBoxes6
theorem wholeAccepted6 : StepValid wholeStep6.shape wholeBoxes6 wholeStep6.proposed := by
  dsimp only [StepValid,wholeStep6]
  exact ⟨by decide,by decide,(⟨⟨95881789440,113940365312⟩,⟨-16941234592,-11969545299⟩,⟨2949239280,5021427061⟩⟩ : DyadicJetEnclosure 40),brwhole6_jet,by decide⟩
noncomputable def wholeStep7 : Instruction 40 := ⟨.log 10,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes8 := wholeStep7.proposed :: wholeBoxes7
theorem wholeAccepted7 : StepValid wholeStep7.shape wholeBoxes7 wholeStep7.proposed := by
  dsimp only [StepValid,wholeStep7]
  exact ⟨by decide,by decide,lc0,by decide⟩
noncomputable def wholeStep8 : Instruction 40 := ⟨.add 6 1,⟨⟨1195393417216,1213451993088⟩,⟨0,0⟩,⟨770822142488,1547460077836⟩,⟨0,0⟩,⟨0,0⟩,⟨-23532433563604,26937824040302⟩⟩⟩
noncomputable def wholeBoxes9 := wholeStep8.proposed :: wholeBoxes8
theorem wholeAccepted8 : StepValid wholeStep8.shape wholeBoxes8 wholeStep8.proposed := by
  dsimp only [StepValid,wholeStep8]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep9 : Instruction 40 := ⟨.log 0,⟨⟨91929336128,108415231104⟩,⟨0,0⟩,⟨698443707241,1423339232588⟩,⟨0,0⟩,⟨0,0⟩,⟨-23487451552227,24333484330705⟩⟩⟩
noncomputable def wholeBoxes10 := wholeStep9.proposed :: wholeBoxes9
theorem wholeAccepted9 : StepValid wholeStep9.shape wholeBoxes9 wholeStep9.proposed := by
  dsimp only [StepValid,wholeStep9]
  exact ⟨by decide,by decide,lc23,by decide⟩
noncomputable def wholeStep10 : Instruction 40 := ⟨.mul 1 0,⟨⟨99945940070,119650101865⟩,⟨0,0⟩,⟨823798634667,1723421583472⟩,⟨0,0⟩,⟨0,0⟩,⟨-27262483283449,33517705340214⟩⟩⟩
noncomputable def wholeBoxes11 := wholeStep10.proposed :: wholeBoxes10
theorem wholeAccepted10 : StepValid wholeStep10.shape wholeBoxes10 wholeStep10.proposed := by
  dsimp only [StepValid,wholeStep10]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep11 : Instruction 40 := ⟨.neg 4,⟨⟨-113940365312,-95881789440⟩,⟨0,0⟩,⟨-1547460077836,-770822142488⟩,⟨0,0⟩,⟨0,0⟩,⟨-26937824040302,23532433563604⟩⟩⟩
noncomputable def wholeBoxes12 := wholeStep11.proposed :: wholeBoxes11
theorem wholeAccepted11 : StepValid wholeStep11.shape wholeBoxes11 wholeStep11.proposed := by
  dsimp only [StepValid,wholeStep11]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep12 : Instruction 40 := ⟨.add 10 0,⟨⟨985571262464,1003629838336⟩,⟨0,0⟩,⟨-1547460077836,-770822142488⟩,⟨0,0⟩,⟨0,0⟩,⟨-26937824040302,23532433563604⟩⟩⟩
noncomputable def wholeBoxes13 := wholeStep12.proposed :: wholeBoxes12
theorem wholeAccepted12 : StepValid wholeStep12.shape wholeBoxes12 wholeStep12.proposed := by
  dsimp only [StepValid,wholeStep12]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep13 : Instruction 40 := ⟨.log 0,⟨⟨-120286517696,-100322563584⟩,⟨0,0⟩,⟨-1726359537764,-844462645727⟩,⟨0,0⟩,⟨0,0⟩,⟨-32762646856467,25604405436984⟩⟩⟩
noncomputable def wholeBoxes14 := wholeStep13.proposed :: wholeBoxes13
theorem wholeAccepted13 : StepValid wholeStep13.shape wholeBoxes13 wholeStep13.proposed := by
  dsimp only [StepValid,wholeStep13]
  exact ⟨by decide,by decide,lc24,by decide⟩
noncomputable def wholeStep14 : Instruction 40 := ⟨.mul 1 0,⟨⟨-109797054674,-89926321056⟩,⟨0,0⟩,⟨-1505482114585,-587660480792⟩,⟨0,0⟩,⟨0,0⟩,⟨-31296025047262,31177976113112⟩⟩⟩
noncomputable def wholeBoxes15 := wholeStep14.proposed :: wholeBoxes14
theorem wholeAccepted14 : StepValid wholeStep14.shape wholeBoxes14 wholeStep14.proposed := by
  dsimp only [StepValid,wholeStep14]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep15 : Instruction 40 := ⟨.add 4 0,⟨⟨-9851114604,29723780809⟩,⟨0,0⟩,⟨-681683479918,1135761102680⟩,⟨0,0⟩,⟨0,0⟩,⟨-58558508330711,64695681453326⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15
theorem wholeAccepted15 : StepValid wholeStep15.shape wholeBoxes15 wholeStep15.proposed := by
  dsimp only [StepValid,wholeStep15]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 0 15,⟨⟨-4925557302,14861890405⟩,⟨0,0⟩,⟨-340841739959,567880551340⟩,⟨0,0⟩,⟨0,0⟩,⟨-29279254165356,32347840726663⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16
theorem wholeAccepted16 : StepValid wholeStep16.shape wholeBoxes16 wholeStep16.proposed := by
  dsimp only [StepValid,wholeStep16]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨-14861890405,4925557302⟩,⟨0,0⟩,⟨-567880551340,340841739959⟩,⟨0,0⟩,⟨0,0⟩,⟨-32347840726663,29279254165356⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17
theorem wholeAccepted17 : StepValid wholeStep17.shape wholeBoxes17 wholeStep17.proposed := by
  dsimp only [StepValid,wholeStep17]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep18 : Instruction 40 := ⟨.add 10 0,⟨⟨747261493211,767048960182⟩,⟨0,0⟩,⟨-567880551340,340841739959⟩,⟨0,0⟩,⟨0,0⟩,⟨-32347840726663,29279254165356⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18
theorem wholeAccepted18 : StepValid wholeStep18.shape wholeBoxes18 wholeStep18.proposed := by
  dsimp only [StepValid,wholeStep18]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep19 : Instruction 40 := ⟨.mul 12 12,⟨⟨8361273600,11807430244⟩,⟨0,0⟩,⟨134437516610,320720876652⟩,⟨0,0⟩,⟨0,0⟩,⟨-3796462445404,9938845695360⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19
theorem wholeAccepted19 : StepValid wholeStep19.shape wholeBoxes19 wholeStep19.proposed := by
  dsimp only [StepValid,wholeStep19]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep20 : Instruction 40 := ⟨.neg 0,⟨⟨-11807430244,-8361273600⟩,⟨0,0⟩,⟨-320720876652,-134437516610⟩,⟨0,0⟩,⟨0,0⟩,⟨-9938845695360,3796462445404⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20
theorem wholeAccepted20 : StepValid wholeStep20.shape wholeBoxes20 wholeStep20.proposed := by
  dsimp only [StepValid,wholeStep20]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep21 : Instruction 40 := ⟨.add 19 0,⟨⟨1087704197532,1091150354176⟩,⟨0,0⟩,⟨-320720876652,-134437516610⟩,⟨0,0⟩,⟨0,0⟩,⟨-9938845695360,3796462445404⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21
theorem wholeAccepted21 : StepValid wholeStep21.shape wholeBoxes21 wholeStep21.proposed := by
  dsimp only [StepValid,wholeStep21]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep22 : Instruction 40 := ⟨.log 0,⟨⟨-11871286656,-8393227456⟩,⟨0,0⟩,⟨-324202420061,-135467685233⟩,⟨0,0⟩,⟨0,0⟩,⟨-10142329981014,3820983859180⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22
theorem wholeAccepted22 : StepValid wholeStep22.shape wholeBoxes22 wholeStep22.proposed := by
  dsimp only [StepValid,wholeStep22]
  exact ⟨by decide,by decide,lc21,by decide⟩
noncomputable def wholeStep23 : Instruction 40 := ⟨.mul 0 22,⟨⟨-5935643328,-4196613728⟩,⟨0,0⟩,⟨-162101210031,-67733842616⟩,⟨0,0⟩,⟨0,0⟩,⟨-5071164990507,1910491929590⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23
theorem wholeAccepted23 : StepValid wholeStep23.shape wholeBoxes23 wholeStep23.proposed := by
  dsimp only [StepValid,wholeStep23]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep24 : Instruction 40 := ⟨.neg 0,⟨⟨4196613728,5935643328⟩,⟨0,0⟩,⟨67733842616,162101210031⟩,⟨0,0⟩,⟨0,0⟩,⟨-1910491929590,5071164990507⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24
theorem wholeAccepted24 : StepValid wholeStep24.shape wholeBoxes24 wholeStep24.proposed := by
  dsimp only [StepValid,wholeStep24]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep25 : Instruction 40 := ⟨.add 17 0,⟨⟨766319997344,768059046208⟩,⟨0,0⟩,⟨67733842616,162101210031⟩,⟨0,0⟩,⟨0,0⟩,⟨-1910491929590,5071164990507⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25
theorem wholeAccepted25 : StepValid wholeStep25.shape wholeBoxes25 wholeStep25.proposed := by
  dsimp only [StepValid,wholeStep25]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep26 : Instruction 40 := ⟨.add 24 26,⟨⟨1307759130076,1308198934728⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26
theorem wholeAccepted26 : StepValid wholeStep26.shape wholeBoxes26 wholeStep26.proposed := by
  dsimp only [StepValid,wholeStep26]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep27 : Instruction 40 := ⟨.neg 27,⟨⟨-208687306952,-208247502300⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27
theorem wholeAccepted27 : StepValid wholeStep27.shape wholeBoxes27 wholeStep27.proposed := by
  dsimp only [StepValid,wholeStep27]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep28 : Instruction 40 := ⟨.add 26 0,⟨⟨890824320824,891264125476⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28
theorem wholeAccepted28 : StepValid wholeStep28.shape wholeBoxes28 wholeStep28.proposed := by
  dsimp only [StepValid,wholeStep28]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep29 : Instruction 40 := ⟨.inv 0,⟨⟨1356417009344,1357086679556⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29
theorem wholeAccepted29 : StepValid wholeStep29.shape wholeBoxes29 wholeStep29.proposed := by
  dsimp only [StepValid,wholeStep29]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep30 : Instruction 40 := ⟨.mul 3 0,⟨⟨1613322390912,1614661731336⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30
theorem wholeAccepted30 : StepValid wholeStep30.shape wholeBoxes30 wholeStep30.proposed := by
  dsimp only [StepValid,wholeStep30]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨421585241024,422497649792⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31
theorem wholeAccepted31 : StepValid wholeStep31.shape wholeBoxes31 wholeStep31.proposed := by
  dsimp only [StepValid,wholeStep31]
  exact ⟨by decide,by decide,lc12,by decide⟩
noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 0 31,⟨⟨210792620512,211248824896⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32
theorem wholeAccepted32 : StepValid wholeStep32.shape wholeBoxes32 wholeStep32.proposed := by
  dsimp only [StepValid,wholeStep32]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep33 : Instruction 40 := ⟨.inv 20,⟨⟨1204553485196,1226624462033⟩,⟨0,0⟩,⟨925138395385,1925941286832⟩,⟨0,0⟩,⟨0,0⟩,⟨-27866972177273,39574234674365⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33
theorem wholeAccepted33 : StepValid wholeStep33.shape wholeBoxes33 wholeStep33.proposed := by
  dsimp only [StepValid,wholeStep33]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep34 : Instruction 40 := ⟨.mul 25 0,⟨⟨1309595342616,1353737296290⟩,⟨0,0⟩,⟨1850276790770,3851882573664⟩,⟨0,0⟩,⟨0,0⟩,⟨-55710604347102,79148469348706⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34
theorem wholeAccepted34 : StepValid wholeStep34.shape wholeBoxes34 wholeStep34.proposed := by
  dsimp only [StepValid,wholeStep34]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨192251899776,228701748736⟩,⟨0,0⟩,⟨1502803277733,3233968189070⟩,⟨0,0⟩,⟨0,0⟩,⟨-56285572025736,64397547858948⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35
theorem wholeAccepted35 : StepValid wholeStep35.shape wholeBoxes35 wholeStep35.proposed := by
  dsimp only [StepValid,wholeStep35]
  exact ⟨by decide,by decide,lc27,by decide⟩
noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 0 35,⟨⟨96125949888,114350874368⟩,⟨0,0⟩,⟨751401638866,1616984094535⟩,⟨0,0⟩,⟨0,0⟩,⟨-28142786012868,32198773929474⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36
theorem wholeAccepted36 : StepValid wholeStep36.shape wholeBoxes36 wholeStep36.proposed := by
  dsimp only [StepValid,wholeStep36]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep37 : Instruction 40 := ⟨.mul 40 11,⟨⟨1532639994688,1536118092416⟩,⟨0,0⟩,⟨135467685232,324202420062⟩,⟨0,0⟩,⟨0,0⟩,⟨-3820983859180,10142329981014⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37
theorem wholeAccepted37 : StepValid wholeStep37.shape wholeBoxes37 wholeStep37.proposed := by
  dsimp only [StepValid,wholeStep37]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep38 : Instruction 40 := ⟨.add 0 17,⟨⟨1520832564444,1527756818816⟩,⟨0,0⟩,⟨-185253191420,189764903452⟩,⟨0,0⟩,⟨0,0⟩,⟨-13759829554540,13938792426418⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38
theorem wholeAccepted38 : StepValid wholeStep38.shape wholeBoxes38 wholeStep38.proposed := by
  dsimp only [StepValid,wholeStep38]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep39 : Instruction 40 := ⟨.mul 20 0,⟨⟨1033603996830,1065804353206⟩,⟨0,0⟩,⟨-918300113365,605980189205⟩,⟨0,0⟩,⟨0,0⟩,⟨-54742144850225,50598573404213⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39
theorem wholeAccepted39 : StepValid wholeStep39.shape wholeBoxes39 wholeStep39.proposed := by
  dsimp only [StepValid,wholeStep39]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep40 : Instruction 40 := ⟨.mul 43 41,⟨⟨1504175208794,1504263610242⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40
theorem wholeAccepted40 : StepValid wholeStep40.shape wholeBoxes40 wholeStep40.proposed := by
  dsimp only [StepValid,wholeStep40]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 19 19,⟨⟨1076023564863,1082852664166⟩,⟨0,0⟩,⟨-636563887658,-265987639290⟩,⟨0,0⟩,⟨0,0⟩,⟨-19693655403391,7722288906080⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41
theorem wholeAccepted41 : StepValid wholeStep41.shape wholeBoxes41 wholeStep41.proposed := by
  dsimp only [StepValid,wholeStep41]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep42 : Instruction 40 := ⟨.mul 1 0,⟨⟨1472042613700,1481472152554⟩,⟨0,0⟩,⟨-870895648221,-363881565922⟩,⟨0,0⟩,⟨0,0⟩,⟨-26943279568484,10565016226967⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42
theorem wholeAccepted42 : StepValid wholeStep42.shape wholeBoxes42 wholeStep42.proposed := by
  dsimp only [StepValid,wholeStep42]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep43 : Instruction 40 := ⟨.mul 17 17,⟨⟨534097433346,536524292750⟩,⟨0,0⟩,⟨94416096714,226470184800⟩,⟨0,0⟩,⟨0,0⟩,⟨-2660786296100,7132677543389⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43
theorem wholeAccepted43 : StepValid wholeStep43.shape wholeBoxes43 wholeStep43.proposed := by
  dsimp only [StepValid,wholeStep43]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep44 : Instruction 40 := ⟨.mul 18 0,⟨⟨372246671489,374786701793⟩,⟨0,0⟩,⟨98706927450,237299637955⟩,⟨0,0⟩,⟨0,0⟩,⟨-2779303018546,7523833940305⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44
theorem wholeAccepted44 : StepValid wholeStep44.shape wholeBoxes44 wholeStep44.proposed := by
  dsimp only [StepValid,wholeStep44]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 2 0,⟨⟨498369411834,504984256490⟩,⟨0,0⟩,⟨-164708857601,196540989884⟩,⟨0,0⟩,⟨0,0⟩,⟨-13304788221361,13673473209967⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45
theorem wholeAccepted45 : StepValid wholeStep45.shape wholeBoxes45 wholeStep45.proposed := by
  dsimp only [StepValid,wholeStep45]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep46 : Instruction 40 := ⟨.inv 0,⟨⟨2393987147277,2425762478411⟩,⟨0,0⟩,⟨-956643299949,801703630166⟩,⟨0,0⟩,⟨0,0⟩,⟨-67186574290775,65514244087957⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46
theorem wholeAccepted46 : StepValid wholeStep46.shape wholeBoxes46 wholeStep46.proposed := by
  dsimp only [StepValid,wholeStep46]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep47 : Instruction 40 := ⟨.mul 7 0,⟨⟨2250485234785,2351396878416⟩,⟨0,0⟩,⟨-2953286232217,2114050607494⟩,⟨0,0⟩,⟨0,0⟩,⟨-187239123434172,176735246598216⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47
theorem wholeAccepted47 : StepValid wholeStep47.shape wholeBoxes47 wholeStep47.proposed := by
  dsimp only [StepValid,wholeStep47]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep48 : Instruction 40 := ⟨.neg 11,⟨⟨-114350874368,-96125949888⟩,⟨0,0⟩,⟨-1616984094535,-751401638866⟩,⟨0,0⟩,⟨0,0⟩,⟨-32198773929474,28142786012868⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48
theorem wholeAccepted48 : StepValid wholeStep48.shape wholeBoxes48 wholeStep48.proposed := by
  dsimp only [StepValid,wholeStep48]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep49 : Instruction 40 := ⟨.mul 0 10,⟨⟨-158889022763,-132960371845⟩,⟨0,0⟩,⟨-2266513783050,-1020063988967⟩,⟨0,0⟩,⟨0,0⟩,⟨-46747575826004,41079951825242⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49
theorem wholeAccepted49 : StepValid wholeStep49.shape wholeBoxes49 wholeStep49.proposed := by
  dsimp only [StepValid,wholeStep49]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 53 43,⟨⟨191763578880,227880730624⟩,⟨0,0⟩,⟨1541644284976,3094920155672⟩,⟨0,0⟩,⟨0,0⟩,⟨-47064867127208,53875648080604⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50
theorem wholeAccepted50 : StepValid wholeStep50.shape wholeBoxes50 wholeStep50.proposed := by
  dsimp only [StepValid,wholeStep50]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep51 : Instruction 40 := ⟨.inv 29,⟨⟨1107936972194,1111447232031⟩,⟨0,0⟩,⟨136505747839,327721756907⟩,⟨0,0⟩,⟨0,0⟩,⟨-3845696850964,10349060876655⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51
theorem wholeAccepted51 : StepValid wholeStep51.shape wholeBoxes51 wholeStep51.proposed := by
  dsimp only [StepValid,wholeStep51]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep52 : Instruction 40 := ⟨.mul 1 0,⟨⟨193233026003,230354460005⟩,⟨0,0⟩,⟨1577265295090,3196439059852⟩,⟨0,0⟩,⟨0,0⟩,⟨-47990024441383,58450347595424⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52
theorem wholeAccepted52 : StepValid wholeStep52.shape wholeBoxes52 wholeStep52.proposed := by
  dsimp only [StepValid,wholeStep52]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep53 : Instruction 40 := ⟨.neg 2,⟨⟨-227880730624,-191763578880⟩,⟨0,0⟩,⟨-3094920155672,-1541644284976⟩,⟨0,0⟩,⟨0,0⟩,⟨-53875648080604,47064867127208⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53
theorem wholeAccepted53 : StepValid wholeStep53.shape wholeBoxes53 wholeStep53.proposed := by
  dsimp only [StepValid,wholeStep53]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep54 : Instruction 40 := ⟨.add 1 0,⟨⟨-34647704621,38590881125⟩,⟨0,0⟩,⟨-1517654860582,1654794774876⟩,⟨0,0⟩,⟨0,0⟩,⟨-101865672521987,105515214722632⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54
theorem wholeAccepted54 : StepValid wholeStep54.shape wholeBoxes54 wholeStep54.proposed := by
  dsimp only [StepValid,wholeStep54]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 36 0,⟨⟨-24171173029,26922039287⟩,⟨0,0⟩,⟨-1078688540998,1172324454262⟩,⟨0,0⟩,⟨0,0⟩,⟨-73908942250080,76205598189738⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55
theorem wholeAccepted55 : StepValid wholeStep55.shape wholeBoxes55 wholeStep55.proposed := by
  dsimp only [StepValid,wholeStep55]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep56 : Instruction 40 := ⟨.add 6 0,⟨⟨-183060195792,-106038332558⟩,⟨0,0⟩,⟨-3345202324048,152260465295⟩,⟨0,0⟩,⟨0,0⟩,⟨-120656518076084,117285550014980⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56
theorem wholeAccepted56 : StepValid wholeStep56.shape wholeBoxes56 wholeStep56.proposed := by
  dsimp only [StepValid,wholeStep56]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep57 : Instruction 40 := ⟨.mul 0 10,⟨⟨-403870721351,-230879236607⟩,⟨0,0⟩,⟨-7513723452462,495193520192⟩,⟨0,0⟩,⟨0,0⟩,⟨-281980488915223,275764618628226⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57
theorem wholeAccepted57 : StepValid wholeStep57.shape wholeBoxes57 wholeStep57.proposed := by
  dsimp only [StepValid,wholeStep57]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 54 51,⟨⟨383527157760,455761461248⟩,⟨0,0⟩,⟨3083288569952,6189840311344⟩,⟨0,0⟩,⟨0,0⟩,⟨-94129734254416,107751296161208⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58
theorem wholeAccepted58 : StepValid wholeStep58.shape wholeBoxes58 wholeStep58.proposed := by
  dsimp only [StepValid,wholeStep58]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep59 : Instruction 40 := ⟨.mul 0 7,⟨⟨386466052007,460708920010⟩,⟨0,0⟩,⟨3154530590180,6392878119704⟩,⟨0,0⟩,⟨0,0⟩,⟨-95980048882765,116900695190846⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59
theorem wholeAccepted59 : StepValid wholeStep59.shape wholeBoxes59 wholeStep59.proposed := by
  dsimp only [StepValid,wholeStep59]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 57 53,⟨⟨287645368320,341821095936⟩,⟨0,0⟩,⟨2312466427464,4642380233508⟩,⟨0,0⟩,⟨0,0⟩,⟨-70597300690812,80813472120906⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60
theorem wholeAccepted60 : StepValid wholeStep60.shape wholeBoxes60 wholeStep60.proposed := by
  dsimp only [StepValid,wholeStep60]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 39 35,⟨⟨758090643797,762218315047⟩,⟨0,0⟩,⟨-157031705106,67170399568⟩,⟨0,0⟩,⟨0,0⟩,⟨-8933268668612,7668039744272⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61
theorem wholeAccepted61 : StepValid wholeStep61.shape wholeBoxes61 wholeStep61.proposed := by
  dsimp only [StepValid,wholeStep61]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep62 : Instruction 40 := ⟨.inv 0,⟨⟨1586062412499,1594698245529⟩,⟨0,0⟩,⟨-141297771209,330327496685⟩,⟨0,0⟩,⟨0,0⟩,⟨-16188810780276,18928622546915⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62
theorem wholeAccepted62 : StepValid wholeStep62.shape wholeBoxes62 wholeStep62.proposed := by
  dsimp only [StepValid,wholeStep62]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep63 : Instruction 40 := ⟨.mul 2 0,⟨⟨414932862278,495766927974⟩,⟨0,0⟩,⟨3291841059542,6835860877244⟩,⟨0,0⟩,⟨0,0⟩,⟨-108618209700341,125883449429468⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63
theorem wholeAccepted63 : StepValid wholeStep63.shape wholeBoxes63 wholeStep63.proposed := by
  dsimp only [StepValid,wholeStep63]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep64 : Instruction 40 := ⟨.neg 0,⟨⟨-495766927974,-414932862278⟩,⟨0,0⟩,⟨-6835860877244,-3291841059542⟩,⟨0,0⟩,⟨0,0⟩,⟨-125883449429468,108618209700341⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64
theorem wholeAccepted64 : StepValid wholeStep64.shape wholeBoxes64 wholeStep64.proposed := by
  dsimp only [StepValid,wholeStep64]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep65 : Instruction 40 := ⟨.add 5 0,⟨⟨-109300875967,45776057732⟩,⟨0,0⟩,⟨-3681330287064,3101037060162⟩,⟨0,0⟩,⟨0,0⟩,⟨-221863498312233,225518904891187⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65
theorem wholeAccepted65 : StepValid wholeStep65.shape wholeBoxes65 wholeStep65.proposed := by
  dsimp only [StepValid,wholeStep65]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 18 0,⟨⟨-233748995522,97895898996⟩,⟨0,0⟩,⟨-8082985121891,6925407101590⟩,⟨0,0⟩,⟨0,0⟩,⟨-508701263919658,520680162751561⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66
theorem wholeAccepted66 : StepValid wholeStep66.shape wholeBoxes66 wholeStep66.proposed := by
  dsimp only [StepValid,wholeStep66]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep67 : Instruction 40 := ⟨.add 9 0,⟨⟨-637619716873,-132983337611⟩,⟨0,0⟩,⟨-15596708574353,7420600621782⟩,⟨0,0⟩,⟨0,0⟩,⟨-790681752834881,796444781379787⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67
theorem wholeAccepted67 : StepValid wholeStep67.shape wholeBoxes67 wholeStep67.proposed := by
  dsimp only [StepValid,wholeStep67]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 61 29,⟨⟨132622651760,158318625876⟩,⟨0,0⟩,⟨1046995384408,2169840234440⟩,⟨0,0⟩,⟨0,0⟩,⟨-34645363195736,39408353302174⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68
theorem wholeAccepted68 : StepValid wholeStep68.shape wholeBoxes68 wholeStep68.proposed := by
  dsimp only [StepValid,wholeStep68]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 27 25,⟨⟨522687900423,528395284886⟩,⟨0,0⟩,⟨-218222380363,93833048158⟩,⟨0,0⟩,⟨0,0⟩,⟨-12492536870038,10747141864059⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69
theorem wholeAccepted69 : StepValid wholeStep69.shape wholeBoxes69 wholeStep69.proposed := by
  dsimp only [StepValid,wholeStep69]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨2287919393291,2312901864835⟩,⟨0,0⟩,⟨-415212657290,965637333641⟩,⟨0,0⟩,⟨0,0⟩,⟨-47902968152962,56085972440818⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70
theorem wholeAccepted70 : StepValid wholeStep70.shape wholeBoxes70 wholeStep70.proposed := by
  dsimp only [StepValid,wholeStep70]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 2 0,⟨⟨275967920016,333034627172⟩,⟨0,0⟩,⟨2118854488184,4703457216591⟩,⟨0,0⟩,⟨0,0⟩,⟨-81415371365381,94785414519037⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71
theorem wholeAccepted71 : StepValid wholeStep71.shape wholeBoxes71 wholeStep71.proposed := by
  dsimp only [StepValid,wholeStep71]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 65 39,⟨⟨18381955356,21891326724⟩,⟨0,0⟩,⟨147777990936,297313020398⟩,⟨0,0⟩,⟨0,0⟩,⟨-4521279094893,5175555701289⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72
theorem wholeAccepted72 : StepValid wholeStep72.shape wholeBoxes72 wholeStep72.proposed := by
  dsimp only [StepValid,wholeStep72]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep73 : Instruction 40 := ⟨.add 54 0,⟨⟨765643448567,788940286906⟩,⟨0,0⟩,⟨-420102560404,638154760357⟩,⟨0,0⟩,⟨0,0⟩,⟨-36869119821556,34454809866645⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73
theorem wholeAccepted73 : StepValid wholeStep73.shape wholeBoxes73 wholeStep73.proposed := by
  dsimp only [StepValid,wholeStep73]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 0 0,⟨⟨533154789385,566093855290⟩,⟨0,0⟩,⟨-602878270976,915799318550⟩,⟨0,0⟩,⟨0,0⟩,⟨-53397569752181,50185970539405⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74
theorem wholeAccepted74 : StepValid wholeStep74.shape wholeBoxes74 wholeStep74.proposed := by
  dsimp only [StepValid,wholeStep74]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep75 : Instruction 40 := ⟨.mul 7 0,⟨⟨-328284480687,-64483814053⟩,⟨0,0⟩,⟨-8561194216688,4170181898191⟩,⟨0,0⟩,⟨0,0⟩,⟨-462174790540410,458126736266808⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75
theorem wholeAccepted75 : StepValid wholeStep75.shape wholeBoxes75 wholeStep75.proposed := by
  dsimp only [StepValid,wholeStep75]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep76 : Instruction 40 := ⟨.mul 79 28,⟨⟨4500970469570,4702793756832⟩,⟨0,0⟩,⟨-5906572464434,4228101214988⟩,⟨0,0⟩,⟨0,0⟩,⟨-374478246868344,353470493196432⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76
theorem wholeAccepted76 : StepValid wholeStep76.shape wholeBoxes76 wholeStep76.proposed := by
  dsimp only [StepValid,wholeStep76]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 0 3,⟨⟨3134244754819,3374428575421⟩,⟨0,0⟩,⟨-6035032741256,5763312954987⟩,⟨0,0⟩,⟨0,0⟩,⟨-433253677976807,405905068768446⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77
theorem wholeAccepted77 : StepValid wholeStep77.shape wholeBoxes77 wholeStep77.proposed := by
  dsimp only [StepValid,wholeStep77]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep78 : Instruction 40 := ⟨.add 45 29,⟨⟨96441746144,115122875008⟩,⟨0,0⟩,⟨-1616984094535,-751401638866⟩,⟨0,0⟩,⟨0,0⟩,⟨-32198773929474,28142786012868⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78
theorem wholeAccepted78 : StepValid wholeStep78.shape wholeBoxes78 wholeStep78.proposed := by
  dsimp only [StepValid,wholeStep78]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 1 0,⟨⟨274914816143,353314971209⟩,⟨0,0⟩,⟨-5594454391523,-1538489858311⟩,⟨0,0⟩,⟨0,0⟩,⟨-161133577983221,146621354102484⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79
theorem wholeAccepted79 : StepValid wholeStep79.shape wholeBoxes79 wholeStep79.proposed := by
  dsimp only [StepValid,wholeStep79]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep80 : Instruction 40 := ⟨.add 4 0,⟨⟨-53369664544,288831157156⟩,⟨0,0⟩,⟨-14155648608211,2631692039880⟩,⟨0,0⟩,⟨0,0⟩,⟨-623308368523631,604748090369292⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80
theorem wholeAccepted80 : StepValid wholeStep80.shape wholeBoxes80 wholeStep80.proposed := by
  dsimp only [StepValid,wholeStep80]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep81 : Instruction 40 := ⟨.mul 81 81,⟨⟨39442076935,39608850860⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81
theorem wholeAccepted81 : StepValid wholeStep81.shape wholeBoxes81 wholeStep81.proposed := by
  dsimp only [StepValid,wholeStep81]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep82 : Instruction 40 := ⟨.neg 0,⟨⟨-39608850860,-39442076935⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82
theorem wholeAccepted82 : StepValid wholeStep82.shape wholeBoxes82 wholeStep82.proposed := by
  dsimp only [StepValid,wholeStep82]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep83 : Instruction 40 := ⟨.add 81 0,⟨⟨1059902776916,1060069550841⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83
theorem wholeAccepted83 : StepValid wholeStep83.shape wholeBoxes83 wholeStep83.proposed := by
  dsimp only [StepValid,wholeStep83]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep84 : Instruction 40 := ⟨.inv 0,⟨⟨1140421228640,1140600672010⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes85 := wholeStep84.proposed :: wholeBoxes84
theorem wholeAccepted84 : StepValid wholeStep84.shape wholeBoxes84 wholeStep84.proposed := by
  dsimp only [StepValid,wholeStep84]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep85 : Instruction 40 := ⟨.mul 13 0,⟨⟨286235876419,345480220454⟩,⟨0,0⟩,⟨2197690845354,4879226673451⟩,⟨0,0⟩,⟨0,0⟩,⟨-84457885615209,98327570865113⟩⟩⟩
noncomputable def wholeBoxes86 := wholeStep85.proposed :: wholeBoxes85
theorem wholeAccepted85 : StepValid wholeStep85.shape wholeBoxes85 wholeStep85.proposed := by
  dsimp only [StepValid,wholeStep85]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep86 : Instruction 40 := ⟨.add 5 0,⟨⟨232866211875,634311377610⟩,⟨0,0⟩,⟨-11957957762857,7510918713331⟩,⟨0,0⟩,⟨0,0⟩,⟨-707766254138840,703075661234405⟩⟩⟩
noncomputable def wholeBoxes87 := wholeStep86.proposed :: wholeBoxes86
theorem wholeAccepted86 : StepValid wholeStep86.shape wholeBoxes86 wholeStep86.proposed := by
  dsimp only [StepValid,wholeStep86]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep87 : Instruction 40 := ⟨.mul 0 68,⟨⟨158262949484,442512721409⟩,⟨0,0⟩,⟨-8669805686385,5436451995314⟩,⟨0,0⟩,⟨0,0⟩,⟨-520176929078970,519728020861919⟩⟩⟩
noncomputable def wholeBoxes88 := wholeStep87.proposed :: wholeBoxes87
theorem wholeAccepted87 : StepValid wholeStep87.shape wholeBoxes87 wholeStep87.proposed := by
  dsimp only [StepValid,wholeStep87]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep88 : Instruction 40 := ⟨.mul 0 69,⟨⟨107560306743,308708806937⟩,⟨0,0⟩,⟨-6276841127084,3929791688283⟩,⟨0,0⟩,⟨0,0⟩,⟨-381523945457245,383315735678037⟩⟩⟩
noncomputable def wholeBoxes89 := wholeStep88.proposed :: wholeBoxes88
theorem wholeAccepted88 : StepValid wholeStep88.shape wholeBoxes88 wholeStep88.proposed := by
  dsimp only [StepValid,wholeStep88]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep89 : Instruction 40 := ⟨.mul 90 63,⟨⟨524177968149,525398388040⟩,⟨0,0⟩,⟨46331282128,110886936194⟩,⟨0,0⟩,⟨0,0⟩,⟨-1306890902626,3468980574668⟩⟩⟩
noncomputable def wholeBoxes90 := wholeStep89.proposed :: wholeBoxes89
theorem wholeAccepted89 : StepValid wholeStep89.shape wholeBoxes89 wholeStep89.proposed := by
  dsimp only [StepValid,wholeStep89]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep90 : Instruction 40 := ⟨.inv 0,⟨⟨2300969791941,2306327035995⟩,⟨0,0⟩,⟨-487890667718,-202906752333⟩,⟨0,0⟩,⟨0,0⟩,⟨-15227357854717,5956601410645⟩⟩⟩
noncomputable def wholeBoxes91 := wholeStep90.proposed :: wholeBoxes90
theorem wholeAccepted90 : StepValid wholeStep90.shape wholeBoxes90 wholeStep90.proposed := by
  dsimp only [StepValid,wholeStep90]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 2 0,⟨⟨225093587348,647545191613⟩,⟨0,0⟩,⟨-13303237699790,8223251010346⟩,⟨0,0⟩,⟨0,0⟩,⟨-808044594255296,811283029405564⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91
theorem wholeAccepted91 : StepValid wholeStep91.shape wholeBoxes91 wholeStep91.proposed := by
  dsimp only [StepValid,wholeStep91]
  exact ⟨by decide,by decide⟩
noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91]
theorem wholeAccepted : Accepted wholeProgram wholeInitial :=
  ⟨wholeAccepted0,⟨wholeAccepted1,⟨wholeAccepted2,⟨wholeAccepted3,⟨wholeAccepted4,⟨wholeAccepted5,⟨wholeAccepted6,⟨wholeAccepted7,⟨wholeAccepted8,⟨wholeAccepted9,⟨wholeAccepted10,⟨wholeAccepted11,⟨wholeAccepted12,⟨wholeAccepted13,⟨wholeAccepted14,⟨wholeAccepted15,⟨wholeAccepted16,⟨wholeAccepted17,⟨wholeAccepted18,⟨wholeAccepted19,⟨wholeAccepted20,⟨wholeAccepted21,⟨wholeAccepted22,⟨wholeAccepted23,⟨wholeAccepted24,⟨wholeAccepted25,⟨wholeAccepted26,⟨wholeAccepted27,⟨wholeAccepted28,⟨wholeAccepted29,⟨wholeAccepted30,⟨wholeAccepted31,⟨wholeAccepted32,⟨wholeAccepted33,⟨wholeAccepted34,⟨wholeAccepted35,⟨wholeAccepted36,⟨wholeAccepted37,⟨wholeAccepted38,⟨wholeAccepted39,⟨wholeAccepted40,⟨wholeAccepted41,⟨wholeAccepted42,⟨wholeAccepted43,⟨wholeAccepted44,⟨wholeAccepted45,⟨wholeAccepted46,⟨wholeAccepted47,⟨wholeAccepted48,⟨wholeAccepted49,⟨wholeAccepted50,⟨wholeAccepted51,⟨wholeAccepted52,⟨wholeAccepted53,⟨wholeAccepted54,⟨wholeAccepted55,⟨wholeAccepted56,⟨wholeAccepted57,⟨wholeAccepted58,⟨wholeAccepted59,⟨wholeAccepted60,⟨wholeAccepted61,⟨wholeAccepted62,⟨wholeAccepted63,⟨wholeAccepted64,⟨wholeAccepted65,⟨wholeAccepted66,⟨wholeAccepted67,⟨wholeAccepted68,⟨wholeAccepted69,⟨wholeAccepted70,⟨wholeAccepted71,⟨wholeAccepted72,⟨wholeAccepted73,⟨wholeAccepted74,⟨wholeAccepted75,⟨wholeAccepted76,⟨wholeAccepted77,⟨wholeAccepted78,⟨wholeAccepted79,⟨wholeAccepted80,⟨wholeAccepted81,⟨wholeAccepted82,⟨wholeAccepted83,⟨wholeAccepted84,⟨wholeAccepted85,⟨wholeAccepted86,⟨wholeAccepted87,⟨wholeAccepted88,⟨wholeAccepted89,⟨wholeAccepted90,⟨wholeAccepted91,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
noncomputable def whole_output : DyadicBivariateJetEnclosure 40 := ⟨⟨225093587348,647545191613⟩,⟨0,0⟩,⟨-13303237699790,8223251010346⟩,⟨0,0⟩,⟨0,0⟩,⟨-808044594255296,811283029405564⟩⟩
theorem whole_output_eq : (finalBoxes wholeProgram wholeInitial).getD 0 (zeroBox 40)=whole_output := rfl
open GeneralCK.Reflection GeneralCK.Reflection.SmallRatio GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed
theorem sameShape : shapes centerProgram=shapes wholeProgram := by decide
theorem scalar_program (a e r : ℝ) :
    (evalRealProgram wholeProgram [a,e,r,2]).getD 0 0=ReflectionMidpointKernel.scalarCore a e r := rfl
attribute [local irreducible] wholeProgram centerProgram
noncomputable def reflection_log_0_out : DyadicInterval 64 := ⟨-12786308645202662930,-12786308645202655416⟩
theorem reflection_log_0_checked : DyadicFastLog.check 1 2 1 16 reflection_log_0_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily.Endpoints0249.sharedTwo_eq]
  decide
theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := DyadicFastLog.check_sound reflection_log_0_checked
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1):ℝ)=((1 / 2):ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [he]
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_0_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_1_out : DyadicInterval 64 := ⟨-3205771583601797615,-3205771583601797566⟩
theorem reflection_log_1_checked : DyadicFastLog.check 5000 5949 0 16 reflection_log_1_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily.Endpoints0249.sharedTwo_eq]
  decide
theorem reflection_log_1 : Bounds (6951409 / 40000000) (86892613 / 500000000) (Real.log (5949 / 5000)) := by
  have h := DyadicFastLog.check_sound reflection_log_1_checked
  have he : Real.log (5949 / 5000) = -Real.log (5000 / 5949) := by
    rw [show ((5949 / 5000):ℝ)=((5000 / 5949):ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [he]
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_1_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_2_out : DyadicInterval 64 := ⟨-3882562746227311555,-3882562746227311506⟩
theorem reflection_log_2_checked : DyadicFastLog.check 4051 5000 0 16 reflection_log_2_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily.Endpoints0249.sharedTwo_eq]
  decide
theorem reflection_log_2 : Bounds (-210474149 / 1000000000) (-52618537 / 250000000) (Real.log (4051 / 5000)) := by
  have h := DyadicFastLog.check_sound reflection_log_2_checked
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_2_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_3_out : DyadicInterval 64 := ⟨-3199568912368605863,-3199568912368605812⟩
theorem reflection_log_3_checked : DyadicFastLog.check 5000 5947 0 16 reflection_log_3_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily.Endpoints0249.sharedTwo_eq]
  decide
theorem reflection_log_3 : Bounds (86724489 / 500000000) (173448979 / 1000000000) (Real.log (5947 / 5000)) := by
  have h := DyadicFastLog.check_sound reflection_log_3_checked
  have he : Real.log (5947 / 5000) = -Real.log (5000 / 5947) := by
    rw [show ((5947 / 5000):ℝ)=((5000 / 5947):ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [he]
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_3_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_4_out : DyadicInterval 64 := ⟨-3873457739095911619,-3873457739095911568⟩
theorem reflection_log_4_checked : DyadicFastLog.check 4053 5000 0 16 reflection_log_4_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily.Endpoints0249.sharedTwo_eq]
  decide
theorem reflection_log_4 : Bounds (-41996113 / 200000000) (-52495141 / 250000000) (Real.log (4053 / 5000)) := by
  have h := DyadicFastLog.check_sound reflection_log_4_checked
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_4_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_5_out : DyadicInterval 64 := ⟨-298671514250801901,-298671514250801856⟩
theorem reflection_log_5_checked : DyadicFastLog.check 2500000 2540807 0 16 reflection_log_5_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily.Endpoints0249.sharedTwo_eq]
  decide
theorem reflection_log_5 : Bounds (3238203 / 200000000) (2023877 / 125000000) (Real.log (2540807 / 2500000)) := by
  have h := DyadicFastLog.check_sound reflection_log_5_checked
  have he : Real.log (2540807 / 2500000) = -Real.log (2500000 / 2540807) := by
    rw [show ((2540807 / 2500000):ℝ)=((2500000 / 2540807):ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [he]
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_5_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_6_out : DyadicInterval 64 := ⟨-303587005224587309,-303587005224587264⟩
theorem reflection_log_6_checked : DyadicFastLog.check 2459193 2500000 0 16 reflection_log_6_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily.Endpoints0249.sharedTwo_eq]
  decide
theorem reflection_log_6 : Bounds (-3291497 / 200000000) (-4114371 / 250000000) (Real.log (2459193 / 2500000)) := by
  have h := DyadicFastLog.check_sound reflection_log_6_checked
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_6_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_7_out : DyadicInterval 64 := ⟨-294608990083444367,-294608990083444322⟩
theorem reflection_log_7_checked : DyadicFastLog.check 1000000 1016099 0 16 reflection_log_7_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily.Endpoints0249.sharedTwo_eq]
  decide
theorem reflection_log_7 : Bounds (3194157 / 200000000) (7985393 / 500000000) (Real.log (1016099 / 1000000)) := by
  have h := DyadicFastLog.check_sound reflection_log_7_checked
  have he : Real.log (1016099 / 1000000) = -Real.log (1000000 / 1016099) := by
    rw [show ((1016099 / 1000000):ℝ)=((1000000 / 1016099):ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [he]
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_7_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_8_out : DyadicInterval 64 := ⟨-299390596317942501,-299390596317942456⟩
theorem reflection_log_8_checked : DyadicFastLog.check 983901 1000000 0 16 reflection_log_8_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily.Endpoints0249.sharedTwo_eq]
  decide
theorem reflection_log_8 : Bounds (-16229997 / 1000000000) (-4057499 / 250000000) (Real.log (983901 / 1000000)) := by
  have h := DyadicFastLog.check_sound reflection_log_8_checked
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_8_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
theorem entropy_bound {a z : ℝ} (ha : Bounds (947 / 5000) (949 / 5000) a) (hz : Bounds (17 / 200) (43 / 500) z) :
  Bounds (684019691469 / 1000000000000) (42753743237 / 62500000000) ((biasE a+biasE (a*z))/2) := by
  let x0 : ℝ := Real.log (2 / 1)
  have hx0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x0 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x1 : ℝ := (1 / 1)+(949 / 5000)
  have hx1 : Bounds (5949 / 5000) (5949 / 5000) x1 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((949 / 5000) : ℝ)) <;> norm_num
  let x2 : ℝ := (1 / 1)+(949 / 5000)
  have hx2 : Bounds (5949 / 5000) (5949 / 5000) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((949 / 5000) : ℝ)) <;> norm_num
  let x3 : ℝ := Real.log x2
  have hx3 : Bounds (6951409 / 40000000) (86892613 / 500000000) x3 := by
    exact bounds_log hx2 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x4 : ℝ := x1*x3
  have hx4 : Bounds (41353932141 / 200000000000) (41353932379 / 200000000000) x4 := by
    apply bounds_mul hx1 hx3 <;> norm_num
  let x5 : ℝ := -(949 / 5000)
  have hx5 : Bounds (-949 / 5000) (-949 / 5000) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((949 / 5000) : ℝ))
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (4051 / 5000) (4051 / 5000) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-(949 / 5000)
  have hx7 : Bounds (4051 / 5000) (4051 / 5000) x7 := by
    exact hx6
  let x8 : ℝ := -(949 / 5000)
  have hx8 : Bounds (-949 / 5000) (-949 / 5000) x8 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((949 / 5000) : ℝ))
  let x9 : ℝ := (1 / 1)+x8
  have hx9 : Bounds (4051 / 5000) (4051 / 5000) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx8 <;> norm_num
  let x10 : ℝ := (1 / 1)-(949 / 5000)
  have hx10 : Bounds (4051 / 5000) (4051 / 5000) x10 := by
    exact hx9
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (-210474149 / 1000000000) (-52618537 / 250000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x12 : ℝ := x7*x11
  have hx12 : Bounds (-133223559 / 781250000) (-170526154709 / 1000000000000) x12 := by
    apply bounds_mul hx7 hx11 <;> norm_num
  let x13 : ℝ := x4+x12
  have hx13 : Bounds (7248701037 / 200000000000) (18121753593 / 500000000000) x13 := by
    apply bounds_add hx4 hx12 <;> norm_num
  let x14 : ℝ := (2 / 1)⁻¹
  have hx14 : Bounds (1 / 2) (1 / 2) x14 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x15 : ℝ := x13*x14
  have hx15 : Bounds (1132609537 / 62500000000) (18121753593 / 1000000000000) x15 := by
    apply bounds_mul hx13 hx14 <;> norm_num
  let x16 : ℝ := x13/(2 / 1)
  have hx16 : Bounds (1132609537 / 62500000000) (18121753593 / 1000000000000) x16 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx15
  let x17 : ℝ := -x16
  have hx17 : Bounds (-18121753593 / 1000000000000) (-1132609537 / 62500000000) x17 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx16
  let x18 : ℝ := x0+x17
  have hx18 : Bounds (675025426407 / 1000000000000) (84378178551 / 125000000000) x18 := by
    apply bounds_add hx0 hx17 <;> norm_num
  let x19 : ℝ := x0-x16
  have hx19 : Bounds (675025426407 / 1000000000000) (84378178551 / 125000000000) x19 := by
    exact hx18
  let x20 : ℝ := biasE (949 / 5000)
  have hx20 : Bounds (675025426407 / 1000000000000) (84378178551 / 125000000000) x20 := by
    simpa +zetaDelta only [biasE, div_one] using hx19
  let x21 : ℝ := Real.log (2 / 1)
  have hx21 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x21 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x22 : ℝ := (1 / 1)+(947 / 5000)
  have hx22 : Bounds (5947 / 5000) (5947 / 5000) x22 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((947 / 5000) : ℝ)) <;> norm_num
  let x23 : ℝ := (1 / 1)+(947 / 5000)
  have hx23 : Bounds (5947 / 5000) (5947 / 5000) x23 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((947 / 5000) : ℝ)) <;> norm_num
  let x24 : ℝ := Real.log x23
  have hx24 : Bounds (86724489 / 500000000) (173448979 / 1000000000) x24 := by
    exact bounds_log hx23 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x25 : ℝ := x22*x24
  have hx25 : Bounds (206300214433 / 1000000000000) (206300215623 / 1000000000000) x25 := by
    apply bounds_mul hx22 hx24 <;> norm_num
  let x26 : ℝ := -(947 / 5000)
  have hx26 : Bounds (-947 / 5000) (-947 / 5000) x26 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((947 / 5000) : ℝ))
  let x27 : ℝ := (1 / 1)+x26
  have hx27 : Bounds (4053 / 5000) (4053 / 5000) x27 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx26 <;> norm_num
  let x28 : ℝ := (1 / 1)-(947 / 5000)
  have hx28 : Bounds (4053 / 5000) (4053 / 5000) x28 := by
    exact hx27
  let x29 : ℝ := -(947 / 5000)
  have hx29 : Bounds (-947 / 5000) (-947 / 5000) x29 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((947 / 5000) : ℝ))
  let x30 : ℝ := (1 / 1)+x29
  have hx30 : Bounds (4053 / 5000) (4053 / 5000) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx29 <;> norm_num
  let x31 : ℝ := (1 / 1)-(947 / 5000)
  have hx31 : Bounds (4053 / 5000) (4053 / 5000) x31 := by
    exact hx30
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (-41996113 / 200000000) (-52495141 / 250000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x33 : ℝ := x28*x32
  have hx33 : Bounds (-170210245989 / 1000000000000) (-85105122589 / 500000000000) x33 := by
    apply bounds_mul hx28 hx32 <;> norm_num
  let x34 : ℝ := x25+x33
  have hx34 : Bounds (9022492111 / 250000000000) (7217994089 / 200000000000) x34 := by
    apply bounds_add hx25 hx33 <;> norm_num
  let x35 : ℝ := (2 / 1)⁻¹
  have hx35 : Bounds (1 / 2) (1 / 2) x35 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x36 : ℝ := x34*x35
  have hx36 : Bounds (9022492111 / 500000000000) (18044985223 / 1000000000000) x36 := by
    apply bounds_mul hx34 hx35 <;> norm_num
  let x37 : ℝ := x34/(2 / 1)
  have hx37 : Bounds (9022492111 / 500000000000) (18044985223 / 1000000000000) x37 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx36
  let x38 : ℝ := -x37
  have hx38 : Bounds (-18044985223 / 1000000000000) (-9022492111 / 500000000000) x38 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx37
  let x39 : ℝ := x21+x38
  have hx39 : Bounds (675102194777 / 1000000000000) (337551098389 / 500000000000) x39 := by
    apply bounds_add hx21 hx38 <;> norm_num
  let x40 : ℝ := x21-x37
  have hx40 : Bounds (675102194777 / 1000000000000) (337551098389 / 500000000000) x40 := by
    exact hx39
  let x41 : ℝ := biasE (947 / 5000)
  have hx41 : Bounds (675102194777 / 1000000000000) (337551098389 / 500000000000) x41 := by
    simpa +zetaDelta only [biasE, div_one] using hx40
  let x42 : ℝ := biasE a
  have hx42 : Bounds (675025426407 / 1000000000000) (337551098389 / 500000000000) x42 := by
    exact bounds_biasE ha (by norm_num) (by norm_num) hx20.1 hx41.2
  let x43 : ℝ := a*z
  have hx43 : Bounds (16099 / 1000000) (40807 / 2500000) x43 := by
    apply bounds_mul ha hz <;> norm_num
  let x44 : ℝ := Real.log (2 / 1)
  have hx44 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x44 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x45 : ℝ := (1 / 1)+(40807 / 2500000)
  have hx45 : Bounds (2540807 / 2500000) (2540807 / 2500000) x45 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((40807 / 2500000) : ℝ)) <;> norm_num
  let x46 : ℝ := (1 / 1)+(40807 / 2500000)
  have hx46 : Bounds (2540807 / 2500000) (2540807 / 2500000) x46 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((40807 / 2500000) : ℝ)) <;> norm_num
  let x47 : ℝ := Real.log x46
  have hx47 : Bounds (3238203 / 200000000) (2023877 / 125000000) x47 := by
    exact bounds_log hx46 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x48 : ℝ := x45*x47
  have hx48 : Bounds (16455297699 / 1000000000000) (4113824679 / 250000000000) x48 := by
    apply bounds_mul hx45 hx47 <;> norm_num
  let x49 : ℝ := -(40807 / 2500000)
  have hx49 : Bounds (-40807 / 2500000) (-40807 / 2500000) x49 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((40807 / 2500000) : ℝ))
  let x50 : ℝ := (1 / 1)+x49
  have hx50 : Bounds (2459193 / 2500000) (2459193 / 2500000) x50 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx49 <;> norm_num
  let x51 : ℝ := (1 / 1)-(40807 / 2500000)
  have hx51 : Bounds (2459193 / 2500000) (2459193 / 2500000) x51 := by
    exact hx50
  let x52 : ℝ := -(40807 / 2500000)
  have hx52 : Bounds (-40807 / 2500000) (-40807 / 2500000) x52 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((40807 / 2500000) : ℝ))
  let x53 : ℝ := (1 / 1)+x52
  have hx53 : Bounds (2459193 / 2500000) (2459193 / 2500000) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx52 <;> norm_num
  let x54 : ℝ := (1 / 1)-(40807 / 2500000)
  have hx54 : Bounds (2459193 / 2500000) (2459193 / 2500000) x54 := by
    exact hx53
  let x55 : ℝ := Real.log x54
  have hx55 : Bounds (-3291497 / 200000000) (-4114371 / 250000000) x55 := by
    exact bounds_log hx54 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x56 : ℝ := x51*x55
  have hx56 : Bounds (-4047213191 / 250000000000) (-809442589 / 50000000000) x56 := by
    apply bounds_mul hx51 hx55 <;> norm_num
  let x57 : ℝ := x48+x56
  have hx57 : Bounds (53288987 / 200000000000) (33305867 / 125000000000) x57 := by
    apply bounds_add hx48 hx56 <;> norm_num
  let x58 : ℝ := (2 / 1)⁻¹
  have hx58 : Bounds (1 / 2) (1 / 2) x58 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x59 : ℝ := x57*x58
  have hx59 : Bounds (133222467 / 1000000000000) (33305867 / 250000000000) x59 := by
    apply bounds_mul hx57 hx58 <;> norm_num
  let x60 : ℝ := x57/(2 / 1)
  have hx60 : Bounds (133222467 / 1000000000000) (33305867 / 250000000000) x60 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx59
  let x61 : ℝ := -x60
  have hx61 : Bounds (-33305867 / 250000000000) (-133222467 / 1000000000000) x61 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx60
  let x62 : ℝ := x44+x61
  have hx62 : Bounds (173253489133 / 250000000000) (693013958533 / 1000000000000) x62 := by
    apply bounds_add hx44 hx61 <;> norm_num
  let x63 : ℝ := x44-x60
  have hx63 : Bounds (173253489133 / 250000000000) (693013958533 / 1000000000000) x63 := by
    exact hx62
  let x64 : ℝ := biasE (40807 / 2500000)
  have hx64 : Bounds (173253489133 / 250000000000) (693013958533 / 1000000000000) x64 := by
    simpa +zetaDelta only [biasE, div_one] using hx63
  let x65 : ℝ := Real.log (2 / 1)
  have hx65 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x65 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x66 : ℝ := (1 / 1)+(16099 / 1000000)
  have hx66 : Bounds (1016099 / 1000000) (1016099 / 1000000) x66 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((16099 / 1000000) : ℝ)) <;> norm_num
  let x67 : ℝ := (1 / 1)+(16099 / 1000000)
  have hx67 : Bounds (1016099 / 1000000) (1016099 / 1000000) x67 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((16099 / 1000000) : ℝ)) <;> norm_num
  let x68 : ℝ := Real.log x67
  have hx68 : Bounds (3194157 / 200000000) (7985393 / 500000000) x68 := by
    exact bounds_log hx67 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x69 : ℝ := x66*x68
  have hx69 : Bounds (16227898667 / 1000000000000) (4056974921 / 250000000000) x69 := by
    apply bounds_mul hx66 hx68 <;> norm_num
  let x70 : ℝ := -(16099 / 1000000)
  have hx70 : Bounds (-16099 / 1000000) (-16099 / 1000000) x70 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((16099 / 1000000) : ℝ))
  let x71 : ℝ := (1 / 1)+x70
  have hx71 : Bounds (983901 / 1000000) (983901 / 1000000) x71 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx70 <;> norm_num
  let x72 : ℝ := (1 / 1)-(16099 / 1000000)
  have hx72 : Bounds (983901 / 1000000) (983901 / 1000000) x72 := by
    exact hx71
  let x73 : ℝ := -(16099 / 1000000)
  have hx73 : Bounds (-16099 / 1000000) (-16099 / 1000000) x73 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((16099 / 1000000) : ℝ))
  let x74 : ℝ := (1 / 1)+x73
  have hx74 : Bounds (983901 / 1000000) (983901 / 1000000) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx73 <;> norm_num
  let x75 : ℝ := (1 / 1)-(16099 / 1000000)
  have hx75 : Bounds (983901 / 1000000) (983901 / 1000000) x75 := by
    exact hx74
  let x76 : ℝ := Real.log x75
  have hx76 : Bounds (-16229997 / 1000000000) (-4057499 / 250000000) x76 := by
    exact bounds_log hx75 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x77 : ℝ := x72*x76
  have hx77 : Bounds (-15968710279 / 1000000000000) (-7984354647 / 500000000000) x77 := by
    apply bounds_mul hx72 hx76 <;> norm_num
  let x78 : ℝ := x69+x77
  have hx78 : Bounds (64797097 / 250000000000) (25919039 / 100000000000) x78 := by
    apply bounds_add hx69 hx77 <;> norm_num
  let x79 : ℝ := (2 / 1)⁻¹
  have hx79 : Bounds (1 / 2) (1 / 2) x79 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x80 : ℝ := x78*x79
  have hx80 : Bounds (64797097 / 500000000000) (25919039 / 200000000000) x80 := by
    apply bounds_mul hx78 hx79 <;> norm_num
  let x81 : ℝ := x78/(2 / 1)
  have hx81 : Bounds (64797097 / 500000000000) (25919039 / 200000000000) x81 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx80
  let x82 : ℝ := -x81
  have hx82 : Bounds (-25919039 / 200000000000) (-64797097 / 500000000000) x82 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx81
  let x83 : ℝ := x65+x82
  have hx83 : Bounds (138603516961 / 200000000000) (346508793403 / 500000000000) x83 := by
    apply bounds_add hx65 hx82 <;> norm_num
  let x84 : ℝ := x65-x81
  have hx84 : Bounds (138603516961 / 200000000000) (346508793403 / 500000000000) x84 := by
    exact hx83
  let x85 : ℝ := biasE (16099 / 1000000)
  have hx85 : Bounds (138603516961 / 200000000000) (346508793403 / 500000000000) x85 := by
    simpa +zetaDelta only [biasE, div_one] using hx84
  let x86 : ℝ := biasE x43
  have hx86 : Bounds (173253489133 / 250000000000) (346508793403 / 500000000000) x86 := by
    exact bounds_biasE hx43 (by norm_num) (by norm_num) hx64.1 hx85.2
  let x87 : ℝ := x42+x86
  have hx87 : Bounds (1368039382939 / 1000000000000) (42753743237 / 31250000000) x87 := by
    apply bounds_add hx42 hx86 <;> norm_num
  let x88 : ℝ := (2 / 1)⁻¹
  have hx88 : Bounds (1 / 2) (1 / 2) x88 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x89 : ℝ := x87*x88
  have hx89 : Bounds (684019691469 / 1000000000000) (42753743237 / 62500000000) x89 := by
    apply bounds_mul hx87 hx88 <;> norm_num
  let x90 : ℝ := x87/(2 / 1)
  have hx90 : Bounds (684019691469 / 1000000000000) (42753743237 / 62500000000) x90 := by
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

theorem center_inputs_eq : centerInitial=inputBoxes ⟨208247502300,208687306952⟩ ⟨752087604397,752131805121⟩ ⟨104123751150,104343653476⟩ := rfl
theorem whole_inputs_eq : wholeInitial=inputBoxes ⟨208247502300,208687306952⟩ ⟨752087604397,752131805121⟩ ⟨95150196951,113317207675⟩ := rfl
noncomputable def centerUpper : ℝ := (437572924321 / 1099511627776)
noncomputable def secondUpper : ℝ := (202820757351391 / 274877906944)


theorem center_inputs {a z : ℝ} (ha : Bounds (947/5000) (949/5000) a)
    (hz : Bounds (17/200) (43/500) z) :
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

theorem whole_inputs {a z s : ℝ} (ha : Bounds (947/5000) (949/5000) a)
    (hz : Bounds (17/200) (43/500) z) (hs : s∈Icc (a*(1-z)/2) (a*(1+z)/2)) :
    RegistersContain wholeInitial (inputJets a ((biasE a+biasE (a*z))/2)) s := by
  rw [whole_inputs_eq]
  apply inputs_contain
  · norm_num [DyadicInterval.Contains,DyadicInterval.scale]
    constructor <;> linarith [ha.1,ha.2]
  · have h := entropy_bound ha hz
    norm_num [DyadicInterval.Contains,DyadicInterval.scale]
    constructor <;> linarith [h.1,h.2]
  · have hb : a*z≤(949/5000:ℝ)*(43/500) :=
      mul_le_mul ha.2 hz.2 (by linarith [hz.1]) (by norm_num)
    norm_num [DyadicInterval.Contains,DyadicInterval.scale]
    constructor <;> nlinarith [ha.1,ha.2,hs.1,hs.2]

theorem curvature_pos {a z : ℝ} (ha : Bounds (947/5000) (949/5000) a)
    (hz : Bounds (17/200) (43/500) z) : 0<curvature a (a*z) := by
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
    have hb : a*z≤(40807/2500000:ℝ) := by
      have h := mul_le_mul ha.2 hz.2 hz0.le (by norm_num : (0:ℝ)≤949/5000)
      norm_num at h
      exact h
    have hb2 := mul_self_le_mul_self hb0 hb
    have hle : centerUpper+secondUpper*(a*z)^2/24 ≤
        centerUpper+secondUpper*(40807/2500000:ℝ)^2/24 := by
      unfold centerUpper secondUpper
      nlinarith
    apply hle.trans_lt
    exact lt_of_lt_of_le (by norm_num [centerUpper,secondUpper] :
      centerUpper+secondUpper*(40807/2500000:ℝ)^2/24 < 2*(947/5000:ℝ)/(1-(947/5000:ℝ)^2)^2)
      (LowRatioFamily.base_mono (by norm_num) ha.1 ha1)

#print axioms entropy_bound
#print axioms curvature_pos
end GeneralCK.Certificates.ReflectionMidpointPostNextBandFamily.Cell0249

end


