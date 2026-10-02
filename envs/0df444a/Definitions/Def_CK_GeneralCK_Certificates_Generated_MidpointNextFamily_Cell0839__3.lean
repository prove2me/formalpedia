-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0839__3
-- name    : CK_GeneralCK_Certificates_Generated_MidpointNextFamily_Cell0839__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T12:05:26.354642+00:00
-- url     : https://prove2.me/theorems/6604acc4-f185-4b71-8cc9-febd2c8356b9
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0839 (+2 modules: GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0840, GeneralCK.Certificates…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0839 (+2 modules: GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0840, GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0841)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0839 (+2 modules: GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0840, GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0841)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0839 (+2 modules: GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0840, GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0841) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/MidpointNextFamily/Cell0839 (+2 modules: GeneralCK/Certificates/Generated/MidpointNextFamily/Cell0840, GeneralCK/Certificates/Generated/MidpointNextFamily/Cell0841).lean)

import Definitions.Def_CK_GeneralCK_Certificates_DyadicFastLog
import Definitions.Def_CK_GeneralCK_Certificates_BivariateProvedProgram
import Definitions.Def_CK_GeneralCK_Certificates_ReflectionMidpointKernel
import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers
import Definitions.Def_CK_GeneralCK_ReflectionSmallRatioMidpointJet

-- ===== source module GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0839 =====
section

namespace GeneralCK.Certificates.ReflectionMidpointNextFamily.Endpoints0839
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
noncomputable def out_w1 : DyadicInterval 40 := ⟨525847340224,525847340288⟩
theorem checked_w1 : DyadicFastLog.check 1099511627776 1773795278848 0 16 (lift40 out_w1.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w1 : out_w1.Contains (Real.log ((1773795278848:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w1
#print axioms endpoint_w1
noncomputable def out_w2 : DyadicInterval 40 := ⟨-1044531605504,-1044531586176⟩
theorem checked_w2 : DyadicFastLog.check 425227976704 1099511627776 1 16 (lift40 out_w2)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w2 : out_w2.Contains (Real.log ((425227976704:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w2
#print axioms endpoint_w2
noncomputable def out_w3 : DyadicInterval 40 := ⟨527812405632,527812405760⟩
theorem checked_w3 : DyadicFastLog.check 1099511627776 1776968269824 0 16 (lift40 out_w3.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w3 : out_w3.Contains (Real.log ((1776968269824:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w3
#print axioms endpoint_w3
noncomputable def out_w4 : DyadicInterval 40 := ⟨-1052766768832,-1052766749504⟩
theorem checked_w4 : DyadicFastLog.check 422054985728 1099511627776 1 16 (lift40 out_w4)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w4 : out_w4.Contains (Real.log ((422054985728:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w4
#print axioms endpoint_w4
noncomputable def out_w5 : DyadicInterval 40 := ⟨-524954345088,-524954344960⟩
theorem checked_w5 : DyadicFastLog.check 682101306447 1099511627776 0 16 (lift40 out_w5)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w5 : out_w5.Contains (Real.log ((682101306447:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w5
#print axioms endpoint_w5
noncomputable def out_w6 : DyadicInterval 40 := ⟨-518684247232,-518684247104⟩
theorem checked_w6 : DyadicFastLog.check 686002183567 1099511627776 0 16 (lift40 out_w6)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w6 : out_w6.Contains (Real.log ((686002183567:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w6
#print axioms endpoint_w6
noncomputable def out_w7 : DyadicInterval 40 := ⟨4528929262656,4528929366464⟩
theorem checked_w7 : DyadicFastLog.check 1099511627776 67619965107894 5 16 (lift40 out_w7.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w7 : out_w7.Contains (Real.log ((67619965107894:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w7
#print axioms endpoint_w7
noncomputable def out_w8 : DyadicInterval 40 := ⟨4601006938816,4601007054464⟩
theorem checked_w8 : DyadicFastLog.check 1099511627776 72201263557914 6 16 (lift40 out_w8.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w8 : out_w8.Contains (Real.log ((72201263557914:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w8
#print axioms endpoint_w8
noncomputable def out_w9 : DyadicInterval 40 := ⟨1570378925248,1570378963840⟩
theorem checked_w9 : DyadicFastLog.check 1099511627776 4586500985904 2 16 (lift40 out_w9.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w9 : out_w9.Contains (Real.log ((4586500985904:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w9
#print axioms endpoint_w9
noncomputable def out_w10 : DyadicInterval 40 := ⟨1580579154048,1580579192640⟩
theorem checked_w10 : DyadicFastLog.check 1099511627776 4629248180758 2 16 (lift40 out_w10.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w10 : out_w10.Contains (Real.log ((4629248180758:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w10
#print axioms endpoint_w10
noncomputable def out_w11 : DyadicInterval 40 := ⟨514352462848,514352462912⟩
theorem checked_w11 : DyadicFastLog.check 1099511627776 1755347681280 0 16 (lift40 out_w11.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w11 : out_w11.Contains (Real.log ((1755347681280:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w11
#print axioms endpoint_w11
noncomputable def out_w12 : DyadicInterval 40 := ⟨-997837363328,-997837344000⟩
theorem checked_w12 : DyadicFastLog.check 443675574272 1099511627776 1 16 (lift40 out_w12)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w12 : out_w12.Contains (Real.log ((443675574272:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w12
#print axioms endpoint_w12
noncomputable def out_w13 : DyadicInterval 40 := ⟨538412718464,538412718592⟩
theorem checked_w13 : DyadicFastLog.check 1099511627776 1794182742016 0 16 (lift40 out_w13.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w13 : out_w13.Contains (Real.log ((1794182742016:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w13
#print axioms endpoint_w13
noncomputable def out_w14 : DyadicInterval 40 := ⟨-1098553080256,-1098553060928⟩
theorem checked_w14 : DyadicFastLog.check 404840513536 1099511627776 1 16 (lift40 out_w14)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w14 : out_w14.Contains (Real.log ((404840513536:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w14
#print axioms endpoint_w14
noncomputable def out_w15 : DyadicInterval 40 := ⟨-560140343808,-560140343616⟩
theorem checked_w15 : DyadicFastLog.check 660618627676 1099511627776 0 16 (lift40 out_w15)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w15 : out_w15.Contains (Real.log ((660618627676:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w15
#print axioms endpoint_w15
noncomputable def out_w16 : DyadicInterval 40 := ⟨-483484882368,-483484882304⟩
theorem checked_w16 : DyadicFastLog.check 708318921660 1099511627776 0 16 (lift40 out_w16)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w16 : out_w16.Contains (Real.log ((708318921660:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w16
#print axioms endpoint_w16
noncomputable def out_w17 : DyadicInterval 40 := ⟨1512189806016,1512189840192⟩
theorem checked_w17 : DyadicFastLog.check 1099511627776 4350082128194 1 16 (lift40 out_w17.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w17 : out_w17.Contains (Real.log ((4350082128194:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w17
#print axioms endpoint_w17
noncomputable def out_w18 : DyadicInterval 40 := ⟨1636965778304,1636965816896⟩
theorem checked_w18 : DyadicFastLog.check 1099511627776 4872844296070 2 16 (lift40 out_w18.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w18 : out_w18.Contains (Real.log ((4872844296070:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w18
#print axioms endpoint_w18
end GeneralCK.Certificates.ReflectionMidpointNextFamily.Endpoints0839

namespace GeneralCK.Certificates.ReflectionMidpointNextFamily.Cell0839
open Set GeneralCK.Certificates.ReflectionMidpointNextFamily.Endpoints0839
open BivariateJetProgram (RegistersContain RegistersSound zeroBox zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
theorem lc0 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc1 : ProvedTranscendental.LogEncloses (⟨1773795278848,1773795278848⟩ : DyadicInterval 40) (⟨525847340224,525847340288⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w1
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w1
theorem lc2 : ProvedTranscendental.LogEncloses (⟨425227976704,425227976704⟩ : DyadicInterval 40) (⟨-1044531605504,-1044531586176⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w2
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w2
theorem lc3 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc4 : ProvedTranscendental.LogEncloses (⟨1776968269824,1776968269824⟩ : DyadicInterval 40) (⟨527812405632,527812405760⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w3
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w3
theorem lc5 : ProvedTranscendental.LogEncloses (⟨422054985728,422054985728⟩ : DyadicInterval 40) (⟨-1052766768832,-1052766749504⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w4
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w4
theorem lc6 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc7 : ProvedTranscendental.LogEncloses (⟨682101306447,686002183567⟩ : DyadicInterval 40) (⟨-524954345088,-518684247104⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w5
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w6
theorem lc8 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc9 : ProvedTranscendental.LogEncloses (⟨1773795278848,1776968269824⟩ : DyadicInterval 40) (⟨525847340224,527812405760⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w1
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w3
theorem lc10 : ProvedTranscendental.LogEncloses (⟨422054985728,425227976704⟩ : DyadicInterval 40) (⟨-1052766768832,-1044531586176⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w4
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w2
theorem lc11 : ProvedTranscendental.LogEncloses (⟨682101306447,686002183567⟩ : DyadicInterval 40) (⟨-524954345088,-518684247104⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w5
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w6
theorem lc12 : ProvedTranscendental.LogEncloses (⟨67619965107894,72201263557914⟩ : DyadicInterval 40) (⟨4528929262656,4601007054464⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w7
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
theorem lc13 : ProvedTranscendental.LogEncloses (⟨4586500985904,4629248180758⟩ : DyadicInterval 40) (⟨1570378925248,1580579192640⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w9
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w10
theorem lc14 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc15 : ProvedTranscendental.LogEncloses (⟨1755347681280,1755347681280⟩ : DyadicInterval 40) (⟨514352462848,514352462912⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w11
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w11
theorem lc16 : ProvedTranscendental.LogEncloses (⟨443675574272,443675574272⟩ : DyadicInterval 40) (⟨-997837363328,-997837344000⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w12
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w12
theorem lc17 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc18 : ProvedTranscendental.LogEncloses (⟨1794182742016,1794182742016⟩ : DyadicInterval 40) (⟨538412718464,538412718592⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w13
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w13
theorem lc19 : ProvedTranscendental.LogEncloses (⟨404840513536,404840513536⟩ : DyadicInterval 40) (⟨-1098553080256,-1098553060928⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w14
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w14
theorem lc20 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc21 : ProvedTranscendental.LogEncloses (⟨660618627676,708318921660⟩ : DyadicInterval 40) (⟨-560140343808,-483484882304⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w15
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w16
theorem lc22 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc23 : ProvedTranscendental.LogEncloses (⟨1755347681280,1794182742016⟩ : DyadicInterval 40) (⟨514352462848,538412718592⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w11
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w13
theorem lc24 : ProvedTranscendental.LogEncloses (⟨404840513536,443675574272⟩ : DyadicInterval 40) (⟨-1098553080256,-997837344000⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w14
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w12
theorem lc25 : ProvedTranscendental.LogEncloses (⟨660618627676,708318921660⟩ : DyadicInterval 40) (⟨-560140343808,-483484882304⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w15
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w16
theorem lc26 : ProvedTranscendental.LogEncloses (⟨67619965107894,72201263557914⟩ : DyadicInterval 40) (⟨4528929262656,4601007054464⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w7
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
theorem lc27 : ProvedTranscendental.LogEncloses (⟨4350082128194,4872844296070⟩ : DyadicInterval 40) (⟨1512189806016,1636965816896⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w17
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w18
theorem ew3_ok (x : ℝ) (hx : (⟨674283651072,674283651072⟩ : DyadicInterval 40).Contains x) : (⟨539942251437,539942274492⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨674283651072,674283651072⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨525847340224,525847340288⟩ : DyadicInterval 40)) (minus:=(⟨-1044531605504,-1044531586176⟩ : DyadicInterval 40))
    (lc0 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc1 lc2 (by decide) hx
theorem ew6_ok (x : ℝ) (hx : (⟨677456642048,677456642048⟩ : DyadicInterval 40).Contains x) : (⟨537668985158,537669008236⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨677456642048,677456642048⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨527812405632,527812405760⟩ : DyadicInterval 40)) (minus:=(⟨-1052766768832,-1052766749504⟩ : DyadicInterval 40))
    (lc3 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc4 lc5 (by decide) hx
theorem ew17_ok (x : ℝ) (hx : (⟨655836053504,655836053504⟩ : DyadicInterval 40).Contains x) : (⟨552870777786,552870801002⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨655836053504,655836053504⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨514352462848,514352462912⟩ : DyadicInterval 40)) (minus:=(⟨-997837363328,-997837344000⟩ : DyadicInterval 40))
    (lc14 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc15 lc16 (by decide) hx
theorem ew20_ok (x : ℝ) (hx : (⟨694671114240,694671114240⟩ : DyadicInterval 40).Contains x) : (⟨525076312316,525076335244⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨694671114240,694671114240⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨538412718464,538412718592⟩ : DyadicInterval 40)) (minus:=(⟨-1098553080256,-1098553060928⟩ : DyadicInterval 40))
    (lc17 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc18 lc19 (by decide) hx
theorem bw9_ok (x : ℝ) (hx : (⟨674283651072,677456642048⟩ : DyadicInterval 40).Contains x) : (⟨1021465507168,1024600575424⟩ : DyadicInterval 40).Contains (Reflection.biasB x) := by
  exact ProvedTranscendental.denominator_encloses (c:=(⟨674283651072,677456642048⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (gapLog:=(⟨-524954345088,-518684247104⟩ : DyadicInterval 40))
    (lc6 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc7 (by decide) hx
theorem bw23_ok (x : ℝ) (hx : (⟨655836053504,694671114240⟩ : DyadicInterval 40).Contains x) : (⟨1003865824768,1042193574784⟩ : DyadicInterval 40).Contains (Reflection.biasB x) := by
  exact ProvedTranscendental.denominator_encloses (c:=(⟨655836053504,694671114240⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (gapLog:=(⟨-560140343808,-483484882304⟩ : DyadicInterval 40))
    (lc20 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc21 (by decide) hx
theorem brcenter6_contact (y : ℝ) (hy : (⟨872641687487,880443372087⟩ : DyadicInterval 40).Contains y) : (⟨674283651072,677456642048⟩ : DyadicInterval 40).Contains (Reflection.biasContact y) := by
  exact ProvedTranscendental.contact_bracket (Y:=(⟨872641687487,880443372087⟩ : DyadicInterval 40)) (c:=(⟨674283651072,677456642048⟩ : DyadicInterval 40)) (elo:=(⟨539942251437,539942274492⟩ : DyadicInterval 40)) (ehi:=(⟨537668985158,537669008236⟩ : DyadicInterval 40))
    (by decide) (by decide) (by decide) (by decide)
    (ew3_ok _ (DyadicContact.point_contains 40 674283651072)) (ew6_ok _ (DyadicContact.point_contains 40 677456642048))
    (by decide) (by decide) hy
theorem brcenter6_jet (y : ℝ) (hy : (⟨872641687487,880443372087⟩ : DyadicInterval 40).Contains y) : (⟨⟨674283651072,677456642048⟩,⟨-449302985402,-443742130356⟩,⟨387763018500,407077226018⟩⟩ : DyadicJetEnclosure 40).Contains reflectionContactJet y := by
  exact ProvedTranscendental.contact_jet (c:=(⟨674283651072,677456642048⟩ : DyadicInterval 40)) (B:=(⟨1021465507168,1024600575424⟩ : DyadicInterval 40)) (by decide) brcenter6_contact bw9_ok (by decide) (by decide) (by decide) hy
theorem brwhole6_contact (y : ℝ) (hy : (⟨831087321417,926883288938⟩ : DyadicInterval 40).Contains y) : (⟨655836053504,694671114240⟩ : DyadicInterval 40).Contains (Reflection.biasContact y) := by
  exact ProvedTranscendental.contact_bracket (Y:=(⟨831087321417,926883288938⟩ : DyadicInterval 40)) (c:=(⟨655836053504,694671114240⟩ : DyadicInterval 40)) (elo:=(⟨552870777786,552870801002⟩ : DyadicInterval 40)) (ehi:=(⟨525076312316,525076335244⟩ : DyadicInterval 40))
    (by decide) (by decide) (by decide) (by decide)
    (ew17_ok _ (DyadicContact.point_contains 40 655836053504)) (ew20_ok _ (DyadicContact.point_contains 40 694671114240))
    (by decide) (by decide) hy
theorem brwhole6_jet (y : ℝ) (hy : (⟨831087321417,926883288938⟩ : DyadicInterval 40).Contains y) : (⟨⟨655836053504,694671114240⟩,⟨-480709617814,-412707331423⟩,⟨277363079924,513976124051⟩⟩ : DyadicJetEnclosure 40).Contains reflectionContactJet y := by
  exact ProvedTranscendental.contact_jet (c:=(⟨655836053504,694671114240⟩ : DyadicInterval 40)) (B:=(⟨1003865824768,1042193574784⟩ : DyadicInterval 40)) (by decide) brwhole6_contact bw23_ok (by decide) (by decide) (by decide) hy
noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨1064327255687,1066526278943⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨423231218432,426134592089⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨532163627843,533263139472⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
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
noncomputable def centerStep4 : Instruction 40 := ⟨.inv 6,⟨⟨2267034284071,2271718239210⟩,⟨0,0⟩,⟨-4693632725648,-4674297492923⟩,⟨0,0⟩,⟨0,0⟩,⟨19275453579036,19395176552294⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4
theorem centerAccepted4 : StepValid centerStep4.shape centerBoxes4 centerStep4.proposed := by
  dsimp only [StepValid,centerStep4]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep5 : Instruction 40 := ⟨.mul 6 0,⟨⟨872641687487,880443372087⟩,⟨0,0⟩,⟨-1819097876214,-1799261211311⟩,⟨0,0⟩,⟨0,0⟩,⟨7419633861068,7516933372796⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5
theorem centerAccepted5 : StepValid centerStep5.shape centerBoxes5 centerStep5.proposed := by
  dsimp only [StepValid,centerStep5]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep6 : Instruction 40 := ⟨.contact 0,⟨⟨674283651072,677456642048⟩,⟨0,0⟩,⟨726147848558,743353763502⟩,⟨0,0⟩,⟨0,0⟩,⟨-2033332505126,-1880157070965⟩⟩⟩
noncomputable def centerBoxes7 := centerStep6.proposed :: centerBoxes6
theorem centerAccepted6 : StepValid centerStep6.shape centerBoxes6 centerStep6.proposed := by
  dsimp only [StepValid,centerStep6]
  exact ⟨by decide,by decide,(⟨⟨674283651072,677456642048⟩,⟨-449302985402,-443742130356⟩,⟨387763018500,407077226018⟩⟩ : DyadicJetEnclosure 40),brcenter6_jet,by decide⟩
noncomputable def centerStep7 : Instruction 40 := ⟨.log 10,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes8 := centerStep7.proposed :: centerBoxes7
theorem centerAccepted7 : StepValid centerStep7.shape centerBoxes7 centerStep7.proposed := by
  dsimp only [StepValid,centerStep7]
  exact ⟨by decide,by decide,lc0,by decide⟩
noncomputable def centerStep8 : Instruction 40 := ⟨.add 6 1,⟨⟨1773795278848,1776968269824⟩,⟨0,0⟩,⟨726147848558,743353763502⟩,⟨0,0⟩,⟨0,0⟩,⟨-2033332505126,-1880157070965⟩⟩⟩
noncomputable def centerBoxes9 := centerStep8.proposed :: centerBoxes8
theorem centerAccepted8 : StepValid centerStep8.shape centerBoxes8 centerStep8.proposed := by
  dsimp only [StepValid,centerStep8]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep9 : Instruction 40 := ⟨.log 0,⟨⟨525847340224,527812405760⟩,⟨0,0⟩,⟨449309093770,460778149694⟩,⟨0,0⟩,⟨0,0⟩,⟨-1453490115228,-1346967998242⟩⟩⟩
noncomputable def centerBoxes10 := centerStep9.proposed :: centerBoxes9
theorem centerAccepted9 : StepValid centerStep9.shape centerBoxes9 centerStep9.proposed := by
  dsimp only [StepValid,centerStep9]
  exact ⟨by decide,by decide,lc9,by decide⟩
noncomputable def centerStep10 : Instruction 40 := ⟨.mul 1 0,⟨⟨848327117168,853020444497⟩,⟨0,0⟩,⟨1072135331966,1101524948973⟩,⟨0,0⟩,⟨0,0⟩,⟨-2731662128051,-2449158935252⟩⟩⟩
noncomputable def centerBoxes11 := centerStep10.proposed :: centerBoxes10
theorem centerAccepted10 : StepValid centerStep10.shape centerBoxes10 centerStep10.proposed := by
  dsimp only [StepValid,centerStep10]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep11 : Instruction 40 := ⟨.neg 4,⟨⟨-677456642048,-674283651072⟩,⟨0,0⟩,⟨-743353763502,-726147848558⟩,⟨0,0⟩,⟨0,0⟩,⟨1880157070965,2033332505126⟩⟩⟩
noncomputable def centerBoxes12 := centerStep11.proposed :: centerBoxes11
theorem centerAccepted11 : StepValid centerStep11.shape centerBoxes11 centerStep11.proposed := by
  dsimp only [StepValid,centerStep11]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep12 : Instruction 40 := ⟨.add 10 0,⟨⟨422054985728,425227976704⟩,⟨0,0⟩,⟨-743353763502,-726147848558⟩,⟨0,0⟩,⟨0,0⟩,⟨1880157070965,2033332505126⟩⟩⟩
noncomputable def centerBoxes13 := centerStep12.proposed :: centerBoxes12
theorem centerAccepted12 : StepValid centerStep12.shape centerBoxes12 centerStep12.proposed := by
  dsimp only [StepValid,centerStep12]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep13 : Instruction 40 := ⟨.log 0,⟨⟨-1052766768832,-1044531586176⟩,⟨0,0⟩,⟨-1936539394534,-1877599891621⟩,⟨0,0⟩,⟨0,0⟩,⟨1450747353392,2090796818593⟩⟩⟩
noncomputable def centerBoxes14 := centerStep13.proposed :: centerBoxes13
theorem centerAccepted13 : StepValid centerStep13.shape centerBoxes13 centerStep13.proposed := by
  dsimp only [StepValid,centerStep13]
  exact ⟨by decide,by decide,lc10,by decide⟩
noncomputable def centerStep14 : Instruction 40 := ⟨.mul 1 0,⟨⟨-407149748800,-400950524359⟩,⟨0,0⟩,⟨-59104754195,-8978764307⟩,⟨0,0⟩,⟨0,0⟩,⟨1090029859964,1640955404099⟩⟩⟩
noncomputable def centerBoxes15 := centerStep14.proposed :: centerBoxes14
theorem centerAccepted14 : StepValid centerStep14.shape centerBoxes14 centerStep14.proposed := by
  dsimp only [StepValid,centerStep14]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep15 : Instruction 40 := ⟨.add 4 0,⟨⟨441177368368,452069920138⟩,⟨0,0⟩,⟨1013030577771,1092546184666⟩,⟨0,0⟩,⟨0,0⟩,⟨-1641632268087,-808203531153⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15
theorem centerAccepted15 : StepValid centerStep15.shape centerBoxes15 centerStep15.proposed := by
  dsimp only [StepValid,centerStep15]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep16 : Instruction 40 := ⟨.mul 0 15,⟨⟨220588684184,226034960069⟩,⟨0,0⟩,⟨506515288885,546273092333⟩,⟨0,0⟩,⟨0,0⟩,⟨-820816134044,-404101765576⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16
theorem centerAccepted16 : StepValid centerStep16.shape centerBoxes16 centerStep16.proposed := by
  dsimp only [StepValid,centerStep16]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨-226034960069,-220588684184⟩,⟨0,0⟩,⟨-546273092333,-506515288885⟩,⟨0,0⟩,⟨0,0⟩,⟨404101765576,820816134044⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17
theorem centerAccepted17 : StepValid centerStep17.shape centerBoxes17 centerStep17.proposed := by
  dsimp only [StepValid,centerStep17]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep18 : Instruction 40 := ⟨.add 10 0,⟨⟨536088423547,541534718696⟩,⟨0,0⟩,⟨-546273092333,-506515288885⟩,⟨0,0⟩,⟨0,0⟩,⟨404101765576,820816134044⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18
theorem centerAccepted18 : StepValid centerStep18.shape centerBoxes18 centerStep18.proposed := by
  dsimp only [StepValid,centerStep18]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep19 : Instruction 40 := ⟨.mul 12 12,⟨⟨413509444209,417410321329⟩,⟨0,0⟩,⟨890631095068,916024772734⟩,⟨0,0⟩,⟨0,0⟩,⟨-1546511908827,-1300912766394⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19
theorem centerAccepted19 : StepValid centerStep19.shape centerBoxes19 centerStep19.proposed := by
  dsimp only [StepValid,centerStep19]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep20 : Instruction 40 := ⟨.neg 0,⟨⟨-417410321329,-413509444209⟩,⟨0,0⟩,⟨-916024772734,-890631095068⟩,⟨0,0⟩,⟨0,0⟩,⟨1300912766394,1546511908827⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20
theorem centerAccepted20 : StepValid centerStep20.shape centerBoxes20 centerStep20.proposed := by
  dsimp only [StepValid,centerStep20]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep21 : Instruction 40 := ⟨.add 19 0,⟨⟨682101306447,686002183567⟩,⟨0,0⟩,⟨-916024772734,-890631095068⟩,⟨0,0⟩,⟨0,0⟩,⟨1300912766394,1546511908827⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21
theorem centerAccepted21 : StepValid centerStep21.shape centerBoxes21 centerStep21.proposed := by
  dsimp only [StepValid,centerStep21]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep22 : Instruction 40 := ⟨.log 0,⟨⟨-524954345088,-518684247104⟩,⟨0,0⟩,⟨-1476584019754,-1427487067160⟩,⟨0,0⟩,⟨0,0⟩,⟨102107318695,639601373143⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22
theorem centerAccepted22 : StepValid centerStep22.shape centerBoxes22 centerStep22.proposed := by
  dsimp only [StepValid,centerStep22]
  exact ⟨by decide,by decide,lc7,by decide⟩
noncomputable def centerStep23 : Instruction 40 := ⟨.mul 0 22,⟨⟨-262477172544,-259342123552⟩,⟨0,0⟩,⟨-738292009877,-713743533580⟩,⟨0,0⟩,⟨0,0⟩,⟨51053659347,319800686572⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23
theorem centerAccepted23 : StepValid centerStep23.shape centerBoxes23 centerStep23.proposed := by
  dsimp only [StepValid,centerStep23]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep24 : Instruction 40 := ⟨.neg 0,⟨⟨259342123552,262477172544⟩,⟨0,0⟩,⟨713743533580,738292009877⟩,⟨0,0⟩,⟨0,0⟩,⟨-319800686572,-51053659347⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24
theorem centerAccepted24 : StepValid centerStep24.shape centerBoxes24 centerStep24.proposed := by
  dsimp only [StepValid,centerStep24]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep25 : Instruction 40 := ⟨.add 17 0,⟨⟨1021465507168,1024600575424⟩,⟨0,0⟩,⟨713743533580,738292009877⟩,⟨0,0⟩,⟨0,0⟩,⟨-319800686572,-51053659347⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25
theorem centerAccepted25 : StepValid centerStep25.shape centerBoxes25 centerStep25.proposed := by
  dsimp only [StepValid,centerStep25]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep26 : Instruction 40 := ⟨.add 24 26,⟨⟨2163838883463,2166037906719⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26
theorem centerAccepted26 : StepValid centerStep26.shape centerBoxes26 centerStep26.proposed := by
  dsimp only [StepValid,centerStep26]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep27 : Instruction 40 := ⟨.neg 27,⟨⟨-1066526278943,-1064327255687⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27
theorem centerAccepted27 : StepValid centerStep27.shape centerBoxes27 centerStep27.proposed := by
  dsimp only [StepValid,centerStep27]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep28 : Instruction 40 := ⟨.add 26 0,⟨⟨32985348833,35184372089⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28
theorem centerAccepted28 : StepValid centerStep28.shape centerBoxes28 centerStep28.proposed := by
  dsimp only [StepValid,centerStep28]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep29 : Instruction 40 := ⟨.inv 0,⟨⟨34359738367835,36650387592845⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29
theorem centerAccepted29 : StepValid centerStep29.shape centerBoxes29 centerStep29.proposed := by
  dsimp only [StepValid,centerStep29]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep30 : Instruction 40 := ⟨.mul 3 0,⟨⟨67619965107894,72201263557914⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30
theorem centerAccepted30 : StepValid centerStep30.shape centerBoxes30 centerStep30.proposed := by
  dsimp only [StepValid,centerStep30]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨4528929262656,4601007054464⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31
theorem centerAccepted31 : StepValid centerStep31.shape centerBoxes31 centerStep31.proposed := by
  dsimp only [StepValid,centerStep31]
  exact ⟨by decide,by decide,lc12,by decide⟩
noncomputable def centerStep32 : Instruction 40 := ⟨.mul 0 31,⟨⟨2264464631328,2300503527232⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32
theorem centerAccepted32 : StepValid centerStep32.shape centerBoxes32 centerStep32.proposed := by
  dsimp only [StepValid,centerStep32]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep33 : Instruction 40 := ⟨.inv 20,⟨⟨2843006306840,2864379904267⟩,⟨0,0⟩,⟨4854908487324,5044953036781⟩,⟨0,0⟩,⟨0,0⟩,⟨2781424662644,5200642515697⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33
theorem centerAccepted33 : StepValid centerStep33.shape centerBoxes33 centerStep33.proposed := by
  dsimp only [StepValid,centerStep33]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep34 : Instruction 40 := ⟨.mul 25 0,⟨⟨4586500985904,4629248180758⟩,⟨0,0⟩,⟨9709816974648,10089906073562⟩,⟨0,0⟩,⟨0,0⟩,⟨5602672785903,10365009052889⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34
theorem centerAccepted34 : StepValid centerStep34.shape centerBoxes34 centerStep34.proposed := by
  dsimp only [StepValid,centerStep34]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨1570378925248,1580579192640⟩,⟨0,0⟩,⟨2306218256250,2418830626044⟩,⟨0,0⟩,⟨0,0⟩,⟨-3990504806022,-2352496858379⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35
theorem centerAccepted35 : StepValid centerStep35.shape centerBoxes35 centerStep35.proposed := by
  dsimp only [StepValid,centerStep35]
  exact ⟨by decide,by decide,lc13,by decide⟩
noncomputable def centerStep36 : Instruction 40 := ⟨.mul 0 35,⟨⟨785189462624,790289596320⟩,⟨0,0⟩,⟨1153109128125,1209415313022⟩,⟨0,0⟩,⟨0,0⟩,⟨-1995252403011,-1176248429189⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36
theorem centerAccepted36 : StepValid centerStep36.shape centerBoxes36 centerStep36.proposed := by
  dsimp only [StepValid,centerStep36]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep37 : Instruction 40 := ⟨.mul 40 11,⟨⟨2042931014336,2049201150848⟩,⟨0,0⟩,⟨1427487067160,1476584019754⟩,⟨0,0⟩,⟨0,0⟩,⟨-639601373144,-102107318694⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37
theorem centerAccepted37 : StepValid centerStep37.shape centerBoxes37 centerStep37.proposed := by
  dsimp only [StepValid,centerStep37]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep38 : Instruction 40 := ⟨.add 0 17,⟨⟨1625520693007,1635691706639⟩,⟨0,0⟩,⟨511462294426,585952924686⟩,⟨0,0⟩,⟨0,0⟩,⟨661311393250,1444404590133⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38
theorem centerAccepted38 : StepValid centerStep38.shape centerBoxes38 centerStep38.proposed := by
  dsimp only [StepValid,centerStep38]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep39 : Instruction 40 := ⟨.mul 20 0,⟨⟨792554443030,805615716880⟩,⟨0,0⟩,⟨-563291315818,-460238180646⟩,⟨0,0⟩,⟨0,0⟩,⟨337619469105,1461258246221⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39
theorem centerAccepted39 : StepValid centerStep39.shape centerBoxes39 centerStep39.proposed := by
  dsimp only [StepValid,centerStep39]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep40 : Instruction 40 := ⟨.mul 43 41,⟨⟨846462436864,852269184178⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40
theorem centerAccepted40 : StepValid centerStep40.shape centerBoxes40 centerStep40.proposed := by
  dsimp only [StepValid,centerStep40]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep41 : Instruction 40 := ⟨.mul 19 19,⟨⟨423153498792,428007293394⟩,⟨0,0⟩,⟨-1143043835868,-1105037214998⟩,⟨0,0⟩,⟨0,0⟩,⟨3056953655745,3456101568428⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41
theorem centerAccepted41 : StepValid centerStep41.shape centerBoxes41 centerStep41.proposed := by
  dsimp only [StepValid,centerStep41]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep42 : Instruction 40 := ⟨.mul 1 0,⟨⟨325766033488,331763136968⟩,⟨0,0⟩,⟨-886012492152,-850716327324⟩,⟨0,0⟩,⟨0,0⟩,⟨2353405253254,2678942895874⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42
theorem centerAccepted42 : StepValid centerStep42.shape centerBoxes42 centerStep42.proposed := by
  dsimp only [StepValid,centerStep42]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep43 : Instruction 40 := ⟨.mul 17 17,⟨⟨948959297906,954793303353⟩,⟨0,0⟩,⟨1326160419040,1375982570882⟩,⟨0,0⟩,⟨0,0⟩,⟨330622905028,896626333653⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43
theorem centerAccepted43 : StepValid centerStep43.shape centerBoxes43 centerStep43.proposed := by
  dsimp only [StepValid,centerStep43]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep44 : Instruction 40 := ⟨.mul 18 0,⟨⟨881599763049,889742084862⟩,⟨0,0⟩,⟨1848039289626,1923352829954⟩,⟨0,0⟩,⟨0,0⟩,⟨1751189471704,2639344428005⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44
theorem centerAccepted44 : StepValid centerStep44.shape centerBoxes44 centerStep44.proposed := by
  dsimp only [StepValid,centerStep44]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep45 : Instruction 40 := ⟨.mul 2 0,⟨⟨261202565463,268467943139⟩,⟨0,0⟩,⟨-169433563197,-101766767537⟩,⟨0,0⟩,⟨0,0⟩,⟨-693935095661,104492783007⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45
theorem centerAccepted45 : StepValid centerStep45.shape centerBoxes45 centerStep45.proposed := by
  dsimp only [StepValid,centerStep45]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep46 : Instruction 40 := ⟨.inv 0,⟨⟨4503054649577,4628307602844⟩,⟨0,0⟩,⟨1706949851709,3002231801712⟩,⟨0,0⟩,⟨0,0⟩,⟨-557441895678,16190892823151⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46
theorem centerAccepted46 : StepValid centerStep46.shape centerBoxes46 centerStep46.proposed := by
  dsimp only [StepValid,centerStep46]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep47 : Instruction 40 := ⟨.mul 7 0,⟨⟨3245910165541,3391175912299⟩,⟨0,0⟩,⟨-1140719896845,314837457978⟩,⟨0,0⟩,⟨0,0⟩,⟨-2101867026995,16585166477804⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47
theorem centerAccepted47 : StepValid centerStep47.shape centerBoxes47 centerStep47.proposed := by
  dsimp only [StepValid,centerStep47]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep48 : Instruction 40 := ⟨.neg 11,⟨⟨-790289596320,-785189462624⟩,⟨0,0⟩,⟨-1209415313022,-1153109128125⟩,⟨0,0⟩,⟨0,0⟩,⟨1176248429189,1995252403011⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48
theorem centerAccepted48 : StepValid centerStep48.shape centerBoxes48 centerStep48.proposed := by
  dsimp only [StepValid,centerStep48]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep49 : Instruction 40 := ⟨.mul 0 10,⟨⟨-1175676642146,-1160826031470⟩,⟨0,0⟩,⟨-2220352232786,-2070007715860⟩,⟨0,0⟩,⟨0,0⟩,⟨-588263572670,1423194944415⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49
theorem centerAccepted49 : StepValid centerStep49.shape centerBoxes49 centerStep49.proposed := by
  dsimp only [StepValid,centerStep49]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep50 : Instruction 40 := ⟨.mul 53 43,⟨⟨1348567302144,1354913284096⟩,⟨0,0⟩,⟨1452295697116,1486707527004⟩,⟨0,0⟩,⟨0,0⟩,⟨-4066665010252,-3760314141930⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50
theorem centerAccepted50 : StepValid centerStep50.shape centerBoxes50 centerStep50.proposed := by
  dsimp only [StepValid,centerStep50]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep51 : Instruction 40 := ⟨.inv 29,⟨⟨1762276926479,1772355232557⟩,⟨0,0⟩,⟨2287949902260,2380176205152⟩,⟨0,0⟩,⟨0,0⟩,⟨1922435314349,3050967072360⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51
theorem centerAccepted51 : StepValid centerStep51.shape centerBoxes51 centerStep51.proposed := by
  dsimp only [StepValid,centerStep51]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep52 : Instruction 40 := ⟨.mul 1 0,⟨⟨2161458760722,2184049343422⟩,⟨0,0⟩,⟨5133917170117,5329553663267⟩,⟨0,0⟩,⟨0,0⟩,⟨1846745355558,4169426326040⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52
theorem centerAccepted52 : StepValid centerStep52.shape centerBoxes52 centerStep52.proposed := by
  dsimp only [StepValid,centerStep52]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep53 : Instruction 40 := ⟨.neg 2,⟨⟨-1354913284096,-1348567302144⟩,⟨0,0⟩,⟨-1486707527004,-1452295697116⟩,⟨0,0⟩,⟨0,0⟩,⟨3760314141930,4066665010252⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53
theorem centerAccepted53 : StepValid centerStep53.shape centerBoxes53 centerStep53.proposed := by
  dsimp only [StepValid,centerStep53]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep54 : Instruction 40 := ⟨.add 1 0,⟨⟨806545476626,835482041278⟩,⟨0,0⟩,⟨3647209643113,3877257966151⟩,⟨0,0⟩,⟨0,0⟩,⟨5607059497488,8236091336292⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54
theorem centerAccepted54 : StepValid centerStep54.shape centerBoxes54 centerStep54.proposed := by
  dsimp only [StepValid,centerStep54]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep55 : Instruction 40 := ⟨.mul 36 0,⟨⟨393247040013,411494085892⟩,⟨0,0⟩,⟨1363173859903,1538084858948⟩,⟨0,0⟩,⟨0,0⟩,⟨-822435376922,1319832928974⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55
theorem centerAccepted55 : StepValid centerStep55.shape centerBoxes55 centerStep55.proposed := by
  dsimp only [StepValid,centerStep55]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep56 : Instruction 40 := ⟨.add 6 0,⟨⟨-782429602133,-749331945578⟩,⟨0,0⟩,⟨-857178372883,-531922856912⟩,⟨0,0⟩,⟨0,0⟩,⟨-1410698949592,2743027873389⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56
theorem centerAccepted56 : StepValid centerStep56.shape centerBoxes56 centerStep56.proposed := by
  dsimp only [StepValid,centerStep56]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep57 : Instruction 40 := ⟨.mul 0 10,⟨⟨-3293575788341,-3068892239399⟩,⟨0,0⟩,⟨-5744659769638,-3341801627737⟩,⟨0,0⟩,⟨0,0⟩,⟨-22140992628135,10291664255797⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57
theorem centerAccepted57 : StepValid centerStep57.shape centerBoxes57 centerStep57.proposed := by
  dsimp only [StepValid,centerStep57]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep58 : Instruction 40 := ⟨.mul 54 51,⟨⟨2697134604288,2709826568192⟩,⟨0,0⟩,⟨2904591394232,2973415054008⟩,⟨0,0⟩,⟨0,0⟩,⟨-8133330020504,-7520628283860⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58
theorem centerAccepted58 : StepValid centerStep58.shape centerBoxes58 centerStep58.proposed := by
  dsimp only [StepValid,centerStep58]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep59 : Instruction 40 := ⟨.mul 0 7,⟨⟨4322917521444,4368098686844⟩,⟨0,0⟩,⟨10267834340235,10659107326533⟩,⟨0,0⟩,⟨0,0⟩,⟨3693490711118,8338852652079⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59
theorem centerAccepted59 : StepValid centerStep59.shape centerBoxes59 centerStep59.proposed := by
  dsimp only [StepValid,centerStep59]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep60 : Instruction 40 := ⟨.mul 57 53,⟨⟨2022850953216,2032369926144⟩,⟨0,0⟩,⟨2178443545674,2230061290506⟩,⟨0,0⟩,⟨0,0⟩,⟨-6099997515378,-5640471212895⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60
theorem centerAccepted60 : StepValid centerStep60.shape centerBoxes60 centerStep60.proposed := by
  dsimp only [StepValid,centerStep60]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep61 : Instruction 40 := ⟨.mul 39 35,⟨⟨633684027825,639264028019⟩,⟨0,0⟩,⟨-410831592056,-366780125057⟩,⟨0,0⟩,⟨0,0⟩,⟨-221129077279,253174997967⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61
theorem centerAccepted61 : StepValid centerStep61.shape centerBoxes61 centerStep61.proposed := by
  dsimp only [StepValid,centerStep61]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep62 : Instruction 40 := ⟨.inv 0,⟨⟨1891121299849,1907773853421⟩,⟨0,0⟩,⟨1085037913060,1236852650641⟩,⟨0,0⟩,⟨0,0⟩,⟨482878580626,2269491569804⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62
theorem centerAccepted62 : StepValid centerStep62.shape centerBoxes62 centerStep62.proposed := by
  dsimp only [StepValid,centerStep62]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep63 : Instruction 40 := ⟨.mul 2 0,⟨⟨3479232440483,3526385813145⟩,⟨0,0⟩,⟨5743068837956,6155637267319⟩,⟨0,0⟩,⟨0,0⟩,⟨-5396247335403,-489175728284⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63
theorem centerAccepted63 : StepValid centerStep63.shape centerBoxes63 centerStep63.proposed := by
  dsimp only [StepValid,centerStep63]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep64 : Instruction 40 := ⟨.neg 0,⟨⟨-3526385813145,-3479232440483⟩,⟨0,0⟩,⟨-6155637267319,-5743068837956⟩,⟨0,0⟩,⟨0,0⟩,⟨489175728284,5396247335403⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64
theorem centerAccepted64 : StepValid centerStep64.shape centerBoxes64 centerStep64.proposed := by
  dsimp only [StepValid,centerStep64]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep65 : Instruction 40 := ⟨.add 5 0,⟨⟨796531708299,888866246361⟩,⟨0,0⟩,⟨4112197072916,4916038488577⟩,⟨0,0⟩,⟨0,0⟩,⟨4182666439402,13735099987482⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65
theorem centerAccepted65 : StepValid centerStep65.shape centerBoxes65 centerStep65.proposed := by
  dsimp only [StepValid,centerStep65]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep66 : Instruction 40 := ⟨.mul 18 0,⟨⟨2351471602326,2741491520206⟩,⟨0,0⟩,⟨11217593845529,15416844413161⟩,⟨0,0⟩,⟨0,0⟩,⟨448048945086,58585684223633⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66
theorem centerAccepted66 : StepValid centerStep66.shape centerBoxes66 centerStep66.proposed := by
  dsimp only [StepValid,centerStep66]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep67 : Instruction 40 := ⟨.add 9 0,⟨⟨-942104186015,-327400719193⟩,⟨0,0⟩,⟨5472934075891,12075042785424⟩,⟨0,0⟩,⟨0,0⟩,⟨-21692943683049,68877348479430⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67
theorem centerAccepted67 : StepValid centerStep67.shape centerBoxes67 centerStep67.proposed := by
  dsimp only [StepValid,centerStep67]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep68 : Instruction 40 := ⟨.mul 61 29,⟨⟨996862607074,1007820365890⟩,⟨0,0⟩,⟨1387196805157,1466883338086⟩,⟨0,0⟩,⟨0,0⟩,⟨-1943771317481,-1097370948596⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68
theorem centerAccepted68 : StepValid centerStep68.shape centerBoxes68 centerStep68.proposed := by
  dsimp only [StepValid,centerStep68]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep69 : Instruction 40 := ⟨.mul 27 25,⟨⟨365212551623,371672738328⟩,⟨0,0⟩,⟨-482215162857,-418099047041⟩,⟨0,0⟩,⟨0,0⟩,⟨-95304092509,684587586242⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69
theorem centerAccepted69 : StepValid centerStep69.shape centerBoxes69 centerStep69.proposed := by
  dsimp only [StepValid,centerStep69]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨3252662073234,3310197895013⟩,⟨0,0⟩,⟨3658957929718,4370681155233⟩,⟨0,0⟩,⟨0,0⟩,⟨2027074196307,12405632929123⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70
theorem centerAccepted70 : StepValid centerStep70.shape centerBoxes70 centerStep70.proposed := by
  dsimp only [StepValid,centerStep70]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep71 : Instruction 40 := ⟨.mul 2 0,⟨⟨2948997638900,3034151499124⟩,⟨0,0⟩,⟨7421077295692,8422408081077⟩,⟨0,0⟩,⟨0,0⟩,⟨5218531664620,19786813371280⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71
theorem centerAccepted71 : StepValid centerStep71.shape centerBoxes71 centerStep71.proposed := by
  dsimp only [StepValid,centerStep71]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep72 : Instruction 40 := ⟨.mul 65 39,⟨⟨1388699710637,1417439666128⟩,⟨0,0⟩,⟨1495514989232,1555315934564⟩,⟨0,0⟩,⟨0,0⟩,⟨-4254332998315,-3872218429516⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72
theorem centerAccepted72 : StepValid centerStep72.shape centerBoxes72 centerStep72.proposed := by
  dsimp only [StepValid,centerStep72]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep73 : Instruction 40 := ⟨.add 54 0,⟨⟨1924788134184,1958974384824⟩,⟨0,0⟩,⟨949241896899,1048800645679⟩,⟨0,0⟩,⟨0,0⟩,⟨-3850231232739,-3051402295472⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73
theorem centerAccepted73 : StepValid centerStep73.shape centerBoxes73 centerStep73.proposed := by
  dsimp only [StepValid,centerStep73]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep74 : Instruction 40 := ⟨.mul 0 0,⟨⟨3369504485358,3490259260068⟩,⟨0,0⟩,⟨3323456511900,3737247606610⟩,⟨0,0⟩,⟨0,0⟩,⟨-12080716590858,-8682618748152⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74
theorem centerAccepted74 : StepValid centerStep74.shape centerBoxes74 centerStep74.proposed := by
  dsimp only [StepValid,centerStep74]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep75 : Instruction 40 := ⟨.mul 7 0,⟨⟨-2990589436366,-1003334720581⟩,⟨0,0⟩,⟨13569842214947,37341058346412⟩,⟨0,0⟩,⟨0,0⟩,⟨-33190358551869,311079881165505⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75
theorem centerAccepted75 : StepValid centerStep75.shape centerBoxes75 centerStep75.proposed := by
  dsimp only [StepValid,centerStep75]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep76 : Instruction 40 := ⟨.mul 79 28,⟨⟨6491820331082,6782351824598⟩,⟨0,0⟩,⟨-2281439793690,629674915956⟩,⟨0,0⟩,⟨0,0⟩,⟨-4203734053990,33170332955608⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76
theorem centerAccepted76 : StepValid centerStep76.shape centerBoxes76 centerStep76.proposed := by
  dsimp only [StepValid,centerStep76]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep77 : Instruction 40 := ⟨.mul 0 3,⟨⟨11364480762968,12083959057465⟩,⟨0,0⟩,⟨1539797930532,7591417674107⟩,⟨0,0⟩,⟨0,0⟩,⟨-35592330474420,42283758423683⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77
theorem centerAccepted77 : StepValid centerStep77.shape centerBoxes77 centerStep77.proposed := by
  dsimp only [StepValid,centerStep77]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep78 : Instruction 40 := ⟨.add 45 29,⟨⟨1474175035008,1515314064608⟩,⟨0,0⟩,⟨-1209415313022,-1153109128125⟩,⟨0,0⟩,⟨0,0⟩,⟨1176248429189,1995252403011⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78
theorem centerAccepted78 : StepValid centerStep78.shape centerBoxes78 centerStep78.proposed := by
  dsimp only [StepValid,centerStep78]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep79 : Instruction 40 := ⟨.mul 1 0,⟨⟨15236977402852,16653751223134⟩,⟨0,0⟩,⟨-11227342345485,-1456196089102⟩,⟨0,0⟩,⟨0,0⟩,⟨-53595122043860,76972912295660⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79
theorem centerAccepted79 : StepValid centerStep79.shape centerBoxes79 centerStep79.proposed := by
  dsimp only [StepValid,centerStep79]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep80 : Instruction 40 := ⟨.add 4 0,⟨⟨12246387966486,15650416502553⟩,⟨0,0⟩,⟨2342499869462,35884862257310⟩,⟨0,0⟩,⟨0,0⟩,⟨-86785480595729,388052793461165⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80
theorem centerAccepted80 : StepValid centerStep80.shape centerBoxes80 centerStep80.proposed := by
  dsimp only [StepValid,centerStep80]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep81 : Instruction 40 := ⟨.mul 81 81,⟨⟨1030268783504,1034530490575⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81
theorem centerAccepted81 : StepValid centerStep81.shape centerBoxes81 centerStep81.proposed := by
  dsimp only [StepValid,centerStep81]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep82 : Instruction 40 := ⟨.neg 0,⟨⟨-1034530490575,-1030268783504⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82
theorem centerAccepted82 : StepValid centerStep82.shape centerBoxes82 centerStep82.proposed := by
  dsimp only [StepValid,centerStep82]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep83 : Instruction 40 := ⟨.add 81 0,⟨⟨64981137201,69242844272⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83
theorem centerAccepted83 : StepValid centerStep83.shape centerBoxes83 centerStep83.proposed := by
  dsimp only [StepValid,centerStep83]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep84 : Instruction 40 := ⟨.inv 0,⟨⟨17459216650109,18604257661346⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes85 := centerStep84.proposed :: centerBoxes84
theorem centerAccepted84 : StepValid centerStep84.shape centerBoxes84 centerStep84.proposed := by
  dsimp only [StepValid,centerStep84]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep85 : Instruction 40 := ⟨.mul 13 0,⟨⟨46827325312019,51339280865489⟩,⟨0,0⟩,⟨117839769047979,142511135044842⟩,⟨0,0⟩,⟨0,0⟩,⟨82865403717782,334802256708153⟩⟩⟩
noncomputable def centerBoxes86 := centerStep85.proposed :: centerBoxes85
theorem centerAccepted85 : StepValid centerStep85.shape centerBoxes85 centerStep85.proposed := by
  dsimp only [StepValid,centerStep85]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep86 : Instruction 40 := ⟨.add 5 0,⟨⟨59073713278505,66989697368042⟩,⟨0,0⟩,⟨120182268917441,178395997302152⟩,⟨0,0⟩,⟨0,0⟩,⟨-3920076877947,722855050169318⟩⟩⟩
noncomputable def centerBoxes87 := centerStep86.proposed :: centerBoxes86
theorem centerAccepted86 : StepValid centerStep86.shape centerBoxes86 centerStep86.proposed := by
  dsimp only [StepValid,centerStep86]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep87 : Instruction 40 := ⟨.mul 0 68,⟨⟨28802545625277,32993963868406⟩,⟨0,0⟩,⟨25314560795377,60650461153948⟩,⟨0,0⟩,⟨0,0⟩,⟨-157485312326157,295302941000678⟩⟩⟩
noncomputable def centerBoxes88 := centerStep87.proposed :: centerBoxes87
theorem centerAccepted87 : StepValid centerStep87.shape centerBoxes87 centerStep87.proposed := by
  dsimp only [StepValid,centerStep87]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep88 : Instruction 40 := ⟨.mul 0 69,⟨⟨14043245099306,16250284663460⟩,⟨0,0⟩,⟨-4049863201672,16603190217007⟩,⟨0,0⟩,⟨0,0⟩,⟨-127245616296040,146750925346735⟩⟩⟩
noncomputable def centerBoxes89 := centerStep88.proposed :: centerBoxes88
theorem centerAccepted88 : StepValid centerStep88.shape centerBoxes88 centerStep88.proposed := by
  dsimp only [StepValid,centerStep88]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep89 : Instruction 40 := ⟨.mul 90 63,⟨⟨393189194423,397101528745⟩,⟨0,0⟩,⟨274738836528,286137732903⟩,⟨0,0⟩,⟨0,0⟩,⟨-123944241862,-19651908997⟩⟩⟩
noncomputable def centerBoxes90 := centerStep89.proposed :: centerBoxes89
theorem centerAccepted89 : StepValid centerStep89.shape centerBoxes89 centerStep89.proposed := by
  dsimp only [StepValid,centerStep89]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep90 : Instruction 40 := ⟨.inv 0,⟨⟨3044374629922,3074666945995⟩,⟨0,0⟩,⟨-2237544270895,-2106282356613⟩,⟨0,0⟩,⟨0,0⟩,⟨3065168006623,4225901873846⟩⟩⟩
noncomputable def centerBoxes91 := centerStep90.proposed :: centerBoxes90
theorem centerAccepted90 : StepValid centerStep90.shape centerBoxes90 centerStep90.proposed := by
  dsimp only [StepValid,centerStep90]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep91 : Instruction 40 := ⟨.mul 2 0,⟨⟨38883535218795,45442187108848⟩,⟨0,0⟩,⟨-44394902825953,19527070231597⟩,⟨0,0⟩,⟨0,0⟩,⟨-384255810020412,489313446703139⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91
theorem centerAccepted91 : StepValid centerStep91.shape centerBoxes91 centerStep91.proposed := by
  dsimp only [StepValid,centerStep91]
  exact ⟨by decide,by decide⟩
noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91]
theorem centerAccepted : Accepted centerProgram centerInitial :=
  ⟨centerAccepted0,⟨centerAccepted1,⟨centerAccepted2,⟨centerAccepted3,⟨centerAccepted4,⟨centerAccepted5,⟨centerAccepted6,⟨centerAccepted7,⟨centerAccepted8,⟨centerAccepted9,⟨centerAccepted10,⟨centerAccepted11,⟨centerAccepted12,⟨centerAccepted13,⟨centerAccepted14,⟨centerAccepted15,⟨centerAccepted16,⟨centerAccepted17,⟨centerAccepted18,⟨centerAccepted19,⟨centerAccepted20,⟨centerAccepted21,⟨centerAccepted22,⟨centerAccepted23,⟨centerAccepted24,⟨centerAccepted25,⟨centerAccepted26,⟨centerAccepted27,⟨centerAccepted28,⟨centerAccepted29,⟨centerAccepted30,⟨centerAccepted31,⟨centerAccepted32,⟨centerAccepted33,⟨centerAccepted34,⟨centerAccepted35,⟨centerAccepted36,⟨centerAccepted37,⟨centerAccepted38,⟨centerAccepted39,⟨centerAccepted40,⟨centerAccepted41,⟨centerAccepted42,⟨centerAccepted43,⟨centerAccepted44,⟨centerAccepted45,⟨centerAccepted46,⟨centerAccepted47,⟨centerAccepted48,⟨centerAccepted49,⟨centerAccepted50,⟨centerAccepted51,⟨centerAccepted52,⟨centerAccepted53,⟨centerAccepted54,⟨centerAccepted55,⟨centerAccepted56,⟨centerAccepted57,⟨centerAccepted58,⟨centerAccepted59,⟨centerAccepted60,⟨centerAccepted61,⟨centerAccepted62,⟨centerAccepted63,⟨centerAccepted64,⟨centerAccepted65,⟨centerAccepted66,⟨centerAccepted67,⟨centerAccepted68,⟨centerAccepted69,⟨centerAccepted70,⟨centerAccepted71,⟨centerAccepted72,⟨centerAccepted73,⟨centerAccepted74,⟨centerAccepted75,⟨centerAccepted76,⟨centerAccepted77,⟨centerAccepted78,⟨centerAccepted79,⟨centerAccepted80,⟨centerAccepted81,⟨centerAccepted82,⟨centerAccepted83,⟨centerAccepted84,⟨centerAccepted85,⟨centerAccepted86,⟨centerAccepted87,⟨centerAccepted88,⟨centerAccepted89,⟨centerAccepted90,⟨centerAccepted91,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
noncomputable def center_output : DyadicBivariateJetEnclosure 40 := ⟨⟨38883535218795,45442187108848⟩,⟨0,0⟩,⟨-44394902825953,19527070231597⟩,⟨0,0⟩,⟨0,0⟩,⟨-384255810020412,489313446703139⟩⟩
theorem center_output_eq : (finalBoxes centerProgram centerInitial).getD 0 (zeroBox 40)=center_output := rfl
noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨1064327255687,1066526278943⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨423231218432,426134592089⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨505500470870,559926296445⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
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
noncomputable def wholeStep4 : Instruction 40 := ⟨.inv 6,⟨⟨2159080270546,2391542420394⟩,⟨0,0⟩,⟨-5201832344523,-4239725617172⟩,⟨0,0⟩,⟨0,0⟩,⟨16650861530368,22628960715710⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4
theorem wholeAccepted4 : StepValid wholeStep4.shape wholeBoxes4 wholeStep4.proposed := by
  dsimp only [StepValid,wholeStep4]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep5 : Instruction 40 := ⟨.mul 6 0,⟨⟨831087321417,926883288938⟩,⟨0,0⟩,⟨-2016059356037,-1631982958108⟩,⟨0,0⟩,⟨0,0⟩,⟨6409358696546,8770241896843⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5
theorem wholeAccepted5 : StepValid wholeStep5.shape wholeBoxes5 wholeStep5.proposed := by
  dsimp only [StepValid,wholeStep5]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep6 : Instruction 40 := ⟨.contact 0,⟨⟨655836053504,694671114240⟩,⟨0,0⟩,⟨612573177539,881426897223⟩,⟨0,0⟩,⟨0,0⟩,⟨-3223319848705,-677761076359⟩⟩⟩
noncomputable def wholeBoxes7 := wholeStep6.proposed :: wholeBoxes6
theorem wholeAccepted6 : StepValid wholeStep6.shape wholeBoxes6 wholeStep6.proposed := by
  dsimp only [StepValid,wholeStep6]
  exact ⟨by decide,by decide,(⟨⟨655836053504,694671114240⟩,⟨-480709617814,-412707331423⟩,⟨277363079924,513976124051⟩⟩ : DyadicJetEnclosure 40),brwhole6_jet,by decide⟩
noncomputable def wholeStep7 : Instruction 40 := ⟨.log 10,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes8 := wholeStep7.proposed :: wholeBoxes7
theorem wholeAccepted7 : StepValid wholeStep7.shape wholeBoxes7 wholeStep7.proposed := by
  dsimp only [StepValid,wholeStep7]
  exact ⟨by decide,by decide,lc0,by decide⟩
noncomputable def wholeStep8 : Instruction 40 := ⟨.add 6 1,⟨⟨1755347681280,1794182742016⟩,⟨0,0⟩,⟨612573177539,881426897223⟩,⟨0,0⟩,⟨0,0⟩,⟨-3223319848705,-677761076359⟩⟩⟩
noncomputable def wholeBoxes9 := wholeStep8.proposed :: wholeBoxes8
theorem wholeAccepted8 : StepValid wholeStep8.shape wholeBoxes8 wholeStep8.proposed := by
  dsimp only [StepValid,wholeStep8]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep9 : Instruction 40 := ⟨.log 0,⟨⟨514352462848,538412718592⟩,⟨0,0⟩,⟨375397285791,552106646944⟩,⟨0,0⟩,⟨0,0⟩,⟨-2296251247223,-543514587265⟩⟩⟩
noncomputable def wholeBoxes10 := wholeStep9.proposed :: wholeBoxes9
theorem wholeAccepted9 : StepValid wholeStep9.shape wholeBoxes9 wholeStep9.proposed := by
  dsimp only [StepValid,wholeStep9]
  exact ⟨by decide,by decide,lc23,by decide⟩
noncomputable def wholeStep10 : Instruction 40 := ⟨.mul 1 0,⟨⟨821153119450,878581711532⟩,⟨0,0⟩,⟨885876286441,1332547680862⟩,⟨0,0⟩,⟨0,0⟩,⟨-4907136958847,-299571049108⟩⟩⟩
noncomputable def wholeBoxes11 := wholeStep10.proposed :: wholeBoxes10
theorem wholeAccepted10 : StepValid wholeStep10.shape wholeBoxes10 wholeStep10.proposed := by
  dsimp only [StepValid,wholeStep10]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep11 : Instruction 40 := ⟨.neg 4,⟨⟨-694671114240,-655836053504⟩,⟨0,0⟩,⟨-881426897223,-612573177539⟩,⟨0,0⟩,⟨0,0⟩,⟨677761076359,3223319848705⟩⟩⟩
noncomputable def wholeBoxes12 := wholeStep11.proposed :: wholeBoxes11
theorem wholeAccepted11 : StepValid wholeStep11.shape wholeBoxes11 wholeStep11.proposed := by
  dsimp only [StepValid,wholeStep11]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep12 : Instruction 40 := ⟨.add 10 0,⟨⟨404840513536,443675574272⟩,⟨0,0⟩,⟨-881426897223,-612573177539⟩,⟨0,0⟩,⟨0,0⟩,⟨677761076359,3223319848705⟩⟩⟩
noncomputable def wholeBoxes13 := wholeStep12.proposed :: wholeBoxes12
theorem wholeAccepted12 : StepValid wholeStep12.shape wholeBoxes12 wholeStep12.proposed := by
  dsimp only [StepValid,wholeStep12]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep13 : Instruction 40 := ⟨.log 0,⟨⟨-1098553080256,-997837344000⟩,⟨0,0⟩,⟨-2393878799498,-1518071696132⟩,⟨0,0⟩,⟨0,0⟩,⟨-3532381417063,6658287949753⟩⟩⟩
noncomputable def wholeBoxes14 := wholeStep13.proposed :: wholeBoxes13
theorem wholeAccepted13 : StepValid wholeStep13.shape wholeBoxes13 wholeStep13.proposed := by
  dsimp only [StepValid,wholeStep13]
  exact ⟨by decide,by decide,lc24,by decide⟩
noncomputable def wholeStep14 : Instruction 40 := ⟨.mul 1 0,⟨⟨-443288780617,-367404011531⟩,⟨0,0⟩,⟨-410052197026,321704017478⟩,⟨0,0⟩,⟨0,0⟩,⟨-2954365570028,5909789927150⟩⟩⟩
noncomputable def wholeBoxes15 := wholeStep14.proposed :: wholeBoxes14
theorem wholeAccepted14 : StepValid wholeStep14.shape wholeBoxes14 wholeStep14.proposed := by
  dsimp only [StepValid,wholeStep14]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep15 : Instruction 40 := ⟨.add 4 0,⟨⟨377864338833,511177700001⟩,⟨0,0⟩,⟨475824089415,1654251698340⟩,⟨0,0⟩,⟨0,0⟩,⟨-7861502528875,5610218878042⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15
theorem wholeAccepted15 : StepValid wholeStep15.shape wholeBoxes15 wholeStep15.proposed := by
  dsimp only [StepValid,wholeStep15]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 0 15,⟨⟨188932169416,255588850001⟩,⟨0,0⟩,⟨237912044707,827125849170⟩,⟨0,0⟩,⟨0,0⟩,⟨-3930751264438,2805109439021⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16
theorem wholeAccepted16 : StepValid wholeStep16.shape wholeBoxes16 wholeStep16.proposed := by
  dsimp only [StepValid,wholeStep16]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨-255588850001,-188932169416⟩,⟨0,0⟩,⟨-827125849170,-237912044707⟩,⟨0,0⟩,⟨0,0⟩,⟨-2805109439021,3930751264438⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17
theorem wholeAccepted17 : StepValid wholeStep17.shape wholeBoxes17 wholeStep17.proposed := by
  dsimp only [StepValid,wholeStep17]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep18 : Instruction 40 := ⟨.add 10 0,⟨⟨506534533615,573191233464⟩,⟨0,0⟩,⟨-827125849170,-237912044707⟩,⟨0,0⟩,⟨0,0⟩,⟨-2805109439021,3930751264438⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18
theorem wholeAccepted18 : StepValid wholeStep18.shape wholeBoxes18 wholeStep18.proposed := by
  dsimp only [StepValid,wholeStep18]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep19 : Instruction 40 := ⟨.mul 12 12,⟨⟨391192706116,438893000100⟩,⟨0,0⟩,⟨730774582260,1113770494732⟩,⟨0,0⟩,⟨0,0⟩,⟨-3390416701245,604656134984⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19
theorem wholeAccepted19 : StepValid wholeStep19.shape wholeBoxes19 wholeStep19.proposed := by
  dsimp only [StepValid,wholeStep19]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep20 : Instruction 40 := ⟨.neg 0,⟨⟨-438893000100,-391192706116⟩,⟨0,0⟩,⟨-1113770494732,-730774582260⟩,⟨0,0⟩,⟨0,0⟩,⟨-604656134984,3390416701245⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20
theorem wholeAccepted20 : StepValid wholeStep20.shape wholeBoxes20 wholeStep20.proposed := by
  dsimp only [StepValid,wholeStep20]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep21 : Instruction 40 := ⟨.add 19 0,⟨⟨660618627676,708318921660⟩,⟨0,0⟩,⟨-1113770494732,-730774582260⟩,⟨0,0⟩,⟨0,0⟩,⟨-604656134984,3390416701245⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21
theorem wholeAccepted21 : StepValid wholeStep21.shape wholeBoxes21 wholeStep21.proposed := by
  dsimp only [StepValid,wholeStep21]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep22 : Instruction 40 := ⟨.log 0,⟨⟨-560140343808,-483484882304⟩,⟨0,0⟩,⟨-1853722493324,-1134369174544⟩,⟨0,0⟩,⟨0,0⟩,⟨-4131654415059,4472564765176⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22
theorem wholeAccepted22 : StepValid wholeStep22.shape wholeBoxes22 wholeStep22.proposed := by
  dsimp only [StepValid,wholeStep22]
  exact ⟨by decide,by decide,lc21,by decide⟩
noncomputable def wholeStep23 : Instruction 40 := ⟨.mul 0 22,⟨⟨-280070171904,-241742441152⟩,⟨0,0⟩,⟨-926861246662,-567184587272⟩,⟨0,0⟩,⟨0,0⟩,⟨-2065827207530,2236282382588⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23
theorem wholeAccepted23 : StepValid wholeStep23.shape wholeBoxes23 wholeStep23.proposed := by
  dsimp only [StepValid,wholeStep23]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep24 : Instruction 40 := ⟨.neg 0,⟨⟨241742441152,280070171904⟩,⟨0,0⟩,⟨567184587272,926861246662⟩,⟨0,0⟩,⟨0,0⟩,⟨-2236282382588,2065827207530⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24
theorem wholeAccepted24 : StepValid wholeStep24.shape wholeBoxes24 wholeStep24.proposed := by
  dsimp only [StepValid,wholeStep24]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep25 : Instruction 40 := ⟨.add 17 0,⟨⟨1003865824768,1042193574784⟩,⟨0,0⟩,⟨567184587272,926861246662⟩,⟨0,0⟩,⟨0,0⟩,⟨-2236282382588,2065827207530⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25
theorem wholeAccepted25 : StepValid wholeStep25.shape wholeBoxes25 wholeStep25.proposed := by
  dsimp only [StepValid,wholeStep25]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep26 : Instruction 40 := ⟨.add 24 26,⟨⟨2163838883463,2166037906719⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26
theorem wholeAccepted26 : StepValid wholeStep26.shape wholeBoxes26 wholeStep26.proposed := by
  dsimp only [StepValid,wholeStep26]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep27 : Instruction 40 := ⟨.neg 27,⟨⟨-1066526278943,-1064327255687⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27
theorem wholeAccepted27 : StepValid wholeStep27.shape wholeBoxes27 wholeStep27.proposed := by
  dsimp only [StepValid,wholeStep27]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep28 : Instruction 40 := ⟨.add 26 0,⟨⟨32985348833,35184372089⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28
theorem wholeAccepted28 : StepValid wholeStep28.shape wholeBoxes28 wholeStep28.proposed := by
  dsimp only [StepValid,wholeStep28]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep29 : Instruction 40 := ⟨.inv 0,⟨⟨34359738367835,36650387592845⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29
theorem wholeAccepted29 : StepValid wholeStep29.shape wholeBoxes29 wholeStep29.proposed := by
  dsimp only [StepValid,wholeStep29]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep30 : Instruction 40 := ⟨.mul 3 0,⟨⟨67619965107894,72201263557914⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30
theorem wholeAccepted30 : StepValid wholeStep30.shape wholeBoxes30 wholeStep30.proposed := by
  dsimp only [StepValid,wholeStep30]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨4528929262656,4601007054464⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31
theorem wholeAccepted31 : StepValid wholeStep31.shape wholeBoxes31 wholeStep31.proposed := by
  dsimp only [StepValid,wholeStep31]
  exact ⟨by decide,by decide,lc12,by decide⟩
noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 0 31,⟨⟨2264464631328,2300503527232⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32
theorem wholeAccepted32 : StepValid wholeStep32.shape wholeBoxes32 wholeStep32.proposed := by
  dsimp only [StepValid,wholeStep32]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep33 : Instruction 40 := ⟨.inv 20,⟨⟨2724796877985,2986177961923⟩,⟨0,0⟩,⟨3762067552251,6501566635574⟩,⟨0,0⟩,⟨0,0⟩,⟨-13387390002410,24148269277345⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33
theorem wholeAccepted33 : StepValid wholeStep33.shape wholeBoxes33 wholeStep33.proposed := by
  dsimp only [StepValid,wholeStep33]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep34 : Instruction 40 := ⟨.mul 25 0,⟨⟨4350082128194,4872844296070⟩,⟨0,0⟩,⟨7524135104501,13003133271149⟩,⟨0,0⟩,⟨0,0⟩,⟨-26407858467972,48149520930976⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34
theorem wholeAccepted34 : StepValid wholeStep34.shape wholeBoxes34 wholeStep34.proposed := by
  dsimp only [StepValid,wholeStep34]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨1512189806016,1636965816896⟩,⟨0,0⟩,⟨1697750540275,3286626736660⟩,⟨0,0⟩,⟨0,0⟩,⟨-16499043191636,9548617105055⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35
theorem wholeAccepted35 : StepValid wholeStep35.shape wholeBoxes35 wholeStep35.proposed := by
  dsimp only [StepValid,wholeStep35]
  exact ⟨by decide,by decide,lc27,by decide⟩
noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 0 35,⟨⟨756094903008,818482908448⟩,⟨0,0⟩,⟨848875270137,1643313368330⟩,⟨0,0⟩,⟨0,0⟩,⟨-8249521595818,4774308552528⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36
theorem wholeAccepted36 : StepValid wholeStep36.shape wholeBoxes36 wholeStep36.proposed := by
  dsimp only [StepValid,wholeStep36]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep37 : Instruction 40 := ⟨.mul 40 11,⟨⟨2007731649536,2084387149568⟩,⟨0,0⟩,⟨1134369174544,1853722493324⟩,⟨0,0⟩,⟨0,0⟩,⟨-4472564765176,4131654415060⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37
theorem wholeAccepted37 : StepValid wholeStep37.shape wholeBoxes37 wholeStep37.proposed := by
  dsimp only [StepValid,wholeStep37]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep38 : Instruction 40 := ⟨.add 0 17,⟨⟨1568838649436,1693194443452⟩,⟨0,0⟩,⟨20598679812,1122947911064⟩,⟨0,0⟩,⟨0,0⟩,⟨-5077220900160,7522071116305⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38
theorem wholeAccepted38 : StepValid wholeStep38.shape wholeBoxes38 wholeStep38.proposed := by
  dsimp only [StepValid,wholeStep38]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep39 : Instruction 40 := ⟨.mul 20 0,⟨⟨722749021960,882686628335⟩,⟨0,0⟩,⟨-1264243973473,245943999614⟩,⟨0,0⟩,⟨0,0⟩,⟨-8656072818470,9965615456926⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39
theorem wholeAccepted39 : StepValid wholeStep39.shape wholeBoxes39 wholeStep39.proposed := by
  dsimp only [StepValid,wholeStep39]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep40 : Instruction 40 := ⟨.mul 43 41,⟨⟨846462436864,852269184178⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40
theorem wholeAccepted40 : StepValid wholeStep40.shape wholeBoxes40 wholeStep40.proposed := by
  dsimp only [StepValid,wholeStep40]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 19 19,⟨⟨396918923099,456307766201⟩,⟨0,0⟩,⟨-1435009318458,-878141330164⟩,⟨0,0⟩,⟨0,0⟩,⟨192343774996,6624724877365⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41
theorem wholeAccepted41 : StepValid wholeStep41.shape wholeBoxes41 wholeStep41.proposed := by
  dsimp only [StepValid,wholeStep41]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep42 : Instruction 40 := ⟨.mul 1 0,⟨⟨305569264022,353699804359⟩,⟨0,0⟩,⟨-1112324954311,-676039826650⟩,⟨0,0⟩,⟨0,0⟩,⟨148076451749,5135051530157⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42
theorem wholeAccepted42 : StepValid wholeStep42.shape wholeBoxes42 wholeStep42.proposed := by
  dsimp only [StepValid,wholeStep42]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep43 : Instruction 40 := ⟨.mul 17 17,⟨⟨916540188097,987863538577⟩,⟨0,0⟩,⟨1035691136162,1757087076818⟩,⟨0,0⟩,⟨0,0⟩,⟨-3654241981164,5478911794609⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43
theorem wholeAccepted43 : StepValid wholeStep43.shape wholeBoxes43 wholeStep43.proposed := by
  dsimp only [StepValid,wholeStep43]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep44 : Instruction 40 := ⟨.mul 18 0,⟨⟨836810951893,936365752449⟩,⟨0,0⟩,⟨1418395554457,2498233964338⟩,⟨0,0⟩,⟨0,0⟩,⟨-4404422035793,10011712112370⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44
theorem wholeAccepted44 : StepValid wholeStep44.shape wholeBoxes44 wholeStep44.proposed := by
  dsimp only [StepValid,wholeStep44]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 2 0,⟨⟨232561166463,301217718016⟩,⟨0,0⟩,⟨-553086381064,289135035540⟩,⟨0,0⟩,⟨0,0⟩,⟨-6358847873631,5849545446684⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45
theorem wholeAccepted45 : StepValid wholeStep45.shape wholeBoxes45 wholeStep45.proposed := by
  dsimp only [StepValid,wholeStep45]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep46 : Instruction 40 := ⟨.inv 0,⟨⟨4013461849380,5198313364184⟩,⟨0,0⟩,⟨-6462878313525,12362839290674⟩,⟨0,0⟩,⟨0,0⟩,⟨-161492268019092,200939480477118⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46
theorem wholeAccepted46 : StepValid wholeStep46.shape wholeBoxes46 wholeStep46.proposed := by
  dsimp only [StepValid,wholeStep46]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep47 : Instruction 40 := ⟨.mul 7 0,⟨⟨2638194588428,4173199792113⟩,⟨0,0⟩,⟨-11165532315135,11087656194075⟩,⟨0,0⟩,⟨0,0⟩,⟨-199000473649038,223292131024317⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47
theorem wholeAccepted47 : StepValid wholeStep47.shape wholeBoxes47 wholeStep47.proposed := by
  dsimp only [StepValid,wholeStep47]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep48 : Instruction 40 := ⟨.neg 11,⟨⟨-818482908448,-756094903008⟩,⟨0,0⟩,⟨-1643313368330,-848875270137⟩,⟨0,0⟩,⟨0,0⟩,⟨-4774308552528,8249521595818⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48
theorem wholeAccepted48 : StepValid wholeStep48.shape wholeBoxes48 wholeStep48.proposed := by
  dsimp only [StepValid,wholeStep48]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep49 : Instruction 40 := ⟨.mul 0 10,⟨⟨-1260423880599,-1078834344735⟩,⟨0,0⟩,⟨-3366551697028,-1225383029264⟩,⟨0,0⟩,⟨0,0⟩,⟨-16308358668242,16451568841689⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49
theorem wholeAccepted49 : StepValid wholeStep49.shape wholeBoxes49 wholeStep49.proposed := by
  dsimp only [StepValid,wholeStep49]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 53 43,⟨⟨1311672107008,1389342228480⟩,⟨0,0⟩,⟨1225146355078,1762853794446⟩,⟨0,0⟩,⟨0,0⟩,⟨-6446639697410,-1355522152718⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50
theorem wholeAccepted50 : StepValid wholeStep50.shape wholeBoxes50 wholeStep50.proposed := by
  dsimp only [StepValid,wholeStep50]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep51 : Instruction 40 := ⟨.inv 29,⟨⟨1706753529584,1829990510361⟩,⟨0,0⟩,⟨1760862317046,3085273939747⟩,⟨0,0⟩,⟨0,0⟩,⟨-5758475983296,12078207939180⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51
theorem wholeAccepted51 : StepValid wholeStep51.shape wholeBoxes51 wholeStep51.proposed := by
  dsimp only [StepValid,wholeStep51]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep52 : Instruction 40 := ⟨.mul 1 0,⟨⟨2036086696801,2312374903124⟩,⟨0,0⟩,⟨4002410470399,6832585391667⟩,⟨0,0⟩,⟨0,0⟩,⟨-14081847644968,23051139450092⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52
theorem wholeAccepted52 : StepValid wholeStep52.shape wholeBoxes52 wholeStep52.proposed := by
  dsimp only [StepValid,wholeStep52]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep53 : Instruction 40 := ⟨.neg 2,⟨⟨-1389342228480,-1311672107008⟩,⟨0,0⟩,⟨-1762853794446,-1225146355078⟩,⟨0,0⟩,⟨0,0⟩,⟨1355522152718,6446639697410⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53
theorem wholeAccepted53 : StepValid wholeStep53.shape wholeBoxes53 wholeStep53.proposed := by
  dsimp only [StepValid,wholeStep53]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep54 : Instruction 40 := ⟨.add 1 0,⟨⟨646744468321,1000702796116⟩,⟨0,0⟩,⟨2239556675953,5607439036589⟩,⟨0,0⟩,⟨0,0⟩,⟨-12726325492250,29497779147502⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54
theorem wholeAccepted54 : StepValid wholeStep54.shape wholeBoxes54 wholeStep54.proposed := by
  dsimp only [StepValid,wholeStep54]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 36 0,⟨⟨297949016047,521680767667⟩,⟨0,0⟩,⟨278947160362,2783296257891⟩,⟨0,0⟩,⟨0,0⟩,⟨-17624019724302,17985937283029⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55
theorem wholeAccepted55 : StepValid wholeStep55.shape wholeBoxes55 wholeStep55.proposed := by
  dsimp only [StepValid,wholeStep55]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep56 : Instruction 40 := ⟨.add 6 0,⟨⟨-962474864552,-557153577068⟩,⟨0,0⟩,⟨-3087604536666,1557913228627⟩,⟨0,0⟩,⟨0,0⟩,⟨-33932378392544,34437506124718⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56
theorem wholeAccepted56 : StepValid wholeStep56.shape wholeBoxes56 wholeStep56.proposed := by
  dsimp only [StepValid,wholeStep56]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep57 : Instruction 40 := ⟨.mul 0 10,⟨⟨-4550425684185,-2033734404729⟩,⟨0,0⟩,⟨-25419702067699,13022944664079⟩,⟨0,0⟩,⟨0,0⟩,⟨-405756011506846,340477365086084⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57
theorem wholeAccepted57 : StepValid wholeStep57.shape wholeBoxes57 wholeStep57.proposed := by
  dsimp only [StepValid,wholeStep57]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 54 51,⟨⟨2623344214016,2778684456960⟩,⟨0,0⟩,⟨2450292710156,3525707588892⟩,⟨0,0⟩,⟨0,0⟩,⟨-12893279394820,-2711044305436⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58
theorem wholeAccepted58 : StepValid wholeStep58.shape wholeBoxes58 wholeStep58.proposed := by
  dsimp only [StepValid,wholeStep58]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep59 : Instruction 40 := ⟨.mul 0 7,⟨⟨4072173393602,4624749806248⟩,⟨0,0⟩,⟨8004820940799,13665170783334⟩,⟨0,0⟩,⟨0,0⟩,⟨-28163695289935,46102278900183⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59
theorem wholeAccepted59 : StepValid wholeStep59.shape wholeBoxes59 wholeStep59.proposed := by
  dsimp only [StepValid,wholeStep59]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 57 53,⟨⟨1967508160512,2084013342720⟩,⟨0,0⟩,⟨1837719532617,2644280691669⟩,⟨0,0⟩,⟨0,0⟩,⟨-9669959546115,-2033283229077⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60
theorem wholeAccepted60 : StepValid wholeStep60.shape wholeBoxes60 wholeStep60.proposed := by
  dsimp only [StepValid,wholeStep60]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 39 35,⟨⟨603151841941,671393926543⟩,⟨0,0⟩,⟨-714928091576,-70109554121⟩,⟨0,0⟩,⟨0,0⟩,⟨-3891538001956,3790561861203⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61
theorem wholeAccepted61 : StepValid wholeStep61.shape wholeBoxes61 wholeStep61.proposed := by
  dsimp only [StepValid,wholeStep61]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep62 : Instruction 40 := ⟨.inv 0,⟨⟨1800620726254,2004347389083⟩,⟨0,0⟩,⟨188027790046,2375793546650⟩,⟨0,0⟩,⟨0,0⟩,⟨-12557231802457,18564209453925⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62
theorem wholeAccepted62 : StepValid wholeStep62.shape wholeBoxes62 wholeStep62.proposed := by
  dsimp only [StepValid,wholeStep62]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep63 : Instruction 40 := ⟨.mul 2 0,⟨⟨3222099597125,3799038224584⟩,⟨0,0⟩,⟨3346014719491,9323450786830⟩,⟨0,0⟩,⟨0,0⟩,⟨-40800216181977,43284142775525⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63
theorem wholeAccepted63 : StepValid wholeStep63.shape wholeBoxes63 wholeStep63.proposed := by
  dsimp only [StepValid,wholeStep63]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep64 : Instruction 40 := ⟨.neg 0,⟨⟨-3799038224584,-3222099597125⟩,⟨0,0⟩,⟨-9323450786830,-3346014719491⟩,⟨0,0⟩,⟨0,0⟩,⟨-43284142775525,40800216181977⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64
theorem wholeAccepted64 : StepValid wholeStep64.shape wholeBoxes64 wholeStep64.proposed := by
  dsimp only [StepValid,wholeStep64]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep65 : Instruction 40 := ⟨.add 5 0,⟨⟨273135169018,1402650209123⟩,⟨0,0⟩,⟨-1318629846031,10319156063843⟩,⟨0,0⟩,⟨0,0⟩,⟨-71447838065460,86902495082160⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65
theorem wholeAccepted65 : StepValid wholeStep65.shape wholeBoxes65 wholeStep65.proposed := by
  dsimp only [StepValid,wholeStep65]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 18 0,⟨⟨655367079900,5323763217457⟩,⟨0,0⟩,⟨-19248765998896,53310944367436⟩,⟨0,0⟩,⟨0,0⟩,⟨-734627883441701,822813251930294⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66
theorem wholeAccepted66 : StepValid wholeStep66.shape wholeBoxes66 wholeStep66.proposed := by
  dsimp only [StepValid,wholeStep66]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep67 : Instruction 40 := ⟨.add 9 0,⟨⟨-3895058604285,3290028812728⟩,⟨0,0⟩,⟨-44668468066595,66333889031515⟩,⟨0,0⟩,⟨0,0⟩,⟨-1140383894948547,1163290617016378⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67
theorem wholeAccepted67 : StepValid wholeStep67.shape wholeBoxes67 wholeStep67.proposed := by
  dsimp only [StepValid,wholeStep67]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 61 29,⟨⟨935779961246,1069759737819⟩,⟨0,0⟩,⟨886336996159,2066832713627⟩,⟨0,0⟩,⟨0,0⟩,⟨-8148590095301,5585807901359⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68
theorem wholeAccepted68 : StepValid wholeStep68.shape wholeBoxes68 wholeStep68.proposed := by
  dsimp only [StepValid,wholeStep68]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 27 25,⟨⟨330867027911,409972749003⟩,⟨0,0⟩,⟨-915413668550,-2800644215⟩,⟨0,0⟩,⟨0,0⟩,⟨-5942675536992,6571488281922⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69
theorem wholeAccepted69 : StepValid wholeStep69.shape wholeBoxes69 wholeStep69.proposed := by
  dsimp only [StepValid,wholeStep69]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨2948795554227,3653811705710⟩,⟨0,0⟩,⟨20144088186,10109043499538⟩,⟨0,0⟩,⟨0,0⟩,⟨-72569605677179,121563429529784⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70
theorem wholeAccepted70 : StepValid wholeStep70.shape wholeBoxes70 wholeStep70.proposed := by
  dsimp only [StepValid,wholeStep70]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 2 0,⟨⟨2509681316457,3554942534120⟩,⟨0,0⟩,⟨2394223909397,16703839070453⟩,⟨0,0⟩,⟨0,0⟩,⟨-97652216315388,174841767524997⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71
theorem wholeAccepted71 : StepValid wholeStep71.shape wholeBoxes71 wholeStep71.proposed := by
  dsimp only [StepValid,wholeStep71]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 65 39,⟨⟨1350706540606,1453457433468⟩,⟨0,0⟩,⟨1261605843535,1844205768120⟩,⟨0,0⟩,⟨0,0⟩,⟨-6744138482957,-1395861532642⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72
theorem wholeAccepted72 : StepValid wholeStep72.shape wholeBoxes72 wholeStep72.proposed := by
  dsimp only [StepValid,wholeStep72]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep73 : Instruction 40 := ⟨.add 54 0,⟨⟨1857241074221,2026648666932⟩,⟨0,0⟩,⟨434479994365,1606293723413⟩,⟨0,0⟩,⟨0,0⟩,⟨-9549247921978,2534889731796⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73
theorem wholeAccepted73 : StepValid wholeStep73.shape wholeBoxes73 wholeStep73.proposed := by
  dsimp only [StepValid,wholeStep73]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 0 0,⟨⟨3137160463460,3735571971609⟩,⟨0,0⟩,⟨1467804561728,5921525431872⟩,⟨0,0⟩,⟨0,0⟩,⟨-34859472554267,14038069678719⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74
theorem wholeAccepted74 : StepValid wholeStep74.shape wholeBoxes74 wholeStep74.proposed := by
  dsimp only [StepValid,wholeStep74]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep75 : Instruction 40 := ⟨.mul 7 0,⟨⟨-13233395065929,11177816685279⟩,⟨0,0⟩,⟨-172737569217307,243087020790072⟩,⟨0,0⟩,⟨0,0⟩,⟨-4459876184466652,4790245961035581⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75
theorem wholeAccepted75 : StepValid wholeStep75.shape wholeBoxes75 wholeStep75.proposed := by
  dsimp only [StepValid,wholeStep75]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep76 : Instruction 40 := ⟨.mul 79 28,⟨⟨5276389176856,8346399584226⟩,⟨0,0⟩,⟨-22331064630270,22175312388150⟩,⟨0,0⟩,⟨0,0⟩,⟨-398000947298076,446584262048634⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76
theorem wholeAccepted76 : StepValid wholeStep76.shape wholeBoxes76 wholeStep76.proposed := by
  dsimp only [StepValid,wholeStep76]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 0 3,⟨⟨8912617616108,15384302597389⟩,⟨0,0⟩,⟨-39076200504753,53067502954478⟩,⟨0,0⟩,⟨0,0⟩,⟨-871341786542374,907190708098654⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77
theorem wholeAccepted77 : StepValid wholeStep77.shape wholeBoxes77 wholeStep77.proposed := by
  dsimp only [StepValid,wholeStep77]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep78 : Instruction 40 := ⟨.add 45 29,⟨⟨1445981722880,1544408624224⟩,⟨0,0⟩,⟨-1643313368330,-848875270137⟩,⟨0,0⟩,⟨0,0⟩,⟨-4774308552528,8249521595818⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78
theorem wholeAccepted78 : StepValid wholeStep78.shape wholeBoxes78 wholeStep78.proposed := by
  dsimp only [StepValid,wholeStep78]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 1 0,⟨⟨11721096758183,21609275435439⟩,⟨0,0⟩,⟨-77880805458490,67659319522525⟩,⟨0,0⟩,⟨0,0⟩,⟨-1449343700465902,1506500825838164⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79
theorem wholeAccepted79 : StepValid wholeStep79.shape wholeBoxes79 wholeStep79.proposed := by
  dsimp only [StepValid,wholeStep79]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep80 : Instruction 40 := ⟨.add 4 0,⟨⟨-1512298307746,32787092120718⟩,⟨0,0⟩,⟨-250618374675797,310746340312597⟩,⟨0,0⟩,⟨0,0⟩,⟨-5909219884932554,6296746786873745⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80
theorem wholeAccepted80 : StepValid wholeStep80.shape wholeBoxes80 wholeStep80.proposed := by
  dsimp only [StepValid,wholeStep80]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep81 : Instruction 40 := ⟨.mul 81 81,⟨⟨1030268783504,1034530490575⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81
theorem wholeAccepted81 : StepValid wholeStep81.shape wholeBoxes81 wholeStep81.proposed := by
  dsimp only [StepValid,wholeStep81]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep82 : Instruction 40 := ⟨.neg 0,⟨⟨-1034530490575,-1030268783504⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82
theorem wholeAccepted82 : StepValid wholeStep82.shape wholeBoxes82 wholeStep82.proposed := by
  dsimp only [StepValid,wholeStep82]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep83 : Instruction 40 := ⟨.add 81 0,⟨⟨64981137201,69242844272⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83
theorem wholeAccepted83 : StepValid wholeStep83.shape wholeBoxes83 wholeStep83.proposed := by
  dsimp only [StepValid,wholeStep83]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep84 : Instruction 40 := ⟨.inv 0,⟨⟨17459216650109,18604257661346⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes85 := wholeStep84.proposed :: wholeBoxes84
theorem wholeAccepted84 : StepValid wholeStep84.shape wholeBoxes84 wholeStep84.proposed := by
  dsimp only [StepValid,wholeStep84]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep85 : Instruction 40 := ⟨.mul 13 0,⟨⟨39851392854646,60151311914567⟩,⟨0,0⟩,⟨38018037178547,282636870906905⟩,⟨0,0⟩,⟨0,0⟩,⟨-1652321765080137,2958405541903814⟩⟩⟩
noncomputable def wholeBoxes86 := wholeStep85.proposed :: wholeBoxes85
theorem wholeAccepted85 : StepValid wholeStep85.shape wholeBoxes85 wholeStep85.proposed := by
  dsimp only [StepValid,wholeStep85]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep86 : Instruction 40 := ⟨.add 5 0,⟨⟨38339094546900,92938404035285⟩,⟨0,0⟩,⟨-212600337497250,593383211219502⟩,⟨0,0⟩,⟨0,0⟩,⟨-7561541650012691,9255152328777559⟩⟩⟩
noncomputable def wholeBoxes87 := wholeStep86.proposed :: wholeBoxes86
theorem wholeAccepted86 : StepValid wholeStep86.shape wholeBoxes86 wholeStep86.proposed := by
  dsimp only [StepValid,wholeStep86]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep87 : Instruction 40 := ⟨.mul 0 68,⟨⟨17662455662080,48450127401485⟩,⟨0,0⟩,⟨-180746070366787,301043403287503⟩,⟨0,0⟩,⟨0,0⟩,⟨-5071812633644563,5476962903938558⟩⟩⟩
noncomputable def wholeBoxes88 := wholeStep87.proposed :: wholeBoxes87
theorem wholeAccepted87 : StepValid wholeStep87.shape wholeBoxes87 wholeStep87.proposed := by
  dsimp only [StepValid,wholeStep87]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep88 : Instruction 40 := ⟨.mul 0 69,⟨⟨8136925081350,25257748608734⟩,⟨0,0⟩,⟨-130672938927691,153116460492541⟩,⟨0,0⟩,⟨0,0⟩,⟨-3220546214138365,3300367112354454⟩⟩⟩
noncomputable def wholeBoxes89 := wholeStep88.proposed :: wholeBoxes88
theorem wholeAccepted88 : StepValid wholeStep88.shape wholeBoxes88 wholeStep88.proposed := by
  dsimp only [StepValid,wholeStep88]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep89 : Instruction 40 := ⟨.mul 90 63,⟨⟨386414609382,403919997433⟩,⟨0,0⟩,⟨218324406839,359220975288⟩,⟨0,0⟩,⟨0,0⟩,⟨-866709597995,800646770956⟩⟩⟩
noncomputable def wholeBoxes90 := wholeStep89.proposed :: wholeBoxes89
theorem wholeAccepted89 : StepValid wholeStep89.shape wholeBoxes89 wholeStep89.proposed := by
  dsimp only [StepValid,wholeStep89]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep90 : Instruction 40 := ⟨.inv 0,⟨⟨2992983331594,3128571721313⟩,⟨0,0⟩,⟨-2908400867105,-1617749343191⟩,⟨0,0⟩,⟨0,0⟩,⟨-4733533510880,12424686371400⟩⟩⟩
noncomputable def wholeBoxes91 := wholeStep90.proposed :: wholeBoxes90
theorem wholeAccepted90 : StepValid wholeStep90.shape wholeBoxes90 wholeStep90.proposed := by
  dsimp only [StepValid,wholeStep90]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 2 0,⟨⟨22149543964505,71868888009084⟩,⟨0,0⟩,⟨-438630485791507,423708409615352⟩,⟨0,0⟩,⟨0,0⟩,⟨-10082582143798268,10367651521249797⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91
theorem wholeAccepted91 : StepValid wholeStep91.shape wholeBoxes91 wholeStep91.proposed := by
  dsimp only [StepValid,wholeStep91]
  exact ⟨by decide,by decide⟩
noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91]
theorem wholeAccepted : Accepted wholeProgram wholeInitial :=
  ⟨wholeAccepted0,⟨wholeAccepted1,⟨wholeAccepted2,⟨wholeAccepted3,⟨wholeAccepted4,⟨wholeAccepted5,⟨wholeAccepted6,⟨wholeAccepted7,⟨wholeAccepted8,⟨wholeAccepted9,⟨wholeAccepted10,⟨wholeAccepted11,⟨wholeAccepted12,⟨wholeAccepted13,⟨wholeAccepted14,⟨wholeAccepted15,⟨wholeAccepted16,⟨wholeAccepted17,⟨wholeAccepted18,⟨wholeAccepted19,⟨wholeAccepted20,⟨wholeAccepted21,⟨wholeAccepted22,⟨wholeAccepted23,⟨wholeAccepted24,⟨wholeAccepted25,⟨wholeAccepted26,⟨wholeAccepted27,⟨wholeAccepted28,⟨wholeAccepted29,⟨wholeAccepted30,⟨wholeAccepted31,⟨wholeAccepted32,⟨wholeAccepted33,⟨wholeAccepted34,⟨wholeAccepted35,⟨wholeAccepted36,⟨wholeAccepted37,⟨wholeAccepted38,⟨wholeAccepted39,⟨wholeAccepted40,⟨wholeAccepted41,⟨wholeAccepted42,⟨wholeAccepted43,⟨wholeAccepted44,⟨wholeAccepted45,⟨wholeAccepted46,⟨wholeAccepted47,⟨wholeAccepted48,⟨wholeAccepted49,⟨wholeAccepted50,⟨wholeAccepted51,⟨wholeAccepted52,⟨wholeAccepted53,⟨wholeAccepted54,⟨wholeAccepted55,⟨wholeAccepted56,⟨wholeAccepted57,⟨wholeAccepted58,⟨wholeAccepted59,⟨wholeAccepted60,⟨wholeAccepted61,⟨wholeAccepted62,⟨wholeAccepted63,⟨wholeAccepted64,⟨wholeAccepted65,⟨wholeAccepted66,⟨wholeAccepted67,⟨wholeAccepted68,⟨wholeAccepted69,⟨wholeAccepted70,⟨wholeAccepted71,⟨wholeAccepted72,⟨wholeAccepted73,⟨wholeAccepted74,⟨wholeAccepted75,⟨wholeAccepted76,⟨wholeAccepted77,⟨wholeAccepted78,⟨wholeAccepted79,⟨wholeAccepted80,⟨wholeAccepted81,⟨wholeAccepted82,⟨wholeAccepted83,⟨wholeAccepted84,⟨wholeAccepted85,⟨wholeAccepted86,⟨wholeAccepted87,⟨wholeAccepted88,⟨wholeAccepted89,⟨wholeAccepted90,⟨wholeAccepted91,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
noncomputable def whole_output : DyadicBivariateJetEnclosure 40 := ⟨⟨22149543964505,71868888009084⟩,⟨0,0⟩,⟨-438630485791507,423708409615352⟩,⟨0,0⟩,⟨0,0⟩,⟨-10082582143798268,10367651521249797⟩⟩
theorem whole_output_eq : (finalBoxes wholeProgram wholeInitial).getD 0 (zeroBox 40)=whole_output := rfl
open GeneralCK.Reflection GeneralCK.Reflection.SmallRatio GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed
theorem sameShape : shapes centerProgram=shapes wholeProgram := by decide
theorem scalar_program (a e r : ℝ) :
    (evalRealProgram wholeProgram [a,e,r,2]).getD 0 0=ReflectionMidpointKernel.scalarCore a e r := rfl
attribute [local irreducible] wholeProgram centerProgram
noncomputable def reflection_log_0_out : DyadicInterval 64 := ⟨-12786308645202662930,-12786308645202655416⟩
theorem reflection_log_0_checked : DyadicFastLog.check 1 2 1 16 reflection_log_0_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointNextFamily.Endpoints0839.sharedTwo_eq]
  decide
theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := DyadicFastLog.check_sound reflection_log_0_checked
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1):ℝ)=((1 / 2):ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [he]
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_0_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_1_out : DyadicInterval 64 := ⟨-12507511236497960661,-12507511236497956826⟩
theorem reflection_log_1_checked : DyadicFastLog.check 100 197 0 16 reflection_log_1_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointNextFamily.Endpoints0839.sharedTwo_eq]
  decide
theorem reflection_log_1 : Bounds (339016771 / 500000000) (678033543 / 1000000000) (Real.log (197 / 100)) := by
  have h := DyadicFastLog.check_sound reflection_log_1_checked
  have he : Real.log (197 / 100) = -Real.log (100 / 197) := by
    rw [show ((197 / 100):ℝ)=((100 / 197):ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [he]
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_1_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_2_out : DyadicInterval 64 := ⟨-64684576111506834767,-64684576111506797190⟩
theorem reflection_log_2_checked : DyadicFastLog.check 3 100 5 16 reflection_log_2_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointNextFamily.Endpoints0839.sharedTwo_eq]
  decide
theorem reflection_log_2 : Bounds (-35065579 / 10000000) (-1753278947 / 500000000) (Real.log (3 / 100)) := by
  have h := DyadicFastLog.check_sound reflection_log_2_checked
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_2_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_3_out : DyadicInterval 64 := ⟨-12488774064674980437,-12488774064674976770⟩
theorem reflection_log_3_checked : DyadicFastLog.check 125 246 0 16 reflection_log_3_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointNextFamily.Endpoints0839.sharedTwo_eq]
  decide
theorem reflection_log_3 : Bounds (338508899 / 500000000) (677017799 / 1000000000) (Real.log (246 / 125)) := by
  have h := DyadicFastLog.check_sound reflection_log_3_checked
  have he : Real.log (246 / 125) = -Real.log (125 / 246) := by
    rw [show ((246 / 125):ℝ)=((125 / 246):ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [he]
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_3_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_4_out : DyadicInterval 64 := ⟨-63494050529186360327,-63494050529186327696⟩
theorem reflection_log_4_checked : DyadicFastLog.check 4 125 4 16 reflection_log_4_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointNextFamily.Endpoints0839.sharedTwo_eq]
  decide
theorem reflection_log_4 : Bounds (-1721009689 / 500000000) (-3442019373 / 1000000000) (Real.log (4 / 125)) := by
  have h := DyadicFastLog.check_sound reflection_log_4_checked
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_4_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_5_out : DyadicInterval 64 := ⟨-873648339059582357,-873648339059582308⟩
theorem reflection_log_5_checked : DyadicFastLog.check 2000 2097 0 16 reflection_log_5_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointNextFamily.Endpoints0839.sharedTwo_eq]
  decide
theorem reflection_log_5 : Bounds (47360571 / 1000000000) (11840143 / 250000000) (Real.log (2097 / 2000)) := by
  have h := DyadicFastLog.check_sound reflection_log_5_checked
  have he : Real.log (2097 / 2000) = -Real.log (2000 / 2097) := by
    rw [show ((2097 / 2000):ℝ)=((2000 / 2097):ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [he]
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_5_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_6_out : DyadicInterval 64 := ⟨-917090806633622749,-917090806633622704⟩
theorem reflection_log_6_checked : DyadicFastLog.check 1903 2000 0 16 reflection_log_6_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointNextFamily.Endpoints0839.sharedTwo_eq]
  decide
theorem reflection_log_6 : Bounds (-49715593 / 1000000000) (-6214449 / 125000000) (Real.log (1903 / 2000)) := by
  have h := DyadicFastLog.check_sound reflection_log_6_checked
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_6_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_7_out : DyadicInterval 64 := ⟨-177705767664229305,-177705767664229260⟩
theorem reflection_log_7_checked : DyadicFastLog.check 12500 12621 0 16 reflection_log_7_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointNextFamily.Endpoints0839.sharedTwo_eq]
  decide
theorem reflection_log_7 : Bounds (1204181 / 125000000) (9633449 / 1000000000) (Real.log (12621 / 12500)) := by
  have h := DyadicFastLog.check_sound reflection_log_7_checked
  have he : Real.log (12621 / 12500) = -Real.log (12500 / 12621) := by
    rw [show ((12621 / 12500):ℝ)=((12500 / 12621):ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [he]
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_7_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_8_out : DyadicInterval 64 := ⟨-179434352843676453,-179434352843676410⟩
theorem reflection_log_8_checked : DyadicFastLog.check 12379 12500 0 16 reflection_log_8_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointNextFamily.Endpoints0839.sharedTwo_eq]
  decide
theorem reflection_log_8 : Bounds (-2431789 / 250000000) (-1945431 / 200000000) (Real.log (12379 / 12500)) := by
  have h := DyadicFastLog.check_sound reflection_log_8_checked
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_8_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
theorem entropy_bound {a z : ℝ} (ha : Bounds (121 / 125) (97 / 100) a) (hz : Bounds (1 / 100) (1 / 20) z) :
  Bounds (384926550789 / 1000000000000) (387567153747 / 1000000000000) ((biasE a+biasE (a*z))/2) := by
  let x0 : ℝ := Real.log (2 / 1)
  have hx0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x0 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x1 : ℝ := (1 / 1)+(97 / 100)
  have hx1 : Bounds (197 / 100) (197 / 100) x1 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((97 / 100) : ℝ)) <;> norm_num
  let x2 : ℝ := (1 / 1)+(97 / 100)
  have hx2 : Bounds (197 / 100) (197 / 100) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((97 / 100) : ℝ)) <;> norm_num
  let x3 : ℝ := Real.log x2
  have hx3 : Bounds (339016771 / 500000000) (678033543 / 1000000000) x3 := by
    exact bounds_log hx2 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x4 : ℝ := x1*x3
  have hx4 : Bounds (66786303887 / 50000000000) (133572607971 / 100000000000) x4 := by
    apply bounds_mul hx1 hx3 <;> norm_num
  let x5 : ℝ := -(97 / 100)
  have hx5 : Bounds (-97 / 100) (-97 / 100) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((97 / 100) : ℝ))
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (3 / 100) (3 / 100) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-(97 / 100)
  have hx7 : Bounds (3 / 100) (3 / 100) x7 := by
    exact hx6
  let x8 : ℝ := -(97 / 100)
  have hx8 : Bounds (-97 / 100) (-97 / 100) x8 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((97 / 100) : ℝ))
  let x9 : ℝ := (1 / 1)+x8
  have hx9 : Bounds (3 / 100) (3 / 100) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx8 <;> norm_num
  let x10 : ℝ := (1 / 1)-(97 / 100)
  have hx10 : Bounds (3 / 100) (3 / 100) x10 := by
    exact hx9
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (-35065579 / 10000000) (-1753278947 / 500000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x12 : ℝ := x7*x11
  have hx12 : Bounds (-105196737 / 1000000000) (-5259836841 / 50000000000) x12 := by
    apply bounds_mul hx7 hx11 <;> norm_num
  let x13 : ℝ := x4+x12
  have hx13 : Bounds (61526467037 / 50000000000) (123052934289 / 100000000000) x13 := by
    apply bounds_add hx4 hx12 <;> norm_num
  let x14 : ℝ := (2 / 1)⁻¹
  have hx14 : Bounds (1 / 2) (1 / 2) x14 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x15 : ℝ := x13*x14
  have hx15 : Bounds (61526467037 / 100000000000) (123052934289 / 200000000000) x15 := by
    apply bounds_mul hx13 hx14 <;> norm_num
  let x16 : ℝ := x13/(2 / 1)
  have hx16 : Bounds (61526467037 / 100000000000) (123052934289 / 200000000000) x16 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx15
  let x17 : ℝ := -x16
  have hx17 : Bounds (-123052934289 / 200000000000) (-61526467037 / 100000000000) x17 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx16
  let x18 : ℝ := x0+x17
  have hx18 : Bounds (15576501711 / 200000000000) (7788251063 / 100000000000) x18 := by
    apply bounds_add hx0 hx17 <;> norm_num
  let x19 : ℝ := x0-x16
  have hx19 : Bounds (15576501711 / 200000000000) (7788251063 / 100000000000) x19 := by
    exact hx18
  let x20 : ℝ := biasE (97 / 100)
  have hx20 : Bounds (15576501711 / 200000000000) (7788251063 / 100000000000) x20 := by
    simpa +zetaDelta only [biasE, div_one] using hx19
  let x21 : ℝ := Real.log (2 / 1)
  have hx21 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x21 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x22 : ℝ := (1 / 1)+(121 / 125)
  have hx22 : Bounds (246 / 125) (246 / 125) x22 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((121 / 125) : ℝ)) <;> norm_num
  let x23 : ℝ := (1 / 1)+(121 / 125)
  have hx23 : Bounds (246 / 125) (246 / 125) x23 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((121 / 125) : ℝ)) <;> norm_num
  let x24 : ℝ := Real.log x23
  have hx24 : Bounds (338508899 / 500000000) (677017799 / 1000000000) x24 := by
    exact bounds_log hx23 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x25 : ℝ := x22*x24
  have hx25 : Bounds (41636594577 / 31250000000) (83273189277 / 62500000000) x25 := by
    apply bounds_mul hx22 hx24 <;> norm_num
  let x26 : ℝ := -(121 / 125)
  have hx26 : Bounds (-121 / 125) (-121 / 125) x26 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((121 / 125) : ℝ))
  let x27 : ℝ := (1 / 1)+x26
  have hx27 : Bounds (4 / 125) (4 / 125) x27 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx26 <;> norm_num
  let x28 : ℝ := (1 / 1)-(121 / 125)
  have hx28 : Bounds (4 / 125) (4 / 125) x28 := by
    exact hx27
  let x29 : ℝ := -(121 / 125)
  have hx29 : Bounds (-121 / 125) (-121 / 125) x29 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((121 / 125) : ℝ))
  let x30 : ℝ := (1 / 1)+x29
  have hx30 : Bounds (4 / 125) (4 / 125) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx29 <;> norm_num
  let x31 : ℝ := (1 / 1)-(121 / 125)
  have hx31 : Bounds (4 / 125) (4 / 125) x31 := by
    exact hx30
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (-1721009689 / 500000000) (-3442019373 / 1000000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x33 : ℝ := x28*x32
  have hx33 : Bounds (-1721009689 / 15625000000) (-3442019373 / 31250000000) x33 := by
    apply bounds_mul hx28 hx32 <;> norm_num
  let x34 : ℝ := x25+x33
  have hx34 : Bounds (38194575199 / 31250000000) (76389150531 / 62500000000) x34 := by
    apply bounds_add hx25 hx33 <;> norm_num
  let x35 : ℝ := (2 / 1)⁻¹
  have hx35 : Bounds (1 / 2) (1 / 2) x35 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x36 : ℝ := x34*x35
  have hx36 : Bounds (38194575199 / 62500000000) (76389150531 / 125000000000) x36 := by
    apply bounds_mul hx34 hx35 <;> norm_num
  let x37 : ℝ := x34/(2 / 1)
  have hx37 : Bounds (38194575199 / 62500000000) (76389150531 / 125000000000) x37 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx36
  let x38 : ℝ := -x37
  have hx38 : Bounds (-76389150531 / 125000000000) (-38194575199 / 62500000000) x38 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx37
  let x39 : ℝ := x21+x38
  have hx39 : Bounds (10254246969 / 125000000000) (10254247227 / 125000000000) x39 := by
    apply bounds_add hx21 hx38 <;> norm_num
  let x40 : ℝ := x21-x37
  have hx40 : Bounds (10254246969 / 125000000000) (10254247227 / 125000000000) x40 := by
    exact hx39
  let x41 : ℝ := biasE (121 / 125)
  have hx41 : Bounds (10254246969 / 125000000000) (10254247227 / 125000000000) x41 := by
    simpa +zetaDelta only [biasE, div_one] using hx40
  let x42 : ℝ := biasE a
  have hx42 : Bounds (15576501711 / 200000000000) (10254247227 / 125000000000) x42 := by
    exact bounds_biasE ha (by norm_num) (by norm_num) hx20.1 hx41.2
  let x43 : ℝ := a*z
  have hx43 : Bounds (121 / 12500) (97 / 2000) x43 := by
    apply bounds_mul ha hz <;> norm_num
  let x44 : ℝ := Real.log (2 / 1)
  have hx44 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x44 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x45 : ℝ := (1 / 1)+(97 / 2000)
  have hx45 : Bounds (2097 / 2000) (2097 / 2000) x45 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((97 / 2000) : ℝ)) <;> norm_num
  let x46 : ℝ := (1 / 1)+(97 / 2000)
  have hx46 : Bounds (2097 / 2000) (2097 / 2000) x46 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((97 / 2000) : ℝ)) <;> norm_num
  let x47 : ℝ := Real.log x46
  have hx47 : Bounds (47360571 / 1000000000) (11840143 / 250000000) x47 := by
    exact bounds_log hx46 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x48 : ℝ := x45*x47
  have hx48 : Bounds (49657558693 / 1000000000000) (24828779871 / 500000000000) x48 := by
    apply bounds_mul hx45 hx47 <;> norm_num
  let x49 : ℝ := -(97 / 2000)
  have hx49 : Bounds (-97 / 2000) (-97 / 2000) x49 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((97 / 2000) : ℝ))
  let x50 : ℝ := (1 / 1)+x49
  have hx50 : Bounds (1903 / 2000) (1903 / 2000) x50 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx49 <;> norm_num
  let x51 : ℝ := (1 / 1)-(97 / 2000)
  have hx51 : Bounds (1903 / 2000) (1903 / 2000) x51 := by
    exact hx50
  let x52 : ℝ := -(97 / 2000)
  have hx52 : Bounds (-97 / 2000) (-97 / 2000) x52 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((97 / 2000) : ℝ))
  let x53 : ℝ := (1 / 1)+x52
  have hx53 : Bounds (1903 / 2000) (1903 / 2000) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx52 <;> norm_num
  let x54 : ℝ := (1 / 1)-(97 / 2000)
  have hx54 : Bounds (1903 / 2000) (1903 / 2000) x54 := by
    exact hx53
  let x55 : ℝ := Real.log x54
  have hx55 : Bounds (-49715593 / 1000000000) (-6214449 / 125000000) x55 := by
    exact bounds_log hx54 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x56 : ℝ := x51*x55
  have hx56 : Bounds (-2365219337 / 50000000000) (-11826096447 / 250000000000) x56 := by
    apply bounds_mul hx51 hx55 <;> norm_num
  let x57 : ℝ := x48+x56
  have hx57 : Bounds (2353171953 / 1000000000000) (1176586977 / 500000000000) x57 := by
    apply bounds_add hx48 hx56 <;> norm_num
  let x58 : ℝ := (2 / 1)⁻¹
  have hx58 : Bounds (1 / 2) (1 / 2) x58 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x59 : ℝ := x57*x58
  have hx59 : Bounds (147073247 / 125000000000) (1176586977 / 1000000000000) x59 := by
    apply bounds_mul hx57 hx58 <;> norm_num
  let x60 : ℝ := x57/(2 / 1)
  have hx60 : Bounds (147073247 / 125000000000) (1176586977 / 1000000000000) x60 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx59
  let x61 : ℝ := -x60
  have hx61 : Bounds (-1176586977 / 1000000000000) (-147073247 / 125000000000) x61 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx60
  let x62 : ℝ := x44+x61
  have hx62 : Bounds (691970593023 / 1000000000000) (43248162189 / 62500000000) x62 := by
    apply bounds_add hx44 hx61 <;> norm_num
  let x63 : ℝ := x44-x60
  have hx63 : Bounds (691970593023 / 1000000000000) (43248162189 / 62500000000) x63 := by
    exact hx62
  let x64 : ℝ := biasE (97 / 2000)
  have hx64 : Bounds (691970593023 / 1000000000000) (43248162189 / 62500000000) x64 := by
    simpa +zetaDelta only [biasE, div_one] using hx63
  let x65 : ℝ := Real.log (2 / 1)
  have hx65 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x65 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x66 : ℝ := (1 / 1)+(121 / 12500)
  have hx66 : Bounds (12621 / 12500) (12621 / 12500) x66 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((121 / 12500) : ℝ)) <;> norm_num
  let x67 : ℝ := (1 / 1)+(121 / 12500)
  have hx67 : Bounds (12621 / 12500) (12621 / 12500) x67 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((121 / 12500) : ℝ)) <;> norm_num
  let x68 : ℝ := Real.log x67
  have hx68 : Bounds (1204181 / 125000000) (9633449 / 1000000000) x68 := by
    exact bounds_log hx67 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x69 : ℝ := x66*x68
  have hx69 : Bounds (37994921 / 3906250000) (9726700787 / 1000000000000) x69 := by
    apply bounds_mul hx66 hx68 <;> norm_num
  let x70 : ℝ := -(121 / 12500)
  have hx70 : Bounds (-121 / 12500) (-121 / 12500) x70 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((121 / 12500) : ℝ))
  let x71 : ℝ := (1 / 1)+x70
  have hx71 : Bounds (12379 / 12500) (12379 / 12500) x71 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx70 <;> norm_num
  let x72 : ℝ := (1 / 1)-(121 / 12500)
  have hx72 : Bounds (12379 / 12500) (12379 / 12500) x72 := by
    exact hx71
  let x73 : ℝ := -(121 / 12500)
  have hx73 : Bounds (-121 / 12500) (-121 / 12500) x73 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((121 / 12500) : ℝ))
  let x74 : ℝ := (1 / 1)+x73
  have hx74 : Bounds (12379 / 12500) (12379 / 12500) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx73 <;> norm_num
  let x75 : ℝ := (1 / 1)-(121 / 12500)
  have hx75 : Bounds (12379 / 12500) (12379 / 12500) x75 := by
    exact hx74
  let x76 : ℝ := Real.log x75
  have hx76 : Bounds (-2431789 / 250000000) (-1945431 / 200000000) x76 := by
    exact bounds_log hx75 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x77 : ℝ := x72*x76
  have hx77 : Bounds (-963299713 / 100000000000) (-9632996139 / 1000000000000) x77 := by
    apply bounds_mul hx72 hx76 <;> norm_num
  let x78 : ℝ := x69+x77
  have hx78 : Bounds (46851323 / 500000000000) (11713081 / 125000000000) x78 := by
    apply bounds_add hx69 hx77 <;> norm_num
  let x79 : ℝ := (2 / 1)⁻¹
  have hx79 : Bounds (1 / 2) (1 / 2) x79 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x80 : ℝ := x78*x79
  have hx80 : Bounds (46851323 / 1000000000000) (11713081 / 250000000000) x80 := by
    apply bounds_mul hx78 hx79 <;> norm_num
  let x81 : ℝ := x78/(2 / 1)
  have hx81 : Bounds (46851323 / 1000000000000) (11713081 / 250000000000) x81 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx80
  let x82 : ℝ := -x81
  have hx82 : Bounds (-11713081 / 250000000000) (-46851323 / 1000000000000) x82 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx81
  let x83 : ℝ := x65+x82
  have hx83 : Bounds (173275081919 / 250000000000) (693100329677 / 1000000000000) x83 := by
    apply bounds_add hx65 hx82 <;> norm_num
  let x84 : ℝ := x65-x81
  have hx84 : Bounds (173275081919 / 250000000000) (693100329677 / 1000000000000) x84 := by
    exact hx83
  let x85 : ℝ := biasE (121 / 12500)
  have hx85 : Bounds (173275081919 / 250000000000) (693100329677 / 1000000000000) x85 := by
    simpa +zetaDelta only [biasE, div_one] using hx84
  let x86 : ℝ := biasE x43
  have hx86 : Bounds (691970593023 / 1000000000000) (693100329677 / 1000000000000) x86 := by
    exact bounds_biasE hx43 (by norm_num) (by norm_num) hx64.1 hx85.2
  let x87 : ℝ := x42+x86
  have hx87 : Bounds (384926550789 / 500000000000) (775134307493 / 1000000000000) x87 := by
    apply bounds_add hx42 hx86 <;> norm_num
  let x88 : ℝ := (2 / 1)⁻¹
  have hx88 : Bounds (1 / 2) (1 / 2) x88 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x89 : ℝ := x87*x88
  have hx89 : Bounds (384926550789 / 1000000000000) (387567153747 / 1000000000000) x89 := by
    apply bounds_mul hx87 hx88 <;> norm_num
  let x90 : ℝ := x87/(2 / 1)
  have hx90 : Bounds (384926550789 / 1000000000000) (387567153747 / 1000000000000) x90 := by
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

theorem center_inputs_eq : centerInitial=inputBoxes ⟨1064327255687,1066526278943⟩ ⟨423231218432,426134592089⟩ ⟨532163627843,533263139472⟩ := rfl
theorem whole_inputs_eq : wholeInitial=inputBoxes ⟨1064327255687,1066526278943⟩ ⟨423231218432,426134592089⟩ ⟨505500470870,559926296445⟩ := rfl
noncomputable def centerUpper : ℝ := (2840136694303 / 68719476736)
noncomputable def secondUpper : ℝ := (10367651521249797 / 1099511627776)


theorem center_inputs {a z : ℝ} (ha : Bounds (121/125) (97/100) a)
    (hz : Bounds (1/100) (1/20) z) :
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

theorem whole_inputs {a z s : ℝ} (ha : Bounds (121/125) (97/100) a)
    (hz : Bounds (1/100) (1/20) z) (hs : s∈Icc (a*(1-z)/2) (a*(1+z)/2)) :
    RegistersContain wholeInitial (inputJets a ((biasE a+biasE (a*z))/2)) s := by
  rw [whole_inputs_eq]
  apply inputs_contain
  · norm_num [DyadicInterval.Contains,DyadicInterval.scale]
    constructor <;> linarith [ha.1,ha.2]
  · have h := entropy_bound ha hz
    norm_num [DyadicInterval.Contains,DyadicInterval.scale]
    constructor <;> linarith [h.1,h.2]
  · have hb : a*z≤(97/100:ℝ)*(1/20) :=
      mul_le_mul ha.2 hz.2 (by linarith [hz.1]) (by norm_num)
    norm_num [DyadicInterval.Contains,DyadicInterval.scale]
    constructor <;> nlinarith [ha.1,ha.2,hs.1,hs.2]

theorem curvature_pos {a z : ℝ} (ha : Bounds (121/125) (97/100) a)
    (hz : Bounds (1/100) (1/20) z) : 0<curvature a (a*z) := by
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
    have hb : a*z≤(97/2000:ℝ) := by
      have h := mul_le_mul ha.2 hz.2 hz0.le (by norm_num : (0:ℝ)≤97/100)
      norm_num at h
      exact h
    have hb2 := mul_self_le_mul_self hb0 hb
    have hle : centerUpper+secondUpper*(a*z)^2/24 ≤
        centerUpper+secondUpper*(97/2000:ℝ)^2/24 := by
      unfold centerUpper secondUpper
      nlinarith
    apply hle.trans_lt
    exact lt_of_lt_of_le (by norm_num [centerUpper,secondUpper] :
      centerUpper+secondUpper*(97/2000:ℝ)^2/24 < 2*(121/125:ℝ)/(1-(121/125:ℝ)^2)^2)
      (LowRatioFamily.base_mono (by norm_num) ha.1 ha1)

#print axioms entropy_bound
#print axioms curvature_pos
end GeneralCK.Certificates.ReflectionMidpointNextFamily.Cell0839

end

-- ===== source module GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0840 =====
section

namespace GeneralCK.Certificates.ReflectionMidpointNextFamily.Endpoints0840
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
noncomputable def out_w1 : DyadicInterval 40 := ⟨527486652864,527486652992⟩
theorem checked_w1 : DyadicFastLog.check 1099511627776 1776441884672 0 16 (lift40 out_w1.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w1 : out_w1.Contains (Real.log ((1776441884672:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w1
#print axioms endpoint_w1
noncomputable def out_w2 : DyadicInterval 40 := ⟨-1051396317120,-1051396297792⟩
theorem checked_w2 : DyadicFastLog.check 422581370880 1099511627776 1 16 (lift40 out_w2)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w2 : out_w2.Contains (Real.log ((422581370880:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w2
#print axioms endpoint_w2
noncomputable def out_w3 : DyadicInterval 40 := ⟨529472763456,529472763584⟩
theorem checked_w3 : DyadicFastLog.check 1099511627776 1779653672960 0 16 (lift40 out_w3.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w3 : out_w3.Contains (Real.log ((1779653672960:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w3
#print axioms endpoint_w3
noncomputable def out_w4 : DyadicInterval 40 := ⟨-1059784966592,-1059784947264⟩
theorem checked_w4 : DyadicFastLog.check 419369582592 1099511627776 1 16 (lift40 out_w4)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w4 : out_w4.Contains (Real.log ((419369582592:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w4
#print axioms endpoint_w4
noncomputable def out_w5 : DyadicInterval 40 := ⟨-530312185024,-530312184896⟩
theorem checked_w5 : DyadicFastLog.check 678785561820 1099511627776 0 16 (lift40 out_w5)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w5 : out_w5.Contains (Real.log ((678785561820:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w5
#print axioms endpoint_w5
noncomputable def out_w6 : DyadicInterval 40 := ⟨-523909646144,-523909646016⟩
theorem checked_w6 : DyadicFastLog.check 682749711735 1099511627776 0 16 (lift40 out_w6)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w6 : out_w6.Contains (Real.log ((682749711735:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w6
#print axioms endpoint_w6
noncomputable def out_w7 : DyadicInterval 40 := ⟨4601006938752,4601007054400⟩
theorem checked_w7 : DyadicFastLog.check 1099511627776 72201263555690 6 16 (lift40 out_w7.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w7 : out_w7.Contains (Real.log ((72201263555690:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w7
#print axioms endpoint_w7
noncomputable def out_w8 : DyadicInterval 40 := ⟨4677981092480,4677981208128⟩
theorem checked_w8 : DyadicFastLog.check 1099511627776 77437033215226 6 16 (lift40 out_w8.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w8 : out_w8.Contains (Real.log ((77437033215226:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w8
#print axioms endpoint_w8
noncomputable def out_w9 : DyadicInterval 40 := ⟨1578882949568,1578882988160⟩
theorem checked_w9 : DyadicFastLog.check 1099511627776 4622112196280 2 16 (lift40 out_w9.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w9 : out_w9.Contains (Real.log ((4622112196280:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w9
#print axioms endpoint_w9
noncomputable def out_w10 : DyadicInterval 40 := ⟨1589257709568,1589257748160⟩
theorem checked_w10 : DyadicFastLog.check 1099511627776 4665931884568 2 16 (lift40 out_w10.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w10 : out_w10.Contains (Real.log ((4665931884568:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w10
#print axioms endpoint_w10
noncomputable def out_w11 : DyadicInterval 40 := ⟨516031944000,516031944128⟩
theorem checked_w11 : DyadicFastLog.check 1099511627776 1758030987264 0 16 (lift40 out_w11.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w11 : out_w11.Contains (Real.log ((1758030987264:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w11
#print axioms endpoint_w11
noncomputable def out_w12 : DyadicInterval 40 := ⟨-1004507290816,-1004507271488⟩
theorem checked_w12 : DyadicFastLog.check 440992268288 1099511627776 1 16 (lift40 out_w12)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w12 : out_w12.Contains (Real.log ((440992268288:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w12
#print axioms endpoint_w12
noncomputable def out_w13 : DyadicInterval 40 := ⟨540030850688,540030850816⟩
theorem checked_w13 : DyadicFastLog.check 1099511627776 1796825153536 0 16 (lift40 out_w13.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w13 : out_w13.Contains (Real.log ((1796825153536:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w13
#print axioms endpoint_w13
noncomputable def out_w14 : DyadicInterval 40 := ⟨-1105753163456,-1105753144128⟩
theorem checked_w14 : DyadicFastLog.check 402198102016 1099511627776 1 16 (lift40 out_w14)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w14 : out_w14.Contains (Real.log ((402198102016:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w14
#print axioms endpoint_w14
noncomputable def out_w15 : DyadicInterval 40 := ⟨-565722294784,-565722294592⟩
theorem checked_w15 : DyadicFastLog.check 657273327676 1099511627776 0 16 (lift40 out_w15)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w15 : out_w15.Contains (Real.log ((657273327676:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w15
#print axioms endpoint_w15
noncomputable def out_w16 : DyadicInterval 40 := ⟨-488475328640,-488475328576⟩
theorem checked_w16 : DyadicFastLog.check 705111299607 1099511627776 0 16 (lift40 out_w16)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w16 : out_w16.Contains (Real.log ((705111299607:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w16
#print axioms endpoint_w16
noncomputable def out_w17 : DyadicInterval 40 := ⟨1520539214528,1520539251520⟩
theorem checked_w17 : DyadicFastLog.check 1099511627776 4383241275388 1 16 (lift40 out_w17.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w17 : out_w17.Contains (Real.log ((4383241275388:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w17
#print axioms endpoint_w17
noncomputable def out_w18 : DyadicInterval 40 := ⟨1645783993664,1645784032256⟩
theorem checked_w18 : DyadicFastLog.check 1099511627776 4912082228860 2 16 (lift40 out_w18.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w18 : out_w18.Contains (Real.log ((4912082228860:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w18
#print axioms endpoint_w18
end GeneralCK.Certificates.ReflectionMidpointNextFamily.Endpoints0840

namespace GeneralCK.Certificates.ReflectionMidpointNextFamily.Cell0840
open Set GeneralCK.Certificates.ReflectionMidpointNextFamily.Endpoints0840
open BivariateJetProgram (RegistersContain RegistersSound zeroBox zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
theorem lc0 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc1 : ProvedTranscendental.LogEncloses (⟨1776441884672,1776441884672⟩ : DyadicInterval 40) (⟨527486652864,527486652992⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w1
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w1
theorem lc2 : ProvedTranscendental.LogEncloses (⟨422581370880,422581370880⟩ : DyadicInterval 40) (⟨-1051396317120,-1051396297792⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w2
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w2
theorem lc3 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc4 : ProvedTranscendental.LogEncloses (⟨1779653672960,1779653672960⟩ : DyadicInterval 40) (⟨529472763456,529472763584⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w3
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w3
theorem lc5 : ProvedTranscendental.LogEncloses (⟨419369582592,419369582592⟩ : DyadicInterval 40) (⟨-1059784966592,-1059784947264⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w4
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w4
theorem lc6 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc7 : ProvedTranscendental.LogEncloses (⟨678785561820,682749711735⟩ : DyadicInterval 40) (⟨-530312185024,-523909646016⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w5
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w6
theorem lc8 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc9 : ProvedTranscendental.LogEncloses (⟨1776441884672,1779653672960⟩ : DyadicInterval 40) (⟨527486652864,529472763584⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w1
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w3
theorem lc10 : ProvedTranscendental.LogEncloses (⟨419369582592,422581370880⟩ : DyadicInterval 40) (⟨-1059784966592,-1051396297792⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w4
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w2
theorem lc11 : ProvedTranscendental.LogEncloses (⟨678785561820,682749711735⟩ : DyadicInterval 40) (⟨-530312185024,-523909646016⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w5
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w6
theorem lc12 : ProvedTranscendental.LogEncloses (⟨72201263555690,77437033215226⟩ : DyadicInterval 40) (⟨4601006938752,4677981208128⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w7
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
theorem lc13 : ProvedTranscendental.LogEncloses (⟨4622112196280,4665931884568⟩ : DyadicInterval 40) (⟨1578882949568,1589257748160⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w9
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w10
theorem lc14 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc15 : ProvedTranscendental.LogEncloses (⟨1758030987264,1758030987264⟩ : DyadicInterval 40) (⟨516031944000,516031944128⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w11
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w11
theorem lc16 : ProvedTranscendental.LogEncloses (⟨440992268288,440992268288⟩ : DyadicInterval 40) (⟨-1004507290816,-1004507271488⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w12
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w12
theorem lc17 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc18 : ProvedTranscendental.LogEncloses (⟨1796825153536,1796825153536⟩ : DyadicInterval 40) (⟨540030850688,540030850816⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w13
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w13
theorem lc19 : ProvedTranscendental.LogEncloses (⟨402198102016,402198102016⟩ : DyadicInterval 40) (⟨-1105753163456,-1105753144128⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w14
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w14
theorem lc20 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc21 : ProvedTranscendental.LogEncloses (⟨657273327676,705111299607⟩ : DyadicInterval 40) (⟨-565722294784,-488475328576⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w15
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w16
theorem lc22 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc23 : ProvedTranscendental.LogEncloses (⟨1758030987264,1796825153536⟩ : DyadicInterval 40) (⟨516031944000,540030850816⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w11
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w13
theorem lc24 : ProvedTranscendental.LogEncloses (⟨402198102016,440992268288⟩ : DyadicInterval 40) (⟨-1105753163456,-1004507271488⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w14
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w12
theorem lc25 : ProvedTranscendental.LogEncloses (⟨657273327676,705111299607⟩ : DyadicInterval 40) (⟨-565722294784,-488475328576⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w15
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w16
theorem lc26 : ProvedTranscendental.LogEncloses (⟨72201263555690,77437033215226⟩ : DyadicInterval 40) (⟨4601006938752,4677981208128⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w7
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
theorem lc27 : ProvedTranscendental.LogEncloses (⟨4383241275388,4912082228860⟩ : DyadicInterval 40) (⟨1520539214528,1645784032256⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w17
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w18
theorem ew3_ok (x : ℝ) (hx : (⟨676930256896,676930256896⟩ : DyadicInterval 40).Contains x) : (⟨538047128907,538047151990⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨676930256896,676930256896⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨527486652864,527486652992⟩ : DyadicInterval 40)) (minus:=(⟨-1051396317120,-1051396297792⟩ : DyadicInterval 40))
    (lc0 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc1 lc2 (by decide) hx
theorem ew6_ok (x : ℝ) (hx : (⟨680142045184,680142045184⟩ : DyadicInterval 40).Contains x) : (⟨535733518835,535733541890⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨680142045184,680142045184⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨529472763456,529472763584⟩ : DyadicInterval 40)) (minus:=(⟨-1059784966592,-1059784947264⟩ : DyadicInterval 40))
    (lc3 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc4 lc5 (by decide) hx
theorem ew17_ok (x : ℝ) (hx : (⟨658519359488,658519359488⟩ : DyadicInterval 40).Contains x) : (⟨551020473786,551020497030⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨658519359488,658519359488⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨516031944000,516031944128⟩ : DyadicInterval 40)) (minus:=(⟨-1004507290816,-1004507271488⟩ : DyadicInterval 40))
    (lc14 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc15 lc16 (by decide) hx
theorem ew20_ok (x : ℝ) (hx : (⟨697313525760,697313525760⟩ : DyadicInterval 40).Contains x) : (⟨523103992057,523104014962⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨697313525760,697313525760⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨540030850688,540030850816⟩ : DyadicInterval 40)) (minus:=(⟨-1105753163456,-1105753144128⟩ : DyadicInterval 40))
    (lc17 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc18 lc19 (by decide) hx
theorem bw9_ok (x : ℝ) (hx : (⟨676930256896,680142045184⟩ : DyadicInterval 40).Contains x) : (⟨1024078206624,1027279495392⟩ : DyadicInterval 40).Contains (Reflection.biasB x) := by
  exact ProvedTranscendental.denominator_encloses (c:=(⟨676930256896,680142045184⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (gapLog:=(⟨-530312185024,-523909646016⟩ : DyadicInterval 40))
    (lc6 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc7 (by decide) hx
theorem bw23_ok (x : ℝ) (hx : (⟨658519359488,697313525760⟩ : DyadicInterval 40).Contains x) : (⟨1006361047904,1044984550272⟩ : DyadicInterval 40).Contains (Reflection.biasB x) := by
  exact ProvedTranscendental.denominator_encloses (c:=(⟨658519359488,697313525760⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (gapLog:=(⟨-565722294784,-488475328576⟩ : DyadicInterval 40))
    (lc20 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc21 (by decide) hx
theorem brcenter6_contact (y : ℝ) (hy : (⟨866067937667,873922045659⟩ : DyadicInterval 40).Contains y) : (⟨676930256896,680142045184⟩ : DyadicInterval 40).Contains (Reflection.biasContact y) := by
  exact ProvedTranscendental.contact_bracket (Y:=(⟨866067937667,873922045659⟩ : DyadicInterval 40)) (c:=(⟨676930256896,680142045184⟩ : DyadicInterval 40)) (elo:=(⟨538047128907,538047151990⟩ : DyadicInterval 40)) (ehi:=(⟨535733518835,535733541890⟩ : DyadicInterval 40))
    (by decide) (by decide) (by decide) (by decide)
    (ew3_ok _ (DyadicContact.point_contains 40 676930256896)) (ew6_ok _ (DyadicContact.point_contains 40 680142045184))
    (by decide) (by decide) hy
theorem brcenter6_jet (y : ℝ) (hy : (⟨866067937667,873922045659⟩ : DyadicInterval 40).Contains y) : (⟨⟨676930256896,680142045184⟩,⟨-451716674211,-446066114194⟩,⟨388225838261,407975460107⟩⟩ : DyadicJetEnclosure 40).Contains reflectionContactJet y := by
  exact ProvedTranscendental.contact_jet (c:=(⟨676930256896,680142045184⟩ : DyadicInterval 40)) (B:=(⟨1024078206624,1027279495392⟩ : DyadicInterval 40)) (by decide) brcenter6_contact bw9_ok (by decide) (by decide) (by decide) hy
theorem brwhole6_contact (y : ℝ) (hy : (⟨824826607302,920017781951⟩ : DyadicInterval 40).Contains y) : (⟨658519359488,697313525760⟩ : DyadicInterval 40).Contains (Reflection.biasContact y) := by
  exact ProvedTranscendental.contact_bracket (Y:=(⟨824826607302,920017781951⟩ : DyadicInterval 40)) (c:=(⟨658519359488,697313525760⟩ : DyadicInterval 40)) (elo:=(⟨551020473786,551020497030⟩ : DyadicInterval 40)) (ehi:=(⟨523103992057,523104014962⟩ : DyadicInterval 40))
    (by decide) (by decide) (by decide) (by decide)
    (ew17_ok _ (DyadicContact.point_contains 40 658519359488)) (ew20_ok _ (DyadicContact.point_contains 40 697313525760))
    (by decide) (by decide) hy
theorem brwhole6_jet (y : ℝ) (hy : (⟨824826607302,920017781951⟩ : DyadicInterval 40).Contains y) : (⟨⟨658519359488,697313525760⟩,⟨-483172668717,-414980055645⟩,⟨276905002632,515680438184⟩⟩ : DyadicJetEnclosure 40).Contains reflectionContactJet y := by
  exact ProvedTranscendental.contact_jet (c:=(⟨658519359488,697313525760⟩ : DyadicInterval 40)) (B:=(⟨1006361047904,1044984550272⟩ : DyadicInterval 40)) (by decide) brwhole6_contact bw23_ok (by decide) (by decide) (by decide) hy
noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨1066526278942,1068725302199⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨420909017707,423852192144⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨533263139471,534362651100⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
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
noncomputable def centerStep4 : Instruction 40 := ⟨.inv 6,⟨⟨2262369604473,2267034284076⟩,⟨0,0⟩,⟨-4674297492944,-4655081490676⟩,⟨0,0⟩,⟨0,0⟩,⟨19156713953362,19275453579166⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4
theorem centerAccepted4 : StepValid centerStep4.shape centerBoxes4 centerStep4.proposed := by
  dsimp only [StepValid,centerStep4]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep5 : Instruction 40 := ⟨.mul 6 0,⟨⟨866067937667,873922045659⟩,⟨0,0⟩,⟨-1801901125071,-1782032793550⟩,⟨0,0⟩,⟨0,0⟩,⟨7333468286200,7430520103389⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5
theorem centerAccepted5 : StepValid centerStep5.shape centerBoxes5 centerStep5.proposed := by
  dsimp only [StepValid,centerStep5]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep6 : Instruction 40 := ⟨.contact 0,⟨⟨676930256896,680142045184⟩,⟨0,0⟩,⟨722961379856,740282106085⟩,⟨0,0⟩,⟨0,0⟩,⟨-2032906993764,-1879438007323⟩⟩⟩
noncomputable def centerBoxes7 := centerStep6.proposed :: centerBoxes6
theorem centerAccepted6 : StepValid centerStep6.shape centerBoxes6 centerStep6.proposed := by
  dsimp only [StepValid,centerStep6]
  exact ⟨by decide,by decide,(⟨⟨676930256896,680142045184⟩,⟨-451716674211,-446066114194⟩,⟨388225838261,407975460107⟩⟩ : DyadicJetEnclosure 40),brcenter6_jet,by decide⟩
noncomputable def centerStep7 : Instruction 40 := ⟨.log 10,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes8 := centerStep7.proposed :: centerBoxes7
theorem centerAccepted7 : StepValid centerStep7.shape centerBoxes7 centerStep7.proposed := by
  dsimp only [StepValid,centerStep7]
  exact ⟨by decide,by decide,lc0,by decide⟩
noncomputable def centerStep8 : Instruction 40 := ⟨.add 6 1,⟨⟨1776441884672,1779653672960⟩,⟨0,0⟩,⟨722961379856,740282106085⟩,⟨0,0⟩,⟨0,0⟩,⟨-2032906993764,-1879438007323⟩⟩⟩
noncomputable def centerBoxes9 := centerStep8.proposed :: centerBoxes8
theorem centerAccepted8 : StepValid centerStep8.shape centerBoxes8 centerStep8.proposed := by
  dsimp only [StepValid,centerStep8]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep9 : Instruction 40 := ⟨.log 0,⟨⟨527486652864,529472763584⟩,⟨0,0⟩,⟨446662435316,458190493311⟩,⟨0,0⟩,⟨0,0⟩,⟨-1449186220738,-1342611582019⟩⟩⟩
noncomputable def centerBoxes10 := centerStep9.proposed :: centerBoxes9
theorem centerAccepted9 : StepValid centerStep9.shape centerBoxes9 centerStep9.proposed := by
  dsimp only [StepValid,centerStep9]
  exact ⟨by decide,by decide,lc9,by decide⟩
noncomputable def centerStep10 : Instruction 40 := ⟨.mul 1 0,⟨⟨852241449822,856996983607⟩,⟨0,0⟩,⟨1068494690857,1098105355484⟩,⟨0,0⟩,⟨0,0⟩,⟨-2737196231016,-2453879884467⟩⟩⟩
noncomputable def centerBoxes11 := centerStep10.proposed :: centerBoxes10
theorem centerAccepted10 : StepValid centerStep10.shape centerBoxes10 centerStep10.proposed := by
  dsimp only [StepValid,centerStep10]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep11 : Instruction 40 := ⟨.neg 4,⟨⟨-680142045184,-676930256896⟩,⟨0,0⟩,⟨-740282106085,-722961379856⟩,⟨0,0⟩,⟨0,0⟩,⟨1879438007323,2032906993764⟩⟩⟩
noncomputable def centerBoxes12 := centerStep11.proposed :: centerBoxes11
theorem centerAccepted11 : StepValid centerStep11.shape centerBoxes11 centerStep11.proposed := by
  dsimp only [StepValid,centerStep11]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep12 : Instruction 40 := ⟨.add 10 0,⟨⟨419369582592,422581370880⟩,⟨0,0⟩,⟨-740282106085,-722961379856⟩,⟨0,0⟩,⟨0,0⟩,⟨1879438007323,2032906993764⟩⟩⟩
noncomputable def centerBoxes13 := centerStep12.proposed :: centerBoxes12
theorem centerAccepted12 : StepValid centerStep12.shape centerBoxes12 centerStep12.proposed := by
  dsimp only [StepValid,centerStep12]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep13 : Instruction 40 := ⟨.log 0,⟨⟨-1059784966592,-1051396297792⟩,⟨0,0⟩,⟨-1940886552726,-1881068353603⟩,⟨0,0⟩,⟨0,0⟩,⟨1463993638676,2111743986708⟩⟩⟩
noncomputable def centerBoxes14 := centerStep13.proposed :: centerBoxes13
theorem centerAccepted13 : StepValid centerStep13.shape centerBoxes13 centerStep13.proposed := by
  dsimp only [StepValid,centerStep13]
  exact ⟨by decide,by decide,lc10,by decide⟩
noncomputable def centerStep14 : Instruction 40 := ⟨.mul 1 0,⟨⟨-407313003981,-401017702228⟩,⟨0,0⟩,⟨-54627509550,-3931748515⟩,⟨0,0⟩,⟨0,0⟩,⟨1072648661416,1627956113108⟩⟩⟩
noncomputable def centerBoxes15 := centerStep14.proposed :: centerBoxes14
theorem centerAccepted14 : StepValid centerStep14.shape centerBoxes14 centerStep14.proposed := by
  dsimp only [StepValid,centerStep14]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep15 : Instruction 40 := ⟨.add 4 0,⟨⟨444928445841,455979281379⟩,⟨0,0⟩,⟨1013867181307,1094173606969⟩,⟨0,0⟩,⟨0,0⟩,⟨-1664547569600,-825923771359⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15
theorem centerAccepted15 : StepValid centerStep15.shape centerBoxes15 centerStep15.proposed := by
  dsimp only [StepValid,centerStep15]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep16 : Instruction 40 := ⟨.mul 0 15,⟨⟨222464222920,227989640690⟩,⟨0,0⟩,⟨506933590653,547086803485⟩,⟨0,0⟩,⟨0,0⟩,⟨-832273784800,-412961885679⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16
theorem centerAccepted16 : StepValid centerStep16.shape centerBoxes16 centerStep16.proposed := by
  dsimp only [StepValid,centerStep16]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨-227989640690,-222464222920⟩,⟨0,0⟩,⟨-547086803485,-506933590653⟩,⟨0,0⟩,⟨0,0⟩,⟨412961885679,832273784800⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17
theorem centerAccepted17 : StepValid centerStep17.shape centerBoxes17 centerStep17.proposed := by
  dsimp only [StepValid,centerStep17]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep18 : Instruction 40 := ⟨.add 10 0,⟨⟨534133742926,539659179960⟩,⟨0,0⟩,⟨-547086803485,-506933590653⟩,⟨0,0⟩,⟨0,0⟩,⟨412961885679,832273784800⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18
theorem centerAccepted18 : StepValid centerStep18.shape centerBoxes18 centerStep18.proposed := by
  dsimp only [StepValid,centerStep18]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep19 : Instruction 40 := ⟨.mul 12 12,⟨⟨416761916041,420726065956⟩,⟨0,0⟩,⟨890203287038,915855681608⟩,⟨0,0⟩,⟨0,0⟩,⟨-1564316996600,-1317368253742⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19
theorem centerAccepted19 : StepValid centerStep19.shape centerBoxes19 centerStep19.proposed := by
  dsimp only [StepValid,centerStep19]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep20 : Instruction 40 := ⟨.neg 0,⟨⟨-420726065956,-416761916041⟩,⟨0,0⟩,⟨-915855681608,-890203287038⟩,⟨0,0⟩,⟨0,0⟩,⟨1317368253742,1564316996600⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20
theorem centerAccepted20 : StepValid centerStep20.shape centerBoxes20 centerStep20.proposed := by
  dsimp only [StepValid,centerStep20]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep21 : Instruction 40 := ⟨.add 19 0,⟨⟨678785561820,682749711735⟩,⟨0,0⟩,⟨-915855681608,-890203287038⟩,⟨0,0⟩,⟨0,0⟩,⟨1317368253742,1564316996600⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21
theorem centerAccepted21 : StepValid centerStep21.shape centerBoxes21 centerStep21.proposed := by
  dsimp only [StepValid,centerStep21]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep22 : Instruction 40 := ⟨.log 0,⟨⟨-530312185024,-523909646016⟩,⟨0,0⟩,⟨-1483522967980,-1433598357288⟩,⟨0,0⟩,⟨0,0⟩,⟨119859329594,664717344240⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22
theorem centerAccepted22 : StepValid centerStep22.shape centerBoxes22 centerStep22.proposed := by
  dsimp only [StepValid,centerStep22]
  exact ⟨by decide,by decide,lc7,by decide⟩
noncomputable def centerStep23 : Instruction 40 := ⟨.mul 0 22,⟨⟨-265156092512,-261954823008⟩,⟨0,0⟩,⟨-741761483990,-716799178644⟩,⟨0,0⟩,⟨0,0⟩,⟨59929664797,332358672120⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23
theorem centerAccepted23 : StepValid centerStep23.shape centerBoxes23 centerStep23.proposed := by
  dsimp only [StepValid,centerStep23]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep24 : Instruction 40 := ⟨.neg 0,⟨⟨261954823008,265156092512⟩,⟨0,0⟩,⟨716799178644,741761483990⟩,⟨0,0⟩,⟨0,0⟩,⟨-332358672120,-59929664797⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24
theorem centerAccepted24 : StepValid centerStep24.shape centerBoxes24 centerStep24.proposed := by
  dsimp only [StepValid,centerStep24]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep25 : Instruction 40 := ⟨.add 17 0,⟨⟨1024078206624,1027279495392⟩,⟨0,0⟩,⟨716799178644,741761483990⟩,⟨0,0⟩,⟨0,0⟩,⟨-332358672120,-59929664797⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25
theorem centerAccepted25 : StepValid centerStep25.shape centerBoxes25 centerStep25.proposed := by
  dsimp only [StepValid,centerStep25]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep26 : Instruction 40 := ⟨.add 24 26,⟨⟨2166037906718,2168236929975⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26
theorem centerAccepted26 : StepValid centerStep26.shape centerBoxes26 centerStep26.proposed := by
  dsimp only [StepValid,centerStep26]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep27 : Instruction 40 := ⟨.neg 27,⟨⟨-1068725302199,-1066526278942⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27
theorem centerAccepted27 : StepValid centerStep27.shape centerBoxes27 centerStep27.proposed := by
  dsimp only [StepValid,centerStep27]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep28 : Instruction 40 := ⟨.add 26 0,⟨⟨30786325577,32985348834⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28
theorem centerAccepted28 : StepValid centerStep28.shape centerBoxes28 centerStep28.proposed := by
  dsimp only [StepValid,centerStep28]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep29 : Instruction 40 := ⟨.inv 0,⟨⟨36650387591733,39268272421501⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29
theorem centerAccepted29 : StepValid centerStep29.shape centerBoxes29 centerStep29.proposed := by
  dsimp only [StepValid,centerStep29]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep30 : Instruction 40 := ⟨.mul 3 0,⟨⟨72201263555690,77437033215226⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30
theorem centerAccepted30 : StepValid centerStep30.shape centerBoxes30 centerStep30.proposed := by
  dsimp only [StepValid,centerStep30]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨4601006938752,4677981208128⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31
theorem centerAccepted31 : StepValid centerStep31.shape centerBoxes31 centerStep31.proposed := by
  dsimp only [StepValid,centerStep31]
  exact ⟨by decide,by decide,lc12,by decide⟩
noncomputable def centerStep32 : Instruction 40 := ⟨.mul 0 31,⟨⟨2300503469376,2338990604064⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32
theorem centerAccepted32 : StepValid centerStep32.shape centerBoxes32 centerStep32.proposed := by
  dsimp only [StepValid,centerStep32]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep33 : Instruction 40 := ⟨.inv 20,⟨⟨2860811912028,2882721756172⟩,⟨0,0⟩,⟨4894339102362,5088655499826⟩,⟨0,0⟩,⟨0,0⟩,⟨2772600422823,5241743550508⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33
theorem centerAccepted33 : StepValid centerStep33.shape centerBoxes33 centerStep33.proposed := by
  dsimp only [StepValid,centerStep33]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep34 : Instruction 40 := ⟨.mul 25 0,⟨⟨4622112196280,4665931884568⟩,⟨0,0⟩,⟨9788678204724,10177310999652⟩,⟨0,0⟩,⟨0,0⟩,⟨5586020600473,10446320397218⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34
theorem centerAccepted34 : StepValid centerStep34.shape centerBoxes34 centerStep34.proposed := by
  dsimp only [StepValid,centerStep34]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨1578882949568,1589257748160⟩,⟨0,0⟩,⟨2306670087113,2420986620064⟩,⟨0,0⟩,⟨0,0⟩,⟨-4014381181047,-2354194132895⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35
theorem centerAccepted35 : StepValid centerStep35.shape centerBoxes35 centerStep35.proposed := by
  dsimp only [StepValid,centerStep35]
  exact ⟨by decide,by decide,lc13,by decide⟩
noncomputable def centerStep36 : Instruction 40 := ⟨.mul 0 35,⟨⟨789441474784,794628874080⟩,⟨0,0⟩,⟨1153335043556,1210493310032⟩,⟨0,0⟩,⟨0,0⟩,⟨-2007190590524,-1177097066447⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36
theorem centerAccepted36 : StepValid centerStep36.shape centerBoxes36 centerStep36.proposed := by
  dsimp only [StepValid,centerStep36]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep37 : Instruction 40 := ⟨.mul 40 11,⟨⟨2048156413248,2054558990784⟩,⟨0,0⟩,⟨1433598357288,1483522967980⟩,⟨0,0⟩,⟨0,0⟩,⟨-664717344240,-119859329594⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37
theorem centerAccepted37 : StepValid centerStep37.shape centerBoxes37 centerStep37.proposed := by
  dsimp only [StepValid,centerStep37]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep38 : Instruction 40 := ⟨.add 0 17,⟨⟨1627430347292,1637797074743⟩,⟨0,0⟩,⟨517742675680,593319680942⟩,⟨0,0⟩,⟨0,0⟩,⟨652650909502,1444457667006⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38
theorem centerAccepted38 : StepValid centerStep38.shape centerBoxes38 centerStep38.proposed := by
  dsimp only [StepValid,centerStep38]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep39 : Instruction 40 := ⟨.mul 20 0,⟨⟨790592332805,803858916968⟩,⟨0,0⟩,⟨-563407714386,-459120835346⟩,⟨0,0⟩,⟨0,0⟩,⟨337854401333,1471278758766⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39
theorem centerAccepted39 : StepValid centerStep39.shape centerBoxes39 centerStep39.proposed := by
  dsimp only [StepValid,centerStep39]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep40 : Instruction 40 := ⟨.mul 43 41,⟨⟨841818035414,847704384288⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40
theorem centerAccepted40 : StepValid centerStep40.shape centerBoxes40 centerStep40.proposed := by
  dsimp only [StepValid,centerStep40]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep41 : Instruction 40 := ⟨.mul 19 19,⟨⟨419049537354,423958380338⟩,⟨0,0⟩,⟨-1137414442582,-1099137331632⟩,⟨0,0⟩,⟨0,0⟩,⟨3068039300146,3468501032375⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41
theorem centerAccepted41 : StepValid centerStep41.shape centerBoxes41 centerStep41.proposed := by
  dsimp only [StepValid,centerStep41]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep42 : Instruction 40 := ⟨.mul 1 0,⟨⟨320836496281,326864553944⟩,⟨0,0⟩,⟨-876926796745,-841531463415⟩,⟨0,0⟩,⟨0,0⟩,⟨2348979993459,2674154104218⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42
theorem centerAccepted42 : StepValid centerStep42.shape centerBoxes42 centerStep42.proposed := by
  dsimp only [StepValid,centerStep42]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep43 : Instruction 40 := ⟨.mul 17 17,⟨⟨953819993157,959792634288⟩,⟨0,0⟩,⟨1335244482788,1386063309792⟩,⟨0,0⟩,⟨0,0⟩,⟨313549778220,889190115200⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43
theorem centerAccepted43 : StepValid centerStep43.shape centerBoxes43 centerStep43.proposed := by
  dsimp only [StepValid,centerStep43]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep44 : Instruction 40 := ⟨.mul 18 0,⟨⟨888381935541,896739305092⟩,⟨0,0⟩,⟨1865457455103,1942509358011⟩,⟨0,0⟩,⟨0,0⟩,⟨1742872324235,2648940986124⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44
theorem centerAccepted44 : StepValid centerStep44.shape centerBoxes44 centerStep44.proposed := by
  dsimp only [StepValid,centerStep44]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep45 : Instruction 40 := ⟨.mul 2 0,⟨⟨259229043475,266584077475⟩,⟨0,0⟩,⟨-170864852838,-102467215991⟩,⟨0,0⟩,⟨0,0⟩,⟨-692042317340,112942618868⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45
theorem centerAccepted45 : StepValid centerStep45.shape centerBoxes45 centerStep45.proposed := by
  dsimp only [StepValid,centerStep45]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep46 : Instruction 40 := ⟨.inv 0,⟨⟨4534876317690,4663543110019⟩,⟨0,0⟩,⟨1743075413724,3073867019357⟩,⟨0,0⟩,⟨0,0⟩,⟨-691867570943,16502012256576⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46
theorem centerAccepted46 : StepValid centerStep46.shape centerBoxes46 centerStep46.proposed := by
  dsimp only [StepValid,centerStep46]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep47 : Instruction 40 := ⟨.mul 7 0,⟨⟨3260755372125,3409541671912⟩,⟨0,0⟩,⟨-1136335510606,353701770943⟩,⟨0,0⟩,⟨0,0⟩,⟨-2262565227499,16849387192165⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47
theorem centerAccepted47 : StepValid centerStep47.shape centerBoxes47 centerStep47.proposed := by
  dsimp only [StepValid,centerStep47]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep48 : Instruction 40 := ⟨.neg 11,⟨⟨-794628874080,-789441474784⟩,⟨0,0⟩,⟨-1210493310032,-1153335043556⟩,⟨0,0⟩,⟨0,0⟩,⟨1177097066447,2007190590524⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48
theorem centerAccepted48 : StepValid centerStep48.shape centerBoxes48 centerStep48.proposed := by
  dsimp only [StepValid,centerStep48]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep49 : Instruction 40 := ⟨.mul 0 10,⟨⟨-1183653553630,-1168483334799⟩,⟨0,0⟩,⟨-2231910322920,-2078832032498⟩,⟨0,0⟩,⟨0,0⟩,⟨-608072960793,1435073171055⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49
theorem centerAccepted49 : StepValid centerStep49.shape centerBoxes49 centerStep49.proposed := by
  dsimp only [StepValid,centerStep49]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep50 : Instruction 40 := ⟨.mul 53 43,⟨⟨1353860513792,1360284090368⟩,⟨0,0⟩,⟨1445922759712,1480564212170⟩,⟨0,0⟩,⟨0,0⟩,⟨-4065813987528,-3758876014646⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50
theorem centerAccepted50 : StepValid centerStep50.shape centerBoxes50 centerStep50.proposed := by
  dsimp only [StepValid,centerStep50]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep51 : Instruction 40 := ⟨.inv 29,⟨⟨1770672032277,1781012867117⟩,⟨0,0⟩,⟨2308690924808,2403042794536⟩,⟨0,0⟩,⟨0,0⟩,⟨1915883615630,3068122510544⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51
theorem centerAccepted51 : StepValid centerStep51.shape centerBoxes51 centerStep51.proposed := by
  dsimp only [StepValid,centerStep51]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep52 : Instruction 40 := ⟨.mul 1 0,⟨⟨2180279759500,2203417778110⟩,⟨0,0⟩,⟨5171296355093,5371225410590⟩,⟨0,0⟩,⟨0,0⟩,⟨1845318962087,4214143637247⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52
theorem centerAccepted52 : StepValid centerStep52.shape centerBoxes52 centerStep52.proposed := by
  dsimp only [StepValid,centerStep52]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep53 : Instruction 40 := ⟨.neg 2,⟨⟨-1360284090368,-1353860513792⟩,⟨0,0⟩,⟨-1480564212170,-1445922759712⟩,⟨0,0⟩,⟨0,0⟩,⟨3758876014646,4065813987528⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53
theorem centerAccepted53 : StepValid centerStep53.shape centerBoxes53 centerStep53.proposed := by
  dsimp only [StepValid,centerStep53]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep54 : Instruction 40 := ⟨.add 1 0,⟨⟨819995669132,849557264318⟩,⟨0,0⟩,⟨3690732142923,3925302650878⟩,⟨0,0⟩,⟨0,0⟩,⟨5604194976733,8279957624775⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54
theorem centerAccepted54 : StepValid centerStep54.shape centerBoxes54 centerStep54.proposed := by
  dsimp only [StepValid,centerStep54]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep55 : Instruction 40 := ⟨.mul 36 0,⟨⟨398347179667,416977287924⟩,⟨0,0⟩,⟨1370211071410,1548544115208⟩,⟨0,0⟩,⟨0,0⟩,⟨-875794251604,1303767191502⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55
theorem centerAccepted55 : StepValid centerStep55.shape centerBoxes55 centerStep55.proposed := by
  dsimp only [StepValid,centerStep55]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep56 : Instruction 40 := ⟨.add 6 0,⟨⟨-785306373963,-751506046875⟩,⟨0,0⟩,⟨-861699251510,-530287917290⟩,⟨0,0⟩,⟨0,0⟩,⟨-1483867212397,2738840362557⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56
theorem centerAccepted56 : StepValid centerStep56.shape centerBoxes56 centerStep56.proposed := by
  dsimp only [StepValid,centerStep56]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep57 : Instruction 40 := ⟨.mul 0 10,⟨⟨-3330851659075,-3099546097086⟩,⟨0,0⟩,⟨-5850323732652,-3378519824079⟩,⟨0,0⟩,⟨0,0⟩,⟨-22898086119773,10429507214212⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57
theorem centerAccepted57 : StepValid centerStep57.shape centerBoxes57 centerStep57.proposed := by
  dsimp only [StepValid,centerStep57]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep58 : Instruction 40 := ⟨.mul 54 51,⟨⟨2707721027584,2720568180736⟩,⟨0,0⟩,⟨2891845519424,2961128424340⟩,⟨0,0⟩,⟨0,0⟩,⟨-8131627975056,-7517752029292⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58
theorem centerAccepted58 : StepValid centerStep58.shape centerBoxes58 centerStep58.proposed := by
  dsimp only [StepValid,centerStep58]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep59 : Instruction 40 := ⟨.mul 0 7,⟨⟨4360559519001,4406835556220⟩,⟨0,0⟩,⟨10342592710188,10742450821179⟩,⟨0,0⟩,⟨0,0⟩,⟨3690637924175,8428287274491⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59
theorem centerAccepted59 : StepValid centerStep59.shape centerBoxes59 centerStep59.proposed := by
  dsimp only [StepValid,centerStep59]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep60 : Instruction 40 := ⟨.mul 57 53,⟨⟨2030790770688,2040426135552⟩,⟨0,0⟩,⟨2168884139568,2220846318255⟩,⟨0,0⟩,⟨0,0⟩,⟨-6098720981292,-5638314021969⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60
theorem centerAccepted60 : StepValid centerStep60.shape centerBoxes60 centerStep60.proposed := by
  dsimp only [StepValid,centerStep60]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep61 : Instruction 40 := ⟨.mul 39 35,⟨⟨632216598051,637896645777⟩,⟨0,0⟩,⟨-413171464304,-368527568161⟩,⟨0,0⟩,⟨0,0⟩,⟨-215116058689,263860250709⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61
theorem centerAccepted61 : StepValid centerStep61.shape centerBoxes61 centerStep61.proposed := by
  dsimp only [StepValid,centerStep61]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep62 : Instruction 40 := ⟨.inv 0,⟨⟨1895175068904,1912201962653⟩,⟨0,0⟩,⟨1094886239026,1249678175788⟩,⟨0,0⟩,⟨0,0⟩,⟨467010375879,2284040118013⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62
theorem centerAccepted62 : StepValid centerStep62.shape centerBoxes62 centerStep62.proposed := by
  dsimp only [StepValid,centerStep62]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep63 : Instruction 40 := ⟨.mul 2 0,⟨⟨3500375931951,3548581717997⟩,⟨0,0⟩,⟨5760648507763,6181455955289⟩,⟨0,0⟩,⟨0,0⟩,⟨-5424429284213,-431546743347⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63
theorem centerAccepted63 : StepValid centerStep63.shape centerBoxes63 centerStep63.proposed := by
  dsimp only [StepValid,centerStep63]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep64 : Instruction 40 := ⟨.neg 0,⟨⟨-3548581717997,-3500375931951⟩,⟨0,0⟩,⟨-6181455955289,-5760648507763⟩,⟨0,0⟩,⟨0,0⟩,⟨431546743347,5424429284213⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64
theorem centerAccepted64 : StepValid centerStep64.shape centerBoxes64 centerStep64.proposed := by
  dsimp only [StepValid,centerStep64]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep65 : Instruction 40 := ⟨.add 5 0,⟨⟨811977801004,906459624269⟩,⟨0,0⟩,⟨4161136754899,4981802313416⟩,⟨0,0⟩,⟨0,0⟩,⟨4122184667522,13852716558704⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65
theorem centerAccepted65 : StepValid centerStep65.shape centerBoxes65 centerStep65.proposed := by
  dsimp only [StepValid,centerStep65]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep66 : Instruction 40 := ⟨.mul 18 0,⟨⟨2408033630372,2810895114500⟩,⟨0,0⟩,⟨11403614523893,15739969024446⟩,⟨0,0⟩,⟨0,0⟩,⟨62313140371,60052887566551⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66
theorem centerAccepted66 : StepValid centerStep66.shape centerBoxes66 centerStep66.proposed := by
  dsimp only [StepValid,centerStep66]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep67 : Instruction 40 := ⟨.add 9 0,⟨⟨-922818028703,-288650982586⟩,⟨0,0⟩,⟨5553290791241,12361449200367⟩,⟨0,0⟩,⟨0,0⟩,⟨-22835772979402,70482394780763⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67
theorem centerAccepted67 : StepValid centerStep67.shape centerBoxes67 centerStep67.proposed := by
  dsimp only [StepValid,centerStep67]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep68 : Instruction 40 := ⟨.mul 61 29,⟨⟨1001951061946,1013117664127⟩,⟨0,0⟩,⟨1388839311358,1469719362899⟩,⟨0,0⟩,⟨0,0⟩,⟨-1945476525490,-1089365624622⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68
theorem centerAccepted68 : StepValid centerStep68.shape centerBoxes68 centerStep68.proposed := by
  dsimp only [StepValid,centerStep68]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep69 : Instruction 40 := ⟨.mul 27 25,⟨⟨363523055831,370084426953⟩,⟨0,0⟩,⟨-483986169781,-419046051565⟩,⟨0,0⟩,⟨0,0⟩,⟨-86680975083,701026900216⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69
theorem centerAccepted69 : StepValid centerStep69.shape centerBoxes69 centerStep69.proposed := by
  dsimp only [StepValid,centerStep69]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨3266621699183,3325582243611⟩,⟨0,0⟩,⟨3698790938783,4427603109514⟩,⟨0,0⟩,⟨0,0⟩,⟨1963135572146,12582591334428⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70
theorem centerAccepted70 : StepValid centerStep70.shape centerBoxes70 centerStep70.proposed := by
  dsimp only [StepValid,centerStep70]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep71 : Instruction 40 := ⟨.mul 2 0,⟨⟨2976771684618,3064275110328⟩,⟨0,0⟩,⟨7496801245169,8525017198137⟩,⟨0,0⟩,⟨0,0⟩,⟨5248854088927,20194209533872⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71
theorem centerAccepted71 : StepValid centerStep71.shape centerBoxes71 centerStep71.proposed := by
  dsimp only [StepValid,centerStep71]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep72 : Instruction 40 := ⟨.mul 65 39,⟨⟨1416338277081,1446865874745⟩,⟨0,0⟩,⟨1512648998490,1574801799952⟩,⟨0,0⟩,⟨0,0⟩,⟨-4324602157204,-3932340092727⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72
theorem centerAccepted72 : StepValid centerStep72.shape centerBoxes72 centerStep72.proposed := by
  dsimp only [StepValid,centerStep72]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep73 : Instruction 40 := ⟨.add 54 0,⟨⟨1950472020007,1986525054705⟩,⟨0,0⟩,⟨965562195005,1067868209299⟩,⟨0,0⟩,⟨0,0⟩,⟨-3911640271525,-3100066307927⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73
theorem centerAccepted73 : StepValid centerStep73.shape centerBoxes73 centerStep73.proposed := by
  dsimp only [StepValid,centerStep73]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep74 : Instruction 40 := ⟨.mul 0 0,⟨⟨3460028074942,3589122382410⟩,⟨0,0⟩,⟨3425706463410,3858707628562⟩,⟨0,0⟩,⟨0,0⟩,⟨-12438724392187,-8924416909114⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74
theorem centerAccepted74 : StepValid centerStep74.shape centerBoxes74 centerStep74.proposed := by
  dsimp only [StepValid,centerStep74]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep75 : Instruction 40 := ⟨.mul 7 0,⟨⟨-3012343624241,-908349196476⟩,⟨0,0⟩,⟨14236918176610,39451988838980⟩,⟨0,0⟩,⟨0,0⟩,⟨-37595285809116,327278991295088⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75
theorem centerAccepted75 : StepValid centerStep75.shape centerBoxes75 centerStep75.proposed := by
  dsimp only [StepValid,centerStep75]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep76 : Instruction 40 := ⟨.mul 79 28,⟨⟨6521510744250,6819083343824⟩,⟨0,0⟩,⟨-2272671021212,707403541886⟩,⟨0,0⟩,⟨0,0⟩,⟨-4525130454998,33698774384330⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76
theorem centerAccepted76 : StepValid centerStep76.shape centerBoxes76 centerStep76.proposed := by
  dsimp only [StepValid,centerStep76]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep77 : Instruction 40 := ⟨.mul 0 3,⟨⟨11568794648005,12320269809269⟩,⟨0,0⟩,⟨1620907191160,7900923427928⟩,⟨0,0⟩,⟨0,0⟩,⟨-36849917082459,43871451816214⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77
theorem centerAccepted77 : StepValid centerStep77.shape centerBoxes77 centerStep77.proposed := by
  dsimp only [StepValid,centerStep77]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep78 : Instruction 40 := ⟨.add 45 29,⟨⟨1505874595296,1549549129280⟩,⟨0,0⟩,⟨-1210493310032,-1153335043556⟩,⟨0,0⟩,⟨0,0⟩,⟨1177097066447,2007190590524⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78
theorem centerAccepted78 : StepValid centerStep78.shape centerBoxes78 centerStep78.proposed := by
  dsimp only [StepValid,centerStep78]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep79 : Instruction 40 := ⟨.mul 1 0,⟨⟨15844447224141,17363039074051⟩,⟨0,0⟩,⟨-11343873867564,-1000287066738⟩,⟨0,0⟩,⟨0,0⟩,⟨-56944547933958,80918836341983⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79
theorem centerAccepted79 : StepValid centerStep79.shape centerBoxes79 centerStep79.proposed := by
  dsimp only [StepValid,centerStep79]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep80 : Instruction 40 := ⟨.add 4 0,⟨⟨12832103599900,16454689877575⟩,⟨0,0⟩,⟨2893044309046,38451701772242⟩,⟨0,0⟩,⟨0,0⟩,⟨-94539833743074,408197827637071⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80
theorem centerAccepted80 : StepValid centerStep80.shape centerBoxes80 centerStep80.proposed := by
  dsimp only [StepValid,centerStep80]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep81 : Instruction 40 := ⟨.mul 81 81,⟨⟨1034530490573,1038800993739⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81
theorem centerAccepted81 : StepValid centerStep81.shape centerBoxes81 centerStep81.proposed := by
  dsimp only [StepValid,centerStep81]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep82 : Instruction 40 := ⟨.neg 0,⟨⟨-1038800993739,-1034530490573⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82
theorem centerAccepted82 : StepValid centerStep82.shape centerBoxes82 centerStep82.proposed := by
  dsimp only [StepValid,centerStep82]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep83 : Instruction 40 := ⟨.add 81 0,⟨⟨60710634037,64981137203⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83
theorem centerAccepted83 : StepValid centerStep83.shape centerBoxes83 centerStep83.proposed := by
  dsimp only [StepValid,centerStep83]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep84 : Instruction 40 := ⟨.inv 0,⟨⟨18604257660772,19912917049720⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes85 := centerStep84.proposed :: centerBoxes84
theorem centerAccepted84 : StepValid centerStep84.shape centerBoxes84 centerStep84.proposed := by
  dsimp only [StepValid,centerStep84]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep85 : Instruction 40 := ⟨.mul 13 0,⟨⟨50368387217462,55496144422690⟩,⟨0,0⟩,⟨126849428849455,154393965489307⟩,⟨0,0⟩,⟨0,0⟩,⟨88813097949418,365731120230210⟩⟩⟩
noncomputable def centerBoxes86 := centerStep85.proposed :: centerBoxes85
theorem centerAccepted85 : StepValid centerStep85.shape centerBoxes85 centerStep85.proposed := by
  dsimp only [StepValid,centerStep85]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep86 : Instruction 40 := ⟨.add 5 0,⟨⟨63200490817362,71950834300265⟩,⟨0,0⟩,⟨129742473158501,192845667261549⟩,⟨0,0⟩,⟨0,0⟩,⟨-5726735793656,773928947867281⟩⟩⟩
noncomputable def centerBoxes87 := centerStep86.proposed :: centerBoxes86
theorem centerAccepted86 : StepValid centerStep86.shape centerBoxes86 centerStep86.proposed := by
  dsimp only [StepValid,centerStep86]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep87 : Instruction 40 := ⟨.mul 0 68,⟨⟨30702280778348,35314704506090⟩,⟨0,0⟩,⟨27227070731182,65513161564131⟩,⟨0,0⟩,⟨0,0⟩,⟨-170982940303096,314684274580109⟩⟩⟩
noncomputable def centerBoxes88 := centerStep87.proposed :: centerBoxes87
theorem centerAccepted87 : StepValid centerStep87.shape centerBoxes87 centerStep87.proposed := by
  dsimp only [StepValid,centerStep87]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep88 : Instruction 40 := ⟨.mul 0 69,⟨⟨14914916526780,17333063146258⟩,⟨0,0⟩,⟨-4344939594100,17999592828421⟩,⟨0,0⟩,⟨0,0⟩,⟨-137585096926050,156077591679737⟩⟩⟩
noncomputable def centerBoxes89 := centerStep88.proposed :: centerBoxes88
theorem centerAccepted88 : StepValid centerStep88.shape centerBoxes88 centerStep88.proposed := by
  dsimp only [StepValid,centerStep88]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep89 : Instruction 40 := ⟨.mul 90 63,⟨⟨392032008681,396007331862⟩,⟨0,0⟩,⟨274401134607,285942615881⟩,⟨0,0⟩,⟨0,0⟩,⟨-128121384256,-22941945954⟩⟩⟩
noncomputable def centerBoxes90 := centerStep89.proposed :: centerBoxes89
theorem centerAccepted89 : StepValid centerStep89.shape centerBoxes89 centerStep89.proposed := by
  dsimp only [StepValid,centerStep89]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep90 : Instruction 40 := ⟨.inv 0,⟨⟨3052786457084,3083742635409⟩,⟨0,0⟩,⟨-2249238369182,-2115334742914⟩,⟨0,0⟩,⟨0,0⟩,⟨3108370148546,4288934433805⟩⟩⟩
noncomputable def centerBoxes91 := centerStep90.proposed :: centerBoxes90
theorem centerAccepted90 : StepValid centerStep90.shape centerBoxes90 centerStep90.proposed := by
  dsimp only [StepValid,centerStep90]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep91 : Instruction 40 := ⟨.mul 2 0,⟨⟨41411162948399,48613133755091⟩,⟨0,0⟩,⟨-47643758224351,21787919384446⟩,⟨0,0⟩,⟨0,0⟩,⟨-417355020296344,523131443478380⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91
theorem centerAccepted91 : StepValid centerStep91.shape centerBoxes91 centerStep91.proposed := by
  dsimp only [StepValid,centerStep91]
  exact ⟨by decide,by decide⟩
noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91]
theorem centerAccepted : Accepted centerProgram centerInitial :=
  ⟨centerAccepted0,⟨centerAccepted1,⟨centerAccepted2,⟨centerAccepted3,⟨centerAccepted4,⟨centerAccepted5,⟨centerAccepted6,⟨centerAccepted7,⟨centerAccepted8,⟨centerAccepted9,⟨centerAccepted10,⟨centerAccepted11,⟨centerAccepted12,⟨centerAccepted13,⟨centerAccepted14,⟨centerAccepted15,⟨centerAccepted16,⟨centerAccepted17,⟨centerAccepted18,⟨centerAccepted19,⟨centerAccepted20,⟨centerAccepted21,⟨centerAccepted22,⟨centerAccepted23,⟨centerAccepted24,⟨centerAccepted25,⟨centerAccepted26,⟨centerAccepted27,⟨centerAccepted28,⟨centerAccepted29,⟨centerAccepted30,⟨centerAccepted31,⟨centerAccepted32,⟨centerAccepted33,⟨centerAccepted34,⟨centerAccepted35,⟨centerAccepted36,⟨centerAccepted37,⟨centerAccepted38,⟨centerAccepted39,⟨centerAccepted40,⟨centerAccepted41,⟨centerAccepted42,⟨centerAccepted43,⟨centerAccepted44,⟨centerAccepted45,⟨centerAccepted46,⟨centerAccepted47,⟨centerAccepted48,⟨centerAccepted49,⟨centerAccepted50,⟨centerAccepted51,⟨centerAccepted52,⟨centerAccepted53,⟨centerAccepted54,⟨centerAccepted55,⟨centerAccepted56,⟨centerAccepted57,⟨centerAccepted58,⟨centerAccepted59,⟨centerAccepted60,⟨centerAccepted61,⟨centerAccepted62,⟨centerAccepted63,⟨centerAccepted64,⟨centerAccepted65,⟨centerAccepted66,⟨centerAccepted67,⟨centerAccepted68,⟨centerAccepted69,⟨centerAccepted70,⟨centerAccepted71,⟨centerAccepted72,⟨centerAccepted73,⟨centerAccepted74,⟨centerAccepted75,⟨centerAccepted76,⟨centerAccepted77,⟨centerAccepted78,⟨centerAccepted79,⟨centerAccepted80,⟨centerAccepted81,⟨centerAccepted82,⟨centerAccepted83,⟨centerAccepted84,⟨centerAccepted85,⟨centerAccepted86,⟨centerAccepted87,⟨centerAccepted88,⟨centerAccepted89,⟨centerAccepted90,⟨centerAccepted91,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
noncomputable def center_output : DyadicBivariateJetEnclosure 40 := ⟨⟨41411162948399,48613133755091⟩,⟨0,0⟩,⟨-47643758224351,21787919384446⟩,⟨0,0⟩,⟨0,0⟩,⟨-417355020296344,523131443478380⟩⟩
theorem center_output_eq : (finalBoxes centerProgram centerInitial).getD 0 (zeroBox 40)=center_output := rfl
noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨1066526278942,1068725302199⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨420909017707,423852192144⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨506545006916,561080783655⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
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
noncomputable def wholeStep4 : Instruction 40 := ⟨.inv 6,⟨⟨2154637718546,2386610869931⟩,⟨0,0⟩,⟨-5180401280516,-4222296136668⟩,⟨0,0⟩,⟨0,0⟩,⟨16548289777230,22489261039818⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4
theorem wholeAccepted4 : StepValid wholeStep4.shape wholeBoxes4 wholeStep4.proposed := by
  dsimp only [StepValid,wholeStep4]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep5 : Instruction 40 := ⟨.mul 6 0,⟨⟨824826607302,920017781951⟩,⟨0,0⟩,⟨-1996999743763,-1616356275329⟩,⟨0,0⟩,⟨0,0⟩,⟨6334925633259,8669414993552⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5
theorem wholeAccepted5 : StepValid wholeStep5.shape wholeBoxes5 wholeStep5.proposed := by
  dsimp only [StepValid,wholeStep5]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep6 : Instruction 40 := ⟨.contact 0,⟨⟨658519359488,697313525760⟩,⟨0,0⟩,⟨610048679917,877567522931⟩,⟨0,0⟩,⟨0,0⟩,⟨-3211294631368,-689813213171⟩⟩⟩
noncomputable def wholeBoxes7 := wholeStep6.proposed :: wholeBoxes6
theorem wholeAccepted6 : StepValid wholeStep6.shape wholeBoxes6 wholeStep6.proposed := by
  dsimp only [StepValid,wholeStep6]
  exact ⟨by decide,by decide,(⟨⟨658519359488,697313525760⟩,⟨-483172668717,-414980055645⟩,⟨276905002632,515680438184⟩⟩ : DyadicJetEnclosure 40),brwhole6_jet,by decide⟩
noncomputable def wholeStep7 : Instruction 40 := ⟨.log 10,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes8 := wholeStep7.proposed :: wholeBoxes7
theorem wholeAccepted7 : StepValid wholeStep7.shape wholeBoxes7 wholeStep7.proposed := by
  dsimp only [StepValid,wholeStep7]
  exact ⟨by decide,by decide,lc0,by decide⟩
noncomputable def wholeStep8 : Instruction 40 := ⟨.add 6 1,⟨⟨1758030987264,1796825153536⟩,⟨0,0⟩,⟨610048679917,877567522931⟩,⟨0,0⟩,⟨0,0⟩,⟨-3211294631368,-689813213171⟩⟩⟩
noncomputable def wholeBoxes9 := wholeStep8.proposed :: wholeBoxes8
theorem wholeAccepted8 : StepValid wholeStep8.shape wholeBoxes8 wholeStep8.proposed := by
  dsimp only [StepValid,wholeStep8]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep9 : Instruction 40 := ⟨.log 0,⟨⟨516031944000,540030850816⟩,⟨0,0⟩,⟨373300438141,548850220851⟩,⟨0,0⟩,⟨0,0⟩,⟨-2282388049612,-548850892048⟩⟩⟩
noncomputable def wholeBoxes10 := wholeStep9.proposed :: wholeBoxes9
theorem wholeAccepted9 : StepValid wholeStep9.shape wholeBoxes9 wholeStep9.proposed := by
  dsimp only [StepValid,wholeStep9]
  exact ⟨by decide,by decide,lc23,by decide⟩
noncomputable def wholeStep10 : Instruction 40 := ⟨.mul 1 0,⟨⟨825093728026,882520013358⟩,⟨0,0⟩,⟨883190608912,1327954504092⟩,⟨0,0⟩,⟨0,0⟩,⟨-4892888274000,-325195534470⟩⟩⟩
noncomputable def wholeBoxes11 := wholeStep10.proposed :: wholeBoxes10
theorem wholeAccepted10 : StepValid wholeStep10.shape wholeBoxes10 wholeStep10.proposed := by
  dsimp only [StepValid,wholeStep10]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep11 : Instruction 40 := ⟨.neg 4,⟨⟨-697313525760,-658519359488⟩,⟨0,0⟩,⟨-877567522931,-610048679917⟩,⟨0,0⟩,⟨0,0⟩,⟨689813213171,3211294631368⟩⟩⟩
noncomputable def wholeBoxes12 := wholeStep11.proposed :: wholeBoxes11
theorem wholeAccepted11 : StepValid wholeStep11.shape wholeBoxes11 wholeStep11.proposed := by
  dsimp only [StepValid,wholeStep11]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep12 : Instruction 40 := ⟨.add 10 0,⟨⟨402198102016,440992268288⟩,⟨0,0⟩,⟨-877567522931,-610048679917⟩,⟨0,0⟩,⟨0,0⟩,⟨689813213171,3211294631368⟩⟩⟩
noncomputable def wholeBoxes13 := wholeStep12.proposed :: wholeBoxes12
theorem wholeAccepted12 : StepValid wholeStep12.shape wholeBoxes12 wholeStep12.proposed := by
  dsimp only [StepValid,wholeStep12]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep13 : Instruction 40 := ⟨.log 0,⟨⟨-1105753163456,-1004507271488⟩,⟨0,0⟩,⟨-2399055815493,-1521014460598⟩,⟨0,0⟩,⟨0,0⟩,⟨-3514679617432,6674794849044⟩⟩⟩
noncomputable def wholeBoxes14 := wholeStep13.proposed :: wholeBoxes13
theorem wholeAccepted13 : StepValid wholeStep13.shape wholeBoxes13 wholeStep13.proposed := by
  dsimp only [StepValid,wholeStep13]
  exact ⟨by decide,by decide,lc24,by decide⟩
noncomputable def wholeStep14 : Instruction 40 := ⟨.mul 1 0,⟨⟨-443495624240,-367445789428⟩,⟨0,0⟩,⟨-404876783147,326166569209⟩,⟨0,0⟩,⟨0,0⟩,⟨-2951364882919,5876497626551⟩⟩⟩
noncomputable def wholeBoxes15 := wholeStep14.proposed :: wholeBoxes14
theorem wholeAccepted14 : StepValid wholeStep14.shape wholeBoxes14 wholeStep14.proposed := by
  dsimp only [StepValid,wholeStep14]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep15 : Instruction 40 := ⟨.add 4 0,⟨⟨381598103786,515074223930⟩,⟨0,0⟩,⟨478313825765,1654121073301⟩,⟨0,0⟩,⟨0,0⟩,⟨-7844253156919,5551302092081⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15
theorem wholeAccepted15 : StepValid wholeStep15.shape wholeBoxes15 wholeStep15.proposed := by
  dsimp only [StepValid,wholeStep15]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 0 15,⟨⟨190799051893,257537111965⟩,⟨0,0⟩,⟨239156912882,827060536651⟩,⟨0,0⟩,⟨0,0⟩,⟨-3922126578460,2775651046041⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16
theorem wholeAccepted16 : StepValid wholeStep16.shape wholeBoxes16 wholeStep16.proposed := by
  dsimp only [StepValid,wholeStep16]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨-257537111965,-190799051893⟩,⟨0,0⟩,⟨-827060536651,-239156912882⟩,⟨0,0⟩,⟨0,0⟩,⟨-2775651046041,3922126578460⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17
theorem wholeAccepted17 : StepValid wholeStep17.shape wholeBoxes17 wholeStep17.proposed := by
  dsimp only [StepValid,wholeStep17]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep18 : Instruction 40 := ⟨.add 10 0,⟨⟨504586271651,571324350987⟩,⟨0,0⟩,⟨-827060536651,-239156912882⟩,⟨0,0⟩,⟨0,0⟩,⟨-2775651046041,3922126578460⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18
theorem wholeAccepted18 : StepValid wholeStep18.shape wholeBoxes18 wholeStep18.proposed := by
  dsimp only [StepValid,wholeStep18]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep19 : Instruction 40 := ⟨.mul 12 12,⟨⟨394400328169,442238300100⟩,⟨0,0⟩,⟨730740550270,1113111836290⟩,⟨0,0⟩,⟨0,0⟩,⟨-3396271112772,574563095143⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19
theorem wholeAccepted19 : StepValid wholeStep19.shape wholeBoxes19 wholeStep19.proposed := by
  dsimp only [StepValid,wholeStep19]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep20 : Instruction 40 := ⟨.neg 0,⟨⟨-442238300100,-394400328169⟩,⟨0,0⟩,⟨-1113111836290,-730740550270⟩,⟨0,0⟩,⟨0,0⟩,⟨-574563095143,3396271112772⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20
theorem wholeAccepted20 : StepValid wholeStep20.shape wholeBoxes20 wholeStep20.proposed := by
  dsimp only [StepValid,wholeStep20]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep21 : Instruction 40 := ⟨.add 19 0,⟨⟨657273327676,705111299607⟩,⟨0,0⟩,⟨-1113111836290,-730740550270⟩,⟨0,0⟩,⟨0,0⟩,⟨-574563095143,3396271112772⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21
theorem wholeAccepted21 : StepValid wholeStep21.shape wholeBoxes21 wholeStep21.proposed := by
  dsimp only [StepValid,wholeStep21]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep22 : Instruction 40 := ⟨.log 0,⟨⟨-565722294784,-488475328576⟩,⟨0,0⟩,⟨-1862055488154,-1139476466136⟩,⟨0,0⟩,⟨0,0⟩,⟨-4114596917021,4500516552600⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22
theorem wholeAccepted22 : StepValid wholeStep22.shape wholeBoxes22 wholeStep22.proposed := by
  dsimp only [StepValid,wholeStep22]
  exact ⟨by decide,by decide,lc21,by decide⟩
noncomputable def wholeStep23 : Instruction 40 := ⟨.mul 0 22,⟨⟨-282861147392,-244237664288⟩,⟨0,0⟩,⟨-931027744077,-569738233068⟩,⟨0,0⟩,⟨0,0⟩,⟨-2057298458511,2250258276300⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23
theorem wholeAccepted23 : StepValid wholeStep23.shape wholeBoxes23 wholeStep23.proposed := by
  dsimp only [StepValid,wholeStep23]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep24 : Instruction 40 := ⟨.neg 0,⟨⟨244237664288,282861147392⟩,⟨0,0⟩,⟨569738233068,931027744077⟩,⟨0,0⟩,⟨0,0⟩,⟨-2250258276300,2057298458511⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24
theorem wholeAccepted24 : StepValid wholeStep24.shape wholeBoxes24 wholeStep24.proposed := by
  dsimp only [StepValid,wholeStep24]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep25 : Instruction 40 := ⟨.add 17 0,⟨⟨1006361047904,1044984550272⟩,⟨0,0⟩,⟨569738233068,931027744077⟩,⟨0,0⟩,⟨0,0⟩,⟨-2250258276300,2057298458511⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25
theorem wholeAccepted25 : StepValid wholeStep25.shape wholeBoxes25 wholeStep25.proposed := by
  dsimp only [StepValid,wholeStep25]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep26 : Instruction 40 := ⟨.add 24 26,⟨⟨2166037906718,2168236929975⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26
theorem wholeAccepted26 : StepValid wholeStep26.shape wholeBoxes26 wholeStep26.proposed := by
  dsimp only [StepValid,wholeStep26]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep27 : Instruction 40 := ⟨.neg 27,⟨⟨-1068725302199,-1066526278942⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27
theorem wholeAccepted27 : StepValid wholeStep27.shape wholeBoxes27 wholeStep27.proposed := by
  dsimp only [StepValid,wholeStep27]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep28 : Instruction 40 := ⟨.add 26 0,⟨⟨30786325577,32985348834⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28
theorem wholeAccepted28 : StepValid wholeStep28.shape wholeBoxes28 wholeStep28.proposed := by
  dsimp only [StepValid,wholeStep28]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep29 : Instruction 40 := ⟨.inv 0,⟨⟨36650387591733,39268272421501⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29
theorem wholeAccepted29 : StepValid wholeStep29.shape wholeBoxes29 wholeStep29.proposed := by
  dsimp only [StepValid,wholeStep29]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep30 : Instruction 40 := ⟨.mul 3 0,⟨⟨72201263555690,77437033215226⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30
theorem wholeAccepted30 : StepValid wholeStep30.shape wholeBoxes30 wholeStep30.proposed := by
  dsimp only [StepValid,wholeStep30]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨4601006938752,4677981208128⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31
theorem wholeAccepted31 : StepValid wholeStep31.shape wholeBoxes31 wholeStep31.proposed := by
  dsimp only [StepValid,wholeStep31]
  exact ⟨by decide,by decide,lc12,by decide⟩
noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 0 31,⟨⟨2300503469376,2338990604064⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32
theorem wholeAccepted32 : StepValid wholeStep32.shape wholeBoxes32 wholeStep32.proposed := by
  dsimp only [StepValid,wholeStep32]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep33 : Instruction 40 := ⟨.inv 20,⟨⟨2741376451582,3005796928318⟩,⟨0,0⟩,⟨3792295706079,6558434143764⟩,⟨0,0⟩,⟨0,0⟩,⟨-13507186841306,24331926923974⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33
theorem wholeAccepted33 : StepValid wholeStep33.shape wholeBoxes33 wholeStep33.proposed := by
  dsimp only [StepValid,wholeStep33]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep34 : Instruction 40 := ⟨.mul 25 0,⟨⟨4383241275388,4912082228860⟩,⟨0,0⟩,⟨7584591412158,13116868287528⟩,⟨0,0⟩,⟨0,0⟩,⟨-26644177187485,48512554934968⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34
theorem wholeAccepted34 : StepValid wholeStep34.shape wholeBoxes34 wholeStep34.proposed := by
  dsimp only [StepValid,wholeStep34]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨1520539214528,1645784032256⟩,⟨0,0⟩,⟨1697721263823,3290293254704⟩,⟨0,0⟩,⟨0,0⟩,⟨-16529759903140,9547705925895⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35
theorem wholeAccepted35 : StepValid wholeStep35.shape wholeBoxes35 wholeStep35.proposed := by
  dsimp only [StepValid,wholeStep35]
  exact ⟨by decide,by decide,lc27,by decide⟩
noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 0 35,⟨⟨760269607264,822892016128⟩,⟨0,0⟩,⟨848860631911,1645146627352⟩,⟨0,0⟩,⟨0,0⟩,⟨-8264879951570,4773852962948⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36
theorem wholeAccepted36 : StepValid wholeStep36.shape wholeBoxes36 wholeStep36.proposed := by
  dsimp only [StepValid,wholeStep36]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep37 : Instruction 40 := ⟨.mul 40 11,⟨⟨2012722095808,2089969100544⟩,⟨0,0⟩,⟨1139476466136,1862055488154⟩,⟨0,0⟩,⟨0,0⟩,⟨-4500516552600,4114596917022⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37
theorem wholeAccepted37 : StepValid wholeStep37.shape wholeBoxes37 wholeStep37.proposed := by
  dsimp only [StepValid,wholeStep37]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep38 : Instruction 40 := ⟨.add 0 17,⟨⟨1570483795708,1695568772375⟩,⟨0,0⟩,⟨26364629846,1131314937884⟩,⟨0,0⟩,⟨0,0⟩,⟨-5075079647743,7510868029794⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38
theorem wholeAccepted38 : StepValid wholeStep38.shape wholeBoxes38 wholeStep38.proposed := by
  dsimp only [StepValid,wholeStep38]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep39 : Instruction 40 := ⟨.mul 20 0,⟨⟨720724131646,881045460511⟩,⟨0,0⟩,⟨-1263319780749,246250889483⟩,⟨0,0⟩,⟨0,0⟩,⟨-8619422898780,9939655304374⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39
theorem wholeAccepted39 : StepValid wholeStep39.shape wholeBoxes39 wholeStep39.proposed := by
  dsimp only [StepValid,wholeStep39]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep40 : Instruction 40 := ⟨.mul 43 41,⟨⟨841818035414,847704384288⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40
theorem wholeAccepted40 : StepValid wholeStep40.shape wholeBoxes40 wholeStep40.proposed := by
  dsimp only [StepValid,wholeStep40]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 19 19,⟨⟨392909193828,452184344644⟩,⟨0,0⟩,⟨-1427666090412,-873653831410⟩,⟨0,0⟩,⟨0,0⟩,⟨234378278193,6609783846641⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41
theorem wholeAccepted41 : StepValid wholeStep41.shape wholeBoxes41 wholeStep41.proposed := by
  dsimp only [StepValid,wholeStep41]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep42 : Instruction 40 := ⟨.mul 1 0,⟨⟨300822690082,348626282595⟩,⟨0,0⟩,⟨-1100705780247,-668894746913⟩,⟨0,0⟩,⟨0,0⟩,⟨179446816848,5096028640759⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42
theorem wholeAccepted42 : StepValid wholeStep42.shape wholeBoxes42 wholeStep42.proposed := by
  dsimp only [StepValid,wholeStep42]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep43 : Instruction 40 := ⟨.mul 17 17,⟨⟨921102181326,993161584400⟩,⟨0,0⟩,⟨1042940066802,1769712268352⟩,⟨0,0⟩,⟨0,0⟩,⟨-3686879569862,5487268508084⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43
theorem wholeAccepted43 : StepValid wholeStep43.shape wholeBoxes43 wholeStep43.proposed := by
  dsimp only [StepValid,wholeStep43]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep44 : Instruction 40 := ⟨.mul 18 0,⟨⟨843066442417,943908627616⟩,⟨0,0⟩,⟨1431873340872,2522922812462⟩,⟨0,0⟩,⟨0,0⟩,⟨-4455793352925,10070510190890⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44
theorem wholeAccepted44 : StepValid wholeStep44.shape wholeBoxes44 wholeStep44.proposed := by
  dsimp only [StepValid,wholeStep44]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 2 0,⟨⟨230660148304,299288654747⟩,⟨0,0⟩,⟨-553178044524,287067893398⟩,⟨0,0⟩,⟨0,0⟩,⟨-6326547489833,5825754506413⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45
theorem wholeAccepted45 : StepValid wholeStep45.shape wholeBoxes45 wholeStep45.proposed := by
  dsimp only [StepValid,wholeStep45]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep46 : Instruction 40 := ⟨.inv 0,⟨⟨4039330594193,5241155997270⟩,⟨0,0⟩,⟨-6522876284307,12569542016396⟩,⟨0,0⟩,⟨0,0⟩,⟨-163662047140487,204043966895877⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46
theorem wholeAccepted46 : StepValid wholeStep46.shape wholeBoxes46 wholeStep46.proposed := by
  dsimp only [StepValid,wholeStep46]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep47 : Instruction 40 := ⟨.mul 7 0,⟨⟨2647760115842,4199770682340⟩,⟨0,0⟩,⟨-11248818359588,11245881305964⟩,⟨0,0⟩,⟨0,0⟩,⟨-201114877053032,225871419445206⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47
theorem wholeAccepted47 : StepValid wholeStep47.shape wholeBoxes47 wholeStep47.proposed := by
  dsimp only [StepValid,wholeStep47]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep48 : Instruction 40 := ⟨.neg 11,⟨⟨-822892016128,-760269607264⟩,⟨0,0⟩,⟨-1645146627352,-848860631911⟩,⟨0,0⟩,⟨0,0⟩,⟨-4773852962948,8264879951570⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48
theorem wholeAccepted48 : StepValid wholeStep48.shape wholeBoxes48 wholeStep48.proposed := by
  dsimp only [StepValid,wholeStep48]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep49 : Instruction 40 := ⟨.mul 0 10,⟨⟨-1268990677621,-1085928578120⟩,⟨0,0⟩,⟨-3383692526248,-1230697393119⟩,⟨0,0⟩,⟨0,0⟩,⟨-16368528352231,16502922411701⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49
theorem wholeAccepted49 : StepValid wholeStep49.shape wholeBoxes49 wholeStep49.proposed := by
  dsimp only [StepValid,wholeStep49]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 53 43,⟨⟨1317038718976,1394627051520⟩,⟨0,0⟩,⟨1220097359834,1755135045862⟩,⟨0,0⟩,⟨0,0⟩,⟨-6422589262736,-1379626426342⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50
theorem wholeAccepted50 : StepValid wholeStep50.shape wholeBoxes50 wholeStep50.proposed := by
  dsimp only [StepValid,wholeStep50]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep51 : Instruction 40 := ⟨.inv 29,⟨⟨1714517722646,1839304546085⟩,⟨0,0⟩,⟨1776836684919,3114916693835⟩,⟨0,0⟩,⟨0,0⟩,⟨-5821236274402,12158256631374⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51
theorem wholeAccepted51 : StepValid wholeStep51.shape wholeBoxes51 wholeStep51.proposed := by
  dsimp only [StepValid,wholeStep51]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep52 : Instruction 40 := ⟨.mul 1 0,⟨⟨2053717457870,2332984764466⟩,⟨0,0⟩,⟨4030918042303,6887034899866⟩,⟨0,0⟩,⟨0,0⟩,⟨-14184228088113,23214887321432⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52
theorem wholeAccepted52 : StepValid wholeStep52.shape wholeBoxes52 wholeStep52.proposed := by
  dsimp only [StepValid,wholeStep52]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep53 : Instruction 40 := ⟨.neg 2,⟨⟨-1394627051520,-1317038718976⟩,⟨0,0⟩,⟨-1755135045862,-1220097359834⟩,⟨0,0⟩,⟨0,0⟩,⟨1379626426342,6422589262736⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53
theorem wholeAccepted53 : StepValid wholeStep53.shape wholeBoxes53 wholeStep53.proposed := by
  dsimp only [StepValid,wholeStep53]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep54 : Instruction 40 := ⟨.add 1 0,⟨⟨659090406350,1015946045490⟩,⟨0,0⟩,⟨2275782996441,5666937540032⟩,⟨0,0⟩,⟨0,0⟩,⟨-12804601661771,29637476584168⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54
theorem wholeAccepted54 : StepValid wholeStep54.shape wholeBoxes54 wholeStep54.proposed := by
  dsimp only [StepValid,wholeStep54]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 36 0,⟨⟨302468807441,527902298088⟩,⟨0,0⟩,⟨280197105592,2801274045169⟩,⟨0,0⟩,⟨0,0⟩,⟨-17743598840752,18034136328429⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55
theorem wholeAccepted55 : StepValid wholeStep55.shape wholeBoxes55 wholeStep55.proposed := by
  dsimp only [StepValid,wholeStep55]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep56 : Instruction 40 := ⟨.add 6 0,⟨⟨-966521870180,-558026280032⟩,⟨0,0⟩,⟨-3103495420656,1570576652050⟩,⟨0,0⟩,⟨0,0⟩,⟨-34112127192983,34537058740130⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56
theorem wholeAccepted56 : StepValid wholeStep56.shape wholeBoxes56 wholeStep56.proposed := by
  dsimp only [StepValid,wholeStep56]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep57 : Instruction 40 := ⟨.mul 0 10,⟨⟨-4607219940578,-2050048920224⟩,⟨0,0⟩,⟨-25842965345387,13220542154455⟩,⟨0,0⟩,⟨0,0⟩,⟨-412927846514820,345321035437625⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57
theorem wholeAccepted57 : StepValid wholeStep57.shape wholeBoxes57 wholeStep57.proposed := by
  dsimp only [StepValid,wholeStep57]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 54 51,⟨⟨2634077437952,2789254103040⟩,⟨0,0⟩,⟨2440194719668,3510270091724⟩,⟨0,0⟩,⟨0,0⟩,⟨-12845178525472,-2759252852684⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58
theorem wholeAccepted58 : StepValid wholeStep58.shape wholeBoxes58 wholeStep58.proposed := by
  dsimp only [StepValid,wholeStep58]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep59 : Instruction 40 := ⟨.mul 0 7,⟨⟨4107434915741,4665969528931⟩,⟨0,0⟩,⟨8061836084606,13774069799731⟩,⟨0,0⟩,⟨0,0⟩,⟨-28368456176225,46429774642864⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59
theorem wholeAccepted59 : StepValid wholeStep59.shape wholeBoxes59 wholeStep59.proposed := by
  dsimp only [StepValid,wholeStep59]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 57 53,⟨⟨1975558078464,2091940577280⟩,⟨0,0⟩,⟨1830146039751,2632702568793⟩,⟨0,0⟩,⟨0,0⟩,⟨-9633883894104,-2069439639513⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60
theorem wholeAccepted60 : StepValid wholeStep60.shape wholeBoxes60 wholeStep60.proposed := by
  dsimp only [StepValid,wholeStep60]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 39 35,⟨⟨601589158395,670143357922⟩,⟨0,0⟩,⟨-717328409607,-71768812012⟩,⟨0,0⟩,⟨0,0⟩,⟨-3874236516757,3789876765277⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61
theorem wholeAccepted61 : StepValid wholeStep61.shape wholeBoxes61 wholeStep61.proposed := by
  dsimp only [StepValid,wholeStep61]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep62 : Instruction 40 := ⟨.inv 0,⟨⟨1803980902479,2009553867028⟩,⟨0,0⟩,⟨193196820848,2396170308822⟩,⟨0,0⟩,⟨0,0⟩,⟨-12618357915179,18655869858966⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62
theorem wholeAccepted62 : StepValid wholeStep62.shape wholeBoxes62 wholeStep62.proposed := by
  dsimp only [StepValid,wholeStep62]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep63 : Instruction 40 := ⟨.mul 2 0,⟨⟨3241320014501,3823395015085⟩,⟨0,0⟩,⟨3349869116043,9370709019051⟩,⟨0,0⟩,⟨0,0⟩,⟨-40972287735865,43574390500468⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63
theorem wholeAccepted63 : StepValid wholeStep63.shape wholeBoxes63 wholeStep63.proposed := by
  dsimp only [StepValid,wholeStep63]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep64 : Instruction 40 := ⟨.neg 0,⟨⟨-3823395015085,-3241320014501⟩,⟨0,0⟩,⟨-9370709019051,-3349869116043⟩,⟨0,0⟩,⟨0,0⟩,⟨-43574390500468,40972287735865⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64
theorem wholeAccepted64 : StepValid wholeStep64.shape wholeBoxes64 wholeStep64.proposed := by
  dsimp only [StepValid,wholeStep64]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep65 : Instruction 40 := ⟨.add 5 0,⟨⟨284039900656,1424649514430⟩,⟨0,0⟩,⟨-1308872934445,10424200683688⟩,⟨0,0⟩,⟨0,0⟩,⟨-71942846676693,87402062378729⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65
theorem wholeAccepted65 : StepValid wholeStep65.shape wholeBoxes65 wholeStep65.proposed := by
  dsimp only [StepValid,wholeStep65]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 18 0,⟨⟨684003244045,5441689848625⟩,⟨0,0⟩,⟨-19574681383246,54388412318132⟩,⟨0,0⟩,⟨0,0⟩,⟨-748679258580986,839749986323182⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66
theorem wholeAccepted66 : StepValid wholeStep66.shape wholeBoxes66 wholeStep66.proposed := by
  dsimp only [StepValid,wholeStep66]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep67 : Instruction 40 := ⟨.add 9 0,⟨⟨-3923216696533,3391640928401⟩,⟨0,0⟩,⟨-45417646728633,67608954472587⟩,⟨0,0⟩,⟨0,0⟩,⟨-1161607105095806,1185071021760807⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67
theorem wholeAccepted67 : StepValid wholeStep67.shape wholeBoxes67 wholeStep67.proposed := by
  dsimp only [StepValid,wholeStep67]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 61 29,⟨⟨940593948358,1075334729498⟩,⟨0,0⟩,⟨887151314201,2070789647054⟩,⟨0,0⟩,⟨0,0⟩,⟨-8141546607710,5584024519896⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68
theorem wholeAccepted68 : StepValid wholeStep68.shape wholeBoxes68 wholeStep68.proposed := by
  dsimp only [StepValid,wholeStep68]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 27 25,⟨⟨329154786866,408446903901⟩,⟨0,0⟩,⟨-916881959247,-4082055567⟩,⟨0,0⟩,⟨0,0⟩,⟨-5915698483847,6569737835253⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69
theorem wholeAccepted69 : StepValid wholeStep69.shape wholeBoxes69 wholeStep69.proposed := by
  dsimp only [StepValid,wholeStep69]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨2959811441997,3672818588256⟩,⟨0,0⟩,⟨29580625189,10230873854892⟩,⟨0,0⟩,⟨0,0⟩,⟨-73306728588132,123006853612152⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70
theorem wholeAccepted70 : StepValid wholeStep70.shape wholeBoxes70 wholeStep70.proposed := by
  dsimp only [StepValid,wholeStep70]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 2 0,⟨⟨2532015724339,3592057858530⟩,⟨0,0⟩,⟨2413456939025,16923194086619⟩,⟨0,0⟩,⟨0,0⟩,⟨-98843165591126,177492098398423⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71
theorem wholeAccepted71 : StepValid wholeStep71.shape wholeBoxes71 wholeStep71.proposed := by
  dsimp only [StepValid,wholeStep71]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 65 39,⟨⟨1377817235291,1483394757852⟩,⟨0,0⟩,⟨1276402240034,1866849007063⟩,⟨0,0⟩,⟨0,0⟩,⟨-6831385662419,-1443293231315⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72
theorem wholeAccepted72 : StepValid wholeStep72.shape wholeBoxes72 wholeStep72.proposed := by
  dsimp only [StepValid,wholeStep72]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep73 : Instruction 40 := ⟨.add 54 0,⟨⟨1882403506942,2054719108839⟩,⟨0,0⟩,⟨449341703383,1627692094181⟩,⟨0,0⟩,⟨0,0⟩,⟨-9607036708460,2478833347145⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73
theorem wholeAccepted73 : StepValid wholeStep73.shape wholeBoxes73 wholeStep73.proposed := by
  dsimp only [StepValid,wholeStep73]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 0 0,⟨⟨3222742600835,3839768957031⟩,⟨0,0⟩,⟨1538578359510,6083519200220⟩,⟨0,0⟩,⟨0,0⟩,⟨-35539149280871,14083867062193⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74
theorem wholeAccepted74 : StepValid wholeStep74.shape wholeBoxes74 wholeStep74.proposed := by
  dsimp only [StepValid,wholeStep74]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep75 : Instruction 40 := ⟨.mul 7 0,⟨⟨-13700851634943,11844456412537⟩,⟨0,0⟩,⟨-180316632495295,254873045659535⟩,⟨0,0⟩,⟨0,0⟩,⟨-4668833923897159,5013523560005538⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75
theorem wholeAccepted75 : StepValid wholeStep75.shape wholeBoxes75 wholeStep75.proposed := by
  dsimp only [StepValid,wholeStep75]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep76 : Instruction 40 := ⟨.mul 79 28,⟨⟨5295520231684,8399541364680⟩,⟨0,0⟩,⟨-22497636719176,22491762611928⟩,⟨0,0⟩,⟨0,0⟩,⟨-402229754106064,451742838890412⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76
theorem wholeAccepted76 : StepValid wholeStep76.shape wholeBoxes76 wholeStep76.proposed := by
  dsimp only [StepValid,wholeStep76]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 0 3,⟨⟨9066121360960,15696694524642⟩,⟨0,0⟩,⟨-39878455926925,54466110217833⟩,⟨0,0⟩,⟨0,0⟩,⟨-891670711081287,929726443209860⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77
theorem wholeAccepted77 : StepValid wholeStep77.shape wholeBoxes77 wholeStep77.proposed := by
  dsimp only [StepValid,wholeStep77]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep78 : Instruction 40 := ⟨.add 45 29,⟨⟨1477611453248,1578720996800⟩,⟨0,0⟩,⟨-1645146627352,-848860631911⟩,⟨0,0⟩,⟨0,0⟩,⟨-4773852962948,8264879951570⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78
theorem wholeAccepted78 : StepValid wholeStep78.shape wholeBoxes78 wholeStep78.proposed := by
  dsimp only [StepValid,wholeStep78]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 1 0,⟨⟨12183777252622,22537916471636⟩,⟨0,0⟩,⟨-80745230433959,71205175397581⟩,⟨0,0⟩,⟨0,0⟩,⟨-1511436913042660,1572263288474092⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79
theorem wholeAccepted79 : StepValid wholeStep79.shape wholeBoxes79 wholeStep79.proposed := by
  dsimp only [StepValid,wholeStep79]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep80 : Instruction 40 := ⟨.add 4 0,⟨⟨-1517074382321,34382372884173⟩,⟨0,0⟩,⟨-261061862929254,326078221057116⟩,⟨0,0⟩,⟨0,0⟩,⟨-6180270836939819,6585786848479630⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80
theorem wholeAccepted80 : StepValid wholeStep80.shape wholeBoxes80 wholeStep80.proposed := by
  dsimp only [StepValid,wholeStep80]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep81 : Instruction 40 := ⟨.mul 81 81,⟨⟨1034530490573,1038800993739⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81
theorem wholeAccepted81 : StepValid wholeStep81.shape wholeBoxes81 wholeStep81.proposed := by
  dsimp only [StepValid,wholeStep81]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep82 : Instruction 40 := ⟨.neg 0,⟨⟨-1038800993739,-1034530490573⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82
theorem wholeAccepted82 : StepValid wholeStep82.shape wholeBoxes82 wholeStep82.proposed := by
  dsimp only [StepValid,wholeStep82]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep83 : Instruction 40 := ⟨.add 81 0,⟨⟨60710634037,64981137203⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83
theorem wholeAccepted83 : StepValid wholeStep83.shape wholeBoxes83 wholeStep83.proposed := by
  dsimp only [StepValid,wholeStep83]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep84 : Instruction 40 := ⟨.inv 0,⟨⟨18604257660772,19912917049720⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes85 := wholeStep84.proposed :: wholeBoxes84
theorem wholeAccepted84 : StepValid wholeStep84.shape wholeBoxes84 wholeStep84.proposed := by
  dsimp only [StepValid,wholeStep84]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep85 : Instruction 40 := ⟨.mul 13 0,⟨⟨42842905656224,65054655510451⟩,⟨0,0⟩,⟨40836834838773,306490765127052⟩,⟨0,0⟩,⟨0,0⟩,⟨-1790118183041914,3214504824780795⟩⟩⟩
noncomputable def wholeBoxes86 := wholeStep85.proposed :: wholeBoxes85
theorem wholeAccepted85 : StepValid wholeStep85.shape wholeBoxes85 wholeStep85.proposed := by
  dsimp only [StepValid,wholeStep85]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep86 : Instruction 40 := ⟨.add 5 0,⟨⟨41325831273903,99437028394624⟩,⟨0,0⟩,⟨-220225028090481,632568986184168⟩,⟨0,0⟩,⟨0,0⟩,⟨-7970389019981733,9800291673260425⟩⟩⟩
noncomputable def wholeBoxes87 := wholeStep86.proposed :: wholeBoxes86
theorem wholeAccepted86 : StepValid wholeStep86.shape wholeBoxes86 wholeStep86.proposed := by
  dsimp only [StepValid,wholeStep86]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep87 : Instruction 40 := ⟨.mul 0 68,⟨⟨18965190179530,51669117703236⟩,⟨0,0⟩,⟨-189229798081148,319704401823789⟩,⟨0,0⟩,⟨0,0⟩,⟨-5344214074464832,5778409787573256⟩⟩⟩
noncomputable def wholeBoxes88 := wholeStep87.proposed :: wholeBoxes87
theorem wholeAccepted87 : StepValid wholeStep87.shape wholeBoxes87 wholeStep87.proposed := by
  dsimp only [StepValid,wholeStep87]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep88 : Instruction 40 := ⟨.mul 0 69,⟨⟨8703477400414,26848124560159⟩,⟨0,0⟩,⟨-137192800859371,161998517382115⟩,⟨0,0⟩,⟨0,0⟩,⟨-3388345127418101,3471548587326079⟩⟩⟩
noncomputable def wholeBoxes89 := wholeStep88.proposed :: wholeBoxes88
theorem wholeAccepted88 : StepValid wholeStep88.shape wholeBoxes88 wholeStep88.proposed := by
  dsimp only [StepValid,wholeStep88]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep89 : Instruction 40 := ⟨.mul 90 63,⟨⟨385249623042,402832476893⟩,⟨0,0⟩,⟨218104069090,358903116898⟩,⟨0,0⟩,⟨0,0⟩,⟨-867455040225,793070704763⟩⟩⟩
noncomputable def wholeBoxes90 := wholeStep89.proposed :: wholeBoxes89
theorem wholeAccepted89 : StepValid wholeStep89.shape wholeBoxes89 wholeStep89.proposed := by
  dsimp only [StepValid,wholeStep89]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep90 : Instruction 40 := ⟨.inv 0,⟨⟨3001063441902,3138032453008⟩,⟨0,0⟩,⟨-2923428242237,-1624854463881⟩,⟨0,0⟩,⟨0,0⟩,⟨-4700441995714,12512814538329⟩⟩⟩
noncomputable def wholeBoxes91 := wholeStep90.proposed :: wholeBoxes90
theorem wholeAccepted90 : StepValid wholeStep90.shape wholeBoxes90 wholeStep90.proposed := by
  dsimp only [StepValid,wholeStep90]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 2 0,⟨⟨23755717705901,76625188896451⟩,⟨0,0⟩,⟨-462936465743075,449485670086605⟩,⟨0,0⟩,⟨0,0⟩,⟨-10646651486103160,10942971448343363⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91
theorem wholeAccepted91 : StepValid wholeStep91.shape wholeBoxes91 wholeStep91.proposed := by
  dsimp only [StepValid,wholeStep91]
  exact ⟨by decide,by decide⟩
noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91]
theorem wholeAccepted : Accepted wholeProgram wholeInitial :=
  ⟨wholeAccepted0,⟨wholeAccepted1,⟨wholeAccepted2,⟨wholeAccepted3,⟨wholeAccepted4,⟨wholeAccepted5,⟨wholeAccepted6,⟨wholeAccepted7,⟨wholeAccepted8,⟨wholeAccepted9,⟨wholeAccepted10,⟨wholeAccepted11,⟨wholeAccepted12,⟨wholeAccepted13,⟨wholeAccepted14,⟨wholeAccepted15,⟨wholeAccepted16,⟨wholeAccepted17,⟨wholeAccepted18,⟨wholeAccepted19,⟨wholeAccepted20,⟨wholeAccepted21,⟨wholeAccepted22,⟨wholeAccepted23,⟨wholeAccepted24,⟨wholeAccepted25,⟨wholeAccepted26,⟨wholeAccepted27,⟨wholeAccepted28,⟨wholeAccepted29,⟨wholeAccepted30,⟨wholeAccepted31,⟨wholeAccepted32,⟨wholeAccepted33,⟨wholeAccepted34,⟨wholeAccepted35,⟨wholeAccepted36,⟨wholeAccepted37,⟨wholeAccepted38,⟨wholeAccepted39,⟨wholeAccepted40,⟨wholeAccepted41,⟨wholeAccepted42,⟨wholeAccepted43,⟨wholeAccepted44,⟨wholeAccepted45,⟨wholeAccepted46,⟨wholeAccepted47,⟨wholeAccepted48,⟨wholeAccepted49,⟨wholeAccepted50,⟨wholeAccepted51,⟨wholeAccepted52,⟨wholeAccepted53,⟨wholeAccepted54,⟨wholeAccepted55,⟨wholeAccepted56,⟨wholeAccepted57,⟨wholeAccepted58,⟨wholeAccepted59,⟨wholeAccepted60,⟨wholeAccepted61,⟨wholeAccepted62,⟨wholeAccepted63,⟨wholeAccepted64,⟨wholeAccepted65,⟨wholeAccepted66,⟨wholeAccepted67,⟨wholeAccepted68,⟨wholeAccepted69,⟨wholeAccepted70,⟨wholeAccepted71,⟨wholeAccepted72,⟨wholeAccepted73,⟨wholeAccepted74,⟨wholeAccepted75,⟨wholeAccepted76,⟨wholeAccepted77,⟨wholeAccepted78,⟨wholeAccepted79,⟨wholeAccepted80,⟨wholeAccepted81,⟨wholeAccepted82,⟨wholeAccepted83,⟨wholeAccepted84,⟨wholeAccepted85,⟨wholeAccepted86,⟨wholeAccepted87,⟨wholeAccepted88,⟨wholeAccepted89,⟨wholeAccepted90,⟨wholeAccepted91,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
noncomputable def whole_output : DyadicBivariateJetEnclosure 40 := ⟨⟨23755717705901,76625188896451⟩,⟨0,0⟩,⟨-462936465743075,449485670086605⟩,⟨0,0⟩,⟨0,0⟩,⟨-10646651486103160,10942971448343363⟩⟩
theorem whole_output_eq : (finalBoxes wholeProgram wholeInitial).getD 0 (zeroBox 40)=whole_output := rfl
open GeneralCK.Reflection GeneralCK.Reflection.SmallRatio GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed
theorem sameShape : shapes centerProgram=shapes wholeProgram := by decide
theorem scalar_program (a e r : ℝ) :
    (evalRealProgram wholeProgram [a,e,r,2]).getD 0 0=ReflectionMidpointKernel.scalarCore a e r := rfl
attribute [local irreducible] wholeProgram centerProgram
noncomputable def reflection_log_0_out : DyadicInterval 64 := ⟨-12786308645202662930,-12786308645202655416⟩
theorem reflection_log_0_checked : DyadicFastLog.check 1 2 1 16 reflection_log_0_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointNextFamily.Endpoints0840.sharedTwo_eq]
  decide
theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := DyadicFastLog.check_sound reflection_log_0_checked
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1):ℝ)=((1 / 2):ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [he]
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_0_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_1_out : DyadicInterval 64 := ⟨-12526229395459408625,-12526229395459404610⟩
theorem reflection_log_1_checked : DyadicFastLog.check 250 493 0 16 reflection_log_1_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointNextFamily.Endpoints0840.sharedTwo_eq]
  decide
theorem reflection_log_1 : Bounds (10610129 / 15625000) (679048257 / 1000000000) (Real.log (493 / 250)) := by
  have h := DyadicFastLog.check_sound reflection_log_1_checked
  have he : Real.log (493 / 250) = -Real.log (250 / 493) := by
    rw [show ((493 / 250):ℝ)=((250 / 493):ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [he]
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_1_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_2_out : DyadicInterval 64 := ⟨-65957269954736961151,-65957269954736923576⟩
theorem reflection_log_2_checked : DyadicFastLog.check 7 250 5 16 reflection_log_2_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointNextFamily.Endpoints0840.sharedTwo_eq]
  decide
theorem reflection_log_2 : Bounds (-893887693 / 250000000) (-1787775383 / 500000000) (Real.log (7 / 250)) := by
  have h := DyadicFastLog.check_sound reflection_log_2_checked
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_2_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_3_out : DyadicInterval 64 := ⟨-12507511236497960661,-12507511236497956826⟩
theorem reflection_log_3_checked : DyadicFastLog.check 100 197 0 16 reflection_log_3_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointNextFamily.Endpoints0840.sharedTwo_eq]
  decide
theorem reflection_log_3 : Bounds (339016771 / 500000000) (678033543 / 1000000000) (Real.log (197 / 100)) := by
  have h := DyadicFastLog.check_sound reflection_log_3_checked
  have he : Real.log (197 / 100) = -Real.log (100 / 197) := by
    rw [show ((197 / 100):ℝ)=((100 / 197):ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [he]
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_3_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_4_out : DyadicInterval 64 := ⟨-64684576111506834767,-64684576111506797190⟩
theorem reflection_log_4_checked : DyadicFastLog.check 3 100 5 16 reflection_log_4_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointNextFamily.Endpoints0840.sharedTwo_eq]
  decide
theorem reflection_log_4 : Bounds (-35065579 / 10000000) (-1753278947 / 500000000) (Real.log (3 / 100)) := by
  have h := DyadicFastLog.check_sound reflection_log_4_checked
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_4_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_5_out : DyadicInterval 64 := ⟨-875407601287200615,-875407601287200570⟩
theorem reflection_log_5_checked : DyadicFastLog.check 5000 5243 0 16 reflection_log_5_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointNextFamily.Endpoints0840.sharedTwo_eq]
  decide
theorem reflection_log_5 : Bounds (47455941 / 1000000000) (23727971 / 500000000) (Real.log (5243 / 5000)) := by
  have h := DyadicFastLog.check_sound reflection_log_5_checked
  have he : Real.log (5243 / 5000) = -Real.log (5000 / 5243) := by
    rw [show ((5243 / 5000):ℝ)=((5000 / 5243):ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [he]
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_5_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_6_out : DyadicInterval 64 := ⟨-919029609943380561,-919029609943380512⟩
theorem reflection_log_6_checked : DyadicFastLog.check 4757 5000 0 16 reflection_log_6_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointNextFamily.Endpoints0840.sharedTwo_eq]
  decide
theorem reflection_log_6 : Bounds (-9964139 / 200000000) (-24910347 / 500000000) (Real.log (4757 / 5000)) := by
  have h := DyadicFastLog.check_sound reflection_log_6_checked
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_6_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_7_out : DyadicInterval 64 := ⟨-178071161875805387,-178071161875805342⟩
theorem reflection_log_7_checked : DyadicFastLog.check 10000 10097 0 16 reflection_log_7_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointNextFamily.Endpoints0840.sharedTwo_eq]
  decide
theorem reflection_log_7 : Bounds (9653257 / 1000000000) (4826629 / 500000000) (Real.log (10097 / 10000)) := by
  have h := DyadicFastLog.check_sound reflection_log_7_checked
  have he : Real.log (10097 / 10000) = -Real.log (10000 / 10097) := by
    rw [show ((10097 / 10000):ℝ)=((10000 / 10097):ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [he]
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_7_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_8_out : DyadicInterval 64 := ⟨-179806897684672437,-179806897684672390⟩
theorem reflection_log_8_checked : DyadicFastLog.check 9903 10000 0 16 reflection_log_8_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointNextFamily.Endpoints0840.sharedTwo_eq]
  decide
theorem reflection_log_8 : Bounds (-1218419 / 125000000) (-9747351 / 1000000000) (Real.log (9903 / 10000)) := by
  have h := DyadicFastLog.check_sound reflection_log_8_checked
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_8_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
theorem entropy_bound {a z : ℝ} (ha : Bounds (97 / 100) (243 / 250) a) (hz : Bounds (1 / 100) (1 / 20) z) :
  Bounds (382814521533 / 1000000000000) (385491323089 / 1000000000000) ((biasE a+biasE (a*z))/2) := by
  let x0 : ℝ := Real.log (2 / 1)
  have hx0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x0 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x1 : ℝ := (1 / 1)+(243 / 250)
  have hx1 : Bounds (493 / 250) (493 / 250) x1 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((243 / 250) : ℝ)) <;> norm_num
  let x2 : ℝ := (1 / 1)+(243 / 250)
  have hx2 : Bounds (493 / 250) (493 / 250) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((243 / 250) : ℝ)) <;> norm_num
  let x3 : ℝ := Real.log x2
  have hx3 : Bounds (10610129 / 15625000) (679048257 / 1000000000) x3 := by
    exact bounds_log hx2 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x4 : ℝ := x1*x3
  have hx4 : Bounds (5230793597 / 3906250000) (334770790701 / 250000000000) x4 := by
    apply bounds_mul hx1 hx3 <;> norm_num
  let x5 : ℝ := -(243 / 250)
  have hx5 : Bounds (-243 / 250) (-243 / 250) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((243 / 250) : ℝ))
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (7 / 250) (7 / 250) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-(243 / 250)
  have hx7 : Bounds (7 / 250) (7 / 250) x7 := by
    exact hx6
  let x8 : ℝ := -(243 / 250)
  have hx8 : Bounds (-243 / 250) (-243 / 250) x8 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((243 / 250) : ℝ))
  let x9 : ℝ := (1 / 1)+x8
  have hx9 : Bounds (7 / 250) (7 / 250) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx8 <;> norm_num
  let x10 : ℝ := (1 / 1)-(243 / 250)
  have hx10 : Bounds (7 / 250) (7 / 250) x10 := by
    exact hx9
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (-893887693 / 250000000) (-1787775383 / 500000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x12 : ℝ := x7*x11
  have hx12 : Bounds (-6257213851 / 62500000000) (-12514427681 / 125000000000) x12 := by
    apply bounds_mul hx7 hx11 <;> norm_num
  let x13 : ℝ := x4+x12
  have hx13 : Bounds (77435483701 / 62500000000) (309741935339 / 250000000000) x13 := by
    apply bounds_add hx4 hx12 <;> norm_num
  let x14 : ℝ := (2 / 1)⁻¹
  have hx14 : Bounds (1 / 2) (1 / 2) x14 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x15 : ℝ := x13*x14
  have hx15 : Bounds (77435483701 / 125000000000) (309741935339 / 500000000000) x15 := by
    apply bounds_mul hx13 hx14 <;> norm_num
  let x16 : ℝ := x13/(2 / 1)
  have hx16 : Bounds (77435483701 / 125000000000) (309741935339 / 500000000000) x16 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx15
  let x17 : ℝ := -x16
  have hx17 : Bounds (-309741935339 / 500000000000) (-77435483701 / 125000000000) x17 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx16
  let x18 : ℝ := x0+x17
  have hx18 : Bounds (36831654661 / 500000000000) (2301978481 / 31250000000) x18 := by
    apply bounds_add hx0 hx17 <;> norm_num
  let x19 : ℝ := x0-x16
  have hx19 : Bounds (36831654661 / 500000000000) (2301978481 / 31250000000) x19 := by
    exact hx18
  let x20 : ℝ := biasE (243 / 250)
  have hx20 : Bounds (36831654661 / 500000000000) (2301978481 / 31250000000) x20 := by
    simpa +zetaDelta only [biasE, div_one] using hx19
  let x21 : ℝ := Real.log (2 / 1)
  have hx21 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x21 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x22 : ℝ := (1 / 1)+(97 / 100)
  have hx22 : Bounds (197 / 100) (197 / 100) x22 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((97 / 100) : ℝ)) <;> norm_num
  let x23 : ℝ := (1 / 1)+(97 / 100)
  have hx23 : Bounds (197 / 100) (197 / 100) x23 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((97 / 100) : ℝ)) <;> norm_num
  let x24 : ℝ := Real.log x23
  have hx24 : Bounds (339016771 / 500000000) (678033543 / 1000000000) x24 := by
    exact bounds_log hx23 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x25 : ℝ := x22*x24
  have hx25 : Bounds (66786303887 / 50000000000) (133572607971 / 100000000000) x25 := by
    apply bounds_mul hx22 hx24 <;> norm_num
  let x26 : ℝ := -(97 / 100)
  have hx26 : Bounds (-97 / 100) (-97 / 100) x26 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((97 / 100) : ℝ))
  let x27 : ℝ := (1 / 1)+x26
  have hx27 : Bounds (3 / 100) (3 / 100) x27 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx26 <;> norm_num
  let x28 : ℝ := (1 / 1)-(97 / 100)
  have hx28 : Bounds (3 / 100) (3 / 100) x28 := by
    exact hx27
  let x29 : ℝ := -(97 / 100)
  have hx29 : Bounds (-97 / 100) (-97 / 100) x29 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((97 / 100) : ℝ))
  let x30 : ℝ := (1 / 1)+x29
  have hx30 : Bounds (3 / 100) (3 / 100) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx29 <;> norm_num
  let x31 : ℝ := (1 / 1)-(97 / 100)
  have hx31 : Bounds (3 / 100) (3 / 100) x31 := by
    exact hx30
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (-35065579 / 10000000) (-1753278947 / 500000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x33 : ℝ := x28*x32
  have hx33 : Bounds (-105196737 / 1000000000) (-5259836841 / 50000000000) x33 := by
    apply bounds_mul hx28 hx32 <;> norm_num
  let x34 : ℝ := x25+x33
  have hx34 : Bounds (61526467037 / 50000000000) (123052934289 / 100000000000) x34 := by
    apply bounds_add hx25 hx33 <;> norm_num
  let x35 : ℝ := (2 / 1)⁻¹
  have hx35 : Bounds (1 / 2) (1 / 2) x35 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x36 : ℝ := x34*x35
  have hx36 : Bounds (61526467037 / 100000000000) (123052934289 / 200000000000) x36 := by
    apply bounds_mul hx34 hx35 <;> norm_num
  let x37 : ℝ := x34/(2 / 1)
  have hx37 : Bounds (61526467037 / 100000000000) (123052934289 / 200000000000) x37 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx36
  let x38 : ℝ := -x37
  have hx38 : Bounds (-123052934289 / 200000000000) (-61526467037 / 100000000000) x38 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx37
  let x39 : ℝ := x21+x38
  have hx39 : Bounds (15576501711 / 200000000000) (7788251063 / 100000000000) x39 := by
    apply bounds_add hx21 hx38 <;> norm_num
  let x40 : ℝ := x21-x37
  have hx40 : Bounds (15576501711 / 200000000000) (7788251063 / 100000000000) x40 := by
    exact hx39
  let x41 : ℝ := biasE (97 / 100)
  have hx41 : Bounds (15576501711 / 200000000000) (7788251063 / 100000000000) x41 := by
    simpa +zetaDelta only [biasE, div_one] using hx40
  let x42 : ℝ := biasE a
  have hx42 : Bounds (36831654661 / 500000000000) (7788251063 / 100000000000) x42 := by
    exact bounds_biasE ha (by norm_num) (by norm_num) hx20.1 hx41.2
  let x43 : ℝ := a*z
  have hx43 : Bounds (97 / 10000) (243 / 5000) x43 := by
    apply bounds_mul ha hz <;> norm_num
  let x44 : ℝ := Real.log (2 / 1)
  have hx44 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x44 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x45 : ℝ := (1 / 1)+(243 / 5000)
  have hx45 : Bounds (5243 / 5000) (5243 / 5000) x45 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((243 / 5000) : ℝ)) <;> norm_num
  let x46 : ℝ := (1 / 1)+(243 / 5000)
  have hx46 : Bounds (5243 / 5000) (5243 / 5000) x46 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((243 / 5000) : ℝ)) <;> norm_num
  let x47 : ℝ := Real.log x46
  have hx47 : Bounds (47455941 / 1000000000) (23727971 / 500000000) x47 := by
    exact bounds_log hx46 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x48 : ℝ := x45*x47
  have hx48 : Bounds (12440574933 / 250000000000) (24881150391 / 500000000000) x48 := by
    apply bounds_mul hx45 hx47 <;> norm_num
  let x49 : ℝ := -(243 / 5000)
  have hx49 : Bounds (-243 / 5000) (-243 / 5000) x49 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((243 / 5000) : ℝ))
  let x50 : ℝ := (1 / 1)+x49
  have hx50 : Bounds (4757 / 5000) (4757 / 5000) x50 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx49 <;> norm_num
  let x51 : ℝ := (1 / 1)-(243 / 5000)
  have hx51 : Bounds (4757 / 5000) (4757 / 5000) x51 := by
    exact hx50
  let x52 : ℝ := -(243 / 5000)
  have hx52 : Bounds (-243 / 5000) (-243 / 5000) x52 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((243 / 5000) : ℝ))
  let x53 : ℝ := (1 / 1)+x52
  have hx53 : Bounds (4757 / 5000) (4757 / 5000) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx52 <;> norm_num
  let x54 : ℝ := (1 / 1)-(243 / 5000)
  have hx54 : Bounds (4757 / 5000) (4757 / 5000) x54 := by
    exact hx53
  let x55 : ℝ := Real.log x54
  have hx55 : Bounds (-9964139 / 200000000) (-24910347 / 500000000) x55 := by
    exact bounds_log hx54 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x56 : ℝ := x51*x55
  have hx56 : Bounds (-47399409223 / 1000000000000) (-47399408271 / 1000000000000) x56 := by
    apply bounds_mul hx51 hx55 <;> norm_num
  let x57 : ℝ := x48+x56
  have hx57 : Bounds (2362890509 / 1000000000000) (2362892511 / 1000000000000) x57 := by
    apply bounds_add hx48 hx56 <;> norm_num
  let x58 : ℝ := (2 / 1)⁻¹
  have hx58 : Bounds (1 / 2) (1 / 2) x58 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x59 : ℝ := x57*x58
  have hx59 : Bounds (590722627 / 500000000000) (73840391 / 62500000000) x59 := by
    apply bounds_mul hx57 hx58 <;> norm_num
  let x60 : ℝ := x57/(2 / 1)
  have hx60 : Bounds (590722627 / 500000000000) (73840391 / 62500000000) x60 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx59
  let x61 : ℝ := -x60
  have hx61 : Bounds (-73840391 / 62500000000) (-590722627 / 500000000000) x61 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx60
  let x62 : ℝ := x44+x61
  have hx62 : Bounds (43247858359 / 62500000000) (345982867873 / 500000000000) x62 := by
    apply bounds_add hx44 hx61 <;> norm_num
  let x63 : ℝ := x44-x60
  have hx63 : Bounds (43247858359 / 62500000000) (345982867873 / 500000000000) x63 := by
    exact hx62
  let x64 : ℝ := biasE (243 / 5000)
  have hx64 : Bounds (43247858359 / 62500000000) (345982867873 / 500000000000) x64 := by
    simpa +zetaDelta only [biasE, div_one] using hx63
  let x65 : ℝ := Real.log (2 / 1)
  have hx65 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x65 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x66 : ℝ := (1 / 1)+(97 / 10000)
  have hx66 : Bounds (10097 / 10000) (10097 / 10000) x66 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((97 / 10000) : ℝ)) <;> norm_num
  let x67 : ℝ := (1 / 1)+(97 / 10000)
  have hx67 : Bounds (10097 / 10000) (10097 / 10000) x67 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((97 / 10000) : ℝ)) <;> norm_num
  let x68 : ℝ := Real.log x67
  have hx68 : Bounds (9653257 / 1000000000) (4826629 / 500000000) x68 := by
    exact bounds_log hx67 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x69 : ℝ := x66*x68
  have hx69 : Bounds (1218361699 / 125000000000) (9746894603 / 1000000000000) x69 := by
    apply bounds_mul hx66 hx68 <;> norm_num
  let x70 : ℝ := -(97 / 10000)
  have hx70 : Bounds (-97 / 10000) (-97 / 10000) x70 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((97 / 10000) : ℝ))
  let x71 : ℝ := (1 / 1)+x70
  have hx71 : Bounds (9903 / 10000) (9903 / 10000) x71 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx70 <;> norm_num
  let x72 : ℝ := (1 / 1)-(97 / 10000)
  have hx72 : Bounds (9903 / 10000) (9903 / 10000) x72 := by
    exact hx71
  let x73 : ℝ := -(97 / 10000)
  have hx73 : Bounds (-97 / 10000) (-97 / 10000) x73 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((97 / 10000) : ℝ))
  let x74 : ℝ := (1 / 1)+x73
  have hx74 : Bounds (9903 / 10000) (9903 / 10000) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx73 <;> norm_num
  let x75 : ℝ := (1 / 1)-(97 / 10000)
  have hx75 : Bounds (9903 / 10000) (9903 / 10000) x75 := by
    exact hx74
  let x76 : ℝ := Real.log x75
  have hx76 : Bounds (-1218419 / 125000000) (-9747351 / 1000000000) x76 := by
    exact bounds_log hx75 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x77 : ℝ := x72*x76
  have hx77 : Bounds (-4826401343 / 500000000000) (-1930560339 / 200000000000) x77 := by
    apply bounds_mul hx72 hx76 <;> norm_num
  let x78 : ℝ := x69+x77
  have hx78 : Bounds (47045453 / 500000000000) (23523227 / 250000000000) x78 := by
    apply bounds_add hx69 hx77 <;> norm_num
  let x79 : ℝ := (2 / 1)⁻¹
  have hx79 : Bounds (1 / 2) (1 / 2) x79 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x80 : ℝ := x78*x79
  have hx80 : Bounds (47045453 / 1000000000000) (23523227 / 500000000000) x80 := by
    apply bounds_mul hx78 hx79 <;> norm_num
  let x81 : ℝ := x78/(2 / 1)
  have hx81 : Bounds (47045453 / 1000000000000) (23523227 / 500000000000) x81 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx80
  let x82 : ℝ := -x81
  have hx82 : Bounds (-23523227 / 500000000000) (-47045453 / 1000000000000) x82 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx81
  let x83 : ℝ := x65+x82
  have hx83 : Bounds (346550066773 / 500000000000) (693100135547 / 1000000000000) x83 := by
    apply bounds_add hx65 hx82 <;> norm_num
  let x84 : ℝ := x65-x81
  have hx84 : Bounds (346550066773 / 500000000000) (693100135547 / 1000000000000) x84 := by
    exact hx83
  let x85 : ℝ := biasE (97 / 10000)
  have hx85 : Bounds (346550066773 / 500000000000) (693100135547 / 1000000000000) x85 := by
    simpa +zetaDelta only [biasE, div_one] using hx84
  let x86 : ℝ := biasE x43
  have hx86 : Bounds (43247858359 / 62500000000) (693100135547 / 1000000000000) x86 := by
    exact bounds_biasE hx43 (by norm_num) (by norm_num) hx64.1 hx85.2
  let x87 : ℝ := x42+x86
  have hx87 : Bounds (382814521533 / 500000000000) (770982646177 / 1000000000000) x87 := by
    apply bounds_add hx42 hx86 <;> norm_num
  let x88 : ℝ := (2 / 1)⁻¹
  have hx88 : Bounds (1 / 2) (1 / 2) x88 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x89 : ℝ := x87*x88
  have hx89 : Bounds (382814521533 / 1000000000000) (385491323089 / 1000000000000) x89 := by
    apply bounds_mul hx87 hx88 <;> norm_num
  let x90 : ℝ := x87/(2 / 1)
  have hx90 : Bounds (382814521533 / 1000000000000) (385491323089 / 1000000000000) x90 := by
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

theorem center_inputs_eq : centerInitial=inputBoxes ⟨1066526278942,1068725302199⟩ ⟨420909017707,423852192144⟩ ⟨533263139471,534362651100⟩ := rfl
theorem whole_inputs_eq : wholeInitial=inputBoxes ⟨1066526278942,1068725302199⟩ ⟨420909017707,423852192144⟩ ⟨506545006916,561080783655⟩ := rfl
noncomputable def centerUpper : ℝ := (48613133755091 / 1099511627776)
noncomputable def secondUpper : ℝ := (10942971448343363 / 1099511627776)


theorem center_inputs {a z : ℝ} (ha : Bounds (97/100) (243/250) a)
    (hz : Bounds (1/100) (1/20) z) :
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

theorem whole_inputs {a z s : ℝ} (ha : Bounds (97/100) (243/250) a)
    (hz : Bounds (1/100) (1/20) z) (hs : s∈Icc (a*(1-z)/2) (a*(1+z)/2)) :
    RegistersContain wholeInitial (inputJets a ((biasE a+biasE (a*z))/2)) s := by
  rw [whole_inputs_eq]
  apply inputs_contain
  · norm_num [DyadicInterval.Contains,DyadicInterval.scale]
    constructor <;> linarith [ha.1,ha.2]
  · have h := entropy_bound ha hz
    norm_num [DyadicInterval.Contains,DyadicInterval.scale]
    constructor <;> linarith [h.1,h.2]
  · have hb : a*z≤(243/250:ℝ)*(1/20) :=
      mul_le_mul ha.2 hz.2 (by linarith [hz.1]) (by norm_num)
    norm_num [DyadicInterval.Contains,DyadicInterval.scale]
    constructor <;> nlinarith [ha.1,ha.2,hs.1,hs.2]

theorem curvature_pos {a z : ℝ} (ha : Bounds (97/100) (243/250) a)
    (hz : Bounds (1/100) (1/20) z) : 0<curvature a (a*z) := by
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
    have hb : a*z≤(243/5000:ℝ) := by
      have h := mul_le_mul ha.2 hz.2 hz0.le (by norm_num : (0:ℝ)≤243/250)
      norm_num at h
      exact h
    have hb2 := mul_self_le_mul_self hb0 hb
    have hle : centerUpper+secondUpper*(a*z)^2/24 ≤
        centerUpper+secondUpper*(243/5000:ℝ)^2/24 := by
      unfold centerUpper secondUpper
      nlinarith
    apply hle.trans_lt
    exact lt_of_lt_of_le (by norm_num [centerUpper,secondUpper] :
      centerUpper+secondUpper*(243/5000:ℝ)^2/24 < 2*(97/100:ℝ)/(1-(97/100:ℝ)^2)^2)
      (LowRatioFamily.base_mono (by norm_num) ha.1 ha1)

#print axioms entropy_bound
#print axioms curvature_pos
end GeneralCK.Certificates.ReflectionMidpointNextFamily.Cell0840

end

-- ===== source module GeneralCK.Certificates.Generated.MidpointNextFamily.Cell0841 =====
section

namespace GeneralCK.Certificates.ReflectionMidpointNextFamily.Endpoints0841
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
noncomputable def out_w1 : DyadicInterval 40 := ⟨529144910208,529144910336⟩
theorem checked_w1 : DyadicFastLog.check 1099511627776 1779123093504 0 16 (lift40 out_w1.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w1 : out_w1.Contains (Real.log ((1779123093504:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w1
#print axioms endpoint_w1
noncomputable def out_w2 : DyadicInterval 40 := ⟨-1058394761920,-1058394742592⟩
theorem checked_w2 : DyadicFastLog.check 419900162048 1099511627776 1 16 (lift40 out_w2)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w2 : out_w2.Contains (Real.log ((419900162048:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w2
#print axioms endpoint_w2
noncomputable def out_w3 : DyadicInterval 40 := ⟨531153257600,531153257728⟩
theorem checked_w3 : DyadicFastLog.check 1099511627776 1782375776256 0 16 (lift40 out_w3.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w3 : out_w3.Contains (Real.log ((1782375776256:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w3
#print axioms endpoint_w3
noncomputable def out_w4 : DyadicInterval 40 := ⟨-1066945095104,-1066945075776⟩
theorem checked_w4 : DyadicFastLog.check 416647479296 1099511627776 1 16 (lift40 out_w4)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w4 : out_w4.Contains (Real.log ((416647479296:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w4
#print axioms endpoint_w4
noncomputable def out_w5 : DyadicInterval 40 := ⟨-535791819392,-535791819264⟩
theorem checked_w5 : DyadicFastLog.check 675411114876 1099511627776 0 16 (lift40 out_w5)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w5 : out_w5.Contains (Real.log ((675411114876:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w5
#print axioms endpoint_w5
noncomputable def out_w6 : DyadicInterval 40 := ⟨-529249833600,-529249833472⟩
theorem checked_w6 : DyadicFastLog.check 679441723392 1099511627776 0 16 (lift40 out_w6)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w6 : out_w6.Contains (Real.log ((679441723392:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w6
#print axioms endpoint_w6
noncomputable def out_w7 : DyadicInterval 40 := ⟨4677981092416,4677981208064⟩
theorem checked_w7 : DyadicFastLog.check 1099511627776 77437033212672 6 16 (lift40 out_w7.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w7 : out_w7.Contains (Real.log ((77437033212672:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w7
#print axioms endpoint_w7
noncomputable def out_w8 : DyadicInterval 40 := ⟨4760578227776,4760578343424⟩
theorem checked_w8 : DyadicFastLog.check 1099511627776 83478305893976 6 16 (lift40 out_w8.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w8 : out_w8.Contains (Real.log ((83478305893976:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w8
#print axioms endpoint_w8
noncomputable def out_w9 : DyadicInterval 40 := ⟨1587539651648,1587539690240⟩
theorem checked_w9 : DyadicFastLog.check 1099511627776 4658646757866 2 16 (lift40 out_w9.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w9 : out_w9.Contains (Real.log ((4658646757866:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w9
#print axioms endpoint_w9
noncomputable def out_w10 : DyadicInterval 40 := ⟨1598098332224,1598098370816⟩
theorem checked_w10 : DyadicFastLog.check 1099511627776 4703599537844 2 16 (lift40 out_w10.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w10 : out_w10.Contains (Real.log ((4703599537844:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w10
#print axioms endpoint_w10
noncomputable def out_w11 : DyadicInterval 40 := ⟨517731126848,517731126976⟩
theorem checked_w11 : DyadicFastLog.check 1099511627776 1760749944832 0 16 (lift40 out_w11.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w11 : out_w11.Contains (Real.log ((1760749944832:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w11
#print axioms endpoint_w11
noncomputable def out_w12 : DyadicInterval 40 := ⟨-1011307363648,-1011307344320⟩
theorem checked_w12 : DyadicFastLog.check 438273310720 1099511627776 1 16 (lift40 out_w12)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w12 : out_w12.Contains (Real.log ((438273310720:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w12
#print axioms endpoint_w12
noncomputable def out_w13 : DyadicInterval 40 := ⟨541668388608,541668388736⟩
theorem checked_w13 : DyadicFastLog.check 1099511627776 1799503216640 0 16 (lift40 out_w13.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w13 : out_w13.Contains (Real.log ((1799503216640:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w13
#print axioms endpoint_w13
noncomputable def out_w14 : DyadicInterval 40 := ⟨-1113098818560,-1113098799232⟩
theorem checked_w14 : DyadicFastLog.check 399520038912 1099511627776 1 16 (lift40 out_w14)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w14 : out_w14.Contains (Real.log ((399520038912:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w14
#print axioms endpoint_w14
noncomputable def out_w15 : DyadicInterval 40 := ⟨-571430411968,-571430411712⟩
theorem checked_w15 : DyadicFastLog.check 653869933680 1099511627776 0 16 (lift40 out_w15)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w15 : out_w15.Contains (Real.log ((653869933680:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w15
#print axioms endpoint_w15
noncomputable def out_w16 : DyadicInterval 40 := ⟨-493576218688,-493576218624⟩
theorem checked_w16 : DyadicFastLog.check 701847700540 1099511627776 0 16 (lift40 out_w16)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w16 : out_w16.Contains (Real.log ((701847700540:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w16
#print axioms endpoint_w16
noncomputable def out_w17 : DyadicInterval 40 := ⟨1529038470016,1529038508608⟩
theorem checked_w17 : DyadicFastLog.check 1099511627776 4417255147862 2 16 (lift40 out_w17.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w17 : out_w17.Contains (Real.log ((4417255147862:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w17
#print axioms endpoint_w17
noncomputable def out_w18 : DyadicInterval 40 := ⟨1654767186688,1654767225280⟩
theorem checked_w18 : DyadicFastLog.check 1099511627776 4952379150504 2 16 (lift40 out_w18.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w18 : out_w18.Contains (Real.log ((4952379150504:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w18
#print axioms endpoint_w18
end GeneralCK.Certificates.ReflectionMidpointNextFamily.Endpoints0841

namespace GeneralCK.Certificates.ReflectionMidpointNextFamily.Cell0841
open Set GeneralCK.Certificates.ReflectionMidpointNextFamily.Endpoints0841
open BivariateJetProgram (RegistersContain RegistersSound zeroBox zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
theorem lc0 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc1 : ProvedTranscendental.LogEncloses (⟨1779123093504,1779123093504⟩ : DyadicInterval 40) (⟨529144910208,529144910336⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w1
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w1
theorem lc2 : ProvedTranscendental.LogEncloses (⟨419900162048,419900162048⟩ : DyadicInterval 40) (⟨-1058394761920,-1058394742592⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w2
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w2
theorem lc3 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc4 : ProvedTranscendental.LogEncloses (⟨1782375776256,1782375776256⟩ : DyadicInterval 40) (⟨531153257600,531153257728⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w3
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w3
theorem lc5 : ProvedTranscendental.LogEncloses (⟨416647479296,416647479296⟩ : DyadicInterval 40) (⟨-1066945095104,-1066945075776⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w4
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w4
theorem lc6 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc7 : ProvedTranscendental.LogEncloses (⟨675411114876,679441723392⟩ : DyadicInterval 40) (⟨-535791819392,-529249833472⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w5
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w6
theorem lc8 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc9 : ProvedTranscendental.LogEncloses (⟨1779123093504,1782375776256⟩ : DyadicInterval 40) (⟨529144910208,531153257728⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w1
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w3
theorem lc10 : ProvedTranscendental.LogEncloses (⟨416647479296,419900162048⟩ : DyadicInterval 40) (⟨-1066945095104,-1058394742592⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w4
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w2
theorem lc11 : ProvedTranscendental.LogEncloses (⟨675411114876,679441723392⟩ : DyadicInterval 40) (⟨-535791819392,-529249833472⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w5
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w6
theorem lc12 : ProvedTranscendental.LogEncloses (⟨77437033212672,83478305893976⟩ : DyadicInterval 40) (⟨4677981092416,4760578343424⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w7
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
theorem lc13 : ProvedTranscendental.LogEncloses (⟨4658646757866,4703599537844⟩ : DyadicInterval 40) (⟨1587539651648,1598098370816⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w9
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w10
theorem lc14 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc15 : ProvedTranscendental.LogEncloses (⟨1760749944832,1760749944832⟩ : DyadicInterval 40) (⟨517731126848,517731126976⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w11
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w11
theorem lc16 : ProvedTranscendental.LogEncloses (⟨438273310720,438273310720⟩ : DyadicInterval 40) (⟨-1011307363648,-1011307344320⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w12
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w12
theorem lc17 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc18 : ProvedTranscendental.LogEncloses (⟨1799503216640,1799503216640⟩ : DyadicInterval 40) (⟨541668388608,541668388736⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w13
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w13
theorem lc19 : ProvedTranscendental.LogEncloses (⟨399520038912,399520038912⟩ : DyadicInterval 40) (⟨-1113098818560,-1113098799232⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w14
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w14
theorem lc20 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc21 : ProvedTranscendental.LogEncloses (⟨653869933680,701847700540⟩ : DyadicInterval 40) (⟨-571430411968,-493576218624⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w15
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w16
theorem lc22 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc23 : ProvedTranscendental.LogEncloses (⟨1760749944832,1799503216640⟩ : DyadicInterval 40) (⟨517731126848,541668388736⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w11
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w13
theorem lc24 : ProvedTranscendental.LogEncloses (⟨399520038912,438273310720⟩ : DyadicInterval 40) (⟨-1113098818560,-1011307344320⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w14
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w12
theorem lc25 : ProvedTranscendental.LogEncloses (⟨653869933680,701847700540⟩ : DyadicInterval 40) (⟨-571430411968,-493576218624⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w15
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w16
theorem lc26 : ProvedTranscendental.LogEncloses (⟨77437033212672,83478305893976⟩ : DyadicInterval 40) (⟨4677981092416,4760578343424⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w7
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
theorem lc27 : ProvedTranscendental.LogEncloses (⟨4417255147862,4952379150504⟩ : DyadicInterval 40) (⟨1529038470016,1654767225280⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w17
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w18
theorem ew3_ok (x : ℝ) (hx : (⟨679611465728,679611465728⟩ : DyadicInterval 40).Contains x) : (⟨536116766992,536116790051⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨679611465728,679611465728⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨529144910208,529144910336⟩ : DyadicInterval 40)) (minus:=(⟨-1058394761920,-1058394742592⟩ : DyadicInterval 40))
    (lc0 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc1 lc2 (by decide) hx
theorem ew6_ok (x : ℝ) (hx : (⟨682864148480,682864148480⟩ : DyadicInterval 40).Contains x) : (⟨533760758338,533760781369⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨682864148480,682864148480⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨531153257600,531153257728⟩ : DyadicInterval 40)) (minus:=(⟨-1066945095104,-1066945075776⟩ : DyadicInterval 40))
    (lc3 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc4 lc5 (by decide) hx
theorem ew17_ok (x : ℝ) (hx : (⟨661238317056,661238317056⟩ : DyadicInterval 40).Contains x) : (⟨549135169813,549135193033⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨661238317056,661238317056⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨517731126848,517731126976⟩ : DyadicInterval 40)) (minus:=(⟨-1011307363648,-1011307344320⟩ : DyadicInterval 40))
    (lc14 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc15 lc16 (by decide) hx
theorem ew20_ok (x : ℝ) (hx : (⟨699991588864,699991588864⟩ : DyadicInterval 40).Contains x) : (⟨521094221708,521094244590⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨699991588864,699991588864⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨541668388608,541668388736⟩ : DyadicInterval 40)) (minus:=(⟨-1113098818560,-1113098799232⟩ : DyadicInterval 40))
    (lc17 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc18 lc19 (by decide) hx
theorem bw9_ok (x : ℝ) (hx : (⟨679611465728,682864148480⟩ : DyadicInterval 40).Contains x) : (⟨1026748300352,1030019312576⟩ : DyadicInterval 40).Contains (Reflection.biasB x) := by
  exact ProvedTranscendental.denominator_encloses (c:=(⟨679611465728,682864148480⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (gapLog:=(⟨-535791819392,-529249833472⟩ : DyadicInterval 40))
    (lc6 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc7 (by decide) hx
theorem bw23_ok (x : ℝ) (hx : (⟨661238317056,699991588864⟩ : DyadicInterval 40).Contains x) : (⟨1008911492928,1047838608864⟩ : DyadicInterval 40).Contains (Reflection.biasB x) := by
  exact ProvedTranscendental.denominator_encloses (c:=(⟨661238317056,699991588864⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (gapLog:=(⟨-571430411968,-493576218624⟩ : DyadicInterval 40))
    (lc20 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc21 (by decide) hx
theorem brcenter6_contact (y : ℝ) (hy : (⟨859439328334,867350938731⟩ : DyadicInterval 40).Contains y) : (⟨679611465728,682864148480⟩ : DyadicInterval 40).Contains (Reflection.biasContact y) := by
  exact ProvedTranscendental.contact_bracket (Y:=(⟨859439328334,867350938731⟩ : DyadicInterval 40)) (c:=(⟨679611465728,682864148480⟩ : DyadicInterval 40)) (elo:=(⟨536116766992,536116790051⟩ : DyadicInterval 40)) (ehi:=(⟨533760758338,533760781369⟩ : DyadicInterval 40))
    (by decide) (by decide) (by decide) (by decide)
    (ew3_ok _ (DyadicContact.point_contains 40 679611465728)) (ew6_ok _ (DyadicContact.point_contains 40 682864148480))
    (by decide) (by decide) hy
theorem brcenter6_jet (y : ℝ) (hy : (⟨859439328334,867350938731⟩ : DyadicInterval 40).Contains y) : (⟨⟨679611465728,682864148480⟩,⟨-454155556060,-448410761535⟩,⟨388626272466,408833742843⟩⟩ : DyadicJetEnclosure 40).Contains reflectionContactJet y := by
  exact ProvedTranscendental.contact_jet (c:=(⟨679611465728,682864148480⟩ : DyadicInterval 40)) (B:=(⟨1026748300352,1030019312576⟩ : DyadicInterval 40)) (by decide) brcenter6_contact bw9_ok (by decide) (by decide) (by decide) hy
theorem brwhole6_contact (y : ℝ) (hy : (⟨818513646031,913099872683⟩ : DyadicInterval 40).Contains y) : (⟨661238317056,699991588864⟩ : DyadicInterval 40).Contains (Reflection.biasContact y) := by
  exact ProvedTranscendental.contact_bracket (Y:=(⟨818513646031,913099872683⟩ : DyadicInterval 40)) (c:=(⟨661238317056,699991588864⟩ : DyadicInterval 40)) (elo:=(⟨549135169813,549135193033⟩ : DyadicInterval 40)) (ehi:=(⟨521094221708,521094244590⟩ : DyadicInterval 40))
    (by decide) (by decide) (by decide) (by decide)
    (ew17_ok _ (DyadicContact.point_contains 40 661238317056)) (ew20_ok _ (DyadicContact.point_contains 40 699991588864))
    (by decide) (by decide) hy
theorem brwhole6_jet (y : ℝ) (hy : (⟨818513646031,913099872683⟩ : DyadicInterval 40).Contains y) : (⟨⟨661238317056,699991588864⟩,⟨-485660266451,-417274290376⟩,⟨276368962596,517356717980⟩⟩ : DyadicJetEnclosure 40).Contains reflectionContactJet y := by
  exact ProvedTranscendental.contact_jet (c:=(⟨661238317056,699991588864⟩ : DyadicInterval 40)) (B:=(⟨1008911492928,1047838608864⟩ : DyadicInterval 40)) (by decide) brwhole6_contact bw23_ok (by decide) (by decide) (by decide) hy
noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨1068725302198,1070924325454⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨418546952899,421532556223⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨534362651099,535462162727⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
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
noncomputable def centerStep4 : Instruction 40 := ⟨.inv 6,⟨⟨2257724081675,2262369604478⟩,⟨0,0⟩,⟨-4655081490697,-4635983740604⟩,⟨0,0⟩,⟨0,0⟩,⟨19038947600010,19156713953492⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4
theorem centerAccepted4 : StepValid centerStep4.shape centerBoxes4 centerStep4.proposed := by
  dsimp only [StepValid,centerStep4]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep5 : Instruction 40 := ⟨.mul 6 0,⟨⟨859439328334,867350938731⟩,⟨0,0⟩,⟨-1784672713439,-1764762481178⟩,⟨0,0⟩,⟨0,0⟩,⟨7247484522293,7344332154070⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5
theorem centerAccepted5 : StepValid centerStep5.shape centerBoxes5 centerStep5.proposed := by
  dsimp only [StepValid,centerStep5]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep6 : Instruction 40 := ⟨.contact 0,⟨⟨679611465728,682864148480⟩,⟨0,0⟩,⟨719718162248,737162762159⟩,⟨0,0⟩,⟨0,0⟩,⟨-2032428067180,-1878601016273⟩⟩⟩
noncomputable def centerBoxes7 := centerStep6.proposed :: centerBoxes6
theorem centerAccepted6 : StepValid centerStep6.shape centerBoxes6 centerStep6.proposed := by
  dsimp only [StepValid,centerStep6]
  exact ⟨by decide,by decide,(⟨⟨679611465728,682864148480⟩,⟨-454155556060,-448410761535⟩,⟨388626272466,408833742843⟩⟩ : DyadicJetEnclosure 40),brcenter6_jet,by decide⟩
noncomputable def centerStep7 : Instruction 40 := ⟨.log 10,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes8 := centerStep7.proposed :: centerBoxes7
theorem centerAccepted7 : StepValid centerStep7.shape centerBoxes7 centerStep7.proposed := by
  dsimp only [StepValid,centerStep7]
  exact ⟨by decide,by decide,lc0,by decide⟩
noncomputable def centerStep8 : Instruction 40 := ⟨.add 6 1,⟨⟨1779123093504,1782375776256⟩,⟨0,0⟩,⟨719718162248,737162762159⟩,⟨0,0⟩,⟨0,0⟩,⟨-2032428067180,-1878601016273⟩⟩⟩
noncomputable def centerBoxes9 := centerStep8.proposed :: centerBoxes8
theorem centerAccepted8 : StepValid centerStep8.shape centerBoxes8 centerStep8.proposed := by
  dsimp only [StepValid,centerStep8]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep9 : Instruction 40 := ⟨.log 0,⟨⟨529144910208,531153257728⟩,⟨0,0⟩,⟨443979602199,455572203811⟩,⟨0,0⟩,⟨0,0⟩,⟨-1444818048846,-1338148709426⟩⟩⟩
noncomputable def centerBoxes10 := centerStep9.proposed :: centerBoxes9
theorem centerAccepted9 : StepValid centerStep9.shape centerBoxes9 centerStep9.proposed := by
  dsimp only [StepValid,centerStep9]
  exact ⟨by decide,by decide,lc9,by decide⟩
noncomputable def centerStep10 : Instruction 40 := ⟨.mul 1 0,⟨⟨856210981111,861032003790⟩,⟨0,0⟩,⟨1064772337171,1094619859037⟩,⟨0,0⟩,⟨0,0⟩,⟨-2742725986175,-2458474872860⟩⟩⟩
noncomputable def centerBoxes11 := centerStep10.proposed :: centerBoxes10
theorem centerAccepted10 : StepValid centerStep10.shape centerBoxes10 centerStep10.proposed := by
  dsimp only [StepValid,centerStep10]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep11 : Instruction 40 := ⟨.neg 4,⟨⟨-682864148480,-679611465728⟩,⟨0,0⟩,⟨-737162762159,-719718162248⟩,⟨0,0⟩,⟨0,0⟩,⟨1878601016273,2032428067180⟩⟩⟩
noncomputable def centerBoxes12 := centerStep11.proposed :: centerBoxes11
theorem centerAccepted11 : StepValid centerStep11.shape centerBoxes11 centerStep11.proposed := by
  dsimp only [StepValid,centerStep11]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep12 : Instruction 40 := ⟨.add 10 0,⟨⟨416647479296,419900162048⟩,⟨0,0⟩,⟨-737162762159,-719718162248⟩,⟨0,0⟩,⟨0,0⟩,⟨1878601016273,2032428067180⟩⟩⟩
noncomputable def centerBoxes13 := centerStep12.proposed :: centerBoxes12
theorem centerAccepted12 : StepValid centerStep12.shape centerBoxes12 centerStep12.proposed := by
  dsimp only [StepValid,centerStep12]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep13 : Instruction 40 := ⟨.log 0,⟨⟨-1066945095104,-1058394742592⟩,⟨0,0⟩,⟨-1945335250623,-1884587241532⟩,⟨0,0⟩,⟨0,0⟩,⟨1477303030922,2133250685838⟩⟩⟩
noncomputable def centerBoxes14 := centerStep13.proposed :: centerBoxes13
theorem centerAccepted13 : StepValid centerStep13.shape centerBoxes13 centerStep13.proposed := by
  dsimp only [StepValid,centerStep13]
  exact ⟨by decide,by decide,lc10,by decide⟩
noncomputable def centerStep14 : Instruction 40 := ⟨.mul 1 0,⟨⟨-407463101811,-401066701307⟩,⟨0,0⟩,⟨-50113765523,1185680668⟩,⟨0,0⟩,⟨0,0⟩,⟨1054803541320,1614815376317⟩⟩⟩
noncomputable def centerBoxes15 := centerStep14.proposed :: centerBoxes14
theorem centerAccepted14 : StepValid centerStep14.shape centerBoxes14 centerStep14.proposed := by
  dsimp only [StepValid,centerStep14]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep15 : Instruction 40 := ⟨.add 4 0,⟨⟨448747879300,459965302483⟩,⟨0,0⟩,⟨1014658571648,1095805539705⟩,⟨0,0⟩,⟨0,0⟩,⟨-1687922444855,-843659496543⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15
theorem centerAccepted15 : StepValid centerStep15.shape centerBoxes15 centerStep15.proposed := by
  dsimp only [StepValid,centerStep15]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep16 : Instruction 40 := ⟨.mul 0 15,⟨⟨224373939650,229982651242⟩,⟨0,0⟩,⟨507329285824,547902769853⟩,⟨0,0⟩,⟨0,0⟩,⟨-843961222428,-421829748271⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16
theorem centerAccepted16 : StepValid centerStep16.shape centerBoxes16 centerStep16.proposed := by
  dsimp only [StepValid,centerStep16]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨-229982651242,-224373939650⟩,⟨0,0⟩,⟨-547902769853,-507329285824⟩,⟨0,0⟩,⟨0,0⟩,⟨421829748271,843961222428⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17
theorem centerAccepted17 : StepValid centerStep17.shape centerBoxes17 centerStep17.proposed := by
  dsimp only [StepValid,centerStep17]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep18 : Instruction 40 := ⟨.add 10 0,⟨⟨532140732374,537749463230⟩,⟨0,0⟩,⟨-547902769853,-507329285824⟩,⟨0,0⟩,⟨0,0⟩,⟨421829748271,843961222428⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18
theorem centerAccepted18 : StepValid centerStep18.shape centerBoxes18 centerStep18.proposed := by
  dsimp only [StepValid,centerStep18]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep19 : Instruction 40 := ⟨.mul 12 12,⟨⟨420069904384,424100512900⟩,⟨0,0⟩,⟨889719949838,915646563724⟩,⟨0,0⟩,⟨0,0⟩,⟨-1582298915987,-1333882850800⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19
theorem centerAccepted19 : StepValid centerStep19.shape centerBoxes19 centerStep19.proposed := by
  dsimp only [StepValid,centerStep19]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep20 : Instruction 40 := ⟨.neg 0,⟨⟨-424100512900,-420069904384⟩,⟨0,0⟩,⟨-915646563724,-889719949838⟩,⟨0,0⟩,⟨0,0⟩,⟨1333882850800,1582298915987⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20
theorem centerAccepted20 : StepValid centerStep20.shape centerBoxes20 centerStep20.proposed := by
  dsimp only [StepValid,centerStep20]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep21 : Instruction 40 := ⟨.add 19 0,⟨⟨675411114876,679441723392⟩,⟨0,0⟩,⟨-915646563724,-889719949838⟩,⟨0,0⟩,⟨0,0⟩,⟨1333882850800,1582298915987⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21
theorem centerAccepted21 : StepValid centerStep21.shape centerBoxes21 centerStep21.proposed := by
  dsimp only [StepValid,centerStep21]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep22 : Instruction 40 := ⟨.log 0,⟨⟨-535791819392,-529249833472⟩,⟨0,0⟩,⟨-1490594426971,-1439795933383⟩,⟨0,0⟩,⟨0,0⟩,⟨137785274207,690453806393⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22
theorem centerAccepted22 : StepValid centerStep22.shape centerBoxes22 centerStep22.proposed := by
  dsimp only [StepValid,centerStep22]
  exact ⟨by decide,by decide,lc7,by decide⟩
noncomputable def centerStep23 : Instruction 40 := ⟨.mul 0 22,⟨⟨-267895909696,-264624916736⟩,⟨0,0⟩,⟨-745297213486,-719897966691⟩,⟨0,0⟩,⟨0,0⟩,⟨68892637103,345226903197⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23
theorem centerAccepted23 : StepValid centerStep23.shape centerBoxes23 centerStep23.proposed := by
  dsimp only [StepValid,centerStep23]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep24 : Instruction 40 := ⟨.neg 0,⟨⟨264624916736,267895909696⟩,⟨0,0⟩,⟨719897966691,745297213486⟩,⟨0,0⟩,⟨0,0⟩,⟨-345226903197,-68892637103⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24
theorem centerAccepted24 : StepValid centerStep24.shape centerBoxes24 centerStep24.proposed := by
  dsimp only [StepValid,centerStep24]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep25 : Instruction 40 := ⟨.add 17 0,⟨⟨1026748300352,1030019312576⟩,⟨0,0⟩,⟨719897966691,745297213486⟩,⟨0,0⟩,⟨0,0⟩,⟨-345226903197,-68892637103⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25
theorem centerAccepted25 : StepValid centerStep25.shape centerBoxes25 centerStep25.proposed := by
  dsimp only [StepValid,centerStep25]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep26 : Instruction 40 := ⟨.add 24 26,⟨⟨2168236929974,2170435953230⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26
theorem centerAccepted26 : StepValid centerStep26.shape centerBoxes26 centerStep26.proposed := by
  dsimp only [StepValid,centerStep26]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep27 : Instruction 40 := ⟨.neg 27,⟨⟨-1070924325454,-1068725302198⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27
theorem centerAccepted27 : StepValid centerStep27.shape centerBoxes27 centerStep27.proposed := by
  dsimp only [StepValid,centerStep27]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep28 : Instruction 40 := ⟨.add 26 0,⟨⟨28587302322,30786325578⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28
theorem centerAccepted28 : StepValid centerStep28.shape centerBoxes28 centerStep28.proposed := by
  dsimp only [StepValid,centerStep28]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep29 : Instruction 40 := ⟨.inv 0,⟨⟨39268272420224,42288908760876⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29
theorem centerAccepted29 : StepValid centerStep29.shape centerBoxes29 centerStep29.proposed := by
  dsimp only [StepValid,centerStep29]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep30 : Instruction 40 := ⟨.mul 3 0,⟨⟨77437033212672,83478305893976⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30
theorem centerAccepted30 : StepValid centerStep30.shape centerBoxes30 centerStep30.proposed := by
  dsimp only [StepValid,centerStep30]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨4677981092416,4760578343424⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31
theorem centerAccepted31 : StepValid centerStep31.shape centerBoxes31 centerStep31.proposed := by
  dsimp only [StepValid,centerStep31]
  exact ⟨by decide,by decide,lc12,by decide⟩
noncomputable def centerStep32 : Instruction 40 := ⟨.mul 0 31,⟨⟨2338990546208,2380289171712⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32
theorem centerAccepted32 : StepValid centerStep32.shape centerBoxes32 centerStep32.proposed := by
  dsimp only [StepValid,centerStep32]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep33 : Instruction 40 := ⟨.inv 20,⟨⟨2879079192821,2901555582810⟩,⟨0,0⟩,⟨4934805396399,5133641349750⟩,⟨0,0⟩,⟨0,0⟩,⟨2762792131352,5284838078859⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33
theorem centerAccepted33 : StepValid centerStep33.shape centerBoxes33 centerStep33.proposed := by
  dsimp only [StepValid,centerStep33]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep34 : Instruction 40 := ⟨.mul 25 0,⟨⟨4658646757866,4703599537844⟩,⟨0,0⟩,⟨9869610792797,10267282699500⟩,⟨0,0⟩,⟨0,0⟩,⟨5567455828302,10531570979094⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34
theorem centerAccepted34 : StepValid centerStep34.shape centerBoxes34 centerStep34.proposed := by
  dsimp only [StepValid,centerStep34]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨1587539651648,1598098370816⟩,⟨0,0⟩,⟨2307116441565,2423235179776⟩,⟨0,0⟩,⟨0,0⟩,⟨-4039169060739,-2355434674442⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35
theorem centerAccepted35 : StepValid centerStep35.shape centerBoxes35 centerStep35.proposed := by
  dsimp only [StepValid,centerStep35]
  exact ⟨by decide,by decide,lc13,by decide⟩
noncomputable def centerStep36 : Instruction 40 := ⟨.mul 0 35,⟨⟨793769825824,799049185408⟩,⟨0,0⟩,⟨1153558220782,1211617589888⟩,⟨0,0⟩,⟨0,0⟩,⟨-2019584530370,-1177717337221⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36
theorem centerAccepted36 : StepValid centerStep36.shape centerBoxes36 centerStep36.proposed := by
  dsimp only [StepValid,centerStep36]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep37 : Instruction 40 := ⟨.mul 40 11,⟨⟨2053496600704,2060038625152⟩,⟨0,0⟩,⟨1439795933382,1490594426972⟩,⟨0,0⟩,⟨0,0⟩,⟨-690453806394,-137785274206⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37
theorem centerAccepted37 : StepValid centerStep37.shape centerBoxes37 centerStep37.proposed := by
  dsimp only [StepValid,centerStep37]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep38 : Instruction 40 := ⟨.add 0 17,⟨⟨1629396087804,1639968720768⟩,⟨0,0⟩,⟨524149369658,600874477134⟩,⟨0,0⟩,⟨0,0⟩,⟨643429044406,1444513641781⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38
theorem centerAccepted38 : StepValid centerStep38.shape centerBoxes38 centerStep38.proposed := by
  dsimp only [StepValid,centerStep38]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep39 : Instruction 40 := ⟨.mul 20 0,⟨⟨788593777080,802076373755⟩,⟨0,0⟩,⟨-563543085390,-457949159683⟩,⟨0,0⟩,⟨0,0⟩,⟨337678069410,1481588507043⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39
theorem centerAccepted39 : StepValid centerStep39.shape centerBoxes39 centerStep39.proposed := by
  dsimp only [StepValid,centerStep39]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep40 : Instruction 40 := ⟨.mul 43 41,⟨⟨837093905798,843065112446⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40
theorem centerAccepted40 : StepValid centerStep40.shape centerBoxes40 centerStep40.proposed := by
  dsimp only [StepValid,centerStep40]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep41 : Instruction 40 := ⟨.mul 19 19,⟨⟨414893451396,419860094086⟩,⟨0,0⟩,⟨-1131645111446,-1093079378274⟩,⟨0,0⟩,⟨0,0⟩,⟨3078677568759,3480615363623⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41
theorem centerAccepted41 : StepValid centerStep41.shape centerBoxes41 centerStep41.proposed := by
  dsimp only [StepValid,centerStep41]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep42 : Instruction 40 := ⟨.mul 1 0,⟨⟨315871857054,321933291555⟩,⟨0,0⟩,⟨-867703886916,-832196825382⟩,⟨0,0⟩,⟨0,0⟩,⟨2343897204559,2668807958721⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42
theorem centerAccepted42 : StepValid centerStep42.shape centerBoxes42 centerStep42.proposed := by
  dsimp only [StepValid,centerStep42]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep43 : Instruction 40 := ⟨.mul 17 17,⟨⟨958800294279,964919112703⟩,⟨0,0⟩,⟨1344513318556,1396384547662⟩,⟨0,0⟩,⟨0,0⟩,⟨295881736621,881723350864⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43
theorem centerAccepted43 : StepValid centerStep43.shape centerBoxes43 centerStep43.proposed := by
  dsimp only [StepValid,centerStep43]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep44 : Instruction 40 := ⟨.mul 18 0,⟨⟨895348941892,903933433763⟩,⟨0,0⟩,⟨1883304455024,1962193507836⟩,⟨0,0⟩,⟨0,0⟩,⟨1733956052249,2658981269330⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44
theorem centerAccepted44 : StepValid centerStep44.shape centerBoxes44 centerStep44.proposed := by
  dsimp only [StepValid,centerStep44]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep45 : Instruction 40 := ⟨.mul 2 0,⟨⟨257219228830,264668656817⟩,⟨0,0⟩,⟨-172316211669,-103146824044⟩,⟨0,0⟩,⟨0,0⟩,⟨-690208314139,121762565872⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45
theorem centerAccepted45 : StepValid centerStep45.shape centerBoxes45 centerStep45.proposed := by
  dsimp only [StepValid,centerStep45]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep46 : Instruction 40 := ⟨.inv 0,⟨⟨4567695450430,4699982287925⟩,⟨0,0⟩,⟨1780124947842,3148610414745⟩,⟨0,0⟩,⟨0,0⟩,⟨-837377266207,16830312836659⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46
theorem centerAccepted46 : StepValid centerStep46.shape centerBoxes46 centerStep46.proposed := by
  dsimp only [StepValid,centerStep46]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep47 : Instruction 40 := ⟨.mul 7 0,⟨⟨3276051036487,3428562877354⟩,⟨0,0⟩,⟨-1132181808792,394405770399⟩,⟨0,0⟩,⟨0,0⟩,⟨-2435613346665,17127806661207⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47
theorem centerAccepted47 : StepValid centerStep47.shape centerBoxes47 centerStep47.proposed := by
  dsimp only [StepValid,centerStep47]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep48 : Instruction 40 := ⟨.neg 11,⟨⟨-799049185408,-793769825824⟩,⟨0,0⟩,⟨-1211617589888,-1153558220782⟩,⟨0,0⟩,⟨0,0⟩,⟨1177717337221,2019584530370⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48
theorem centerAccepted48 : StepValid centerStep48.shape centerBoxes48 centerStep48.proposed := by
  dsimp only [StepValid,centerStep48]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep49 : Instruction 40 := ⟨.mul 0 10,⟨⟨-1191816109372,-1176309023152⟩,⟨0,0⟩,⟨-2243853678407,-2087888065811⟩,⟨0,0⟩,⟨0,0⟩,⟨-628760607098,1447958556740⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49
theorem centerAccepted49 : StepValid centerStep49.shape centerBoxes49 centerStep49.proposed := by
  dsimp only [StepValid,centerStep49]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep50 : Instruction 40 := ⟨.mul 53 43,⟨⟨1359222931456,1365728296960⟩,⟨0,0⟩,⟨1439436324496,1474325524318⟩,⟨0,0⟩,⟨0,0⟩,⟨-4064856134360,-3757202032546⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50
theorem centerAccepted50 : StepValid centerStep50.shape centerBoxes50 centerStep50.proposed := by
  dsimp only [StepValid,centerStep50]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep51 : Instruction 40 := ⟨.inv 29,⟨⟨1779292878246,1789911052673⟩,⟨0,0⟩,⟨2329960489438,2426560458741⟩,⟨0,0⟩,⟨0,0⟩,⟨1908845023282,3086201231843⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51
theorem centerAccepted51 : StepValid centerStep51.shape centerBoxes51 centerStep51.proposed := by
  dsimp only [StepValid,centerStep51]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep52 : Instruction 40 := ⟨.mul 1 0,⟨⟨2199572629150,2223289060273⟩,⟨0,0⟩,⟨5209689813904,5414161782031⟩,⟨0,0⟩,⟨0,0⟩,⟨1843067850220,4260827677215⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52
theorem centerAccepted52 : StepValid centerStep52.shape centerBoxes52 centerStep52.proposed := by
  dsimp only [StepValid,centerStep52]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep53 : Instruction 40 := ⟨.neg 2,⟨⟨-1365728296960,-1359222931456⟩,⟨0,0⟩,⟨-1474325524318,-1439436324496⟩,⟨0,0⟩,⟨0,0⟩,⟨3757202032546,4064856134360⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53
theorem centerAccepted53 : StepValid centerStep53.shape centerBoxes53 centerStep53.proposed := by
  dsimp only [StepValid,centerStep53]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep54 : Instruction 40 := ⟨.add 1 0,⟨⟨833844332190,864066128817⟩,⟨0,0⟩,⟨3735364289586,3974725457535⟩,⟨0,0⟩,⟨0,0⟩,⟨5600269882766,8325683811575⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54
theorem centerAccepted54 : StepValid centerStep54.shape centerBoxes54 centerStep54.proposed := by
  dsimp only [StepValid,centerStep54]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep55 : Instruction 40 := ⟨.mul 36 0,⟨⟨403563293382,422597710865⟩,⟨0,0⟩,⟨1377261708902,1559213007330⟩,⟨0,0⟩,⟨0,0⟩,⟨-931007992701,1288072701189⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55
theorem centerAccepted55 : StepValid centerStep55.shape centerBoxes55 centerStep55.proposed := by
  dsimp only [StepValid,centerStep55]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep56 : Instruction 40 := ⟨.add 6 0,⟨⟨-788252815990,-753711312287⟩,⟨0,0⟩,⟨-866591969505,-528675058481⟩,⟨0,0⟩,⟨0,0⟩,⟨-1559768599799,2736031257929⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56
theorem centerAccepted56 : StepValid centerStep56.shape centerBoxes56 centerStep56.proposed := by
  dsimp only [StepValid,centerStep56]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep57 : Instruction 40 := ⟨.mul 0 10,⟨⟨-3369472573068,-3131138993986⟩,⟨0,0⟩,⟨-5961617656259,-3416541376147⟩,⟨0,0⟩,⟨0,0⟩,⟨-23696472709019,10583924556889⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57
theorem centerAccepted57 : StepValid centerStep57.shape centerBoxes57 centerStep57.proposed := by
  dsimp only [StepValid,centerStep57]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep58 : Instruction 40 := ⟨.mul 54 51,⟨⟨2718445862912,2731456593920⟩,⟨0,0⟩,⟨2878872648992,2948651048636⟩,⟨0,0⟩,⟨0,0⟩,⟨-8129712268720,-7514404065092⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58
theorem centerAccepted58 : StepValid centerStep58.shape centerBoxes58 centerStep58.proposed := by
  dsimp only [StepValid,centerStep58]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep59 : Instruction 40 := ⟨.mul 0 7,⟨⟨4399145258300,4446578120546⟩,⟨0,0⟩,⟨10419379627809,10828323564060⟩,⟨0,0⟩,⟨0,0⟩,⟨3686135700442,8521655354428⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59
theorem centerAccepted59 : StepValid centerStep59.shape centerBoxes59 centerStep59.proposed := by
  dsimp only [StepValid,centerStep59]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep60 : Instruction 40 := ⟨.mul 57 53,⟨⟨2038834397184,2048592445440⟩,⟨0,0⟩,⟨2159154486744,2211488286477⟩,⟨0,0⟩,⟨0,0⟩,⟨-6097284201540,-5635803048819⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60
theorem centerAccepted60 : StepValid centerStep60.shape centerBoxes60 centerStep60.proposed := by
  dsimp only [StepValid,centerStep60]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep61 : Instruction 40 := ⟨.mul 39 35,⟨⟨630713852149,636499041197⟩,⟨0,0⟩,⟨-415554091752,-370284781742⟩,⟨0,0⟩,⟨0,0⟩,⟨-209053975693,274896977569⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61
theorem centerAccepted61 : StepValid centerStep61.shape centerBoxes61 centerStep61.proposed := by
  dsimp only [StepValid,centerStep61]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep62 : Instruction 40 := ⟨.inv 0,⟨⟨1899336434727,1916757996508⟩,⟨0,0⟩,⟨1104943341099,1262881139576⟩,⟨0,0⟩,⟨0,0⟩,⟨450186640536,2299452793949⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62
theorem centerAccepted62 : StepValid centerStep62.shape centerBoxes62 centerStep62.proposed := by
  dsimp only [StepValid,centerStep62]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep63 : Instruction 40 := ⟨.mul 2 0,⟨⟨3521956800747,3571272783468⟩,⟨0,0⟩,⟨5778708578553,6208225949480⟩,⟨0,0⟩,⟨0,0⟩,⟨-5454854087787,-371029047952⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63
theorem centerAccepted63 : StepValid centerStep63.shape centerBoxes63 centerStep63.proposed := by
  dsimp only [StepValid,centerStep63]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep64 : Instruction 40 := ⟨.neg 0,⟨⟨-3571272783468,-3521956800747⟩,⟨0,0⟩,⟨-6208225949480,-5778708578553⟩,⟨0,0⟩,⟨0,0⟩,⟨371029047952,5454854087787⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64
theorem centerAccepted64 : StepValid centerStep64.shape centerBoxes64 centerStep64.proposed := by
  dsimp only [StepValid,centerStep64]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep65 : Instruction 40 := ⟨.add 5 0,⟨⟨827872474832,924621319799⟩,⟨0,0⟩,⟨4211153678329,5049614985507⟩,⟨0,0⟩,⟨0,0⟩,⟨4057164748394,13976509442215⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65
theorem centerAccepted65 : StepValid centerStep65.shape centerBoxes65 centerStep65.proposed := by
  dsimp only [StepValid,centerStep65]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep66 : Instruction 40 := ⟨.mul 18 0,⟨⟨2466688310280,2883209465539⟩,⟨0,0⟩,⟨11595252485128,16077682146900⟩,⟨0,0⟩,⟨0,0⟩,⟨-358982746484,61608508263879⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66
theorem centerAccepted66 : StepValid centerStep66.shape centerBoxes66 centerStep66.proposed := by
  dsimp only [StepValid,centerStep66]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep67 : Instruction 40 := ⟨.add 9 0,⟨⟨-902784262788,-247929528447⟩,⟨0,0⟩,⟨5633634828869,12661140770753⟩,⟨0,0⟩,⟨0,0⟩,⟨-24055455455503,72192432820768⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67
theorem centerAccepted67 : StepValid centerStep67.shape centerBoxes67 centerStep67.proposed := by
  dsimp only [StepValid,centerStep67]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep68 : Instruction 40 := ⟨.mul 61 29,⟨⟨1007134654613,1018521146799⟩,⟨0,0⟩,⟨1390548167602,1472689755454⟩,⟨0,0⟩,⟨0,0⟩,⟨-1947552900019,-1081110885885⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68
theorem centerAccepted68 : StepValid centerStep68.shape centerBoxes68 centerStep68.proposed := by
  dsimp only [StepValid,centerStep68]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep69 : Instruction 40 := ⟨.mul 27 25,⟨⟨361796958980,368464524804⟩,⟨0,0⟩,⟨-485775877359,-419967074773⟩,⟨0,0⟩,⟨0,0⟩,⟨-78059329366,717948908209⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69
theorem centerAccepted69 : StepValid centerStep69.shape centerBoxes69 centerStep69.proposed := by
  dsimp only [StepValid,centerStep69]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨3280982939287,3341448261542⟩,⟨0,0⟩,⟨3739586078538,4486480387998⟩,⟨0,0⟩,⟨0,0⟩,⟨1893821086008,12768706284595⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70
theorem centerAccepted70 : StepValid centerStep70.shape centerBoxes70 centerStep70.proposed := by
  dsimp only [StepValid,centerStep70]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep71 : Instruction 40 := ⟨.mul 2 0,⟨⟨3005326670381,3095315801434⟩,⟨0,0⟩,⟨7574846265708,8631551984789⟩,⟨0,0⟩,⟨0,0⟩,⟨5274918959481,20620498987192⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71
theorem centerAccepted71 : StepValid centerStep71.shape centerBoxes71 centerStep71.proposed := by
  dsimp only [StepValid,centerStep71]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep72 : Instruction 40 := ⟨.mul 65 39,⟨⟨1445737137539,1478305547041⟩,⟨0,0⟩,⟨1531056093365,1595854465047⟩,⟨0,0⟩,⟨0,0⟩,⟨-4399923018893,-3996347020037⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72
theorem centerAccepted72 : StepValid centerStep72.shape centerBoxes72 centerStep72.proposed := by
  dsimp only [StepValid,centerStep72]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep73 : Instruction 40 := ⟨.add 54 0,⟨⟨1977877869913,2016055010271⟩,⟨0,0⟩,⟨983153323512,1088525179223⟩,⟨0,0⟩,⟨0,0⟩,⟨-3978093270622,-3152385797609⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73
theorem centerAccepted73 : StepValid centerStep73.shape centerBoxes73 centerStep73.proposed := by
  dsimp only [StepValid,centerStep73]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep74 : Instruction 40 := ⟨.mul 0 0,⟨⟨3557944063042,3696621028611⟩,⟨0,0⟩,⟨3537128943764,3991820706468⟩,⟨0,0⟩,⟨0,0⟩,⟨-12830177023772,-9186163953410⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74
theorem centerAccepted74 : StepValid centerStep74.shape centerBoxes74 centerStep74.proposed := by
  dsimp only [StepValid,centerStep74]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep75 : Instruction 40 := ⟨.mul 7 0,⟨⟨-3035212366851,-802282914983⟩,⟨0,0⟩,⟨14952460950598,41769890693364⟩,⟨0,0⟩,⟨0,0⟩,⟨-42557617752067,345183211693513⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75
theorem centerAccepted75 : StepValid centerStep75.shape centerBoxes75 centerStep75.proposed := by
  dsimp only [StepValid,centerStep75]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep76 : Instruction 40 := ⟨.mul 79 28,⟨⟨6552102072974,6857125754708⟩,⟨0,0⟩,⟨-2264363617584,788811540798⟩,⟨0,0⟩,⟨0,0⟩,⟨-4871226693330,34255613322414⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76
theorem centerAccepted76 : StepValid centerStep76.shape centerBoxes76 centerStep76.proposed := by
  dsimp only [StepValid,centerStep76]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep77 : Instruction 40 := ⟨.mul 0 3,⟨⟨11786376209371,12573166471919⟩,⟨0,0⟩,⟨1706793512065,8234966571840⟩,⟨0,0⟩,⟨0,0⟩,⟨-38224771221559,45587266683354⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77
theorem centerAccepted77 : StepValid centerStep77.shape centerBoxes77 centerStep77.proposed := by
  dsimp only [StepValid,centerStep77]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep78 : Instruction 40 := ⟨.add 45 29,⟨⟨1539941360800,1586519345888⟩,⟨0,0⟩,⟨-1211617589888,-1153558220782⟩,⟨0,0⟩,⟨0,0⟩,⟨1177717337221,2019584530370⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78
theorem centerAccepted78 : StepValid centerStep78.shape centerBoxes78 centerStep78.proposed := by
  dsimp only [StepValid,centerStep78]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep79 : Instruction 40 := ⟨.mul 1 0,⟨⟨16507627350401,18142210907873⟩,⟨0,0⟩,⟨-11464642497589,-483248541590⟩,⟨0,0⟩,⟨0,0⟩,⟨-60680195139434,85292305493306⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79
theorem centerAccepted79 : StepValid centerStep79.shape centerBoxes79 centerStep79.proposed := by
  dsimp only [StepValid,centerStep79]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep80 : Instruction 40 := ⟨.add 4 0,⟨⟨13472414983550,17339927992890⟩,⟨0,0⟩,⟨3487818453009,41286642151774⟩,⟨0,0⟩,⟨0,0⟩,⟨-103237812891501,430475517186819⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80
theorem centerAccepted80 : StepValid centerStep80.shape centerBoxes80 centerStep80.proposed := by
  dsimp only [StepValid,centerStep80]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep81 : Instruction 40 := ⟨.mul 81 81,⟨⟨1038800993736,1043080292993⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81
theorem centerAccepted81 : StepValid centerStep81.shape centerBoxes81 centerStep81.proposed := by
  dsimp only [StepValid,centerStep81]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep82 : Instruction 40 := ⟨.neg 0,⟨⟨-1043080292993,-1038800993736⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82
theorem centerAccepted82 : StepValid centerStep82.shape centerBoxes82 centerStep82.proposed := by
  dsimp only [StepValid,centerStep82]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep83 : Instruction 40 := ⟨.add 81 0,⟨⟨56431334783,60710634040⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83
theorem centerAccepted83 : StepValid centerStep83.shape centerBoxes83 centerStep83.proposed := by
  dsimp only [StepValid,centerStep83]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep84 : Instruction 40 := ⟨.inv 0,⟨⟨19912917048735,21422952766640⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes85 := centerStep84.proposed :: centerBoxes84
theorem centerAccepted84 : StepValid centerStep84.shape centerBoxes84 centerStep84.proposed := by
  dsimp only [StepValid,centerStep84]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep85 : Instruction 40 := ⟨.mul 13 0,⟨⟨54428547347604,60309325101076⟩,⟨0,0⟩,⟨137185711851965,168177694352319⟩,⟨0,0⟩,⟨0,0⟩,⟨95532435515401,401771081512527⟩⟩⟩
noncomputable def centerBoxes86 := centerStep85.proposed :: centerBoxes85
theorem centerAccepted85 : StepValid centerStep85.shape centerBoxes85 centerStep85.proposed := by
  dsimp only [StepValid,centerStep85]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep86 : Instruction 40 := ⟨.add 5 0,⟨⟨67900962331154,77649253093966⟩,⟨0,0⟩,⟨140673530304974,209464336504093⟩,⟨0,0⟩,⟨0,0⟩,⟨-7705377376100,832246598699346⟩⟩⟩
noncomputable def centerBoxes87 := centerStep86.proposed :: centerBoxes86
theorem centerAccepted86 : StepValid centerStep86.shape centerBoxes86 centerStep86.proposed := by
  dsimp only [StepValid,centerStep86]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep87 : Instruction 40 := ⟨.mul 0 68,⟨⟨32862651845607,37976719042027⟩,⟨0,0⟩,⟨29389297737837,71114471024592⟩,⟨0,0⟩,⟨0,0⟩,⟨-186476515420964,336820009542359⟩⟩⟩
noncomputable def centerBoxes88 := centerStep87.proposed :: centerBoxes87
theorem centerAccepted87 : StepValid centerStep87.shape centerBoxes87 centerStep87.proposed := by
  dsimp only [StepValid,centerStep87]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep88 : Instruction 40 := ⟨.mul 0 69,⟨⟨15904839184143,18573664674556⟩,⟨0,0⟩,⟨-4700547952676,19617421394510⟩,⟨0,0⟩,⟨0,0⟩,⟨-149468936087111,166760905539042⟩⟩⟩
noncomputable def centerBoxes89 := centerStep88.proposed :: centerBoxes88
theorem centerAccepted88 : StepValid centerStep88.shape centerBoxes88 centerStep88.proposed := by
  dsimp only [StepValid,centerStep88]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep89 : Instruction 40 := ⟨.mul 90 63,⟨⟨390848410922,394890479392⟩,⟨0,0⟩,⟨274040849359,285733257940⟩,⟨0,0⟩,⟨0,0⟩,⟨-132353651663,-26225100861⟩⟩⟩
noncomputable def centerBoxes90 := centerStep89.proposed :: centerBoxes89
theorem centerAccepted89 : StepValid centerStep89.shape centerBoxes89 centerStep89.proposed := by
  dsimp only [StepValid,centerStep89]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep90 : Instruction 40 := ⟨.inv 0,⟨⟨3061420527220,3093081066296⟩,⟨0,0⟩,⟨-2261224826425,-2124523951086⟩,⟨0,0⟩,⟨0,0⟩,⟨3152010046174,4353592849920⟩⟩⟩
noncomputable def centerBoxes91 := centerStep90.proposed :: centerBoxes90
theorem centerAccepted90 : StepValid centerStep90.shape centerBoxes90 centerStep90.proposed := by
  dsimp only [StepValid,centerStep90]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep91 : Instruction 40 := ⟨.mul 2 0,⟨⟨44284571377346,52250334680685⟩,⟨0,0⟩,⟨-51421382116531,24454550748512⟩,⟨0,0⟩,⟨0,0⟩,⟨-455571465767811,561999663388570⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91
theorem centerAccepted91 : StepValid centerStep91.shape centerBoxes91 centerStep91.proposed := by
  dsimp only [StepValid,centerStep91]
  exact ⟨by decide,by decide⟩
noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91]
theorem centerAccepted : Accepted centerProgram centerInitial :=
  ⟨centerAccepted0,⟨centerAccepted1,⟨centerAccepted2,⟨centerAccepted3,⟨centerAccepted4,⟨centerAccepted5,⟨centerAccepted6,⟨centerAccepted7,⟨centerAccepted8,⟨centerAccepted9,⟨centerAccepted10,⟨centerAccepted11,⟨centerAccepted12,⟨centerAccepted13,⟨centerAccepted14,⟨centerAccepted15,⟨centerAccepted16,⟨centerAccepted17,⟨centerAccepted18,⟨centerAccepted19,⟨centerAccepted20,⟨centerAccepted21,⟨centerAccepted22,⟨centerAccepted23,⟨centerAccepted24,⟨centerAccepted25,⟨centerAccepted26,⟨centerAccepted27,⟨centerAccepted28,⟨centerAccepted29,⟨centerAccepted30,⟨centerAccepted31,⟨centerAccepted32,⟨centerAccepted33,⟨centerAccepted34,⟨centerAccepted35,⟨centerAccepted36,⟨centerAccepted37,⟨centerAccepted38,⟨centerAccepted39,⟨centerAccepted40,⟨centerAccepted41,⟨centerAccepted42,⟨centerAccepted43,⟨centerAccepted44,⟨centerAccepted45,⟨centerAccepted46,⟨centerAccepted47,⟨centerAccepted48,⟨centerAccepted49,⟨centerAccepted50,⟨centerAccepted51,⟨centerAccepted52,⟨centerAccepted53,⟨centerAccepted54,⟨centerAccepted55,⟨centerAccepted56,⟨centerAccepted57,⟨centerAccepted58,⟨centerAccepted59,⟨centerAccepted60,⟨centerAccepted61,⟨centerAccepted62,⟨centerAccepted63,⟨centerAccepted64,⟨centerAccepted65,⟨centerAccepted66,⟨centerAccepted67,⟨centerAccepted68,⟨centerAccepted69,⟨centerAccepted70,⟨centerAccepted71,⟨centerAccepted72,⟨centerAccepted73,⟨centerAccepted74,⟨centerAccepted75,⟨centerAccepted76,⟨centerAccepted77,⟨centerAccepted78,⟨centerAccepted79,⟨centerAccepted80,⟨centerAccepted81,⟨centerAccepted82,⟨centerAccepted83,⟨centerAccepted84,⟨centerAccepted85,⟨centerAccepted86,⟨centerAccepted87,⟨centerAccepted88,⟨centerAccepted89,⟨centerAccepted90,⟨centerAccepted91,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
noncomputable def center_output : DyadicBivariateJetEnclosure 40 := ⟨⟨44284571377346,52250334680685⟩,⟨0,0⟩,⟨-51421382116531,24454550748512⟩,⟨0,0⟩,⟨0,0⟩,⟨-455571465767811,561999663388570⟩⟩
theorem center_output_eq : (finalBoxes centerProgram centerInitial).getD 0 (zeroBox 40)=center_output := rfl
noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨1068725302198,1070924325454⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨418546952899,421532556223⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨507589542962,562235270864⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
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
noncomputable def wholeStep4 : Instruction 40 := ⟨.inv 6,⟨⟨2150213411116,2381699616112⟩,⟨0,0⟩,⟨-5159102385177,-4204973914368⟩,⟨0,0⟩,⟨0,0⟩,⟨16446558773290,22350708914490⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4
theorem wholeAccepted4 : StepValid wholeStep4.shape wholeBoxes4 wholeStep4.proposed := by
  dsimp only [StepValid,wholeStep4]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep5 : Instruction 40 := ⟨.mul 6 0,⟨⟨818513646031,913099872683⟩,⟨0,0⟩,⟨-1977905063759,-1600691592901⟩,⟨0,0⟩,⟨0,0⟩,⟨6260649625105,8568851137281⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5
theorem wholeAccepted5 : StepValid wholeStep5.shape wholeBoxes5 wholeStep5.proposed := by
  dsimp only [StepValid,wholeStep5]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep6 : Instruction 40 := ⟨.contact 0,⟨⟨661238317056,699991588864⟩,⟨0,0⟩,⟨607476475614,873651424882⟩,⟨0,0⟩,⟨0,0⟩,⟨-3199168073750,-701794533370⟩⟩⟩
noncomputable def wholeBoxes7 := wholeStep6.proposed :: wholeBoxes6
theorem wholeAccepted6 : StepValid wholeStep6.shape wholeBoxes6 wholeStep6.proposed := by
  dsimp only [StepValid,wholeStep6]
  exact ⟨by decide,by decide,(⟨⟨661238317056,699991588864⟩,⟨-485660266451,-417274290376⟩,⟨276368962596,517356717980⟩⟩ : DyadicJetEnclosure 40),brwhole6_jet,by decide⟩
noncomputable def wholeStep7 : Instruction 40 := ⟨.log 10,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes8 := wholeStep7.proposed :: wholeBoxes7
theorem wholeAccepted7 : StepValid wholeStep7.shape wholeBoxes7 wholeStep7.proposed := by
  dsimp only [StepValid,wholeStep7]
  exact ⟨by decide,by decide,lc0,by decide⟩
noncomputable def wholeStep8 : Instruction 40 := ⟨.add 6 1,⟨⟨1760749944832,1799503216640⟩,⟨0,0⟩,⟨607476475614,873651424882⟩,⟨0,0⟩,⟨0,0⟩,⟨-3199168073750,-701794533370⟩⟩⟩
noncomputable def wholeBoxes9 := wholeStep8.proposed :: wholeBoxes8
theorem wholeAccepted8 : StepValid wholeStep8.shape wholeBoxes8 wholeStep8.proposed := by
  dsimp only [StepValid,wholeStep8]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep9 : Instruction 40 := ⟨.log 0,⟨⟨517731126848,541668388736⟩,⟨0,0⟩,⟨371173245127,545557251387⟩,⟨0,0⟩,⟨0,0⟩,⟨-2268436456895,-554103074292⟩⟩⟩
noncomputable def wholeBoxes10 := wholeStep9.proposed :: wholeBoxes9
theorem wholeAccepted9 : StepValid wholeStep9.shape wholeBoxes9 wholeStep9.proposed := by
  dsimp only [StepValid,wholeStep9]
  exact ⟨by decide,by decide,lc23,by decide⟩
noncomputable def wholeStep10 : Instruction 40 := ⟨.mul 1 0,⟨⟨829090870898,886515415808⟩,⟨0,0⟩,⟨880438848192,1323279674003⟩,⟨0,0⟩,⟨0,0⟩,⟨-4878519473230,-350814018028⟩⟩⟩
noncomputable def wholeBoxes11 := wholeStep10.proposed :: wholeBoxes10
theorem wholeAccepted10 : StepValid wholeStep10.shape wholeBoxes10 wholeStep10.proposed := by
  dsimp only [StepValid,wholeStep10]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep11 : Instruction 40 := ⟨.neg 4,⟨⟨-699991588864,-661238317056⟩,⟨0,0⟩,⟨-873651424882,-607476475614⟩,⟨0,0⟩,⟨0,0⟩,⟨701794533370,3199168073750⟩⟩⟩
noncomputable def wholeBoxes12 := wholeStep11.proposed :: wholeBoxes11
theorem wholeAccepted11 : StepValid wholeStep11.shape wholeBoxes11 wholeStep11.proposed := by
  dsimp only [StepValid,wholeStep11]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep12 : Instruction 40 := ⟨.add 10 0,⟨⟨399520038912,438273310720⟩,⟨0,0⟩,⟨-873651424882,-607476475614⟩,⟨0,0⟩,⟨0,0⟩,⟨701794533370,3199168073750⟩⟩⟩
noncomputable def wholeBoxes13 := wholeStep12.proposed :: wholeBoxes12
theorem wholeAccepted12 : StepValid wholeStep12.shape wholeBoxes12 wholeStep12.proposed := by
  dsimp only [StepValid,wholeStep12]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep13 : Instruction 40 := ⟨.log 0,⟨⟨-1113098818560,-1011307344320⟩,⟨0,0⟩,⟨-2404359748505,-1523997542630⟩,⟨0,0⟩,⟨0,0⟩,⟨-3497123014058,6692006874714⟩⟩⟩
noncomputable def wholeBoxes14 := wholeStep13.proposed :: wholeBoxes13
theorem wholeAccepted13 : StepValid wholeStep13.shape wholeBoxes13 wholeStep13.proposed := by
  dsimp only [StepValid,wholeStep13]
  exact ⟨by decide,by decide,lc24,by decide⟩
noncomputable def wholeStep14 : Instruction 40 := ⟨.mul 1 0,⟨⟨-443689263529,-367470010637⟩,⟨0,0⟩,⟨-399651331327,330685735514⟩,⟨0,0⟩,⟨0,0⟩,⟨-2948673293350,5842905632529⟩⟩⟩
noncomputable def wholeBoxes15 := wholeStep14.proposed :: wholeBoxes14
theorem wholeAccepted14 : StepValid wholeStep14.shape wholeBoxes14 wholeStep14.proposed := by
  dsimp only [StepValid,wholeStep14]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep15 : Instruction 40 := ⟨.add 4 0,⟨⟨385401607369,519045405171⟩,⟨0,0⟩,⟨480787516865,1653965409517⟩,⟨0,0⟩,⟨0,0⟩,⟨-7827192766580,5492091614501⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15
theorem wholeAccepted15 : StepValid wholeStep15.shape wholeBoxes15 wholeStep15.proposed := by
  dsimp only [StepValid,wholeStep15]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 0 15,⟨⟨192700803684,259522702586⟩,⟨0,0⟩,⟨240393758432,826982704759⟩,⟨0,0⟩,⟨0,0⟩,⟨-3913596383290,2746045807251⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16
theorem wholeAccepted16 : StepValid wholeStep16.shape wholeBoxes16 wholeStep16.proposed := by
  dsimp only [StepValid,wholeStep16]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨-259522702586,-192700803684⟩,⟨0,0⟩,⟨-826982704759,-240393758432⟩,⟨0,0⟩,⟨0,0⟩,⟨-2746045807251,3913596383290⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17
theorem wholeAccepted17 : StepValid wholeStep17.shape wholeBoxes17 wholeStep17.proposed := by
  dsimp only [StepValid,wholeStep17]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep18 : Instruction 40 := ⟨.add 10 0,⟨⟨502600681030,569422599196⟩,⟨0,0⟩,⟨-826982704759,-240393758432⟩,⟨0,0⟩,⟨0,0⟩,⟨-2746045807251,3913596383290⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18
theorem wholeAccepted18 : StepValid wholeStep18.shape wholeBoxes18 wholeStep18.proposed := by
  dsimp only [StepValid,wholeStep18]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep19 : Instruction 40 := ⟨.mul 12 12,⟨⟨397663927236,445641694096⟩,⟨0,0⟩,⟨730663891564,1112400512314⟩,⟨0,0⟩,⟨0,0⟩,⟨-3402170613415,544265960406⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19
theorem wholeAccepted19 : StepValid wholeStep19.shape wholeBoxes19 wholeStep19.proposed := by
  dsimp only [StepValid,wholeStep19]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep20 : Instruction 40 := ⟨.neg 0,⟨⟨-445641694096,-397663927236⟩,⟨0,0⟩,⟨-1112400512314,-730663891564⟩,⟨0,0⟩,⟨0,0⟩,⟨-544265960406,3402170613415⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20
theorem wholeAccepted20 : StepValid wholeStep20.shape wholeBoxes20 wholeStep20.proposed := by
  dsimp only [StepValid,wholeStep20]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep21 : Instruction 40 := ⟨.add 19 0,⟨⟨653869933680,701847700540⟩,⟨0,0⟩,⟨-1112400512314,-730663891564⟩,⟨0,0⟩,⟨0,0⟩,⟨-544265960406,3402170613415⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21
theorem wholeAccepted21 : StepValid wholeStep21.shape wholeBoxes21 wholeStep21.proposed := by
  dsimp only [StepValid,wholeStep21]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep22 : Instruction 40 := ⟨.log 0,⟨⟨-571430411968,-493576218624⟩,⟨0,0⟩,⟨-1870551366616,-1144654950286⟩,⟨0,0⟩,⟨0,0⟩,⟨-4097495407879,4529250766771⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22
theorem wholeAccepted22 : StepValid wholeStep22.shape wholeBoxes22 wholeStep22.proposed := by
  dsimp only [StepValid,wholeStep22]
  exact ⟨by decide,by decide,lc21,by decide⟩
noncomputable def wholeStep23 : Instruction 40 := ⟨.mul 0 22,⟨⟨-285715205984,-246788109312⟩,⟨0,0⟩,⟨-935275683308,-572327475143⟩,⟨0,0⟩,⟨0,0⟩,⟨-2048747703940,2264625383386⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23
theorem wholeAccepted23 : StepValid wholeStep23.shape wholeBoxes23 wholeStep23.proposed := by
  dsimp only [StepValid,wholeStep23]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep24 : Instruction 40 := ⟨.neg 0,⟨⟨246788109312,285715205984⟩,⟨0,0⟩,⟨572327475143,935275683308⟩,⟨0,0⟩,⟨0,0⟩,⟨-2264625383386,2048747703940⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24
theorem wholeAccepted24 : StepValid wholeStep24.shape wholeBoxes24 wholeStep24.proposed := by
  dsimp only [StepValid,wholeStep24]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep25 : Instruction 40 := ⟨.add 17 0,⟨⟨1008911492928,1047838608864⟩,⟨0,0⟩,⟨572327475143,935275683308⟩,⟨0,0⟩,⟨0,0⟩,⟨-2264625383386,2048747703940⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25
theorem wholeAccepted25 : StepValid wholeStep25.shape wholeBoxes25 wholeStep25.proposed := by
  dsimp only [StepValid,wholeStep25]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep26 : Instruction 40 := ⟨.add 24 26,⟨⟨2168236929974,2170435953230⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26
theorem wholeAccepted26 : StepValid wholeStep26.shape wholeBoxes26 wholeStep26.proposed := by
  dsimp only [StepValid,wholeStep26]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep27 : Instruction 40 := ⟨.neg 27,⟨⟨-1070924325454,-1068725302198⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27
theorem wholeAccepted27 : StepValid wholeStep27.shape wholeBoxes27 wholeStep27.proposed := by
  dsimp only [StepValid,wholeStep27]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep28 : Instruction 40 := ⟨.add 26 0,⟨⟨28587302322,30786325578⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28
theorem wholeAccepted28 : StepValid wholeStep28.shape wholeBoxes28 wholeStep28.proposed := by
  dsimp only [StepValid,wholeStep28]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep29 : Instruction 40 := ⟨.inv 0,⟨⟨39268272420224,42288908760876⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29
theorem wholeAccepted29 : StepValid wholeStep29.shape wholeBoxes29 wholeStep29.proposed := by
  dsimp only [StepValid,wholeStep29]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep30 : Instruction 40 := ⟨.mul 3 0,⟨⟨77437033212672,83478305893976⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30
theorem wholeAccepted30 : StepValid wholeStep30.shape wholeBoxes30 wholeStep30.proposed := by
  dsimp only [StepValid,wholeStep30]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨4677981092416,4760578343424⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31
theorem wholeAccepted31 : StepValid wholeStep31.shape wholeBoxes31 wholeStep31.proposed := by
  dsimp only [StepValid,wholeStep31]
  exact ⟨by decide,by decide,lc12,by decide⟩
noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 0 31,⟨⟨2338990546208,2380289171712⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32
theorem wholeAccepted32 : StepValid wholeStep32.shape wholeBoxes32 wholeStep32.proposed := by
  dsimp only [StepValid,wholeStep32]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep33 : Instruction 40 := ⟨.inv 20,⟨⟨2758383387819,3025945389140⟩,⟨0,0⟩,⟨3823306091971,6616993500594⟩,⟨0,0⟩,⟨0,0⟩,⟨-13631621669776,24522533003260⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33
theorem wholeAccepted33 : StepValid wholeStep33.shape wholeBoxes33 wholeStep33.proposed := by
  dsimp only [StepValid,wholeStep33]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep34 : Instruction 40 := ⟨.mul 25 0,⟨⟨4417255147862,4952379150504⟩,⟨0,0⟩,⟨7646612183941,13233987001189⟩,⟨0,0⟩,⟨0,0⟩,⟨-26889681889536,48889387687701⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34
theorem wholeAccepted34 : StepValid wholeStep34.shape wholeBoxes34 wholeStep34.proposed := by
  dsimp only [StepValid,wholeStep34]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨1529038470016,1654767225280⟩,⟨0,0⟩,⟨1697676763796,3294109600334⟩,⟨0,0⟩,⟨0,0⟩,⟨-16562258481335,9547936989826⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35
theorem wholeAccepted35 : StepValid wholeStep35.shape wholeBoxes35 wholeStep35.proposed := by
  dsimp only [StepValid,wholeStep35]
  exact ⟨by decide,by decide,lc27,by decide⟩
noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 0 35,⟨⟨764519235008,827383612640⟩,⟨0,0⟩,⟨848838381898,1647054800167⟩,⟨0,0⟩,⟨0,0⟩,⟨-8281129240668,4773968494913⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36
theorem wholeAccepted36 : StepValid wholeStep36.shape wholeBoxes36 wholeStep36.proposed := by
  dsimp only [StepValid,wholeStep36]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep37 : Instruction 40 := ⟨.mul 40 11,⟨⟨2017822985856,2095677217728⟩,⟨0,0⟩,⟨1144654950286,1870551366616⟩,⟨0,0⟩,⟨0,0⟩,⟨-4529250766772,4097495407880⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37
theorem wholeAccepted37 : StepValid wholeStep37.shape wholeBoxes37 wholeStep37.proposed := by
  dsimp only [StepValid,wholeStep37]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep38 : Instruction 40 := ⟨.add 0 17,⟨⟨1572181291760,1698013290492⟩,⟨0,0⟩,⟨32254437972,1139887475052⟩,⟨0,0⟩,⟨0,0⟩,⟨-5073516727178,7499666021295⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38
theorem wholeAccepted38 : StepValid wholeStep38.shape wholeBoxes38 wholeStep38.proposed := by
  dsimp only [StepValid,wholeStep38]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep39 : Instruction 40 := ⟨.mul 20 0,⟨⟨718663966782,879378732263⟩,⟨0,0⟩,⟨-1262393672003,246595954353⟩,⟨0,0⟩,⟨0,0⟩,⟨-8583021384172,9913774611284⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39
theorem wholeAccepted39 : StepValid wholeStep39.shape wholeBoxes39 wholeStep39.proposed := by
  dsimp only [StepValid,wholeStep39]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep40 : Instruction 40 := ⟨.mul 43 41,⟨⟨837093905798,843065112446⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40
theorem wholeAccepted40 : StepValid wholeStep40.shape wholeBoxes40 wholeStep40.proposed := by
  dsimp only [StepValid,wholeStep40]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 19 19,⟨⟨388850721875,448008172274⟩,⟨0,0⟩,⟨-1420150041026,-869038831876⟩,⟨0,0⟩,⟨0,0⟩,⟨276264308270,6594274094218⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41
theorem wholeAccepted41 : StepValid wholeStep41.shape wholeBoxes41 wholeStep41.proposed := by
  dsimp only [StepValid,wholeStep41]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep42 : Instruction 40 := ⟨.mul 1 0,⟨⟨296044681405,343516203553⟩,⟨0,0⟩,⟨-1088918865233,-661627482318⟩,⟨0,0⟩,⟨0,0⟩,⟨210328988798,5056247055784⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42
theorem wholeAccepted42 : StepValid wholeStep42.shape wholeBoxes42 wholeStep42.proposed := by
  dsimp only [StepValid,wholeStep42]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep43 : Instruction 40 := ⟨.mul 17 17,⟨⟨925776840233,998594032559⟩,⟨0,0⟩,⟨1050334990194,1782642304356⟩,⟨0,0⟩,⟨0,0⟩,⟨-3720566696798,5496072022285⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43
theorem wholeAccepted43 : StepValid wholeStep43.shape wholeBoxes43 wholeStep43.proposed := by
  dsimp only [StepValid,wholeStep43]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep44 : Instruction 40 := ⟨.mul 18 0,⟨⟨849492511404,951663770954⟩,⟨0,0⟩,⟨1445680540697,2548296969006⟩,⟨0,0⟩,⟨0,0⟩,⟨-4509023419457,10131214086889⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44
theorem wholeAccepted44 : StepValid wholeStep44.shape wholeBoxes44 wholeStep44.proposed := by
  dsimp only [StepValid,wholeStep44]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 2 0,⟨⟨228726766994,297324664332⟩,⟨0,0⟩,⟨-553244352402,284975347996⟩,⟨0,0⟩,⟨0,0⟩,⟨-6293727886626,5801738905338⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45
theorem wholeAccepted45 : StepValid wholeStep45.shape wholeBoxes45 wholeStep45.proposed := by
  dsimp only [StepValid,wholeStep45]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep46 : Instruction 40 := ⟨.inv 0,⟨⟨4066012560144,5285458433671⟩,⟨0,0⟩,⟨-6585260554545,12784467977730⟩,⟨0,0⟩,⟨0,0⟩,⟨-165924464144463,207282720667026⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46
theorem wholeAccepted46 : StepValid wholeStep46.shape wholeBoxes46 wholeStep46.proposed := by
  dsimp only [StepValid,wholeStep46]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep47 : Instruction 40 := ⟨.mul 7 0,⟨⟨2657631480777,4227258374914⟩,⟨0,0⟩,⟨-11335275629226,11410303986448⟩,⟨0,0⟩,⟨0,0⟩,⟨-203320915390713,228560786357792⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47
theorem wholeAccepted47 : StepValid wholeStep47.shape wholeBoxes47 wholeStep47.proposed := by
  dsimp only [StepValid,wholeStep47]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep48 : Instruction 40 := ⟨.neg 11,⟨⟨-827383612640,-764519235008⟩,⟨0,0⟩,⟨-1647054800167,-848838381898⟩,⟨0,0⟩,⟨0,0⟩,⟨-4773968494913,8281129240668⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48
theorem wholeAccepted48 : StepValid wholeStep48.shape wholeBoxes48 wholeStep48.proposed := by
  dsimp only [StepValid,wholeStep48]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep49 : Instruction 40 := ⟨.mul 0 10,⟨⟨-1277756719536,-1093178833316⟩,⟨0,0⟩,⟨-3401369356620,-1236173340650⟩,⟨0,0⟩,⟨0,0⟩,⟨-16431183206729,16556854916039⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49
theorem wholeAccepted49 : StepValid wholeStep49.shape wholeBoxes49 wholeStep49.proposed := by
  dsimp only [StepValid,wholeStep49]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 53 43,⟨⟨1322476634112,1399983177728⟩,⟨0,0⟩,⟨1214952951228,1747302849764⟩,⟨0,0⟩,⟨0,0⟩,⟨-6398336147500,-1403589066740⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50
theorem wholeAccepted50 : StepValid wholeStep50.shape wholeBoxes50 wholeStep50.proposed := by
  dsimp only [StepValid,wholeStep50]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep51 : Instruction 40 := ⟨.inv 29,⟨⟨1722490247790,1848878129036⟩,⟨0,0⟩,⟨1793211585166,3145416040728⟩,⟨0,0⟩,⟨0,0⟩,⟨-5886281092515,12241282017395⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51
theorem wholeAccepted51 : StepValid wholeStep51.shape wholeBoxes51 wholeStep51.proposed := by
  dsimp only [StepValid,wholeStep51]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep52 : Instruction 40 := ⟨.mul 1 0,⟨⟨2071786280055,2354134520210⟩,⟨0,0⟩,⟨4060189013593,6943154919742⟩,⟨0,0⟩,⟨0,0⟩,⟨-14290983798752,23384845228183⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52
theorem wholeAccepted52 : StepValid wholeStep52.shape wholeBoxes52 wholeStep52.proposed := by
  dsimp only [StepValid,wholeStep52]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep53 : Instruction 40 := ⟨.neg 2,⟨⟨-1399983177728,-1322476634112⟩,⟨0,0⟩,⟨-1747302849764,-1214952951228⟩,⟨0,0⟩,⟨0,0⟩,⟨1403589066740,6398336147500⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53
theorem wholeAccepted53 : StepValid wholeStep53.shape wholeBoxes53 wholeStep53.proposed := by
  dsimp only [StepValid,wholeStep53]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep54 : Instruction 40 := ⟨.add 1 0,⟨⟨671803102327,1031657886098⟩,⟨0,0⟩,⟨2312886163829,5728201968514⟩,⟨0,0⟩,⟨0,0⟩,⟨-12887394732012,29783181375683⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54
theorem wholeAccepted54 : StepValid wholeStep54.shape wholeBoxes54 wholeStep54.proposed := by
  dsimp only [StepValid,wholeStep54]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 36 0,⟨⟨307089700752,534282039538⟩,⟨0,0⟩,⟨281302101987,2819679485526⟩,⟨0,0⟩,⟨0,0⟩,⟨-17867570506915,18085031413283⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55
theorem wholeAccepted55 : StepValid wholeStep55.shape wholeBoxes55 wholeStep55.proposed := by
  dsimp only [StepValid,wholeStep55]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep56 : Instruction 40 := ⟨.add 6 0,⟨⟨-970667018784,-558896793778⟩,⟨0,0⟩,⟨-3120067254633,1583506144876⟩,⟨0,0⟩,⟨0,0⟩,⟨-34298753713644,34641886329322⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56
theorem wholeAccepted56 : StepValid wholeStep56.shape wholeBoxes56 wholeStep56.proposed := by
  dsimp only [StepValid,wholeStep56]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep57 : Instruction 40 := ⟨.mul 0 10,⟨⟨-4666089972233,-2066809778012⟩,⟨0,0⟩,⟨-26284803610274,13425643499979⟩,⟨0,0⟩,⟨0,0⟩,⟨-420426601891380,350381530416554⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57
theorem wholeAccepted57 : StepValid wholeStep57.shape wholeBoxes57 wholeStep57.proposed := by
  dsimp only [StepValid,wholeStep57]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 54 51,⟨⟨2644953268224,2799966355456⟩,⟨0,0⟩,⟨2429905902456,3494605699528⟩,⟨0,0⟩,⟨0,0⟩,⟨-12796672295000,-2807178133480⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58
theorem wholeAccepted58 : StepValid wholeStep58.shape wholeBoxes58 wholeStep58.proposed := by
  dsimp only [StepValid,wholeStep58]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep59 : Instruction 40 := ⟨.mul 0 7,⟨⟨4143572560111,4708269040420⟩,⟨0,0⟩,⟨8120378027187,13886309839484⟩,⟨0,0⟩,⟨0,0⟩,⟨-28581967597503,46769690456365⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59
theorem wholeAccepted59 : StepValid wholeStep59.shape wholeBoxes59 wholeStep59.proposed := by
  dsimp only [StepValid,wholeStep59]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 57 53,⟨⟨1983714951168,2099974766592⟩,⟨0,0⟩,⟨1822429426842,2620954274646⟩,⟨0,0⟩,⟨0,0⟩,⟨-9597504221250,-2105383600110⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60
theorem wholeAccepted60 : StepValid wholeStep60.shape wholeBoxes60 wholeStep60.proposed := by
  dsimp only [StepValid,wholeStep60]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 39 35,⟨⟨599990827113,668863429536⟩,⟨0,0⟩,⟨-719763626974,-73445435160⟩,⟨0,0⟩,⟨0,0⟩,⟨-3856737115031,3789388344742⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61
theorem wholeAccepted61 : StepValid wholeStep61.shape wholeBoxes61 wholeStep61.proposed := by
  dsimp only [StepValid,wholeStep61]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep62 : Instruction 40 := ⟨.inv 0,⟨⟨1807432976943,2014907170218⟩,⟨0,0⟩,⟨198467572978,2417131774883⟩,⟨0,0⟩,⟨0,0⟩,⟨-12682051472672,18751110558123⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62
theorem wholeAccepted62 : StepValid wholeStep62.shape wholeBoxes62 wholeStep62.proposed := by
  dsimp only [StepValid,wholeStep62]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep63 : Instruction 40 := ⟨.mul 2 0,⟨⟨3260931243490,3848303289927⟩,⟨0,0⟩,⟨3353872794890,9419541398148⟩,⟨0,0⟩,⟨0,0⟩,⟨-41151617426558,43875755168490⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63
theorem wholeAccepted63 : StepValid wholeStep63.shape wholeBoxes63 wholeStep63.proposed := by
  dsimp only [StepValid,wholeStep63]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep64 : Instruction 40 := ⟨.neg 0,⟨⟨-3848303289927,-3260931243490⟩,⟨0,0⟩,⟨-9419541398148,-3353872794890⟩,⟨0,0⟩,⟨0,0⟩,⟨-43875755168490,41151617426558⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64
theorem wholeAccepted64 : StepValid wholeStep64.shape wholeBoxes64 wholeStep64.proposed := by
  dsimp only [StepValid,wholeStep64]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep65 : Instruction 40 := ⟨.add 5 0,⟨⟨295269270184,1447337796930⟩,⟨0,0⟩,⟨-1299163370961,10532437044594⟩,⟨0,0⟩,⟨0,0⟩,⟨-72457722765993,87921307882923⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65
theorem wholeAccepted65 : StepValid wholeStep65.shape wholeBoxes65 wholeStep65.proposed := by
  dsimp only [StepValid,wholeStep65]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 18 0,⟨⟨713695869987,5564534897896⟩,⟨0,0⟩,⟨-19915998652392,55513643873439⟩,⟨0,0⟩,⟨0,0⟩,⟨-763382299771379,857496494852096⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66
theorem wholeAccepted66 : StepValid wholeStep66.shape wholeBoxes66 wholeStep66.proposed := by
  dsimp only [StepValid,wholeStep66]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep67 : Instruction 40 := ⟨.add 9 0,⟨⟨-3952394102246,3497725119884⟩,⟨0,0⟩,⟨-46200802262666,68939287373418⟩,⟨0,0⟩,⟨0,0⟩,⟨-1183808901662759,1207878025268650⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67
theorem wholeAccepted67 : StepValid wholeStep67.shape wholeBoxes67 wholeStep67.proposed := by
  dsimp only [StepValid,wholeStep67]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 61 29,⟨⟨945498424216,1081020874266⟩,⟨0,0⟩,⟨888022459936,2074906092726⟩,⟨0,0⟩,⟨0,0⟩,⟨-8134940179050,5582554451159⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68
theorem wholeAccepted68 : StepValid wholeStep68.shape wholeBoxes68 wholeStep68.proposed := by
  dsimp only [StepValid,wholeStep68]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 27 25,⟨⟨327408081484,406888182052⟩,⟨0,0⟩,⟨-918343937119,-5363929831⟩,⟨0,0⟩,⟨0,0⟩,⟨-5888363621679,6568119856659⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69
theorem wholeAccepted69 : StepValid wholeStep69.shape wholeBoxes69 wholeStep69.proposed := by
  dsimp only [StepValid,wholeStep69]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨2971149993882,3692412887719⟩,⟨0,0⟩,⟨39168107572,10356815181251⟩,⟨0,0⟩,⟨0,0⟩,⟨-74072308127995,124506720782919⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70
theorem wholeAccepted70 : StepValid wholeStep70.shape wholeBoxes70 wholeStep70.proposed := by
  dsimp only [StepValid,wholeStep70]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 2 0,⟨⟨2554968557273,3630316685334⟩,⟨0,0⟩,⟨2433336076495,17150653911300⟩,⟨0,0⟩,⟨0,0⟩,⟨-100082347608714,180249387991560⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71
theorem wholeAccepted71 : StepValid wholeStep71.shape wholeBoxes71 wholeStep71.proposed := by
  dsimp only [StepValid,wholeStep71]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 65 39,⟨⟨1406651947385,1515384064317⟩,⟨0,0⟩,⟨1292284408468,1891333364709⟩,⟨0,0⟩,⟨0,0⟩,⟨-6925752244965,-1492927166448⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72
theorem wholeAccepted72 : StepValid wholeStep72.shape wholeBoxes72 wholeStep72.proposed := by
  dsimp only [StepValid,wholeStep72]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep73 : Instruction 40 := ⟨.add 54 0,⟨⟨1909252628415,2084806663513⟩,⟨0,0⟩,⟨465301703709,1650939606277⟩,⟨0,0⟩,⟨0,0⟩,⟨-9671798052216,2420669216842⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73
theorem wholeAccepted73 : StepValid wholeStep73.shape wholeBoxes73 wholeStep73.proposed := by
  dsimp only [StepValid,wholeStep73]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 0 0,⟨⟨3315331559051,3953044892322⟩,⟨0,0⟩,⟨1615951079314,6260761242128⟩,⟨0,0⟩,⟨0,0⟩,⟨-36283969806279,14137602005590⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74
theorem wholeAccepted74 : StepValid wholeStep74.shape wholeBoxes74 wholeStep74.proposed := by
  dsimp only [StepValid,wholeStep74]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep75 : Instruction 40 := ⟨.mul 7 0,⟨⟨-14209937324565,12575278033095⟩,⟨0,0⟩,⟨-188609957344459,267772083769156⟩,⟨0,0⟩,⟨0,0⟩,⟨-4897688512907243,5258179447536778⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75
theorem wholeAccepted75 : StepValid wholeStep75.shape wholeBoxes75 wholeStep75.proposed := by
  dsimp only [StepValid,wholeStep75]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep76 : Instruction 40 := ⟨.mul 79 28,⟨⟨5315262961554,8454516749828⟩,⟨0,0⟩,⟨-22670551258452,22820607972896⟩,⟨0,0⟩,⟨0,0⟩,⟨-406641830781426,457121572715584⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76
theorem wholeAccepted76 : StepValid wholeStep76.shape wholeBoxes76 wholeStep76.proposed := by
  dsimp only [StepValid,wholeStep76]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 0 3,⟨⟨9229715742607,16030783496557⟩,⟨0,0⟩,⟨-40736736461860,55965258181037⟩,⟨0,0⟩,⟨0,0⟩,⟨-913492293918426,953902217912516⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77
theorem wholeAccepted77 : StepValid wholeStep77.shape wholeBoxes77 wholeStep77.proposed := by
  dsimp only [StepValid,wholeStep77]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep78 : Instruction 40 := ⟨.add 45 29,⟨⟨1511606933568,1615769936704⟩,⟨0,0⟩,⟨-1647054800167,-848838381898⟩,⟨0,0⟩,⟨0,0⟩,⟨-4773968494913,8281129240668⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78
theorem wholeAccepted78 : StepValid wholeStep78.shape wholeBoxes78 wholeStep78.proposed := by
  dsimp only [StepValid,wholeStep78]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 1 0,⟨⟨12688999332919,23557784548346⟩,⟨0,0⟩,⟨-83877942418394,75117390854271⟩,⟨0,0⟩,⟨0,0⟩,⟨-1579682735195845,1644576323895088⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79
theorem wholeAccepted79 : StepValid wholeStep79.shape wholeBoxes79 wholeStep79.proposed := by
  dsimp only [StepValid,wholeStep79]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep80 : Instruction 40 := ⟨.add 4 0,⟨⟨-1520937991646,36133062581441⟩,⟨0,0⟩,⟨-272487899762853,342889474623427⟩,⟨0,0⟩,⟨0,0⟩,⟨-6477371248103088,6902755771431866⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80
theorem wholeAccepted80 : StepValid wholeStep80.shape wholeBoxes80 wholeStep80.proposed := by
  dsimp only [StepValid,wholeStep80]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep81 : Instruction 40 := ⟨.mul 81 81,⟨⟨1038800993736,1043080292993⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81
theorem wholeAccepted81 : StepValid wholeStep81.shape wholeBoxes81 wholeStep81.proposed := by
  dsimp only [StepValid,wholeStep81]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep82 : Instruction 40 := ⟨.neg 0,⟨⟨-1043080292993,-1038800993736⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82
theorem wholeAccepted82 : StepValid wholeStep82.shape wholeBoxes82 wholeStep82.proposed := by
  dsimp only [StepValid,wholeStep82]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep83 : Instruction 40 := ⟨.add 81 0,⟨⟨56431334783,60710634040⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83
theorem wholeAccepted83 : StepValid wholeStep83.shape wholeBoxes83 wholeStep83.proposed := by
  dsimp only [StepValid,wholeStep83]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep84 : Instruction 40 := ⟨.inv 0,⟨⟨19912917048735,21422952766640⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes85 := wholeStep84.proposed :: wholeBoxes84
theorem wholeAccepted84 : StepValid wholeStep84.shape wholeBoxes84 wholeStep84.proposed := by
  dsimp only [StepValid,wholeStep84]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep85 : Instruction 40 := ⟨.mul 13 0,⟨⟨46272250022505,70733315513149⟩,⟨0,0⟩,⟨44069401558717,334164404793019⟩,⟨0,0⟩,⟨0,0⟩,⟨-1950010669675909,3511990257865325⟩⟩⟩
noncomputable def wholeBoxes86 := wholeStep85.proposed :: wholeBoxes85
theorem wholeAccepted85 : StepValid wholeStep85.shape wholeBoxes85 wholeStep85.proposed := by
  dsimp only [StepValid,wholeStep85]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep86 : Instruction 40 := ⟨.add 5 0,⟨⟨44751312030859,106866378094590⟩,⟨0,0⟩,⟨-228418498204136,677053879416446⟩,⟨0,0⟩,⟨0,0⟩,⟨-8427381917778997,10414746029297191⟩⟩⟩
noncomputable def wholeBoxes87 := wholeStep86.proposed :: wholeBoxes86
theorem wholeAccepted86 : StepValid wholeStep86.shape wholeBoxes86 wholeStep86.proposed := by
  dsimp only [StepValid,wholeStep86]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep87 : Instruction 40 := ⟨.mul 0 68,⟨⟨20456391124476,55344690537172⟩,⟨0,0⟩,⟨-198673025221350,340853006236273⟩,⟨0,0⟩,⟨0,0⟩,⟨-5649804172641426,6117643278865769⟩⟩⟩
noncomputable def wholeBoxes88 := wholeStep87.proposed :: wholeBoxes87
theorem wholeAccepted87 : StepValid wholeStep87.shape wholeBoxes87 wholeStep87.proposed := by
  dsimp only [StepValid,wholeStep87]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep88 : Instruction 40 := ⟨.mul 0 69,⟨⟨9350875289399,28662286729173⟩,⟨0,0⟩,⟨-144516900296508,172050764384460⟩,⟨0,0⟩,⟨0,0⟩,⟨-3576919256722352,3664098975647611⟩⟩⟩
noncomputable def wholeBoxes89 := wholeStep88.proposed :: wholeBoxes88
theorem wholeAccepted88 : StepValid wholeStep88.shape wholeBoxes88 wholeStep88.proposed := by
  dsimp only [StepValid,wholeStep88]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep89 : Instruction 40 := ⟨.mul 90 63,⟨⟨384058540575,401722070186⟩,⟨0,0⟩,⟨217865745782,358567512702⟩,⟨0,0⟩,⟨0,0⟩,⟨-868215762918,785452227045⟩⟩⟩
noncomputable def wholeBoxes90 := wholeStep89.proposed :: wholeBoxes89
theorem wholeAccepted89 : StepValid wholeStep89.shape wholeBoxes89 wholeStep89.proposed := by
  dsimp only [StepValid,wholeStep89]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep90 : Instruction 40 := ⟨.inv 0,⟨⟨3009358731659,3147764447068⟩,⟨0,0⟩,⟨-2938838612123,-1632064138509⟩,⟨0,0⟩,⟨0,0⟩,⟨-4667375492892,12603502597324⟩⟩⟩
noncomputable def wholeBoxes91 := wholeStep90.proposed :: wholeBoxes90
theorem wholeAccepted90 : StepValid wholeStep90.shape wholeBoxes90 wholeStep90.proposed := by
  dsimp only [StepValid,wholeStep90]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 2 0,⟨⟨25593306600792,82056546614476⟩,⟨0,0⟩,⟨-490344060113106,478679840850218⟩,⟨0,0⟩,⟨0,0⟩,⟨-11281677671131691,11590954622724550⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91
theorem wholeAccepted91 : StepValid wholeStep91.shape wholeBoxes91 wholeStep91.proposed := by
  dsimp only [StepValid,wholeStep91]
  exact ⟨by decide,by decide⟩
noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91]
theorem wholeAccepted : Accepted wholeProgram wholeInitial :=
  ⟨wholeAccepted0,⟨wholeAccepted1,⟨wholeAccepted2,⟨wholeAccepted3,⟨wholeAccepted4,⟨wholeAccepted5,⟨wholeAccepted6,⟨wholeAccepted7,⟨wholeAccepted8,⟨wholeAccepted9,⟨wholeAccepted10,⟨wholeAccepted11,⟨wholeAccepted12,⟨wholeAccepted13,⟨wholeAccepted14,⟨wholeAccepted15,⟨wholeAccepted16,⟨wholeAccepted17,⟨wholeAccepted18,⟨wholeAccepted19,⟨wholeAccepted20,⟨wholeAccepted21,⟨wholeAccepted22,⟨wholeAccepted23,⟨wholeAccepted24,⟨wholeAccepted25,⟨wholeAccepted26,⟨wholeAccepted27,⟨wholeAccepted28,⟨wholeAccepted29,⟨wholeAccepted30,⟨wholeAccepted31,⟨wholeAccepted32,⟨wholeAccepted33,⟨wholeAccepted34,⟨wholeAccepted35,⟨wholeAccepted36,⟨wholeAccepted37,⟨wholeAccepted38,⟨wholeAccepted39,⟨wholeAccepted40,⟨wholeAccepted41,⟨wholeAccepted42,⟨wholeAccepted43,⟨wholeAccepted44,⟨wholeAccepted45,⟨wholeAccepted46,⟨wholeAccepted47,⟨wholeAccepted48,⟨wholeAccepted49,⟨wholeAccepted50,⟨wholeAccepted51,⟨wholeAccepted52,⟨wholeAccepted53,⟨wholeAccepted54,⟨wholeAccepted55,⟨wholeAccepted56,⟨wholeAccepted57,⟨wholeAccepted58,⟨wholeAccepted59,⟨wholeAccepted60,⟨wholeAccepted61,⟨wholeAccepted62,⟨wholeAccepted63,⟨wholeAccepted64,⟨wholeAccepted65,⟨wholeAccepted66,⟨wholeAccepted67,⟨wholeAccepted68,⟨wholeAccepted69,⟨wholeAccepted70,⟨wholeAccepted71,⟨wholeAccepted72,⟨wholeAccepted73,⟨wholeAccepted74,⟨wholeAccepted75,⟨wholeAccepted76,⟨wholeAccepted77,⟨wholeAccepted78,⟨wholeAccepted79,⟨wholeAccepted80,⟨wholeAccepted81,⟨wholeAccepted82,⟨wholeAccepted83,⟨wholeAccepted84,⟨wholeAccepted85,⟨wholeAccepted86,⟨wholeAccepted87,⟨wholeAccepted88,⟨wholeAccepted89,⟨wholeAccepted90,⟨wholeAccepted91,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
noncomputable def whole_output : DyadicBivariateJetEnclosure 40 := ⟨⟨25593306600792,82056546614476⟩,⟨0,0⟩,⟨-490344060113106,478679840850218⟩,⟨0,0⟩,⟨0,0⟩,⟨-11281677671131691,11590954622724550⟩⟩
theorem whole_output_eq : (finalBoxes wholeProgram wholeInitial).getD 0 (zeroBox 40)=whole_output := rfl
open GeneralCK.Reflection GeneralCK.Reflection.SmallRatio GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed
theorem sameShape : shapes centerProgram=shapes wholeProgram := by decide
theorem scalar_program (a e r : ℝ) :
    (evalRealProgram wholeProgram [a,e,r,2]).getD 0 0=ReflectionMidpointKernel.scalarCore a e r := rfl
attribute [local irreducible] wholeProgram centerProgram
noncomputable def reflection_log_0_out : DyadicInterval 64 := ⟨-12786308645202662930,-12786308645202655416⟩
theorem reflection_log_0_checked : DyadicFastLog.check 1 2 1 16 reflection_log_0_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointNextFamily.Endpoints0841.sharedTwo_eq]
  decide
theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := DyadicFastLog.check_sound reflection_log_0_checked
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1):ℝ)=((1 / 2):ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [he]
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_0_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_1_out : DyadicInterval 64 := ⟨-12544928580105429600,-12544928580105425396⟩
theorem reflection_log_1_checked : DyadicFastLog.check 500 987 0 16 reflection_log_1_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointNextFamily.Endpoints0841.sharedTwo_eq]
  decide
theorem reflection_log_1 : Bounds (680061941 / 1000000000) (340030971 / 500000000) (Real.log (987 / 500)) := by
  have h := DyadicFastLog.check_sound reflection_log_1_checked
  have he : Real.log (987 / 500) = -Real.log (500 / 987) := by
    rw [show ((987 / 500):ℝ)=((500 / 987):ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [he]
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_1_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_2_out : DyadicInterval 64 := ⟨-67324320750878262691,-67324320750878225112⟩
theorem reflection_log_2_checked : DyadicFastLog.check 13 500 5 16 reflection_log_2_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointNextFamily.Endpoints0841.sharedTwo_eq]
  decide
theorem reflection_log_2 : Bounds (-456207343 / 125000000) (-1824829369 / 500000000) (Real.log (13 / 500)) := by
  have h := DyadicFastLog.check_sound reflection_log_2_checked
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_2_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_3_out : DyadicInterval 64 := ⟨-12526229395459408625,-12526229395459404610⟩
theorem reflection_log_3_checked : DyadicFastLog.check 250 493 0 16 reflection_log_3_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointNextFamily.Endpoints0841.sharedTwo_eq]
  decide
theorem reflection_log_3 : Bounds (10610129 / 15625000) (679048257 / 1000000000) (Real.log (493 / 250)) := by
  have h := DyadicFastLog.check_sound reflection_log_3_checked
  have he : Real.log (493 / 250) = -Real.log (250 / 493) := by
    rw [show ((493 / 250):ℝ)=((250 / 493):ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [he]
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_3_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_4_out : DyadicInterval 64 := ⟨-65957269954736961151,-65957269954736923576⟩
theorem reflection_log_4_checked : DyadicFastLog.check 7 250 5 16 reflection_log_4_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointNextFamily.Endpoints0841.sharedTwo_eq]
  decide
theorem reflection_log_4 : Bounds (-893887693 / 250000000) (-1787775383 / 500000000) (Real.log (7 / 250)) := by
  have h := DyadicFastLog.check_sound reflection_log_4_checked
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_4_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_5_out : DyadicInterval 64 := ⟨-877166695750337847,-877166695750337804⟩
theorem reflection_log_5_checked : DyadicFastLog.check 10000 10487 0 16 reflection_log_5_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointNextFamily.Endpoints0841.sharedTwo_eq]
  decide
theorem reflection_log_5 : Bounds (47551301 / 1000000000) (23775651 / 500000000) (Real.log (10487 / 10000)) := by
  have h := DyadicFastLog.check_sound reflection_log_5_checked
  have he : Real.log (10487 / 10000) = -Real.log (10000 / 10487) := by
    rw [show ((10487 / 10000):ℝ)=((10000 / 10487):ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [he]
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_5_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_6_out : DyadicInterval 64 := ⟨-920968617048094309,-920968617048094264⟩
theorem reflection_log_6_checked : DyadicFastLog.check 9513 10000 0 16 reflection_log_6_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointNextFamily.Endpoints0841.sharedTwo_eq]
  decide
theorem reflection_log_6 : Bounds (-49925809 / 1000000000) (-3120363 / 62500000) (Real.log (9513 / 10000)) := by
  have h := DyadicFastLog.check_sound reflection_log_6_checked
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_6_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_7_out : DyadicInterval 64 := ⟨-178436548849774403,-178436548849774354⟩
theorem reflection_log_7_checked : DyadicFastLog.check 25000 25243 0 16 reflection_log_7_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointNextFamily.Endpoints0841.sharedTwo_eq]
  decide
theorem reflection_log_7 : Bounds (1209133 / 125000000) (1934613 / 200000000) (Real.log (25243 / 25000)) := by
  have h := DyadicFastLog.check_sound reflection_log_7_checked
  have he : Real.log (25243 / 25000) = -Real.log (25000 / 25243) := by
    rw [show ((25243 / 25000):ℝ)=((25000 / 25243):ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [he]
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_7_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
noncomputable def reflection_log_8_out : DyadicInterval 64 := ⟨-180179450049622835,-180179450049622792⟩
theorem reflection_log_8_checked : DyadicFastLog.check 24757 25000 0 16 reflection_log_8_out=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,GeneralCK.Certificates.ReflectionMidpointNextFamily.Endpoints0841.sharedTwo_eq]
  decide
theorem reflection_log_8 : Bounds (-2441887 / 250000000) (-9767547 / 1000000000) (Real.log (24757 / 25000)) := by
  have h := DyadicFastLog.check_sound reflection_log_8_checked
  norm_num [DyadicInterval.Contains,DyadicInterval.scale,reflection_log_8_out,Bounds] at h ⊢
  constructor <;> linarith [h.1,h.2]
theorem entropy_bound {a z : ℝ} (ha : Bounds (243 / 250) (487 / 500) a) (hz : Bounds (1 / 100) (1 / 20) z) :
  Bounds (76133247221 / 200000000000) (383381626509 / 1000000000000) ((biasE a+biasE (a*z))/2) := by
  let x0 : ℝ := Real.log (2 / 1)
  have hx0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x0 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x1 : ℝ := (1 / 1)+(487 / 500)
  have hx1 : Bounds (987 / 500) (987 / 500) x1 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((487 / 500) : ℝ)) <;> norm_num
  let x2 : ℝ := (1 / 1)+(487 / 500)
  have hx2 : Bounds (987 / 500) (987 / 500) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((487 / 500) : ℝ)) <;> norm_num
  let x3 : ℝ := Real.log x2
  have hx3 : Bounds (680061941 / 1000000000) (340030971 / 500000000) x3 := by
    exact bounds_log hx2 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x4 : ℝ := x1*x3
  have hx4 : Bounds (671221135767 / 500000000000) (335610568377 / 250000000000) x4 := by
    apply bounds_mul hx1 hx3 <;> norm_num
  let x5 : ℝ := -(487 / 500)
  have hx5 : Bounds (-487 / 500) (-487 / 500) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((487 / 500) : ℝ))
  let x6 : ℝ := (1 / 1)+x5
  have hx6 : Bounds (13 / 500) (13 / 500) x6 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (1 / 1)-(487 / 500)
  have hx7 : Bounds (13 / 500) (13 / 500) x7 := by
    exact hx6
  let x8 : ℝ := -(487 / 500)
  have hx8 : Bounds (-487 / 500) (-487 / 500) x8 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((487 / 500) : ℝ))
  let x9 : ℝ := (1 / 1)+x8
  have hx9 : Bounds (13 / 500) (13 / 500) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx8 <;> norm_num
  let x10 : ℝ := (1 / 1)-(487 / 500)
  have hx10 : Bounds (13 / 500) (13 / 500) x10 := by
    exact hx9
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (-456207343 / 125000000) (-1824829369 / 500000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x12 : ℝ := x7*x11
  have hx12 : Bounds (-5930695459 / 62500000000) (-23722781797 / 250000000000) x12 := by
    apply bounds_mul hx7 hx11 <;> norm_num
  let x13 : ℝ := x4+x12
  have hx13 : Bounds (124755114419 / 100000000000) (15594389329 / 12500000000) x13 := by
    apply bounds_add hx4 hx12 <;> norm_num
  let x14 : ℝ := (2 / 1)⁻¹
  have hx14 : Bounds (1 / 2) (1 / 2) x14 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x15 : ℝ := x13*x14
  have hx15 : Bounds (124755114419 / 200000000000) (15594389329 / 25000000000) x15 := by
    apply bounds_mul hx13 hx14 <;> norm_num
  let x16 : ℝ := x13/(2 / 1)
  have hx16 : Bounds (124755114419 / 200000000000) (15594389329 / 25000000000) x16 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx15
  let x17 : ℝ := -x16
  have hx17 : Bounds (-15594389329 / 25000000000) (-124755114419 / 200000000000) x17 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx16
  let x18 : ℝ := x0+x17
  have hx18 : Bounds (1734290171 / 25000000000) (13874321781 / 200000000000) x18 := by
    apply bounds_add hx0 hx17 <;> norm_num
  let x19 : ℝ := x0-x16
  have hx19 : Bounds (1734290171 / 25000000000) (13874321781 / 200000000000) x19 := by
    exact hx18
  let x20 : ℝ := biasE (487 / 500)
  have hx20 : Bounds (1734290171 / 25000000000) (13874321781 / 200000000000) x20 := by
    simpa +zetaDelta only [biasE, div_one] using hx19
  let x21 : ℝ := Real.log (2 / 1)
  have hx21 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x21 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x22 : ℝ := (1 / 1)+(243 / 250)
  have hx22 : Bounds (493 / 250) (493 / 250) x22 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((243 / 250) : ℝ)) <;> norm_num
  let x23 : ℝ := (1 / 1)+(243 / 250)
  have hx23 : Bounds (493 / 250) (493 / 250) x23 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((243 / 250) : ℝ)) <;> norm_num
  let x24 : ℝ := Real.log x23
  have hx24 : Bounds (10610129 / 15625000) (679048257 / 1000000000) x24 := by
    exact bounds_log hx23 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x25 : ℝ := x22*x24
  have hx25 : Bounds (5230793597 / 3906250000) (334770790701 / 250000000000) x25 := by
    apply bounds_mul hx22 hx24 <;> norm_num
  let x26 : ℝ := -(243 / 250)
  have hx26 : Bounds (-243 / 250) (-243 / 250) x26 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((243 / 250) : ℝ))
  let x27 : ℝ := (1 / 1)+x26
  have hx27 : Bounds (7 / 250) (7 / 250) x27 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx26 <;> norm_num
  let x28 : ℝ := (1 / 1)-(243 / 250)
  have hx28 : Bounds (7 / 250) (7 / 250) x28 := by
    exact hx27
  let x29 : ℝ := -(243 / 250)
  have hx29 : Bounds (-243 / 250) (-243 / 250) x29 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((243 / 250) : ℝ))
  let x30 : ℝ := (1 / 1)+x29
  have hx30 : Bounds (7 / 250) (7 / 250) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx29 <;> norm_num
  let x31 : ℝ := (1 / 1)-(243 / 250)
  have hx31 : Bounds (7 / 250) (7 / 250) x31 := by
    exact hx30
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (-893887693 / 250000000) (-1787775383 / 500000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x33 : ℝ := x28*x32
  have hx33 : Bounds (-6257213851 / 62500000000) (-12514427681 / 125000000000) x33 := by
    apply bounds_mul hx28 hx32 <;> norm_num
  let x34 : ℝ := x25+x33
  have hx34 : Bounds (77435483701 / 62500000000) (309741935339 / 250000000000) x34 := by
    apply bounds_add hx25 hx33 <;> norm_num
  let x35 : ℝ := (2 / 1)⁻¹
  have hx35 : Bounds (1 / 2) (1 / 2) x35 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x36 : ℝ := x34*x35
  have hx36 : Bounds (77435483701 / 125000000000) (309741935339 / 500000000000) x36 := by
    apply bounds_mul hx34 hx35 <;> norm_num
  let x37 : ℝ := x34/(2 / 1)
  have hx37 : Bounds (77435483701 / 125000000000) (309741935339 / 500000000000) x37 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx36
  let x38 : ℝ := -x37
  have hx38 : Bounds (-309741935339 / 500000000000) (-77435483701 / 125000000000) x38 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx37
  let x39 : ℝ := x21+x38
  have hx39 : Bounds (36831654661 / 500000000000) (2301978481 / 31250000000) x39 := by
    apply bounds_add hx21 hx38 <;> norm_num
  let x40 : ℝ := x21-x37
  have hx40 : Bounds (36831654661 / 500000000000) (2301978481 / 31250000000) x40 := by
    exact hx39
  let x41 : ℝ := biasE (243 / 250)
  have hx41 : Bounds (36831654661 / 500000000000) (2301978481 / 31250000000) x41 := by
    simpa +zetaDelta only [biasE, div_one] using hx40
  let x42 : ℝ := biasE a
  have hx42 : Bounds (1734290171 / 25000000000) (2301978481 / 31250000000) x42 := by
    exact bounds_biasE ha (by norm_num) (by norm_num) hx20.1 hx41.2
  let x43 : ℝ := a*z
  have hx43 : Bounds (243 / 25000) (487 / 10000) x43 := by
    apply bounds_mul ha hz <;> norm_num
  let x44 : ℝ := Real.log (2 / 1)
  have hx44 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x44 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x45 : ℝ := (1 / 1)+(487 / 10000)
  have hx45 : Bounds (10487 / 10000) (10487 / 10000) x45 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((487 / 10000) : ℝ)) <;> norm_num
  let x46 : ℝ := (1 / 1)+(487 / 10000)
  have hx46 : Bounds (10487 / 10000) (10487 / 10000) x46 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((487 / 10000) : ℝ)) <;> norm_num
  let x47 : ℝ := Real.log x46
  have hx47 : Bounds (47551301 / 1000000000) (23775651 / 500000000) x47 := by
    exact bounds_log hx46 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x48 : ℝ := x45*x47
  have hx48 : Bounds (24933524679 / 500000000000) (6233381301 / 125000000000) x48 := by
    apply bounds_mul hx45 hx47 <;> norm_num
  let x49 : ℝ := -(487 / 10000)
  have hx49 : Bounds (-487 / 10000) (-487 / 10000) x49 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((487 / 10000) : ℝ))
  let x50 : ℝ := (1 / 1)+x49
  have hx50 : Bounds (9513 / 10000) (9513 / 10000) x50 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx49 <;> norm_num
  let x51 : ℝ := (1 / 1)-(487 / 10000)
  have hx51 : Bounds (9513 / 10000) (9513 / 10000) x51 := by
    exact hx50
  let x52 : ℝ := -(487 / 10000)
  have hx52 : Bounds (-487 / 10000) (-487 / 10000) x52 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((487 / 10000) : ℝ))
  let x53 : ℝ := (1 / 1)+x52
  have hx53 : Bounds (9513 / 10000) (9513 / 10000) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx52 <;> norm_num
  let x54 : ℝ := (1 / 1)-(487 / 10000)
  have hx54 : Bounds (9513 / 10000) (9513 / 10000) x54 := by
    exact hx53
  let x55 : ℝ := Real.log x54
  have hx55 : Bounds (-49925809 / 1000000000) (-3120363 / 62500000) x55 := by
    exact bounds_log hx54 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x56 : ℝ := x51*x55
  have hx56 : Bounds (-23747211051 / 500000000000) (-949888423 / 20000000000) x56 := by
    apply bounds_mul hx51 hx55 <;> norm_num
  let x57 : ℝ := x48+x56
  have hx57 : Bounds (296578407 / 125000000000) (1186314629 / 500000000000) x57 := by
    apply bounds_add hx48 hx56 <;> norm_num
  let x58 : ℝ := (2 / 1)⁻¹
  have hx58 : Bounds (1 / 2) (1 / 2) x58 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x59 : ℝ := x57*x58
  have hx59 : Bounds (296578407 / 250000000000) (1186314629 / 1000000000000) x59 := by
    apply bounds_mul hx57 hx58 <;> norm_num
  let x60 : ℝ := x57/(2 / 1)
  have hx60 : Bounds (296578407 / 250000000000) (1186314629 / 1000000000000) x60 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx59
  let x61 : ℝ := -x60
  have hx61 : Bounds (-1186314629 / 1000000000000) (-296578407 / 250000000000) x61 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx60
  let x62 : ℝ := x44+x61
  have hx62 : Bounds (691960865371 / 1000000000000) (172990216843 / 250000000000) x62 := by
    apply bounds_add hx44 hx61 <;> norm_num
  let x63 : ℝ := x44-x60
  have hx63 : Bounds (691960865371 / 1000000000000) (172990216843 / 250000000000) x63 := by
    exact hx62
  let x64 : ℝ := biasE (487 / 10000)
  have hx64 : Bounds (691960865371 / 1000000000000) (172990216843 / 250000000000) x64 := by
    simpa +zetaDelta only [biasE, div_one] using hx63
  let x65 : ℝ := Real.log (2 / 1)
  have hx65 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x65 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x66 : ℝ := (1 / 1)+(243 / 25000)
  have hx66 : Bounds (25243 / 25000) (25243 / 25000) x66 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((243 / 25000) : ℝ)) <;> norm_num
  let x67 : ℝ := (1 / 1)+(243 / 25000)
  have hx67 : Bounds (25243 / 25000) (25243 / 25000) x67 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((243 / 25000) : ℝ)) <;> norm_num
  let x68 : ℝ := Real.log x67
  have hx68 : Bounds (1209133 / 125000000) (1934613 / 200000000) x68 := by
    exact bounds_log hx67 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x69 : ℝ := x66*x68
  have hx69 : Bounds (4883543091 / 500000000000) (1220885899 / 125000000000) x69 := by
    apply bounds_mul hx66 hx68 <;> norm_num
  let x70 : ℝ := -(243 / 25000)
  have hx70 : Bounds (-243 / 25000) (-243 / 25000) x70 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((243 / 25000) : ℝ))
  let x71 : ℝ := (1 / 1)+x70
  have hx71 : Bounds (24757 / 25000) (24757 / 25000) x71 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx70 <;> norm_num
  let x72 : ℝ := (1 / 1)-(243 / 25000)
  have hx72 : Bounds (24757 / 25000) (24757 / 25000) x72 := by
    exact hx71
  let x73 : ℝ := -(243 / 25000)
  have hx73 : Bounds (-243 / 25000) (-243 / 25000) x73 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((243 / 25000) : ℝ))
  let x74 : ℝ := (1 / 1)+x73
  have hx74 : Bounds (24757 / 25000) (24757 / 25000) x74 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx73 <;> norm_num
  let x75 : ℝ := (1 / 1)-(243 / 25000)
  have hx75 : Bounds (24757 / 25000) (24757 / 25000) x75 := by
    exact hx74
  let x76 : ℝ := Real.log x75
  have hx76 : Bounds (-2441887 / 250000000) (-9767547 / 1000000000) x76 := by
    exact bounds_log hx75 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x77 : ℝ := x72*x76
  have hx77 : Bounds (-4836303717 / 500000000000) (-9672606443 / 1000000000000) x77 := by
    apply bounds_mul hx72 hx76 <;> norm_num
  let x78 : ℝ := x69+x77
  have hx78 : Bounds (23619687 / 250000000000) (94480749 / 1000000000000) x78 := by
    apply bounds_add hx69 hx77 <;> norm_num
  let x79 : ℝ := (2 / 1)⁻¹
  have hx79 : Bounds (1 / 2) (1 / 2) x79 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x80 : ℝ := x78*x79
  have hx80 : Bounds (23619687 / 500000000000) (377923 / 8000000000) x80 := by
    apply bounds_mul hx78 hx79 <;> norm_num
  let x81 : ℝ := x78/(2 / 1)
  have hx81 : Bounds (23619687 / 500000000000) (377923 / 8000000000) x81 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx80
  let x82 : ℝ := -x81
  have hx82 : Bounds (-377923 / 8000000000) (-23619687 / 500000000000) x82 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx81
  let x83 : ℝ := x65+x82
  have hx83 : Bounds (5544799517 / 8000000000) (346549970813 / 500000000000) x83 := by
    apply bounds_add hx65 hx82 <;> norm_num
  let x84 : ℝ := x65-x81
  have hx84 : Bounds (5544799517 / 8000000000) (346549970813 / 500000000000) x84 := by
    exact hx83
  let x85 : ℝ := biasE (243 / 25000)
  have hx85 : Bounds (5544799517 / 8000000000) (346549970813 / 500000000000) x85 := by
    simpa +zetaDelta only [biasE, div_one] using hx84
  let x86 : ℝ := biasE x43
  have hx86 : Bounds (691960865371 / 1000000000000) (346549970813 / 500000000000) x86 := by
    exact bounds_biasE hx43 (by norm_num) (by norm_num) hx64.1 hx85.2
  let x87 : ℝ := x42+x86
  have hx87 : Bounds (761332472211 / 1000000000000) (383381626509 / 500000000000) x87 := by
    apply bounds_add hx42 hx86 <;> norm_num
  let x88 : ℝ := (2 / 1)⁻¹
  have hx88 : Bounds (1 / 2) (1 / 2) x88 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x89 : ℝ := x87*x88
  have hx89 : Bounds (76133247221 / 200000000000) (383381626509 / 1000000000000) x89 := by
    apply bounds_mul hx87 hx88 <;> norm_num
  let x90 : ℝ := x87/(2 / 1)
  have hx90 : Bounds (76133247221 / 200000000000) (383381626509 / 1000000000000) x90 := by
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

theorem center_inputs_eq : centerInitial=inputBoxes ⟨1068725302198,1070924325454⟩ ⟨418546952899,421532556223⟩ ⟨534362651099,535462162727⟩ := rfl
theorem whole_inputs_eq : wholeInitial=inputBoxes ⟨1068725302198,1070924325454⟩ ⟨418546952899,421532556223⟩ ⟨507589542962,562235270864⟩ := rfl
noncomputable def centerUpper : ℝ := (52250334680685 / 1099511627776)
noncomputable def secondUpper : ℝ := (5795477311362275 / 549755813888)


theorem center_inputs {a z : ℝ} (ha : Bounds (243/250) (487/500) a)
    (hz : Bounds (1/100) (1/20) z) :
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

theorem whole_inputs {a z s : ℝ} (ha : Bounds (243/250) (487/500) a)
    (hz : Bounds (1/100) (1/20) z) (hs : s∈Icc (a*(1-z)/2) (a*(1+z)/2)) :
    RegistersContain wholeInitial (inputJets a ((biasE a+biasE (a*z))/2)) s := by
  rw [whole_inputs_eq]
  apply inputs_contain
  · norm_num [DyadicInterval.Contains,DyadicInterval.scale]
    constructor <;> linarith [ha.1,ha.2]
  · have h := entropy_bound ha hz
    norm_num [DyadicInterval.Contains,DyadicInterval.scale]
    constructor <;> linarith [h.1,h.2]
  · have hb : a*z≤(487/500:ℝ)*(1/20) :=
      mul_le_mul ha.2 hz.2 (by linarith [hz.1]) (by norm_num)
    norm_num [DyadicInterval.Contains,DyadicInterval.scale]
    constructor <;> nlinarith [ha.1,ha.2,hs.1,hs.2]

theorem curvature_pos {a z : ℝ} (ha : Bounds (243/250) (487/500) a)
    (hz : Bounds (1/100) (1/20) z) : 0<curvature a (a*z) := by
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
    have hb : a*z≤(487/10000:ℝ) := by
      have h := mul_le_mul ha.2 hz.2 hz0.le (by norm_num : (0:ℝ)≤487/500)
      norm_num at h
      exact h
    have hb2 := mul_self_le_mul_self hb0 hb
    have hle : centerUpper+secondUpper*(a*z)^2/24 ≤
        centerUpper+secondUpper*(487/10000:ℝ)^2/24 := by
      unfold centerUpper secondUpper
      nlinarith
    apply hle.trans_lt
    exact lt_of_lt_of_le (by norm_num [centerUpper,secondUpper] :
      centerUpper+secondUpper*(487/10000:ℝ)^2/24 < 2*(243/250:ℝ)/(1-(243/250:ℝ)^2)^2)
      (LowRatioFamily.base_mono (by norm_num) ha.1 ha1)

#print axioms entropy_bound
#print axioms curvature_pos
end GeneralCK.Certificates.ReflectionMidpointNextFamily.Cell0841

end


