-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_BivariateFastPilot
-- name    : CK_GeneralCK_Certificates_Generated_BivariateFastPilot
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:05:59.720755+00:00
-- url     : https://prove2.me/theorems/2ed74666-f887-4dc4-8fca-9a0105f97361
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.BivariateFastPilot` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.BivariateFastPilot` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.BivariateFastPilot` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.BivariateFastPilot (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/BivariateFastPilot.lean)

import Definitions.Def_CK_GeneralCK_Certificates_DyadicFastLog
import Definitions.Def_CK_GeneralCK_Certificates_BivariateProvedProgram
import Definitions.Def_CK_GeneralCK_Certificates_ReflectionExpressionJet

-- ===== source module GeneralCK.Certificates.Generated.BivariateFastPilot =====
section

namespace BivariateFastEndpoints
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

noncomputable def out_w1 : DyadicInterval 40 := ⟨215931784512,215931784576⟩
theorem checked_w1 : DyadicFastLog.check 1099511627776 1338105651003 0 16 (lift40 out_w1.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w1 : out_w1.Contains (Real.log ((1338105651003:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w1
#print axioms endpoint_w1

noncomputable def out_w2 : DyadicInterval 40 := ⟨215931784512,215931784576⟩
theorem checked_w2 : DyadicFastLog.check 1099511627776 1338105651004 0 16 (lift40 out_w2.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w2 : out_w2.Contains (Real.log ((1338105651004:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w2
#print axioms endpoint_w2

noncomputable def out_w3 : DyadicInterval 40 := ⟨-268965374464,-268965374400⟩
theorem checked_w3 : DyadicFastLog.check 860917604548 1099511627776 0 16 (lift40 out_w3)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w3 : out_w3.Contains (Real.log ((860917604548:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w3
#print axioms endpoint_w3

noncomputable def out_w4 : DyadicInterval 40 := ⟨-268965374464,-268965374400⟩
theorem checked_w4 : DyadicFastLog.check 860917604549 1099511627776 0 16 (lift40 out_w4)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w4 : out_w4.Contains (Real.log ((860917604549:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w4
#print axioms endpoint_w4

noncomputable def out_w5 : DyadicInterval 40 := ⟨25354268160,25354268224⟩
theorem checked_w5 : DyadicFastLog.check 1099511627776 1125160485272 0 16 (lift40 out_w5.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w5 : out_w5.Contains (Real.log ((1125160485272:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w5
#print axioms endpoint_w5

noncomputable def out_w6 : DyadicInterval 40 := ⟨25354268160,25354268224⟩
theorem checked_w6 : DyadicFastLog.check 1099511627776 1125160485274 0 16 (lift40 out_w6.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w6 : out_w6.Contains (Real.log ((1125160485274:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w6
#print axioms endpoint_w6

noncomputable def out_w7 : DyadicInterval 40 := ⟨-25952754816,-25952754752⟩
theorem checked_w7 : DyadicFastLog.check 1073862770278 1099511627776 0 16 (lift40 out_w7)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w7 : out_w7.Contains (Real.log ((1073862770278:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w7
#print axioms endpoint_w7

noncomputable def out_w8 : DyadicInterval 40 := ⟨-25952754816,-25952754752⟩
theorem checked_w8 : DyadicFastLog.check 1073862770280 1099511627776 0 16 (lift40 out_w8)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w8 : out_w8.Contains (Real.log ((1073862770280:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w8
#print axioms endpoint_w8

noncomputable def out_w9 : DyadicInterval 40 := ⟨102651944192,102651944256⟩
theorem checked_w9 : DyadicFastLog.check 1099511627776 1207108108288 0 16 (lift40 out_w9.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w9 : out_w9.Contains (Real.log ((1207108108288:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w9
#print axioms endpoint_w9

noncomputable def out_w10 : DyadicInterval 40 := ⟨-113231906368,-113231906304⟩
theorem checked_w10 : DyadicFastLog.check 991915147264 1099511627776 0 16 (lift40 out_w10)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w10 : out_w10.Contains (Real.log ((991915147264:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w10
#print axioms endpoint_w10

noncomputable def out_w11 : DyadicInterval 40 := ⟨102656719744,102656719808⟩
theorem checked_w11 : DyadicFastLog.check 1099511627776 1207113351168 0 16 (lift40 out_w11.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w11 : out_w11.Contains (Real.log ((1207113351168:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w11
#print axioms endpoint_w11

noncomputable def out_w12 : DyadicInterval 40 := ⟨-113237717952,-113237717888⟩
theorem checked_w12 : DyadicFastLog.check 991909904384 1099511627776 0 16 (lift40 out_w12)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w12 : out_w12.Contains (Real.log ((991909904384:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w12
#print axioms endpoint_w12

noncomputable def out_w13 : DyadicInterval 40 := ⟨-10580998208,-10580998144⟩
theorem checked_w13 : DyadicFastLog.check 1088981379087 1099511627776 0 16 (lift40 out_w13)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w13 : out_w13.Contains (Real.log ((1088981379087:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w13
#print axioms endpoint_w13

noncomputable def out_w14 : DyadicInterval 40 := ⟨-10579962112,-10579962048⟩
theorem checked_w14 : DyadicFastLog.check 1088982405232 1099511627776 0 16 (lift40 out_w14)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w14 : out_w14.Contains (Real.log ((1088982405232:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w14
#print axioms endpoint_w14

noncomputable def out_w15 : DyadicInterval 40 := ⟨125571858624,125571858688⟩
theorem checked_w15 : DyadicFastLog.check 1099511627776 1232535027712 0 16 (lift40 out_w15.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w15 : out_w15.Contains (Real.log ((1232535027712:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w15
#print axioms endpoint_w15

noncomputable def out_w16 : DyadicInterval 40 := ⟨-141784517120,-141784517056⟩
theorem checked_w16 : DyadicFastLog.check 966488227840 1099511627776 0 16 (lift40 out_w16)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w16 : out_w16.Contains (Real.log ((966488227840:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w16
#print axioms endpoint_w16

noncomputable def out_w17 : DyadicInterval 40 := ⟨125576535616,125576535680⟩
theorem checked_w17 : DyadicFastLog.check 1099511627776 1232540270592 0 16 (lift40 out_w17.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w17 : out_w17.Contains (Real.log ((1232540270592:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w17
#print axioms endpoint_w17

noncomputable def out_w18 : DyadicInterval 40 := ⟨-141790481600,-141790481536⟩
theorem checked_w18 : DyadicFastLog.check 966482984960 1099511627776 0 16 (lift40 out_w18)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w18 : out_w18.Contains (Real.log ((966482984960:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w18
#print axioms endpoint_w18

noncomputable def out_w19 : DyadicInterval 40 := ⟨-16213945984,-16213945920⟩
theorem checked_w19 : DyadicFastLog.check 1083416645820 1099511627776 0 16 (lift40 out_w19)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w19 : out_w19.Contains (Real.log ((1083416645820:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w19
#print axioms endpoint_w19

noncomputable def out_w20 : DyadicInterval 40 := ⟨-16212658496,-16212658432⟩
theorem checked_w20 : DyadicFastLog.check 1083417914455 1099511627776 0 16 (lift40 out_w20)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w20 : out_w20.Contains (Real.log ((1083417914455:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w20
#print axioms endpoint_w20

noncomputable def out_w21 : DyadicInterval 40 := ⟨484897158976,484897159040⟩
theorem checked_w21 : DyadicFastLog.check 1099511627776 1708947191572 0 16 (lift40 out_w21.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w21 : out_w21.Contains (Real.log ((1708947191572:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w21
#print axioms endpoint_w21

noncomputable def out_w22 : DyadicInterval 40 := ⟨484897158976,484897159040⟩
theorem checked_w22 : DyadicFastLog.check 1099511627776 1708947191578 0 16 (lift40 out_w22.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w22 : out_w22.Contains (Real.log ((1708947191578:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w22
#print axioms endpoint_w22

noncomputable def out_w23 : DyadicInterval 40 := ⟨215027952512,215027952576⟩
theorem checked_w23 : DyadicFastLog.check 1099511627776 1337006139375 0 16 (lift40 out_w23.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w23 : out_w23.Contains (Real.log ((1337006139375:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w23
#print axioms endpoint_w23

noncomputable def out_w24 : DyadicInterval 40 := ⟨216834874240,216834874304⟩
theorem checked_w24 : DyadicFastLog.check 1099511627776 1339205162632 0 16 (lift40 out_w24.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w24 : out_w24.Contains (Real.log ((1339205162632:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w24
#print axioms endpoint_w24

noncomputable def out_w25 : DyadicInterval 40 := ⟨-270370501312,-270370501248⟩
theorem checked_w25 : DyadicFastLog.check 859818092920 1099511627776 0 16 (lift40 out_w25)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w25 : out_w25.Contains (Real.log ((859818092920:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w25
#print axioms endpoint_w25

noncomputable def out_w26 : DyadicInterval 40 := ⟨-267562040960,-267562040896⟩
theorem checked_w26 : DyadicFastLog.check 862017116177 1099511627776 0 16 (lift40 out_w26)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w26 : out_w26.Contains (Real.log ((862017116177:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w26
#print axioms endpoint_w26

noncomputable def out_w27 : DyadicInterval 40 := ⟨24658343232,24658343296⟩
theorem checked_w27 : DyadicFastLog.check 1099511627776 1124448551493 0 16 (lift40 out_w27.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w27 : out_w27.Contains (Real.log ((1124448551493:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w27
#print axioms endpoint_w27

noncomputable def out_w28 : DyadicInterval 40 := ⟨26055121728,26055121792⟩
theorem checked_w28 : DyadicFastLog.check 1099511627776 1125877916611 0 16 (lift40 out_w28.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w28 : out_w28.Contains (Real.log ((1125877916611:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w28
#print axioms endpoint_w28

noncomputable def out_w29 : DyadicInterval 40 := ⟨-26687567232,-26687567168⟩
theorem checked_w29 : DyadicFastLog.check 1073145338941 1099511627776 0 16 (lift40 out_w29)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w29 : out_w29.Contains (Real.log ((1073145338941:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w29
#print axioms endpoint_w29

noncomputable def out_w30 : DyadicInterval 40 := ⟨-25224058240,-25224058176⟩
theorem checked_w30 : DyadicFastLog.check 1074574704059 1099511627776 0 16 (lift40 out_w30)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w30 : out_w30.Contains (Real.log ((1074574704059:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w30
#print axioms endpoint_w30

noncomputable def out_w31 : DyadicInterval 40 := ⟨101803478848,101803478912⟩
theorem checked_w31 : DyadicFastLog.check 1099511627776 1206176972800 0 16 (lift40 out_w31.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w31 : out_w31.Contains (Real.log ((1206176972800:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w31
#print axioms endpoint_w31

noncomputable def out_w32 : DyadicInterval 40 := ⟨-112200251520,-112200251456⟩
theorem checked_w32 : DyadicFastLog.check 992846282752 1099511627776 0 16 (lift40 out_w32)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w32 : out_w32.Contains (Real.log ((992846282752:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w32
#print axioms endpoint_w32

noncomputable def out_w33 : DyadicInterval 40 := ⟨103508344576,103508344640⟩
theorem checked_w33 : DyadicFastLog.check 1099511627776 1208048680960 0 16 (lift40 out_w33.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w33 : out_w33.Contains (Real.log ((1208048680960:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w33
#print axioms endpoint_w33

noncomputable def out_w34 : DyadicInterval 40 := ⟨-114275000832,-114275000768⟩
theorem checked_w34 : DyadicFastLog.check 990974574592 1099511627776 0 16 (lift40 out_w34)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w34 : out_w34.Contains (Real.log ((990974574592:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w34
#print axioms endpoint_w34

noncomputable def out_w35 : DyadicInterval 40 := ⟨-10766656192,-10766656128⟩
theorem checked_w35 : DyadicFastLog.check 1088797514695 1099511627776 0 16 (lift40 out_w35)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w35 : out_w35.Contains (Real.log ((1088797514695:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w35
#print axioms endpoint_w35

noncomputable def out_w36 : DyadicInterval 40 := ⟨-10396772608,-10396772544⟩
theorem checked_w36 : DyadicFastLog.check 1089163855600 1099511627776 0 16 (lift40 out_w36)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w36 : out_w36.Contains (Real.log ((1089163855600:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w36
#print axioms endpoint_w36

noncomputable def out_w37 : DyadicInterval 40 := ⟨124615457152,124615457216⟩
theorem checked_w37 : DyadicFastLog.check 1099511627776 1231463383040 0 16 (lift40 out_w37.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w37 : out_w37.Contains (Real.log ((1231463383040:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w37
#print axioms endpoint_w37

noncomputable def out_w38 : DyadicInterval 40 := ⟨-140566051136,-140566051072⟩
theorem checked_w38 : DyadicFastLog.check 967559872512 1099511627776 0 16 (lift40 out_w38)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w38 : out_w38.Contains (Real.log ((967559872512:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w38
#print axioms endpoint_w38

noncomputable def out_w39 : DyadicInterval 40 := ⟨126536774784,126536774848⟩
theorem checked_w39 : DyadicFastLog.check 1099511627776 1233617158144 0 16 (lift40 out_w39.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w39 : out_w39.Contains (Real.log ((1233617158144:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w39
#print axioms endpoint_w39

noncomputable def out_w40 : DyadicInterval 40 := ⟨-143016277120,-143016277056⟩
theorem checked_w40 : DyadicFastLog.check 965406097408 1099511627776 0 16 (lift40 out_w40)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w40 : out_w40.Contains (Real.log ((965406097408:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w40
#print axioms endpoint_w40

noncomputable def out_w41 : DyadicInterval 40 := ⟨-16479502336,-16479502272⟩
theorem checked_w41 : DyadicFastLog.check 1083155008327 1099511627776 0 16 (lift40 out_w41)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w41 : out_w41.Contains (Real.log ((1083155008327:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w41
#print axioms endpoint_w41

noncomputable def out_w42 : DyadicInterval 40 := ⟨-15950593984,-15950593920⟩
theorem checked_w42 : DyadicFastLog.check 1083676173855 1099511627776 0 16 (lift40 out_w42)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w42 : out_w42.Contains (Real.log ((1083676173855:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w42
#print axioms endpoint_w42

noncomputable def out_w43 : DyadicInterval 40 := ⟨482589993408,482589993472⟩
theorem checked_w43 : DyadicFastLog.check 1099511627776 1705364973690 0 16 (lift40 out_w43.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w43 : out_w43.Contains (Real.log ((1705364973690:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w43
#print axioms endpoint_w43

noncomputable def out_w44 : DyadicInterval 40 := ⟨487205375488,487205375552⟩
theorem checked_w44 : DyadicFastLog.check 1099511627776 1712538571144 0 16 (lift40 out_w44.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w44 : out_w44.Contains (Real.log ((1712538571144:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w44
#print axioms endpoint_w44

end BivariateFastEndpoints

namespace GeneralCK.Certificates.BivariateFastPilot
open Set BivariateFastEndpoints
open BivariateJetProgram (RegistersContain RegistersSound zeroBox zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
theorem lc0 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc1 : ProvedTranscendental.LogEncloses (⟨1338105651003,1338105651004⟩ : DyadicInterval 40) (⟨215931784512,215931784576⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w1
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w2
theorem lc2 : ProvedTranscendental.LogEncloses (⟨860917604548,860917604549⟩ : DyadicInterval 40) (⟨-268965374464,-268965374400⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w3
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w4
theorem lc3 : ProvedTranscendental.LogEncloses (⟨1125160485272,1125160485274⟩ : DyadicInterval 40) (⟨25354268160,25354268224⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w5
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w6
theorem lc4 : ProvedTranscendental.LogEncloses (⟨1073862770278,1073862770280⟩ : DyadicInterval 40) (⟨-25952754816,-25952754752⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w7
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
theorem lc5 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc6 : ProvedTranscendental.LogEncloses (⟨1207108108288,1207108108288⟩ : DyadicInterval 40) (⟨102651944192,102651944256⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w9
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w9
theorem lc7 : ProvedTranscendental.LogEncloses (⟨991915147264,991915147264⟩ : DyadicInterval 40) (⟨-113231906368,-113231906304⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w10
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w10
theorem lc8 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc9 : ProvedTranscendental.LogEncloses (⟨1207113351168,1207113351168⟩ : DyadicInterval 40) (⟨102656719744,102656719808⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w11
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w11
theorem lc10 : ProvedTranscendental.LogEncloses (⟨991909904384,991909904384⟩ : DyadicInterval 40) (⟨-113237717952,-113237717888⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w12
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w12
theorem lc11 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc12 : ProvedTranscendental.LogEncloses (⟨1088981379087,1088982405232⟩ : DyadicInterval 40) (⟨-10580998208,-10579962048⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w13
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w14
theorem lc13 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc14 : ProvedTranscendental.LogEncloses (⟨1232535027712,1232535027712⟩ : DyadicInterval 40) (⟨125571858624,125571858688⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w15
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w15
theorem lc15 : ProvedTranscendental.LogEncloses (⟨966488227840,966488227840⟩ : DyadicInterval 40) (⟨-141784517120,-141784517056⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w16
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w16
theorem lc16 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc17 : ProvedTranscendental.LogEncloses (⟨1232540270592,1232540270592⟩ : DyadicInterval 40) (⟨125576535616,125576535680⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w17
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w17
theorem lc18 : ProvedTranscendental.LogEncloses (⟨966482984960,966482984960⟩ : DyadicInterval 40) (⟨-141790481600,-141790481536⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w18
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w18
theorem lc19 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc20 : ProvedTranscendental.LogEncloses (⟨1083416645820,1083417914455⟩ : DyadicInterval 40) (⟨-16213945984,-16212658432⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w19
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w20
theorem lc21 : ProvedTranscendental.LogEncloses (⟨1708947191572,1708947191578⟩ : DyadicInterval 40) (⟨484897158976,484897159040⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w21
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w22
theorem lc22 : ProvedTranscendental.LogEncloses (⟨1207108108288,1207113351168⟩ : DyadicInterval 40) (⟨102651944192,102656719808⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w9
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w11
theorem lc23 : ProvedTranscendental.LogEncloses (⟨991909904384,991915147264⟩ : DyadicInterval 40) (⟨-113237717952,-113231906304⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w12
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w10
theorem lc24 : ProvedTranscendental.LogEncloses (⟨1088981379087,1088982405232⟩ : DyadicInterval 40) (⟨-10580998208,-10579962048⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w13
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w14
theorem lc25 : ProvedTranscendental.LogEncloses (⟨1232535027712,1232540270592⟩ : DyadicInterval 40) (⟨125571858624,125576535680⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w15
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w17
theorem lc26 : ProvedTranscendental.LogEncloses (⟨966482984960,966488227840⟩ : DyadicInterval 40) (⟨-141790481600,-141784517056⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w18
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w16
theorem lc27 : ProvedTranscendental.LogEncloses (⟨1083416645820,1083417914455⟩ : DyadicInterval 40) (⟨-16213945984,-16212658432⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w19
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w20
theorem lc28 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc29 : ProvedTranscendental.LogEncloses (⟨1337006139375,1339205162632⟩ : DyadicInterval 40) (⟨215027952512,216834874304⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w23
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w24
theorem lc30 : ProvedTranscendental.LogEncloses (⟨859818092920,862017116177⟩ : DyadicInterval 40) (⟨-270370501312,-267562040896⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w25
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w26
theorem lc31 : ProvedTranscendental.LogEncloses (⟨1124448551493,1125877916611⟩ : DyadicInterval 40) (⟨24658343232,26055121792⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w27
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w28
theorem lc32 : ProvedTranscendental.LogEncloses (⟨1073145338941,1074574704059⟩ : DyadicInterval 40) (⟨-26687567232,-25224058176⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w29
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w30
theorem lc33 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc34 : ProvedTranscendental.LogEncloses (⟨1206176972800,1206176972800⟩ : DyadicInterval 40) (⟨101803478848,101803478912⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w31
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w31
theorem lc35 : ProvedTranscendental.LogEncloses (⟨992846282752,992846282752⟩ : DyadicInterval 40) (⟨-112200251520,-112200251456⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w32
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w32
theorem lc36 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc37 : ProvedTranscendental.LogEncloses (⟨1208048680960,1208048680960⟩ : DyadicInterval 40) (⟨103508344576,103508344640⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w33
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w33
theorem lc38 : ProvedTranscendental.LogEncloses (⟨990974574592,990974574592⟩ : DyadicInterval 40) (⟨-114275000832,-114275000768⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w34
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w34
theorem lc39 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc40 : ProvedTranscendental.LogEncloses (⟨1088797514695,1089163855600⟩ : DyadicInterval 40) (⟨-10766656192,-10396772544⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w35
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w36
theorem lc41 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc42 : ProvedTranscendental.LogEncloses (⟨1231463383040,1231463383040⟩ : DyadicInterval 40) (⟨124615457152,124615457216⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w37
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w37
theorem lc43 : ProvedTranscendental.LogEncloses (⟨967559872512,967559872512⟩ : DyadicInterval 40) (⟨-140566051136,-140566051072⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w38
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w38
theorem lc44 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc45 : ProvedTranscendental.LogEncloses (⟨1233617158144,1233617158144⟩ : DyadicInterval 40) (⟨126536774784,126536774848⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w39
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w39
theorem lc46 : ProvedTranscendental.LogEncloses (⟨965406097408,965406097408⟩ : DyadicInterval 40) (⟨-143016277120,-143016277056⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w40
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w40
theorem lc47 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
theorem lc48 : ProvedTranscendental.LogEncloses (⟨1083155008327,1083676173855⟩ : DyadicInterval 40) (⟨-16479502336,-15950593920⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w41
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w42
theorem lc49 : ProvedTranscendental.LogEncloses (⟨1705364973690,1712538571144⟩ : DyadicInterval 40) (⟨482589993408,487205375552⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w43
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w44
theorem lc50 : ProvedTranscendental.LogEncloses (⟨1206176972800,1208048680960⟩ : DyadicInterval 40) (⟨101803478848,103508344640⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w31
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w33
theorem lc51 : ProvedTranscendental.LogEncloses (⟨990974574592,992846282752⟩ : DyadicInterval 40) (⟨-114275000832,-112200251456⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w34
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w32
theorem lc52 : ProvedTranscendental.LogEncloses (⟨1088797514695,1089163855600⟩ : DyadicInterval 40) (⟨-10766656192,-10396772544⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w35
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w36
theorem lc53 : ProvedTranscendental.LogEncloses (⟨1231463383040,1233617158144⟩ : DyadicInterval 40) (⟨124615457152,126536774848⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w37
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w39
theorem lc54 : ProvedTranscendental.LogEncloses (⟨965406097408,967559872512⟩ : DyadicInterval 40) (⟨-143016277120,-140566051072⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w40
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w38
theorem lc55 : ProvedTranscendental.LogEncloses (⟨1083155008327,1083676173855⟩ : DyadicInterval 40) (⟨-16479502336,-15950593920⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w41
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w42
theorem ew11_ok (x : ℝ) (hx : (⟨107596480512,107596480512⟩ : DyadicInterval 40).Contains x) : (⟨756850337413,756850356743⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨107596480512,107596480512⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨102651944192,102651944256⟩ : DyadicInterval 40)) (minus:=(⟨-113231906368,-113231906304⟩ : DyadicInterval 40))
    (lc5 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc6 lc7 (by decide) hx
theorem ew14_ok (x : ℝ) (hx : (⟨107601723392,107601723392⟩ : DyadicInterval 40).Contains x) : (⟨756849822676,756849842006⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨107601723392,107601723392⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨102656719744,102656719808⟩ : DyadicInterval 40)) (minus:=(⟨-113237717952,-113237717888⟩ : DyadicInterval 40))
    (lc8 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc9 lc10 (by decide) hx
theorem ew21_ok (x : ℝ) (hx : (⟨133023399936,133023399936⟩ : DyadicInterval 40).Contains x) : (⟨754056780564,754056799894⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨133023399936,133023399936⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨125571858624,125571858688⟩ : DyadicInterval 40)) (minus:=(⟨-141784517120,-141784517056⟩ : DyadicInterval 40))
    (lc13 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc14 lc15 (by decide) hx
theorem ew24_ok (x : ℝ) (hx : (⟨133028642816,133028642816⟩ : DyadicInterval 40).Contains x) : (⟨754056143131,754056162461⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨133028642816,133028642816⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨125576535616,125576535680⟩ : DyadicInterval 40)) (minus:=(⟨-141790481600,-141790481536⟩ : DyadicInterval 40))
    (lc16 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc17 lc18 (by decide) hx
theorem ew41_ok (x : ℝ) (hx : (⟨106665345024,106665345024⟩ : DyadicInterval 40).Contains x) : (⟨756941351363,756941370693⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨106665345024,106665345024⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨101803478848,101803478912⟩ : DyadicInterval 40)) (minus:=(⟨-112200251520,-112200251456⟩ : DyadicInterval 40))
    (lc33 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc34 lc35 (by decide) hx
theorem ew44_ok (x : ℝ) (hx : (⟨108537053184,108537053184⟩ : DyadicInterval 40).Contains x) : (⟨756757592731,756757612061⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨108537053184,108537053184⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨103508344576,103508344640⟩ : DyadicInterval 40)) (minus:=(⟨-114275000832,-114275000768⟩ : DyadicInterval 40))
    (lc36 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc37 lc38 (by decide) hx
theorem ew51_ok (x : ℝ) (hx : (⟨131951755264,131951755264⟩ : DyadicInterval 40).Contains x) : (⟨754186540736,754186560065⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨131951755264,131951755264⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨124615457152,124615457216⟩ : DyadicInterval 40)) (minus:=(⟨-140566051136,-140566051072⟩ : DyadicInterval 40))
    (lc41 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc42 lc43 (by decide) hx
theorem ew54_ok (x : ℝ) (hx : (⟨134105530368,134105530368⟩ : DyadicInterval 40).Contains x) : (⟨753924675100,753924694430⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨134105530368,134105530368⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨126536774784,126536774848⟩ : DyadicInterval 40)) (minus:=(⟨-143016277120,-143016277056⟩ : DyadicInterval 40))
    (lc44 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc45 lc46 (by decide) hx
theorem bw17_ok (x : ℝ) (hx : (⟨107596480512,107601723392⟩ : DyadicInterval 40).Contains x) : (⟨767413364640,767413901984⟩ : DyadicInterval 40).Contains (Reflection.biasB x) := by
  exact ProvedTranscendental.denominator_encloses (c:=(⟨107596480512,107601723392⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (gapLog:=(⟨-10580998208,-10579962048⟩ : DyadicInterval 40))
    (lc11 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc12 (by decide) hx
theorem bw27_ok (x : ℝ) (hx : (⟨133023399936,133028642816⟩ : DyadicInterval 40).Contains x) : (⟨770229712832,770230375872⟩ : DyadicInterval 40).Contains (Reflection.biasB x) := by
  exact ProvedTranscendental.denominator_encloses (c:=(⟨133023399936,133028642816⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (gapLog:=(⟨-16213945984,-16212658432⟩ : DyadicInterval 40))
    (lc19 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc20 (by decide) hx
theorem bw47_ok (x : ℝ) (hx : (⟨106665345024,108537053184⟩ : DyadicInterval 40).Contains x) : (⟨767321769888,767506730976⟩ : DyadicInterval 40).Contains (Reflection.biasB x) := by
  exact ProvedTranscendental.denominator_encloses (c:=(⟨106665345024,108537053184⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (gapLog:=(⟨-10766656192,-10396772544⟩ : DyadicInterval 40))
    (lc39 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc40 (by decide) hx
theorem bw57_ok (x : ℝ) (hx : (⟨131951755264,134105530368⟩ : DyadicInterval 40).Contains x) : (⟨770098680576,770363154048⟩ : DyadicInterval 40).Contains (Reflection.biasB x) := by
  exact ProvedTranscendental.denominator_encloses (c:=(⟨131951755264,134105530368⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (gapLog:=(⟨-16479502336,-15950593920⟩ : DyadicInterval 40))
    (lc47 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc48 (by decide) hx
theorem brcenter33_contact (y : ℝ) (hy : (⟨7733947934565,7733948134254⟩ : DyadicInterval 40).Contains y) : (⟨107596480512,107601723392⟩ : DyadicInterval 40).Contains (Reflection.biasContact y) := by
  exact ProvedTranscendental.contact_bracket (Y:=(⟨7733947934565,7733948134254⟩ : DyadicInterval 40)) (c:=(⟨107596480512,107601723392⟩ : DyadicInterval 40)) (elo:=(⟨756850337413,756850356743⟩ : DyadicInterval 40)) (ehi:=(⟨756849822676,756849842006⟩ : DyadicInterval 40))
    (by decide) (by decide) (by decide) (by decide)
    (ew11_ok _ (DyadicContact.point_contains 40 107596480512)) (ew14_ok _ (DyadicContact.point_contains 40 107601723392))
    (by decide) (by decide) hy
theorem brcenter33_jet (y : ℝ) (hy : (⟨7733947934565,7733948134254⟩ : DyadicInterval 40).Contains y) : (⟨⟨107596480512,107601723392⟩,⟨-15087215588,-15085734814⟩,⟨4200930542,4201562125⟩⟩ : DyadicJetEnclosure 40).Contains reflectionContactJet y := by
  exact ProvedTranscendental.contact_jet (c:=(⟨107596480512,107601723392⟩ : DyadicInterval 40)) (B:=(⟨767413364640,767413901984⟩ : DyadicInterval 40)) (by decide) brcenter33_contact bw17_ok (by decide) (by decide) (by decide) hy
theorem brcenter39_contact (y : ℝ) (hy : (⟨6232549464204,6232549625163⟩ : DyadicInterval 40).Contains y) : (⟨133023399936,133028642816⟩ : DyadicInterval 40).Contains (Reflection.biasContact y) := by
  exact ProvedTranscendental.contact_bracket (Y:=(⟨6232549464204,6232549625163⟩ : DyadicInterval 40)) (c:=(⟨133023399936,133028642816⟩ : DyadicInterval 40)) (elo:=(⟨754056780564,754056799894⟩ : DyadicInterval 40)) (ehi:=(⟨754056143131,754056162461⟩ : DyadicInterval 40))
    (by decide) (by decide) (by decide) (by decide)
    (ew21_ok _ (DyadicContact.point_contains 40 133023399936)) (ew24_ok _ (DyadicContact.point_contains 40 133028642816))
    (by decide) (by decide) hy
theorem brcenter39_jet (y : ℝ) (hy : (⟨6232549464204,6232549625163⟩ : DyadicInterval 40).Contains y) : (⟨⟨133023399936,133028642816⟩,⟨-22975768806,-22973938038⟩,⟨7851320462,7852289362⟩⟩ : DyadicJetEnclosure 40).Contains reflectionContactJet y := by
  exact ProvedTranscendental.contact_jet (c:=(⟨133023399936,133028642816⟩ : DyadicInterval 40)) (B:=(⟨770229712832,770230375872⟩ : DyadicInterval 40)) (by decide) brcenter39_contact bw27_ok (by decide) (by decide) (by decide) hy
theorem brwhole33_contact (y : ℝ) (hy : (⟨7666345741241,7802368895838⟩ : DyadicInterval 40).Contains y) : (⟨106665345024,108537053184⟩ : DyadicInterval 40).Contains (Reflection.biasContact y) := by
  exact ProvedTranscendental.contact_bracket (Y:=(⟨7666345741241,7802368895838⟩ : DyadicInterval 40)) (c:=(⟨106665345024,108537053184⟩ : DyadicInterval 40)) (elo:=(⟨756941351363,756941370693⟩ : DyadicInterval 40)) (ehi:=(⟨756757592731,756757612061⟩ : DyadicInterval 40))
    (by decide) (by decide) (by decide) (by decide)
    (ew41_ok _ (DyadicContact.point_contains 40 106665345024)) (ew44_ok _ (DyadicContact.point_contains 40 108537053184))
    (by decide) (by decide) hy
theorem brwhole33_jet (y : ℝ) (hy : (⟨7666345741241,7802368895838⟩ : DyadicInterval 40).Contains y) : (⟨⟨106665345024,108537053184⟩,⟨-15352479724,-14823968793⟩,⟨4089744130,4315152136⟩⟩ : DyadicJetEnclosure 40).Contains reflectionContactJet y := by
  exact ProvedTranscendental.contact_jet (c:=(⟨106665345024,108537053184⟩ : DyadicInterval 40)) (B:=(⟨767321769888,767506730976⟩ : DyadicInterval 40)) (by decide) brwhole33_contact bw47_ok (by decide) (by decide) (by decide) hy
theorem brwhole39_contact (y : ℝ) (hy : (⟨6181422917498,6284260920619⟩ : DyadicInterval 40).Contains y) : (⟨131951755264,134105530368⟩ : DyadicInterval 40).Contains (Reflection.biasContact y) := by
  exact ProvedTranscendental.contact_bracket (Y:=(⟨6181422917498,6284260920619⟩ : DyadicInterval 40)) (c:=(⟨131951755264,134105530368⟩ : DyadicInterval 40)) (elo:=(⟨754186540736,754186560065⟩ : DyadicInterval 40)) (ehi:=(⟨753924675100,753924694430⟩ : DyadicInterval 40))
    (by decide) (by decide) (by decide) (by decide)
    (ew51_ok _ (DyadicContact.point_contains 40 131951755264)) (ew54_ok _ (DyadicContact.point_contains 40 134105530368))
    (by decide) (by decide) hy
theorem brwhole39_jet (y : ℝ) (hy : (⟨6181422917498,6284260920619⟩ : DyadicInterval 40).Contains y) : (⟨⟨131951755264,134105530368⟩,⟨-23353232163,-22601373943⟩,⟨7654878035,8052756626⟩⟩ : DyadicJetEnclosure 40).Contains reflectionContactJet y := by
  exact ProvedTranscendental.contact_jet (c:=(⟨131951755264,134105530368⟩ : DyadicInterval 40)) (B:=(⟨770098680576,770363154048⟩ : DyadicInterval 40)) (by decide) brwhole39_contact bw57_ok (by decide) (by decide) (by decide) hy
noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨238594023227,238594023228⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨118197499985,118197499986⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.log 3,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0
theorem centerAccepted0 : StepValid centerStep0.shape centerBoxes0 centerStep0.proposed := by
  dsimp only [StepValid,centerStep0]
  exact ⟨by decide,by decide,lc0,by decide⟩
noncomputable def centerStep1 : Instruction 40 := ⟨.mul 1 2,⟨⟨25648857496,25648857498⟩,⟨118197499985,118197499986⟩,⟨238594023227,238594023228⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1
theorem centerAccepted1 : StepValid centerStep1.shape centerBoxes1 centerStep1.proposed := by
  dsimp only [StepValid,centerStep1]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep2 : Instruction 40 := ⟨.add 4 2,⟨⟨1338105651003,1338105651004⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2
theorem centerAccepted2 : StepValid centerStep2.shape centerBoxes2 centerStep2.proposed := by
  dsimp only [StepValid,centerStep2]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep3 : Instruction 40 := ⟨.log 0,⟨⟨215931784512,215931784576⟩,⟨903460663743,903460663744⟩,⟨0,0⟩,⟨-742367020333,-742367020330⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3
theorem centerAccepted3 : StepValid centerStep3.shape centerBoxes3 centerStep3.proposed := by
  dsimp only [StepValid,centerStep3]
  exact ⟨by decide,by decide,lc1,by decide⟩
noncomputable def centerStep4 : Instruction 40 := ⟨.mul 1 0,⟨⟨262788981751,262788981830⟩,⟨1315443412286,1315443412353⟩,⟨0,0⟩,⟨903460663740,903460663747⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4
theorem centerAccepted4 : StepValid centerStep4.shape centerBoxes4 centerStep4.proposed := by
  dsimp only [StepValid,centerStep4]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep5 : Instruction 40 := ⟨.neg 5,⟨⟨-238594023228,-238594023227⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5
theorem centerAccepted5 : StepValid centerStep5.shape centerBoxes5 centerStep5.proposed := by
  dsimp only [StepValid,centerStep5]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep6 : Instruction 40 := ⟨.add 8 0,⟨⟨860917604548,860917604549⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes7 := centerStep6.proposed :: centerBoxes6
theorem centerAccepted6 : StepValid centerStep6.shape centerBoxes6 centerStep6.proposed := by
  dsimp only [StepValid,centerStep6]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep7 : Instruction 40 := ⟨.log 0,⟨⟨-268965374464,-268965374400⟩,⟨-1404229409677,-1404229409674⟩,⟨0,0⟩,⟨-1793396436371,-1793396436363⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes8 := centerStep7.proposed :: centerBoxes7
theorem centerAccepted7 : StepValid centerStep7.shape centerBoxes7 centerStep7.proposed := by
  dsimp only [StepValid,centerStep7]
  exact ⟨by decide,by decide,lc2,by decide⟩
noncomputable def centerStep8 : Instruction 40 := ⟨.mul 1 0,⟨⟨-210599888206,-210599888155⟩,⟨-830546253378,-830546253309⟩,⟨0,0⟩,⟨1404229409668,1404229409683⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes9 := centerStep8.proposed :: centerBoxes8
theorem centerAccepted8 : StepValid centerStep8.shape centerBoxes8 centerStep8.proposed := by
  dsimp only [StepValid,centerStep8]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep9 : Instruction 40 := ⟨.add 4 0,⟨⟨52189093545,52189093675⟩,⟨484897158908,484897159044⟩,⟨0,0⟩,⟨2307690073408,2307690073430⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes10 := centerStep9.proposed :: centerBoxes9
theorem centerAccepted9 : StepValid centerStep9.shape centerBoxes9 centerStep9.proposed := by
  dsimp only [StepValid,centerStep9]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep10 : Instruction 40 := ⟨.inv 13,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes11 := centerStep10.proposed :: centerBoxes10
theorem centerAccepted10 : StepValid centerStep10.shape centerBoxes10 centerStep10.proposed := by
  dsimp only [StepValid,centerStep10]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep11 : Instruction 40 := ⟨.mul 1 0,⟨⟨26094546772,26094546838⟩,⟨242448579454,242448579522⟩,⟨0,0⟩,⟨1153845036704,1153845036715⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes12 := centerStep11.proposed :: centerBoxes11
theorem centerAccepted11 : StepValid centerStep11.shape centerBoxes11 centerStep11.proposed := by
  dsimp only [StepValid,centerStep11]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep12 : Instruction 40 := ⟨.neg 0,⟨⟨-26094546838,-26094546772⟩,⟨-242448579522,-242448579454⟩,⟨0,0⟩,⟨-1153845036715,-1153845036704⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes13 := centerStep12.proposed :: centerBoxes12
theorem centerAccepted12 : StepValid centerStep12.shape centerBoxes12 centerStep12.proposed := by
  dsimp only [StepValid,centerStep12]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep13 : Instruction 40 := ⟨.add 12 0,⟨⟨736028836778,736028856108⟩,⟨-242448579522,-242448579454⟩,⟨0,0⟩,⟨-1153845036715,-1153845036704⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes14 := centerStep13.proposed :: centerBoxes13
theorem centerAccepted13 : StepValid centerStep13.shape centerBoxes13 centerStep13.proposed := by
  dsimp only [StepValid,centerStep13]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep14 : Instruction 40 := ⟨.add 16 12,⟨⟨1125160485272,1125160485274⟩,⟨118197499985,118197499986⟩,⟨238594023227,238594023228⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes15 := centerStep14.proposed :: centerBoxes14
theorem centerAccepted14 : StepValid centerStep14.shape centerBoxes14 centerStep14.proposed := by
  dsimp only [StepValid,centerStep14]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep15 : Instruction 40 := ⟨.log 0,⟨⟨25354268160,25354268224⟩,⟨115503101387,115503101389⟩,⟨233155097685,233155097687⟩,⟨-12133538285,-12133538284⟩,⟨1049954637955,1049954637960⟩,⟨-49441313948,-49441313946⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15
theorem centerAccepted15 : StepValid centerStep15.shape centerBoxes15 centerStep15.proposed := by
  dsimp only [StepValid,centerStep15]
  exact ⟨by decide,by decide,lc3,by decide⟩
noncomputable def centerStep16 : Instruction 40 := ⟨.mul 1 0,⟨⟨25945719850,25945719917⟩,⟨120923083811,120923083822⟩,⟨244095899416,244095899434⟩,⟨12416583398,12416583401⟩,⟨1149930068930,1149930069007⟩,⟨50594656195,50594656200⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16
theorem centerAccepted16 : StepValid centerStep16.shape centerBoxes16 centerStep16.proposed := by
  dsimp only [StepValid,centerStep16]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep17 : Instruction 40 := ⟨.neg 15,⟨⟨-25648857498,-25648857496⟩,⟨-118197499986,-118197499985⟩,⟨-238594023228,-238594023227⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17
theorem centerAccepted17 : StepValid centerStep17.shape centerBoxes17 centerStep17.proposed := by
  dsimp only [StepValid,centerStep17]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep18 : Instruction 40 := ⟨.add 20 0,⟨⟨1073862770278,1073862770280⟩,⟨-118197499986,-118197499985⟩,⟨-238594023228,-238594023227⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18
theorem centerAccepted18 : StepValid centerStep18.shape centerBoxes18 centerStep18.proposed := by
  dsimp only [StepValid,centerStep18]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep19 : Instruction 40 := ⟨.log 0,⟨⟨-25952754816,-25952754752⟩,⟨-121020608225,-121020608223⟩,⟨-244292762649,-244292762647⟩,⟨-13320448139,-13320448137⟩,⟨-1152661818330,-1152661818325⟩,⟨-54277692364,-54277692362⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19
theorem centerAccepted19 : StepValid centerStep19.shape centerBoxes19 centerStep19.proposed := by
  dsimp only [StepValid,centerStep19]
  exact ⟨by decide,by decide,lc4,by decide⟩
noncomputable def centerStep20 : Instruction 40 := ⟨.mul 1 0,⟨⟨-25347341929,-25347341865⟩,⟨-115407578852,-115407578841⟩,⟨-232962275448,-232962275430⟩,⟨13009715381,13009715386⟩,⟨-1047297401044,-1047297400970⟩,⟨53011529492,53011529497⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20
theorem centerAccepted20 : StepValid centerStep20.shape centerBoxes20 centerStep20.proposed := by
  dsimp only [StepValid,centerStep20]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep21 : Instruction 40 := ⟨.add 4 0,⟨⟨598377921,598378052⟩,⟨5515504959,5515504981⟩,⟨11133623968,11133624004⟩,⟨25426298779,25426298787⟩,⟨102632667886,102632668037⟩,⟨103606185687,103606185697⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21
theorem centerAccepted21 : StepValid centerStep21.shape centerBoxes21 centerStep21.proposed := by
  dsimp only [StepValid,centerStep21]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep22 : Instruction 40 := ⟨.mul 0 11,⟨⟨299188960,299189026⟩,⟨2757752479,2757752491⟩,⟨5566811984,5566812002⟩,⟨12713149389,12713149394⟩,⟨51316333943,51316334019⟩,⟨51803092843,51803092849⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22
theorem centerAccepted22 : StepValid centerStep22.shape centerBoxes22 centerStep22.proposed := by
  dsimp only [StepValid,centerStep22]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep23 : Instruction 40 := ⟨.neg 0,⟨⟨-299189026,-299188960⟩,⟨-2757752491,-2757752479⟩,⟨-5566812002,-5566811984⟩,⟨-12713149394,-12713149389⟩,⟨-51316334019,-51316333943⟩,⟨-51803092849,-51803092843⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23
theorem centerAccepted23 : StepValid centerStep23.shape centerBoxes23 centerStep23.proposed := by
  dsimp only [StepValid,centerStep23]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep24 : Instruction 40 := ⟨.add 23 0,⟨⟨761824194590,761824213920⟩,⟨-2757752491,-2757752479⟩,⟨-5566812002,-5566811984⟩,⟨-12713149394,-12713149389⟩,⟨-51316334019,-51316333943⟩,⟨-51803092849,-51803092843⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24
theorem centerAccepted24 : StepValid centerStep24.shape centerBoxes24 centerStep24.proposed := by
  dsimp only [StepValid,centerStep24]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep25 : Instruction 40 := ⟨.add 11 0,⟨⟨1497853031368,1497853070028⟩,⟨-245206332013,-245206331933⟩,⟨-5566812002,-5566811984⟩,⟨-1166558186109,-1166558186093⟩,⟨-51316334019,-51316333943⟩,⟨-51803092849,-51803092843⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25
theorem centerAccepted25 : StepValid centerStep25.shape centerBoxes25 centerStep25.proposed := by
  dsimp only [StepValid,centerStep25]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep26 : Instruction 40 := ⟨.mul 0 15,⟨⟨748926515684,748926535014⟩,⟨-122603166007,-122603165966⟩,⟨-2783406001,-2783405992⟩,⟨-583279093055,-583279093046⟩,⟨-25658167010,-25658166971⟩,⟨-25901546425,-25901546421⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26
theorem centerAccepted26 : StepValid centerStep26.shape centerBoxes26 centerStep26.proposed := by
  dsimp only [StepValid,centerStep26]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep27 : Instruction 40 := ⟨.neg 28,⟨⟨-118197499986,-118197499985⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27
theorem centerAccepted27 : StepValid centerStep27.shape centerBoxes27 centerStep27.proposed := by
  dsimp only [StepValid,centerStep27]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep28 : Instruction 40 := ⟨.add 30 0,⟨⟨981314127790,981314127791⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28
theorem centerAccepted28 : StepValid centerStep28.shape centerBoxes28 centerStep28.proposed := by
  dsimp only [StepValid,centerStep28]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep29 : Instruction 40 := ⟨.mul 29 0,⟨⟨212945165730,212945165732⟩,⟨981314127790,981314127791⟩,⟨-238594023228,-238594023227⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29
theorem centerAccepted29 : StepValid centerStep29.shape centerBoxes29 centerStep29.proposed := by
  dsimp only [StepValid,centerStep29]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep30 : Instruction 40 := ⟨.mul 0 19,⟨⟨106472582865,106472582866⟩,⟨490657063895,490657063896⟩,⟨-119297011614,-119297011613⟩,⟨0,0⟩,⟨-549755813888,-549755813888⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30
theorem centerAccepted30 : StepValid centerStep30.shape centerBoxes30 centerStep30.proposed := by
  dsimp only [StepValid,centerStep30]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep31 : Instruction 40 := ⟨.inv 0,⟨⟨11354339183601,11354339183708⟩,⟨-52324143703938,-52324143702844⟩,⟨12721948664932,12721948665279⟩,⟨482250172372889,482250172388495⟩,⟨-58626491546798,-58626491541153⟩,⟨28508568436448,28508568437733⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31
theorem centerAccepted31 : StepValid centerStep31.shape centerBoxes31 centerStep31.proposed := by
  dsimp only [StepValid,centerStep31]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep32 : Instruction 40 := ⟨.mul 5 0,⟨⟨7733947934565,7733948134254⟩,⟨-36906401486345,-36906400565277⟩,⟨8636744451465,8636744675455⟩,⟨334127802462516,334127810955660⟩,⟨-41484216630368,-41484215594485⟩,⟨19086571397779,19086571900108⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32
theorem centerAccepted32 : StepValid centerStep32.shape centerBoxes32 centerStep32.proposed := by
  dsimp only [StepValid,centerStep32]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep33 : Instruction 40 := ⟨.contact 0,⟨⟨107596480512,107601723392⟩,⟨506370426471,506420143031⟩,⟨-118511187700,-118499553037⟩,⟨148322855260,149484793875⟩,⟨-538624114149,-538401648237⟩,⟨-2694468294,-2629772947⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33
theorem centerAccepted33 : StepValid centerStep33.shape centerBoxes33 centerStep33.proposed := by
  dsimp only [StepValid,centerStep33]
  exact ⟨by decide,by decide,(⟨⟨107596480512,107601723392⟩,⟨-15087215588,-15085734814⟩,⟨4200930542,4201562125⟩⟩ : DyadicJetEnclosure 40),brcenter33_jet,by decide⟩
noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 35,⟨⟨1217709127761,1217709127762⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34
theorem centerAccepted34 : StepValid centerStep34.shape centerBoxes34 centerStep34.proposed := by
  dsimp only [StepValid,centerStep34]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep35 : Instruction 40 := ⟨.mul 35 0,⟨⟨264242880723,264242880726⟩,⟨1217709127761,1217709127762⟩,⟨238594023227,238594023228⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35
theorem centerAccepted35 : StepValid centerStep35.shape centerBoxes35 centerStep35.proposed := by
  dsimp only [StepValid,centerStep35]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep36 : Instruction 40 := ⟨.mul 0 25,⟨⟨132121440361,132121440363⟩,⟨608854563880,608854563881⟩,⟨119297011613,119297011614⟩,⟨0,0⟩,⟨549755813888,549755813888⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36
theorem centerAccepted36 : StepValid centerStep36.shape centerBoxes36 centerStep36.proposed := by
  dsimp only [StepValid,centerStep36]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep37 : Instruction 40 := ⟨.inv 0,⟨⟨9150110809367,9150110809506⟩,⟨-42166409260775,-42166409259423⟩,⟨-8261951069626,-8261951069305⟩,⟨388630500083789,388630500102787⟩,⟨38073507229842,38073507235237⟩,⟨14920001930844,14920001931776⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37
theorem centerAccepted37 : StepValid centerStep37.shape centerBoxes37 centerStep37.proposed := by
  dsimp only [StepValid,centerStep37]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep38 : Instruction 40 := ⟨.mul 11 0,⟨⟨6232549464204,6232549625163⟩,⟨-29741727608976,-29741726866389⟩,⟨-5650747753287,-5650747607741⟩,⟨269263262932515,269263269781384⟩,⟨26748049670049,26748050344100⟩,⟨9988958271025,9988958534138⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38
theorem centerAccepted38 : StepValid centerStep38.shape centerBoxes38 centerStep38.proposed := by
  dsimp only [StepValid,centerStep38]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep39 : Instruction 40 := ⟨.contact 0,⟨⟨133023399936,133028642816⟩,⟨621443714564,621493252252⟩,⟨118070534343,118079946297⟩,⟨118189767648,119347484466⟩,⟨532542035969,532721337885⟩,⟨-1358403586,-1316163819⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39
theorem centerAccepted39 : StepValid centerStep39.shape centerBoxes39 centerStep39.proposed := by
  dsimp only [StepValid,centerStep39]
  exact ⟨by decide,by decide,(⟨⟨133023399936,133028642816⟩,⟨-22975768806,-22973938038⟩,⟨7851320462,7852289362⟩⟩ : DyadicJetEnclosure 40),brcenter39_jet,by decide⟩
noncomputable def centerStep40 : Instruction 40 := ⟨.inv 33,⟨⟨1404229409674,1404229409677⟩,⟨1793396436363,1793396436371⟩,⟨0,0⟩,⟨4580833809350,4580833809382⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40
theorem centerAccepted40 : StepValid centerStep40.shape centerBoxes40 centerStep40.proposed := by
  dsimp only [StepValid,centerStep40]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep41 : Instruction 40 := ⟨.mul 38 0,⟨⟨1708947191572,1708947191578⟩,⟨3586792872727,3586792872742⟩,⟨0,0⟩,⟨9161667618703,9161667618763⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41
theorem centerAccepted41 : StepValid centerStep41.shape centerBoxes41 centerStep41.proposed := by
  dsimp only [StepValid,centerStep41]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep42 : Instruction 40 := ⟨.log 0,⟨⟨484897158976,484897159040⟩,⟨2307690073410,2307690073430⟩,⟨0,0⟩,⟨1051029415952,1051029416113⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42
theorem centerAccepted42 : StepValid centerStep42.shape centerBoxes42 centerStep42.proposed := by
  dsimp only [StepValid,centerStep42]
  exact ⟨by decide,by decide,lc21,by decide⟩
noncomputable def centerStep43 : Instruction 40 := ⟨.mul 0 32,⟨⟨242448579488,242448579520⟩,⟨1153845036705,1153845036715⟩,⟨0,0⟩,⟨525514707976,525514708057⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43
theorem centerAccepted43 : StepValid centerStep43.shape centerBoxes43 centerStep43.proposed := by
  dsimp only [StepValid,centerStep43]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep44 : Instruction 40 := ⟨.mul 47 44,⟨⟨477188046454,477188046456⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44
theorem centerAccepted44 : StepValid centerStep44.shape centerBoxes44 centerStep44.proposed := by
  dsimp only [StepValid,centerStep44]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 43,⟨⟨11131604153,11131604155⟩,⟨102595429985,102595429991⟩,⟨103549806080,103549806082⟩,⟨472789999940,472789999944⟩,⟨954376092908,954376092912⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45
theorem centerAccepted45 : StepValid centerStep45.shape centerBoxes45 centerStep45.proposed := by
  dsimp only [StepValid,centerStep45]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep46 : Instruction 40 := ⟨.mul 46 46,⟨⟨51774903040,51774903041⟩,⟨477188046454,477188046456⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46
theorem centerAccepted46 : StepValid centerStep46.shape centerBoxes46 centerStep46.proposed := by
  dsimp only [StepValid,centerStep46]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep47 : Instruction 40 := ⟨.neg 0,⟨⟨-51774903041,-51774903040⟩,⟨-477188046456,-477188046454⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47
theorem centerAccepted47 : StepValid centerStep47.shape centerBoxes47 centerStep47.proposed := by
  dsimp only [StepValid,centerStep47]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep48 : Instruction 40 := ⟨.add 50 0,⟨⟨1047736724735,1047736724736⟩,⟨-477188046456,-477188046454⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48
theorem centerAccepted48 : StepValid centerStep48.shape centerBoxes48 centerStep48.proposed := by
  dsimp only [StepValid,centerStep48]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep49 : Instruction 40 := ⟨.mul 0 0,⟨⟨998399850103,998399850106⟩,⟨-909435477074,-909435477068⟩,⟨0,0⟩,⟨-3776747674623,-3776747674615⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49
theorem centerAccepted49 : StepValid centerStep49.shape centerBoxes49 centerStep49.proposed := by
  dsimp only [StepValid,centerStep49]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep50 : Instruction 40 := ⟨.inv 0,⟨⟨1210863382527,1210863382532⟩,⟨1102967030528,1102967030546⟩,⟨0,0⟩,⟨6589824866985,6589824867092⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50
theorem centerAccepted50 : StepValid centerStep50.shape centerBoxes50 centerStep50.proposed := by
  dsimp only [StepValid,centerStep50]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep51 : Instruction 40 := ⟨.mul 5 0,⟨⟨12258944350,12258944353⟩,⟨124152249336,124152249348⟩,⟨114036691638,114036691642⟩,⟨793223238288,793223238326⟩,⟨1154904645031,1154904645046⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51
theorem centerAccepted51 : StepValid centerStep51.shape centerBoxes51 centerStep51.proposed := by
  dsimp only [StepValid,centerStep51]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep52 : Instruction 40 := ⟨.add 54 18,⟨⟨1207108108288,1207113351168⟩,⟨506370426471,506420143031⟩,⟨-118511187700,-118499553037⟩,⟨148322855260,149484793875⟩,⟨-538624114149,-538401648237⟩,⟨-2694468294,-2629772947⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52
theorem centerAccepted52 : StepValid centerStep52.shape centerBoxes52 centerStep52.proposed := by
  dsimp only [StepValid,centerStep52]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep53 : Instruction 40 := ⟨.log 0,⟨⟨102651944192,102656719808⟩,⟨461232717977,461280006306⟩,⟨-107947604696,-107936538291⟩,⟨-58420194998,-57321563980⟩,⟨-445335292903,-445121241748⟩,⟨-13052350452,-12991238529⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53
theorem centerAccepted53 : StepValid centerStep53.shape centerBoxes53 centerStep53.proposed := by
  dsimp only [StepValid,centerStep53]
  exact ⟨by decide,by decide,lc22,by decide⟩
noncomputable def centerStep54 : Instruction 40 := ⟨.mul 1 0,⟨⟨112697302179,112703034636⟩,⟨553643678754,553704635393⟩,⟨-129576587502,-129562322451⟩,⟨374543604547,375944425726⟩,⟨-638644674290,-638364488517⟩,⟨8684393211,8762269330⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54
theorem centerAccepted54 : StepValid centerStep54.shape centerBoxes54 centerStep54.proposed := by
  dsimp only [StepValid,centerStep54]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep55 : Instruction 40 := ⟨.neg 21,⟨⟨-107601723392,-107596480512⟩,⟨-506420143031,-506370426471⟩,⟨118499553037,118511187700⟩,⟨-149484793875,-148322855260⟩,⟨538401648237,538624114149⟩,⟨2629772947,2694468294⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55
theorem centerAccepted55 : StepValid centerStep55.shape centerBoxes55 centerStep55.proposed := by
  dsimp only [StepValid,centerStep55]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep56 : Instruction 40 := ⟨.add 58 0,⟨⟨991909904384,991915147264⟩,⟨-506420143031,-506370426471⟩,⟨118499553037,118511187700⟩,⟨-149484793875,-148322855260⟩,⟨538401648237,538624114149⟩,⟨2629772947,2694468294⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56
theorem centerAccepted56 : StepValid centerStep56.shape centerBoxes56 centerStep56.proposed := by
  dsimp only [StepValid,centerStep56]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep57 : Instruction 40 := ⟨.log 0,⟨⟨-113237717952,-113231906304⟩,⟨-561356261634,-561298185033⟩,⟨131353611052,131367202124⟩,⟨-452301550139,-450953397161⟩,⟨663859664319,664123294753⟩,⟨-12780427379,-12705451020⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57
theorem centerAccepted57 : StepValid centerStep57.shape centerBoxes57 centerStep57.proposed := by
  dsimp only [StepValid,centerStep57]
  exact ⟨by decide,by decide,lc23,by decide⟩
noncomputable def centerStep58 : Instruction 40 := ⟨.mul 1 0,⟨⟨-102156452775,-102150669913⟩,⟨-454274859514,-454211992951⟩,⟨106293565597,106308277604⟩,⟨124236724877,125679810012⟩,⟨422407916683,422699070112⟩,⟨16505940449,16586026858⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58
theorem centerAccepted58 : StepValid centerStep58.shape centerBoxes58 centerStep58.proposed := by
  dsimp only [StepValid,centerStep58]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨10540849404,10552364723⟩,⟨99368819240,99492642442⟩,⟨-23283021905,-23254044847⟩,⟨498780329424,501624235738⟩,⟨-216236757607,-215665418405⟩,⟨25190333660,25348296188⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59
theorem centerAccepted59 : StepValid centerStep59.shape centerBoxes59 centerStep59.proposed := by
  dsimp only [StepValid,centerStep59]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep60 : Instruction 40 := ⟨.mul 0 49,⟨⟨5270424702,5276182362⟩,⟨49684409620,49746321221⟩,⟨-11641510953,-11627022423⟩,⟨249390164712,250812117869⟩,⟨-108118378804,-107832709202⟩,⟨12595166830,12674148094⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60
theorem centerAccepted60 : StepValid centerStep60.shape centerBoxes60 centerStep60.proposed := by
  dsimp only [StepValid,centerStep60]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep61 : Instruction 40 := ⟨.neg 0,⟨⟨-5276182362,-5270424702⟩,⟨-49746321221,-49684409620⟩,⟨11627022423,11641510953⟩,⟨-250812117869,-249390164712⟩,⟨107832709202,108118378804⟩,⟨-12674148094,-12595166830⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61
theorem centerAccepted61 : StepValid centerStep61.shape centerBoxes61 centerStep61.proposed := by
  dsimp only [StepValid,centerStep61]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep62 : Instruction 40 := ⟨.add 61 0,⟨⟨756847201254,756852978178⟩,⟨-49746321221,-49684409620⟩,⟨11627022423,11641510953⟩,⟨-250812117869,-249390164712⟩,⟨107832709202,108118378804⟩,⟨-12674148094,-12595166830⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62
theorem centerAccepted62 : StepValid centerStep62.shape centerBoxes62 centerStep62.proposed := by
  dsimp only [StepValid,centerStep62]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep63 : Instruction 40 := ⟨.mul 29 29,⟨⟨10529222544,10530248689⟩,⟨99105228806,99119788776⟩,⟨-23195767496,-23192360184⟩,⟨495438191153,495758618327⟩,⟨-214592247302,-214522136338⟩,⟨25015132700,25032836305⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63
theorem centerAccepted63 : StepValid centerStep63.shape centerBoxes63 centerStep63.proposed := by
  dsimp only [StepValid,centerStep63]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep64 : Instruction 40 := ⟨.neg 0,⟨⟨-10530248689,-10529222544⟩,⟨-99119788776,-99105228806⟩,⟨23192360184,23195767496⟩,⟨-495758618327,-495438191153⟩,⟨214522136338,214592247302⟩,⟨-25032836305,-25015132700⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64
theorem centerAccepted64 : StepValid centerStep64.shape centerBoxes64 centerStep64.proposed := by
  dsimp only [StepValid,centerStep64]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep65 : Instruction 40 := ⟨.add 67 0,⟨⟨1088981379087,1088982405232⟩,⟨-99119788776,-99105228806⟩,⟨23192360184,23195767496⟩,⟨-495758618327,-495438191153⟩,⟨214522136338,214592247302⟩,⟨-25032836305,-25015132700⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65
theorem centerAccepted65 : StepValid centerStep65.shape centerBoxes65 centerStep65.proposed := by
  dsimp only [StepValid,centerStep65]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep66 : Instruction 40 := ⟨.log 0,⟨⟨-10580998208,-10579962048⟩,⟨-100078258816,-100063463763⟩,⟨23416603955,23420066282⟩,⟨-509661700333,-509335010210⟩,⟨218727400981,218799024243⟩,⟨-25773756600,-25755710516⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66
theorem centerAccepted66 : StepValid centerStep66.shape centerBoxes66 centerStep66.proposed := by
  dsimp only [StepValid,centerStep66]
  exact ⟨by decide,by decide,lc12,by decide⟩
noncomputable def centerStep67 : Instruction 40 := ⟨.mul 0 56,⟨⟨-5290499104,-5289981024⟩,⟨-50039129408,-50031731881⟩,⟨11708301977,11710033141⟩,⟨-254830850167,-254667505105⟩,⟨109363700490,109399512122⟩,⟨-12886878300,-12877855258⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67
theorem centerAccepted67 : StepValid centerStep67.shape centerBoxes67 centerStep67.proposed := by
  dsimp only [StepValid,centerStep67]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep68 : Instruction 40 := ⟨.neg 0,⟨⟨5289981024,5290499104⟩,⟨50031731881,50039129408⟩,⟨-11710033141,-11708301977⟩,⟨254667505105,254830850167⟩,⟨-109399512122,-109363700490⟩,⟨12877855258,12886878300⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68
theorem centerAccepted68 : StepValid centerStep68.shape centerBoxes68 centerStep68.proposed := by
  dsimp only [StepValid,centerStep68]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep69 : Instruction 40 := ⟨.add 68 0,⟨⟨767413364640,767413901984⟩,⟨50031731881,50039129408⟩,⟨-11710033141,-11708301977⟩,⟨254667505105,254830850167⟩,⟨-109399512122,-109363700490⟩,⟨12877855258,12886878300⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69
theorem centerAccepted69 : StepValid centerStep69.shape centerBoxes69 centerStep69.proposed := by
  dsimp only [StepValid,centerStep69]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep70 : Instruction 40 := ⟨.mul 73 0,⟨⟨1534826729280,1534827803968⟩,⟨100063463762,100078258816⟩,⟨-23420066282,-23416603954⟩,⟨509335010210,509661700334⟩,⟨-218799024244,-218727400980⟩,⟨25755710516,25773756600⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70
theorem centerAccepted70 : StepValid centerStep70.shape centerBoxes70 centerStep70.proposed := by
  dsimp only [StepValid,centerStep70]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep71 : Instruction 40 := ⟨.add 0 6,⟨⟨1524296480591,1524298581424⟩,⟨943674986,973030010⟩,⟨-227706098,-220836458⟩,⟨13576391883,14223509181⟩,⟨-4276887906,-4135153678⟩,⟨722874211,758623900⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71
theorem centerAccepted71 : StepValid centerStep71.shape centerBoxes71 centerStep71.proposed := by
  dsimp only [StepValid,centerStep71]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep72 : Instruction 40 := ⟨.mul 9 0,⟨⟨1049247225834,1049256680730⟩,⟨-68315811493,-68209674338⟩,⟨15962258949,15987097120⟩,⟨-338454001939,-336033933262⟩,⟨146568698290,147063171455⟩,⟨-17077929738,-16943647145⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72
theorem centerAccepted72 : StepValid centerStep72.shape centerBoxes72 centerStep72.proposed := by
  dsimp only [StepValid,centerStep72]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep73 : Instruction 40 := ⟨.mul 39 29,⟨⟨23725637091,23726793180⟩,⟨224571027136,224587491900⟩,⟨-26132392227,-26129826713⟩,⟨1146918480329,1147281546990⟩,⟨-243137216871,-243075952250⟩,⟨-594145614,-579879920⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73
theorem centerAccepted73 : StepValid centerStep73.shape centerBoxes73 centerStep73.proposed := by
  dsimp only [StepValid,centerStep73]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep74 : Instruction 40 := ⟨.add 11 0,⟨⟨780572838345,780579771358⟩,⟨174824705915,174903082280⟩,⟨-14505369804,-14488315760⟩,⟨896106362460,897891382278⟩,⟨-135304507669,-134957573446⟩,⟨-13268293708,-13175046750⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74
theorem centerAccepted74 : StepValid centerStep74.shape centerBoxes74 centerStep74.proposed := by
  dsimp only [StepValid,centerStep74]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep75 : Instruction 40 := ⟨.mul 0 0,⟨⟨554149624769,554159468678⟩,⟨248225509328,248338998020⟩,⟨-20595686230,-20571289052⟩,⟨1327934959776,1330530609403⟩,⟨-196729152866,-196227359450⟩,⟨-18457377112,-18323913324⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75
theorem centerAccepted75 : StepValid centerStep75.shape centerBoxes75 centerStep75.proposed := by
  dsimp only [StepValid,centerStep75]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep76 : Instruction 40 := ⟨.mul 3 0,⟨⟨528816559822,528830719032⟩,⟨202446311272,202610851665⟩,⟨-11609410253,-11573289815⟩,⟨1065785565874,1069558757535⟩,⟨-108987467680,-108245633673⟩,⟨-26820046685,-26623055795⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76
theorem centerAccepted76 : StepValid centerStep76.shape centerBoxes76 centerStep76.proposed := by
  dsimp only [StepValid,centerStep76]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep77 : Instruction 40 := ⟨.mul 80 50,⟨⟨1497853031368,1497853070028⟩,⟨-245206332014,-245206331932⟩,⟨-5566812002,-5566811984⟩,⟨-1166558186110,-1166558186092⟩,⟨-51316334020,-51316333942⟩,⟨-51803092850,-51803092842⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77
theorem centerAccepted77 : StepValid centerStep77.shape centerBoxes77 centerStep77.proposed := by
  dsimp only [StepValid,centerStep77]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep78 : Instruction 40 := ⟨.mul 12 12,⟨⟨1078551980752,1078554013389⟩,⟨-196341181414,-196312155348⟩,⟨45940484374,45947277030⟩,⟨-964156363306,-963515471314⟩,⟨420753080650,420893588762⟩,⟨-48607821953,-48572419610⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78
theorem centerAccepted78 : StepValid centerStep78.shape centerBoxes78 centerStep78.proposed := by
  dsimp only [StepValid,centerStep78]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep79 : Instruction 40 := ⟨.mul 1 0,⟨⟨1469299926481,1469302733445⟩,⟨-508006009893,-507966007698⟩,⟨57123530818,57132796308⟩,⟨-2370221968880,-2369333751551⟩,⟨513596304599,513789488878⟩,⟨-117498865390,-117450470882⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79
theorem centerAccepted79 : StepValid centerStep79.shape centerBoxes79 centerStep79.proposed := by
  dsimp only [StepValid,centerStep79]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep80 : Instruction 40 := ⟨.mul 10 10,⟨⟨535622595842,535623345930⟩,⟨69840133986,69850509228⟩,⟨-16346243184,-16343815176⟩,⟨360047890629,360277502378⟩,⟨-153778576236,-153728164128⟩,⟨18225769177,18238450935⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80
theorem centerAccepted80 : StepValid centerStep80.shape centerBoxes80 centerStep80.proposed := by
  dsimp only [StepValid,centerStep80]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep81 : Instruction 40 := ⟨.mul 11 0,⟨⟨373842284218,373843069514⟩,⟨73118261128,73129174566⟩,⟨-17113508327,-17110954370⟩,⟨381714634436,381956700815⟩,⟨-162112567992,-162059346235⟩,⟨19342301816,19355669585⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81
theorem centerAccepted81 : StepValid centerStep81.shape centerBoxes81 centerStep81.proposed := by
  dsimp only [StepValid,centerStep81]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep82 : Instruction 40 := ⟨.mul 2 0,⟨⟨499573107587,499575111386⟩,⟨-75016824095,-74988089670⟩,⟨-3446742377,-3440094638⟩,⟨-363377596222,-362734044373⟩,⟨-30304242664,-30163670621⟩,⟨-15881577418,-15846572155⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82
theorem centerAccepted82 : StepValid centerStep82.shape centerBoxes82 centerStep82.proposed := by
  dsimp only [StepValid,centerStep82]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep83 : Instruction 40 := ⟨.inv 0,⟨⟨2419908021960,2419917728266⟩,⟨363237230214,363379332852⟩,⟨16663585557,16695920690⟩,⟨1866105685711,1869322027057⟩,⟨151113311457,151807058475⟩,⟨76989215083,77160285925⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83
theorem centerAccepted83 : StepValid centerStep83.shape centerBoxes83 centerStep83.proposed := by
  dsimp only [StepValid,centerStep83]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep84 : Instruction 40 := ⟨.mul 7 0,⟨⟨1163868942293,1163904773637⟩,⟨620263849799,620700798898⟩,⟨-17536729227,-17441362724⟩,⟨3376956287207,3387002200422⟩,⟨-167960590276,-165969428421⟩,⟨-22352464084,-21833622495⟩⟩⟩
noncomputable def centerBoxes85 := centerStep84.proposed :: centerBoxes84
theorem centerAccepted84 : StepValid centerStep84.shape centerBoxes84 centerStep84.proposed := by
  dsimp only [StepValid,centerStep84]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep85 : Instruction 40 := ⟨.mul 36 19,⟨⟨1037702334926,1037703312753⟩,⟨-567070700915,-567056381208⟩,⟨22100255135,22103502001⟩,⟨-2564355312610,-2564035283685⟩,⟨194353540365,194421828650⟩,⟨-23854065077,-23837195116⟩⟩⟩
noncomputable def centerBoxes86 := centerStep85.proposed :: centerBoxes85
theorem centerAccepted85 : StepValid centerStep85.shape centerBoxes85 centerStep85.proposed := by
  dsimp only [StepValid,centerStep85]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep86 : Instruction 40 := ⟨.mul 0 16,⟨⟨724273050164,724274239785⟩,⟨-348572843266,-348555545396⟩,⟨4373297060,4377218301⟩,⟨-1601078384029,-1600690440999⟩,⟨39445012212,39528007165⟩,⟨-4966046775,-4945594560⟩⟩⟩
noncomputable def centerBoxes87 := centerStep86.proposed :: centerBoxes86
theorem centerAccepted86 : StepValid centerStep86.shape centerBoxes86 centerStep86.proposed := by
  dsimp only [StepValid,centerStep86]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep87 : Instruction 40 := ⟨.inv 0,⟨⟨1669154794147,1669157535740⟩,⟨803277443357,803319946753⟩,⟨-10087724390,-10078654400⟩,⟨4462085713890,4463072435272⟩,⟨-100806021378,-100605225201⟩,⟨11519278624,11566669145⟩⟩⟩
noncomputable def centerBoxes88 := centerStep87.proposed :: centerBoxes87
theorem centerAccepted87 : StepValid centerStep87.shape centerBoxes87 centerStep87.proposed := by
  dsimp only [StepValid,centerStep87]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep88 : Instruction 40 := ⟨.mul 24 0,⟨⟨15984280515,15985864550⟩,⟨158142806641,158166313844⟩,⟨-35309873384,-35304546676⟩,⟨939656561144,940186785768⟩,⟨-344592349386,-344479025686⟩,⟨38510655290,38538503107⟩⟩⟩
noncomputable def centerBoxes89 := centerStep88.proposed :: centerBoxes88
theorem centerAccepted88 : StepValid centerStep88.shape centerBoxes88 centerStep88.proposed := by
  dsimp only [StepValid,centerStep88]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep89 : Instruction 40 := ⟨.add 4 0,⟨⟨1179853222808,1179890638187⟩,⟨778406656440,778867112742⟩,⟨-52846602611,-52745909400⟩,⟨4316612848351,4327188986190⟩,⟨-512552939662,-510448454107⟩,⟨16158191206,16704880612⟩⟩⟩
noncomputable def centerBoxes90 := centerStep89.proposed :: centerBoxes89
theorem centerAccepted89 : StepValid centerStep89.shape centerBoxes89 centerStep89.proposed := by
  dsimp only [StepValid,centerStep89]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep90 : Instruction 40 := ⟨.add 38 0,⟨⟨1192112167158,1192149582540⟩,⟨902558905776,903019362090⟩,⟨61190089027,61290782242⟩,⟨5109836086639,5120412224516⟩,⟨642351705369,644456190939⟩,⟨16158191206,16704880612⟩⟩⟩
noncomputable def centerBoxes91 := centerStep90.proposed :: centerBoxes90
theorem centerAccepted90 : StepValid centerStep90.shape centerBoxes90 centerStep90.proposed := by
  dsimp only [StepValid,centerStep90]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep91 : Instruction 40 := ⟨.add 93 51,⟨⟨1232535027712,1232540270592⟩,⟨621443714564,621493252252⟩,⟨118070534343,118079946297⟩,⟨118189767648,119347484466⟩,⟨532542035969,532721337885⟩,⟨-1358403586,-1316163819⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91
theorem centerAccepted91 : StepValid centerStep91.shape centerBoxes91 centerStep91.proposed := by
  dsimp only [StepValid,centerStep91]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep92 : Instruction 40 := ⟨.log 0,⟨⟨125571858624,125576535680⟩,⟨554371006346,554417555747⟩,⟨105327126833,105335971021⟩,⟨-174125922562,-173045763622⟩,⟨421949935067,422120825093⟩,⟨-11303245771,-11263865286⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92
theorem centerAccepted92 : StepValid centerStep92.shape centerBoxes92 centerStep92.proposed := by
  dsimp only [StepValid,centerStep92]
  exact ⟨by decide,by decide,lc25,by decide⟩
noncomputable def centerStep93 : Instruction 40 := ⟨.mul 1 0,⟨⟨140764054093,140769895795⟩,⟨692414256206,692477382244⟩,⟨131554506547,131566500218⟩,⟨444965600710,446412576124⟩,⟨652880889946,653116700501⟩,⟨9795049730,9847781216⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93
theorem centerAccepted93 : StepValid centerStep93.shape centerBoxes93 centerStep93.proposed := by
  dsimp only [StepValid,centerStep93]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep94 : Instruction 40 := ⟨.neg 54,⟨⟨-133028642816,-133023399936⟩,⟨-621493252252,-621443714564⟩,⟨-118079946297,-118070534343⟩,⟨-119347484466,-118189767648⟩,⟨-532721337885,-532542035969⟩,⟨1316163819,1358403586⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94
theorem centerAccepted94 : StepValid centerStep94.shape centerBoxes94 centerStep94.proposed := by
  dsimp only [StepValid,centerStep94]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep95 : Instruction 40 := ⟨.add 97 0,⟨⟨966482984960,966488227840⟩,⟨-621493252252,-621443714564⟩,⟨-118079946297,-118070534343⟩,⟨-119347484466,-118189767648⟩,⟨-532721337885,-532542035969⟩,⟨1316163819,1358403586⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95
theorem centerAccepted95 : StepValid centerStep95.shape centerBoxes95 centerStep95.proposed := by
  dsimp only [StepValid,centerStep95]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep96 : Instruction 40 := ⟨.log 0,⟨⟨-141790481600,-141784517056⟩,⟨-707036821206,-706976629915⟩,⟨-134332705264,-134321269176⟩,⟨-590432081341,-589036876412⟩,⟨-692428305166,-692206330111⟩,⟨-14914767540,-14863911396⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96
theorem centerAccepted96 : StepValid centerStep96.shape centerBoxes96 centerStep96.proposed := by
  dsimp only [StepValid,centerStep96]
  exact ⟨by decide,by decide,lc26,by decide⟩
noncomputable def centerStep97 : Instruction 40 := ⟨.mul 1 0,⟨⟨-124636090992,-124630171981⟩,⟨-541360047827,-541294008170⟩,⟨-102855123770,-102842576528⟩,⟨295407689173,296918593160⟩,⟨-388146302851,-387896839418⟩,⟨15562556748,15617541197⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97
theorem centerAccepted97 : StepValid centerStep97.shape centerBoxes97 centerStep97.proposed := by
  dsimp only [StepValid,centerStep97]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep98 : Instruction 40 := ⟨.add 4 0,⟨⟨16127963101,16139723814⟩,⟨151054208379,151183374074⟩,⟨28699382777,28723923690⟩,⟨740373289883,743331169284⟩,⟨264734587095,265219861083⟩,⟨25357606478,25465322413⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98
theorem centerAccepted98 : StepValid centerStep98.shape centerBoxes98 centerStep98.proposed := by
  dsimp only [StepValid,centerStep98]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep99 : Instruction 40 := ⟨.mul 0 88,⟨⟨8063981550,8069861907⟩,⟨75527104189,75591687037⟩,⟨14349691388,14361961845⟩,⟨370186644941,371665584642⟩,⟨132367293547,132609930542⟩,⟨12678803239,12732661207⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99
theorem centerAccepted99 : StepValid centerStep99.shape centerBoxes99 centerStep99.proposed := by
  dsimp only [StepValid,centerStep99]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep100 : Instruction 40 := ⟨.neg 0,⟨⟨-8069861907,-8063981550⟩,⟨-75591687037,-75527104189⟩,⟨-14361961845,-14349691388⟩,⟨-371665584642,-370186644941⟩,⟨-132609930542,-132367293547⟩,⟨-12732661207,-12678803239⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100
theorem centerAccepted100 : StepValid centerStep100.shape centerBoxes100 centerStep100.proposed := by
  dsimp only [StepValid,centerStep100]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep101 : Instruction 40 := ⟨.add 100 0,⟨⟨754053521709,754059421330⟩,⟨-75591687037,-75527104189⟩,⟨-14361961845,-14349691388⟩,⟨-371665584642,-370186644941⟩,⟨-132609930542,-132367293547⟩,⟨-12732661207,-12678803239⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101
theorem centerAccepted101 : StepValid centerStep101.shape centerBoxes101 centerStep101.proposed := by
  dsimp only [StepValid,centerStep101]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep102 : Instruction 40 := ⟨.mul 62 62,⟨⟨16093713321,16094981956⟩,⟨150369588990,150387502558⟩,⟨28569309342,28572712836⟩,⟨731077843922,731471111935⟩,⟨262325090578,262394835644⟩,⟨25029193227,25043469818⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102
theorem centerAccepted102 : StepValid centerStep102.shape centerBoxes102 centerStep102.proposed := by
  dsimp only [StepValid,centerStep102]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep103 : Instruction 40 := ⟨.neg 0,⟨⟨-16094981956,-16093713321⟩,⟨-150387502558,-150369588990⟩,⟨-28572712836,-28569309342⟩,⟨-731471111935,-731077843922⟩,⟨-262394835644,-262325090578⟩,⟨-25043469818,-25029193227⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103
theorem centerAccepted103 : StepValid centerStep103.shape centerBoxes103 centerStep103.proposed := by
  dsimp only [StepValid,centerStep103]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep104 : Instruction 40 := ⟨.add 106 0,⟨⟨1083416645820,1083417914455⟩,⟨-150387502558,-150369588990⟩,⟨-28572712836,-28569309342⟩,⟨-731471111935,-731077843922⟩,⟨-262394835644,-262325090578⟩,⟨-25043469818,-25029193227⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104
theorem centerAccepted104 : StepValid centerStep104.shape centerBoxes104 centerStep104.proposed := by
  dsimp only [StepValid,centerStep104]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep105 : Instruction 40 := ⟨.log 0,⟨⟨-16213945984,-16212658432⟩,⟨-152621623798,-152603265418⟩,⟨-28997182314,-28993694307⟩,⟨-763522861668,-763117786284⟩,⟨-270317968456,-270245907268⟩,⟨-26180246112,-26165543720⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105
theorem centerAccepted105 : StepValid centerStep105.shape centerBoxes105 centerStep105.proposed := by
  dsimp only [StepValid,centerStep105]
  exact ⟨by decide,by decide,lc20,by decide⟩
noncomputable def centerStep106 : Instruction 40 := ⟨.mul 0 95,⟨⟨-8106972992,-8106329216⟩,⟨-76310811899,-76301632709⟩,⟨-14498591157,-14496847153⟩,⟨-381761430834,-381558893142⟩,⟨-135158984228,-135122953634⟩,⟨-13090123056,-13082771860⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106
theorem centerAccepted106 : StepValid centerStep106.shape centerBoxes106 centerStep106.proposed := by
  dsimp only [StepValid,centerStep106]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep107 : Instruction 40 := ⟨.neg 0,⟨⟨8106329216,8106972992⟩,⟨76301632709,76310811899⟩,⟨14496847153,14498591157⟩,⟨381558893142,381761430834⟩,⟨135122953634,135158984228⟩,⟨13082771860,13090123056⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107
theorem centerAccepted107 : StepValid centerStep107.shape centerBoxes107 centerStep107.proposed := by
  dsimp only [StepValid,centerStep107]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep108 : Instruction 40 := ⟨.add 107 0,⟨⟨770229712832,770230375872⟩,⟨76301632709,76310811899⟩,⟨14496847153,14498591157⟩,⟨381558893142,381761430834⟩,⟨135122953634,135158984228⟩,⟨13082771860,13090123056⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108
theorem centerAccepted108 : StepValid centerStep108.shape centerBoxes108 centerStep108.proposed := by
  dsimp only [StepValid,centerStep108]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep109 : Instruction 40 := ⟨.mul 112 0,⟨⟨1540459425664,1540460751744⟩,⟨152603265418,152621623798⟩,⟨28993694306,28997182314⟩,⟨763117786284,763522861668⟩,⟨270245907268,270317968456⟩,⟨26165543720,26180246112⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109
theorem centerAccepted109 : StepValid centerStep109.shape centerBoxes109 centerStep109.proposed := by
  dsimp only [StepValid,centerStep109]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep110 : Instruction 40 := ⟨.add 0 6,⟨⟨1524364443708,1524367038423⟩,⟨2215762860,2252034808⟩,⟨420981470,427872972⟩,⟨31646674349,32445017746⟩,⟨7851071624,7992877878⟩,⟨1122073902,1151052885⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110
theorem centerAccepted110 : StepValid centerStep110.shape centerBoxes110 centerStep110.proposed := by
  dsimp only [StepValid,centerStep110]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep111 : Instruction 40 := ⟨.mul 9 0,⟨⟨1045420846954,1045430805687⟩,⟨-103281010808,-103166407003⟩,⟨-19622765362,-19600991148⟩,⟨-493884681894,-491280468923⟩,⟨-178525411829,-178090414873⟩,⟨-16894260144,-16799491714⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111
theorem centerAccepted111 : StepValid centerStep111.shape centerBoxes111 centerStep111.proposed := by
  dsimp only [StepValid,centerStep111]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep112 : Instruction 40 := ⟨.mul 72 68,⟨⟨29332417719,29333573809⟩,⟨276628757646,276645182971⟩,⟨26035225647,26037301041⟩,⟨1393946318538,1394308078850⟩,⟨241333655295,241383069462⟩,⟨-299535732,-290221622⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112
theorem centerAccepted112 : StepValid centerStep112.shape centerBoxes112 centerStep112.proposed := by
  dsimp only [StepValid,centerStep112]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep113 : Instruction 40 := ⟨.add 11 0,⟨⟨783385939428,783392995139⟩,⟨201037070609,201118078782⟩,⟨11673263802,11687609653⟩,⟨1022280733896,1024121433909⟩,⟨108723724753,109015775915⟩,⟨-13032196939,-12969024861⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113
theorem centerAccepted113 : StepValid centerStep113.shape centerBoxes113 centerStep113.proposed := by
  dsimp only [StepValid,centerStep113]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 0,⟨⟨558151014132,558161068360⟩,⟨286471939796,286589955274⟩,⟨16634059156,16654651576⟩,⟨1530236216860,1532931563106⟩,⟨159196853950,159621385704⟩,⟨-18322801600,-18232006376⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114
theorem centerAccepted114 : StepValid centerStep114.shape centerBoxes114 centerStep114.proposed := by
  dsimp only [StepValid,centerStep114]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep115 : Instruction 40 := ⟨.mul 3 0,⟨⟨530692619506,530707234611⟩,⟨219948832269,220122759085⟩,⟨5854352395,5885315413⟩,⟨1150397146957,1154382176226⟩,⟨54058526616,54697518974⟩,⟨-26592315564,-26456164938⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115
theorem centerAccepted115 : StepValid centerStep115.shape centerBoxes115 centerStep115.proposed := by
  dsimp only [StepValid,centerStep115]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep116 : Instruction 40 := ⟨.mul 11 11,⟨⟨1067557267051,1067559767182⟩,⟨-296372517154,-296336867426⟩,⟨-56308979678,-56302206394⟩,⟨-1400399729909,-1399613219417⟩,⟨-509293950554,-509154034850⟩,⟨-47869140699,-47840593932⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116
theorem centerAccepted116 : StepValid centerStep116.shape centerBoxes116 centerStep116.proposed := by
  dsimp only [StepValid,centerStep116]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep117 : Instruction 40 := ⟨.mul 39 0,⟨⟨1454321944594,1454325388033⟩,⟨-641825772080,-641776638768⟩,⟨-82114168078,-82104926247⟩,⟨-2908233243693,-2907143186134⟩,⟨-729574323351,-729381891959⟩,⟨-114939202381,-114900125348⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117
theorem centerAccepted117 : StepValid centerStep117.shape centerBoxes117 centerStep117.proposed := by
  dsimp only [StepValid,centerStep117]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep118 : Instruction 40 := ⟨.mul 9 9,⟨⟨539561197482,539562126429⟩,⟨106901615526,106914567974⟩,⟨20310658182,20313119088⟩,⟨545169197443,545455969365⟩,⟨191324664922,191375792362⟩,⟨18711758801,18722165893⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118
theorem centerAccepted118 : StepValid centerStep118.shape centerBoxes118 centerStep118.proposed := by
  dsimp only [StepValid,centerStep118]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep119 : Instruction 40 := ⟨.mul 10 0,⟨⟨377973325332,377974301451⟩,⟨112330054382,112343761262⟩,⟨21342028620,21344632866⟩,⟨583980566527,584285081176⟩,⟨203154301881,203208709210⟩,⟨20063625626,20074675125⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119
theorem centerAccepted119 : StepValid centerStep119.shape centerBoxes119 centerStep119.proposed := by
  dsimp only [StepValid,centerStep119]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep120 : Instruction 40 := ⟨.mul 2 0,⟨⟨499944600507,499947075354⟩,⟨-72058887537,-72022945537⟩,⟨1032499,7793893⟩,⟨-358479081339,-357671123623⟩,⟨-2940519904,-2796678461⟩,⟨-16162163989,-16133202860⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120
theorem centerAccepted120 : StepValid centerStep120.shape centerBoxes120 centerStep120.proposed := by
  dsimp only [StepValid,centerStep120]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep121 : Instruction 40 := ⟨.inv 0,⟨⟨2418107594206,2418119564426⟩,⟨348355336285,348532628550⟩,⟨-37697308,-4993915⟩,⟨1830326568943,1834353298469⟩,⟨13515903740,14221194415⟩,⟨78031900350,78172752529⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121
theorem centerAccepted121 : StepValid centerStep121.shape centerBoxes121 centerStep121.proposed := by
  dsimp only [StepValid,centerStep121]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep122 : Instruction 40 := ⟨.mul 6 0,⟨⟨1167128951616,1167166871706⟩,⟨651861726125,652336837256⟩,⟨12857024331,12940969200⟩,⟨3552818796100,3563744593651⟩,⟨127259428120,129023244485⟩,⟨-20820960934,-20451867844⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122
theorem centerAccepted122 : StepValid centerStep122.shape centerBoxes122 centerStep122.proposed := by
  dsimp only [StepValid,centerStep122]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep123 : Instruction 40 := ⟨.mul 74 18,⟨⟨1032399639384,1032400848282⟩,⟨-613509280326,-613491659698⟩,⟨-27227252362,-27224009134⟩,⟨-2733341894413,-2732949058748⟩,⟨-237639844975,-237571907016⟩,⟨-23864197868,-23850593547⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123
theorem centerAccepted123 : StepValid centerStep123.shape centerBoxes123 centerStep123.proposed := by
  dsimp only [StepValid,centerStep123]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep124 : Instruction 40 := ⟨.mul 0 15,⟨⟨723216433262,723217902690⟩,⟨-358131460866,-358110044486⟩,⟨-5461258341,-5457316481⟩,⟨-1641652919368,-1641172797685⟩,⟨-49575912704,-49492539721⟩,⟨-5151191312,-5134558040⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124
theorem centerAccepted124 : StepValid centerStep124.shape centerBoxes124 centerStep124.proposed := by
  dsimp only [StepValid,centerStep124]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep125 : Instruction 40 := ⟨.inv 0,⟨⟨1671592773240,1671596169576⟩,⟨827709270139,827762134067⟩,⟨12613640725,12622802946⟩,⟨4612986740151,4614214919572⟩,⟨126885015246,127088029628⟩,⟨12058002628,12096772197⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125
theorem centerAccepted125 : StepValid centerStep125.shape centerBoxes125 centerStep125.proposed := by
  dsimp only [StepValid,centerStep125]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep126 : Instruction 40 := ⟨.mul 23 0,⟨⟨24467349141,24469327570⟩,⟨240722905780,240752333267⟩,⟨43618685003,43624096286⟩,⟨1405377708790,1406042588176⟩,⟨423903263128,424018620186⟩,⟨38883993112,38906910959⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126
theorem centerAccepted126 : StepValid centerStep126.shape centerBoxes126 centerStep126.proposed := by
  dsimp only [StepValid,centerStep126]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep127 : Instruction 40 := ⟨.add 4 0,⟨⟨1191596300757,1191636199276⟩,⟨892584631905,893089170523⟩,⟨56475709334,56565065486⟩,⟨4958196504890,4969787181827⟩,⟨551162691248,553041864671⟩,⟨18063032178,18455043115⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127
theorem centerAccepted127 : StepValid centerStep127.shape centerBoxes127 centerStep127.proposed := by
  dsimp only [StepValid,centerStep127]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep128 : Instruction 40 := ⟨.neg 0,⟨⟨-1191636199276,-1191596300757⟩,⟨-893089170523,-892584631905⟩,⟨-56565065486,-56475709334⟩,⟨-4969787181827,-4958196504890⟩,⟨-553041864671,-551162691248⟩,⟨-18455043115,-18063032178⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128
theorem centerAccepted128 : StepValid centerStep128.shape centerBoxes128 centerStep128.proposed := by
  dsimp only [StepValid,centerStep128]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep129 : Instruction 40 := ⟨.add 38 0,⟨⟨475967882,553281783⟩,⟨9469735253,10434730185⟩,⟨4625023541,4815072908⟩,⟨140048904812,162215719626⟩,⟨89309840698,93293499691⟩,⟨-2296851909,-1358151566⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129
theorem centerAccepted129 : StepValid centerStep129.shape centerBoxes129 centerStep129.proposed := by
  dsimp only [StepValid,centerStep129]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep130 : Instruction 40 := ⟨.mul 130 83,⟨⟨11235153959,11235153960⟩,⟨155324709120,155324709123⟩,⟨0,0⟩,⟨1431564139362,1431564139368⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130
theorem centerAccepted130 : StepValid centerStep130.shape centerBoxes130 centerStep130.proposed := by
  dsimp only [StepValid,centerStep130]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep131 : Instruction 40 := ⟨.mul 0 129,⟨⟨262088053,262088055⟩,⟨4831116201,4831116204⟩,⟨2438028409,2438028410⟩,⟨66789624919,66789624925⟩,⟨44940615837,44940615840⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131
theorem centerAccepted131 : StepValid centerStep131.shape centerBoxes131 centerStep131.proposed := by
  dsimp only [StepValid,centerStep131]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep132 : Instruction 40 := ⟨.inv 0,⟨⟨4612670423360687,4612670458560083⟩,⟨-85026183914082229,-85026182563609550⟩,⟨-42908562581207056,-42908561908734874⟩,⟨1959128598988097297,1959128692687655170⟩,⟨790941214551930523,790941264521403833⟩,⟨798298823064110078,798298841994493716⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132
theorem centerAccepted132 : StepValid centerStep132.shape centerBoxes132 centerStep132.proposed := by
  dsimp only [StepValid,centerStep132]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep133 : Instruction 40 := ⟨.mul 3 0,⟨⟨1996780130658,2321127372583⟩,⟨-3058331384729,6968766354521⟩,⟨-2188987051323,1625491883878⟩,⟨-178232625995326,201768668510656⟩,⟨-62506908231534,62177374058867⟩,⟨-39877463990162,35027627045485⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133
theorem centerAccepted133 : StepValid centerStep133.shape centerBoxes133 centerStep133.proposed := by
  dsimp only [StepValid,centerStep133]
  exact ⟨by decide,by decide⟩
noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133]
theorem centerAccepted : Accepted centerProgram centerInitial :=
  ⟨centerAccepted0,⟨centerAccepted1,⟨centerAccepted2,⟨centerAccepted3,⟨centerAccepted4,⟨centerAccepted5,⟨centerAccepted6,⟨centerAccepted7,⟨centerAccepted8,⟨centerAccepted9,⟨centerAccepted10,⟨centerAccepted11,⟨centerAccepted12,⟨centerAccepted13,⟨centerAccepted14,⟨centerAccepted15,⟨centerAccepted16,⟨centerAccepted17,⟨centerAccepted18,⟨centerAccepted19,⟨centerAccepted20,⟨centerAccepted21,⟨centerAccepted22,⟨centerAccepted23,⟨centerAccepted24,⟨centerAccepted25,⟨centerAccepted26,⟨centerAccepted27,⟨centerAccepted28,⟨centerAccepted29,⟨centerAccepted30,⟨centerAccepted31,⟨centerAccepted32,⟨centerAccepted33,⟨centerAccepted34,⟨centerAccepted35,⟨centerAccepted36,⟨centerAccepted37,⟨centerAccepted38,⟨centerAccepted39,⟨centerAccepted40,⟨centerAccepted41,⟨centerAccepted42,⟨centerAccepted43,⟨centerAccepted44,⟨centerAccepted45,⟨centerAccepted46,⟨centerAccepted47,⟨centerAccepted48,⟨centerAccepted49,⟨centerAccepted50,⟨centerAccepted51,⟨centerAccepted52,⟨centerAccepted53,⟨centerAccepted54,⟨centerAccepted55,⟨centerAccepted56,⟨centerAccepted57,⟨centerAccepted58,⟨centerAccepted59,⟨centerAccepted60,⟨centerAccepted61,⟨centerAccepted62,⟨centerAccepted63,⟨centerAccepted64,⟨centerAccepted65,⟨centerAccepted66,⟨centerAccepted67,⟨centerAccepted68,⟨centerAccepted69,⟨centerAccepted70,⟨centerAccepted71,⟨centerAccepted72,⟨centerAccepted73,⟨centerAccepted74,⟨centerAccepted75,⟨centerAccepted76,⟨centerAccepted77,⟨centerAccepted78,⟨centerAccepted79,⟨centerAccepted80,⟨centerAccepted81,⟨centerAccepted82,⟨centerAccepted83,⟨centerAccepted84,⟨centerAccepted85,⟨centerAccepted86,⟨centerAccepted87,⟨centerAccepted88,⟨centerAccepted89,⟨centerAccepted90,⟨centerAccepted91,⟨centerAccepted92,⟨centerAccepted93,⟨centerAccepted94,⟨centerAccepted95,⟨centerAccepted96,⟨centerAccepted97,⟨centerAccepted98,⟨centerAccepted99,⟨centerAccepted100,⟨centerAccepted101,⟨centerAccepted102,⟨centerAccepted103,⟨centerAccepted104,⟨centerAccepted105,⟨centerAccepted106,⟨centerAccepted107,⟨centerAccepted108,⟨centerAccepted109,⟨centerAccepted110,⟨centerAccepted111,⟨centerAccepted112,⟨centerAccepted113,⟨centerAccepted114,⟨centerAccepted115,⟨centerAccepted116,⟨centerAccepted117,⟨centerAccepted118,⟨centerAccepted119,⟨centerAccepted120,⟨centerAccepted121,⟨centerAccepted122,⟨centerAccepted123,⟨centerAccepted124,⟨centerAccepted125,⟨centerAccepted126,⟨centerAccepted127,⟨centerAccepted128,⟨centerAccepted129,⟨centerAccepted130,⟨centerAccepted131,⟨centerAccepted132,⟨centerAccepted133,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
noncomputable def centerOutput : DyadicBivariateJetEnclosure 40 := ⟨⟨1996780130658,2321127372583⟩,⟨-3058331384729,6968766354521⟩,⟨-2188987051323,1625491883878⟩,⟨-178232625995326,201768668510656⟩,⟨-62506908231534,62177374058867⟩,⟨-39877463990162,35027627045485⟩⟩
theorem centerOutput_eq : (finalBoxes centerProgram centerInitial).getD 0 (zeroBox 40)=centerOutput := rfl
noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨237494511599,239693534856⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨115448720916,120946279056⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.log 3,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0
theorem wholeAccepted0 : StepValid wholeStep0.shape wholeBoxes0 wholeStep0.proposed := by
  dsimp only [StepValid,wholeStep0]
  exact ⟨by decide,by decide,lc0,by decide⟩
noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 1 2,⟨⟨24936923717,26366288835⟩,⟨115448720916,120946279056⟩,⟨237494511599,239693534856⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1
theorem wholeAccepted1 : StepValid wholeStep1.shape wholeBoxes1 wholeStep1.proposed := by
  dsimp only [StepValid,wholeStep1]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep2 : Instruction 40 := ⟨.add 4 2,⟨⟨1337006139375,1339205162632⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2
theorem wholeAccepted2 : StepValid wholeStep2.shape wholeBoxes2 wholeStep2.proposed := by
  dsimp only [StepValid,wholeStep2]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep3 : Instruction 40 := ⟨.log 0,⟨⟨215027952512,216834874304⟩,⟨902718906219,904203641264⟩,⟨0,0⟩,⟨-743588520778,-741148527272⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3
theorem wholeAccepted3 : StepValid wholeStep3.shape wholeBoxes3 wholeStep3.proposed := by
  dsimp only [StepValid,wholeStep3]
  exact ⟨by decide,by decide,lc29,by decide⟩
noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 1 0,⟨⟨261473990254,264104876903⟩,⟨1312734142473,1318154909365⟩,⟨0,0⟩,⟨899746994129,907170673366⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4
theorem wholeAccepted4 : StepValid wholeStep4.shape wholeBoxes4 wholeStep4.proposed := by
  dsimp only [StepValid,wholeStep4]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep5 : Instruction 40 := ⟨.neg 5,⟨⟨-239693534856,-237494511599⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5
theorem wholeAccepted5 : StepValid wholeStep5.shape wholeBoxes5 wholeStep5.proposed := by
  dsimp only [StepValid,wholeStep5]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep6 : Instruction 40 := ⟨.add 8 0,⟨⟨859818092920,862017116177⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes7 := wholeStep6.proposed :: wholeBoxes6
theorem wholeAccepted6 : StepValid wholeStep6.shape wholeBoxes6 wholeStep6.proposed := by
  dsimp only [StepValid,wholeStep6]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep7 : Instruction 40 := ⟨.log 0,⟨⟨-270370501312,-267562040896⟩,⟨-1406025099460,-1402438300733⟩,⟨0,0⟩,⟨-1797986060694,-1788824363177⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes8 := wholeStep7.proposed :: wholeBoxes7
theorem wholeAccepted7 : StepValid wholeStep7.shape wholeBoxes7 wholeStep7.proposed := by
  dsimp only [StepValid,wholeStep7]
  exact ⟨by decide,by decide,lc30,by decide⟩
noncomputable def wholeStep8 : Instruction 40 := ⟨.mul 1 0,⟨⟨-211970473029,-209233515980⟩,⟨-834761637082,-826336249860⟩,⟨0,0⟩,⟨1395255529880,1413189546917⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes9 := wholeStep8.proposed :: wholeBoxes8
theorem wholeAccepted8 : StepValid wholeStep8.shape wholeBoxes8 wholeStep8.proposed := by
  dsimp only [StepValid,wholeStep8]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep9 : Instruction 40 := ⟨.add 4 0,⟨⟨49503517225,54871360923⟩,⟨477972505391,491818659505⟩,⟨0,0⟩,⟨2295002524009,2320360220283⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes10 := wholeStep9.proposed :: wholeBoxes9
theorem wholeAccepted9 : StepValid wholeStep9.shape wholeBoxes9 wholeStep9.proposed := by
  dsimp only [StepValid,wholeStep9]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep10 : Instruction 40 := ⟨.inv 13,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes11 := wholeStep10.proposed :: wholeBoxes10
theorem wholeAccepted10 : StepValid wholeStep10.shape wholeBoxes10 wholeStep10.proposed := by
  dsimp only [StepValid,wholeStep10]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep11 : Instruction 40 := ⟨.mul 1 0,⟨⟨24751758612,27435680462⟩,⟨238986252695,245909329753⟩,⟨0,0⟩,⟨1147501262004,1160180110142⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes12 := wholeStep11.proposed :: wholeBoxes11
theorem wholeAccepted11 : StepValid wholeStep11.shape wholeBoxes11 wholeStep11.proposed := by
  dsimp only [StepValid,wholeStep11]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep12 : Instruction 40 := ⟨.neg 0,⟨⟨-27435680462,-24751758612⟩,⟨-245909329753,-238986252695⟩,⟨0,0⟩,⟨-1160180110142,-1147501262004⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes13 := wholeStep12.proposed :: wholeBoxes12
theorem wholeAccepted12 : StepValid wholeStep12.shape wholeBoxes12 wholeStep12.proposed := by
  dsimp only [StepValid,wholeStep12]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep13 : Instruction 40 := ⟨.add 12 0,⟨⟨734687703154,737371644268⟩,⟨-245909329753,-238986252695⟩,⟨0,0⟩,⟨-1160180110142,-1147501262004⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes14 := wholeStep13.proposed :: wholeBoxes13
theorem wholeAccepted13 : StepValid wholeStep13.shape wholeBoxes13 wholeStep13.proposed := by
  dsimp only [StepValid,wholeStep13]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep14 : Instruction 40 := ⟨.add 16 12,⟨⟨1124448551493,1125877916611⟩,⟨115448720916,120946279056⟩,⟨237494511599,239693534856⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes15 := wholeStep14.proposed :: wholeBoxes14
theorem wholeAccepted14 : StepValid wholeStep14.shape wholeBoxes14 wholeStep14.proposed := by
  dsimp only [StepValid,wholeStep14]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep15 : Instruction 40 := ⟨.log 0,⟨⟨24658343232,26055121792⟩,⟨112745093571,118264050394⟩,⟨231932763919,234377845325⟩,⟨-12720543615,-11561001997⟩,⟨1048552991310,1051345098163⟩,⟨-49961249151,-48924272941⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15
theorem wholeAccepted15 : StepValid wholeStep15.shape wholeBoxes15 wholeStep15.proposed := by
  dsimp only [StepValid,wholeStep15]
  exact ⟨by decide,by decide,lc31,by decide⟩
noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 1 0,⟨⟨25217594456,26679923613⟩,⟨117891278332,123966085721⟩,⟨242519201142,245678242608⟩,⟨10650887398,14194885565⟩,⟨1145698396805,1154174601382⟩,⟨49035634106,52154865112⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16
theorem wholeAccepted16 : StepValid wholeStep16.shape wholeBoxes16 wholeStep16.proposed := by
  dsimp only [StepValid,wholeStep16]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 15,⟨⟨-26366288835,-24936923717⟩,⟨-120946279056,-115448720916⟩,⟨-239693534856,-237494511599⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17
theorem wholeAccepted17 : StepValid wholeStep17.shape wholeBoxes17 wholeStep17.proposed := by
  dsimp only [StepValid,wholeStep17]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep18 : Instruction 40 := ⟨.add 20 0,⟨⟨1073145338941,1074574704059⟩,⟨-120946279056,-115448720916⟩,⟨-239693534856,-237494511599⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18
theorem wholeAccepted18 : StepValid wholeStep18.shape wholeBoxes18 wholeStep18.proposed := by
  dsimp only [StepValid,wholeStep18]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep19 : Instruction 40 := ⟨.log 0,⟨⟨-26687567232,-25224058176⟩,⟨-123917828586,-118127860798⟩,⟨-245582605743,-243005885072⟩,⟨-13965862528,-12691263233⟩,⟨-1154203514692,-1151134987216⟩,⟨-54852367833,-53707353963⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19
theorem wholeAccepted19 : StepValid wholeStep19.shape wholeBoxes19 wholeStep19.proposed := by
  dsimp only [StepValid,wholeStep19]
  exact ⟨by decide,by decide,lc32,by decide⟩
noncomputable def wholeStep20 : Instruction 40 := ⟨.mul 1 0,⟨⟨-26082293208,-24619185260⟩,⟨-118458846126,-112359522299⟩,⟨-234564395679,-231360714290⟩,⟨11157734001,14874995550⟩,⟨-1051770884940,-1042815029725⟩,⟨51370226219,54654564491⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20
theorem wholeAccepted20 : StepValid wholeStep20.shape wholeBoxes20 wholeStep20.proposed := by
  dsimp only [StepValid,wholeStep20]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep21 : Instruction 40 := ⟨.add 4 0,⟨⟨-864698752,2060738353⟩,⟨-567567794,11606563422⟩,⟨7954805463,14317528318⟩,⟨21808621399,29069881115⟩,⟨93927511865,111359571657⟩,⟨100405860325,106809429603⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21
theorem wholeAccepted21 : StepValid wholeStep21.shape wholeBoxes21 wholeStep21.proposed := by
  dsimp only [StepValid,wholeStep21]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep22 : Instruction 40 := ⟨.mul 0 11,⟨⟨-432349376,1030369177⟩,⟨-283783897,5803281711⟩,⟨3977402731,7158764159⟩,⟨10904310699,14534940558⟩,⟨46963755932,55679785829⟩,⟨50202930162,53404714802⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22
theorem wholeAccepted22 : StepValid wholeStep22.shape wholeBoxes22 wholeStep22.proposed := by
  dsimp only [StepValid,wholeStep22]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep23 : Instruction 40 := ⟨.neg 0,⟨⟨-1030369177,432349376⟩,⟨-5803281711,283783897⟩,⟨-7158764159,-3977402731⟩,⟨-14534940558,-10904310699⟩,⟨-55679785829,-46963755932⟩,⟨-53404714802,-50202930162⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23
theorem wholeAccepted23 : StepValid wholeStep23.shape wholeBoxes23 wholeStep23.proposed := by
  dsimp only [StepValid,wholeStep23]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep24 : Instruction 40 := ⟨.add 23 0,⟨⟨761093014439,762555752256⟩,⟨-5803281711,283783897⟩,⟨-7158764159,-3977402731⟩,⟨-14534940558,-10904310699⟩,⟨-55679785829,-46963755932⟩,⟨-53404714802,-50202930162⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24
theorem wholeAccepted24 : StepValid wholeStep24.shape wholeBoxes24 wholeStep24.proposed := by
  dsimp only [StepValid,wholeStep24]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep25 : Instruction 40 := ⟨.add 11 0,⟨⟨1495780717593,1499927396524⟩,⟨-251712611464,-238702468798⟩,⟨-7158764159,-3977402731⟩,⟨-1174715050700,-1158405572703⟩,⟨-55679785829,-46963755932⟩,⟨-53404714802,-50202930162⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25
theorem wholeAccepted25 : StepValid wholeStep25.shape wholeBoxes25 wholeStep25.proposed := by
  dsimp only [StepValid,wholeStep25]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep26 : Instruction 40 := ⟨.mul 0 15,⟨⟨747890358796,749963698262⟩,⟨-125856305732,-119351234399⟩,⟨-3579382080,-1988701365⟩,⟨-587357525350,-579202786351⟩,⟨-27839892915,-23481877966⟩,⟨-26702357401,-25101465081⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26
theorem wholeAccepted26 : StepValid wholeStep26.shape wholeBoxes26 wholeStep26.proposed := by
  dsimp only [StepValid,wholeStep26]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep27 : Instruction 40 := ⟨.neg 28,⟨⟨-120946279056,-115448720916⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27
theorem wholeAccepted27 : StepValid wholeStep27.shape wholeBoxes27 wholeStep27.proposed := by
  dsimp only [StepValid,wholeStep27]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep28 : Instruction 40 := ⟨.add 30 0,⟨⟨978565348720,984062906860⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28
theorem wholeAccepted28 : StepValid wholeStep28.shape wholeBoxes28 wholeStep28.proposed := by
  dsimp only [StepValid,wholeStep28]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep29 : Instruction 40 := ⟨.mul 29 0,⟨⟨211370115322,214525713697⟩,⟨978565348720,984062906860⟩,⟨-239693534856,-237494511599⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29
theorem wholeAccepted29 : StepValid wholeStep29.shape wholeBoxes29 wholeStep29.proposed := by
  dsimp only [StepValid,wholeStep29]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep30 : Instruction 40 := ⟨.mul 0 19,⟨⟨105685057661,107262856849⟩,⟨489282674360,492031453430⟩,⟨-119846767428,-118747255799⟩,⟨0,0⟩,⟨-549755813888,-549755813888⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30
theorem wholeAccepted30 : StepValid wholeStep30.shape wholeBoxes30 wholeStep30.proposed := by
  dsimp only [StepValid,wholeStep30]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep31 : Instruction 40 := ⟨.inv 0,⟨⟨11270684513992,11438947438459⟩,⟨-53255607352823,-51411558696750⟩,⟨12477411998235,12971756874805⟩,⟨469030672333716,495877742209490⟩,⟨-63017832540520,-54328691269859⟩,⟨27626682297857,29419922999788⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31
theorem wholeAccepted31 : StepValid wholeStep31.shape wholeBoxes31 wholeStep31.proposed := by
  dsimp only [StepValid,wholeStep31]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 5 0,⟨⟨7666345741241,7802368895838⟩,⟨-37634377722115,-36193686527658⟩,⟨8449925892572,8827494396526⟩,⟨324086460699251,344486944923606⟩,⟨-44665176558240,-38376250452126⟩,⟨18429473789260,19764534835481⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32
theorem wholeAccepted32 : StepValid wholeStep32.shape wholeBoxes32 wholeStep32.proposed := by
  dsimp only [StepValid,wholeStep32]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep33 : Instruction 40 := ⟨.contact 0,⟨⟨106665345024,108537053184⟩,⟨487974902707,525488777298⟩,⟨-123258295150,-113924613956⟩,⟨-378454813061,686083500890⟩,⟨-668418736374,-410963368572⟩,⟨-34424825274,29672982779⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33
theorem wholeAccepted33 : StepValid wholeStep33.shape wholeBoxes33 wholeStep33.proposed := by
  dsimp only [StepValid,wholeStep33]
  exact ⟨by decide,by decide,(⟨⟨106665345024,108537053184⟩,⟨-15352479724,-14823968793⟩,⟨4089744130,4315152136⟩⟩ : DyadicJetEnclosure 40),brwhole33_jet,by decide⟩
noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 35,⟨⟨1214960348692,1220457906832⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34
theorem wholeAccepted34 : StepValid wholeStep34.shape wholeBoxes34 wholeStep34.proposed := by
  dsimp only [StepValid,wholeStep34]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep35 : Instruction 40 := ⟨.mul 35 0,⟨⟨262431435316,266059823691⟩,⟨1214960348692,1220457906832⟩,⟨237494511599,239693534856⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35
theorem wholeAccepted35 : StepValid wholeStep35.shape wholeBoxes35 wholeStep35.proposed := by
  dsimp only [StepValid,wholeStep35]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 0 25,⟨⟨131215717658,133029911846⟩,⟨607480174346,610228953416⟩,⟨118747255799,119846767428⟩,⟨0,0⟩,⟨549755813888,549755813888⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36
theorem wholeAccepted36 : StepValid wholeStep36.shape wholeBoxes36 wholeStep36.proposed := by
  dsimp only [StepValid,wholeStep36]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep37 : Instruction 40 := ⟨.inv 0,⟨⟨9087624000037,9213269882543⟩,⟨-42847031882397,-41498572278418⟩,⟨-8415002658009,-8111938110480⟩,⟨379005887818441,398526943101841⟩,⟨35485289171044,40713986462047⟩,⟨14482011999615,15371799727363⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37
theorem wholeAccepted37 : StepValid wholeStep37.shape wholeBoxes37 wholeStep37.proposed := by
  dsimp only [StepValid,wholeStep37]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 11 0,⟨⟨6181422917498,6284260920619⟩,⟨-30280049578507,-29213880455231⟩,⟨-5769765564220,-5534196019862⟩,⟨261888251481821,276852280196341⟩,⟨24859498168892,28679155025803⟩,⟨9656292213576,10332241904877⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38
theorem wholeAccepted38 : StepValid wholeStep38.shape wholeBoxes38 wholeStep38.proposed := by
  dsimp only [StepValid,wholeStep38]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep39 : Instruction 40 := ⟨.contact 0,⟨⟨131951755264,134105530368⟩,⟨600515556011,643137380134⟩,⟨113759991762,122547748786⟩,⟨-476220901024,724093847192⟩,⟨414587920686,652742321120⟩,⟨-25521902192,23255688567⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39
theorem wholeAccepted39 : StepValid wholeStep39.shape wholeBoxes39 wholeStep39.proposed := by
  dsimp only [StepValid,wholeStep39]
  exact ⟨by decide,by decide,(⟨⟨131951755264,134105530368⟩,⟨-23353232163,-22601373943⟩,⟨7654878035,8052756626⟩⟩ : DyadicJetEnclosure 40),brwhole39_jet,by decide⟩
noncomputable def wholeStep40 : Instruction 40 := ⟨.inv 33,⟨⟨1402438300733,1406025099460⟩,⟨1788824363177,1797986060694⟩,⟨0,0⟩,⟨4563327457078,4598429822754⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40
theorem wholeAccepted40 : StepValid wholeStep40.shape wholeBoxes40 wholeStep40.proposed := by
  dsimp only [StepValid,wholeStep40]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 38 0,⟨⟨1705364973690,1712538571144⟩,⟨3577648726355,3595972121387⟩,⟨0,0⟩,⟨9126654914158,9196859645506⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41
theorem wholeAccepted41 : StepValid wholeStep41.shape wholeBoxes41 wholeStep41.proposed := by
  dsimp only [StepValid,wholeStep41]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep42 : Instruction 40 := ⟨.log 0,⟨⟨482589993408,487205375552⟩,⟨2296979724139,2318455709848⟩,⟨0,0⟩,⟨970892691604,1130954830807⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42
theorem wholeAccepted42 : StepValid wholeStep42.shape wholeBoxes42 wholeStep42.proposed := by
  dsimp only [StepValid,wholeStep42]
  exact ⟨by decide,by decide,lc49,by decide⟩
noncomputable def wholeStep43 : Instruction 40 := ⟨.mul 0 32,⟨⟨241294996704,243602687776⟩,⟨1148489862069,1159227854924⟩,⟨0,0⟩,⟨485446345802,565477415404⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43
theorem wholeAccepted43 : StepValid wholeStep43.shape wholeBoxes43 wholeStep43.proposed := by
  dsimp only [StepValid,wholeStep43]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep44 : Instruction 40 := ⟨.mul 47 44,⟨⟨474989023198,479387069712⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44
theorem wholeAccepted44 : StepValid wholeStep44.shape wholeBoxes44 wholeStep44.proposed := by
  dsimp only [StepValid,wholeStep44]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 43,⟨⟨10772751045,11495701933⟩,⟨99747694869,105465155339⟩,⟨102597629010,104506381198⟩,⟨461794883664,483785116224⟩,⟨949978046396,958774139424⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45
theorem wholeAccepted45 : StepValid wholeStep45.shape wholeBoxes45 wholeStep45.proposed := by
  dsimp only [StepValid,wholeStep45]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep46 : Instruction 40 := ⟨.mul 46 46,⟨⟨51298814505,52253190599⟩,⟨474989023198,479387069712⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46
theorem wholeAccepted46 : StepValid wholeStep46.shape wholeBoxes46 wholeStep46.proposed := by
  dsimp only [StepValid,wholeStep46]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep47 : Instruction 40 := ⟨.neg 0,⟨⟨-52253190599,-51298814505⟩,⟨-479387069712,-474989023198⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47
theorem wholeAccepted47 : StepValid wholeStep47.shape wholeBoxes47 wholeStep47.proposed := by
  dsimp only [StepValid,wholeStep47]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep48 : Instruction 40 := ⟨.add 50 0,⟨⟨1047258437177,1048212813271⟩,⟨-479387069712,-474989023198⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48
theorem wholeAccepted48 : StepValid wholeStep48.shape wholeBoxes48 wholeStep48.proposed := by
  dsimp only [StepValid,wholeStep48]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep49 : Instruction 40 := ⟨.mul 0 0,⟨⟨997488527208,999307396256⟩,⟨-914041573176,-904831289718⟩,⟨0,0⟩,⟨-3782460737042,-3771008223917⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49
theorem wholeAccepted49 : StepValid wholeStep49.shape wholeBoxes49 wholeStep49.proposed := by
  dsimp only [StepValid,wholeStep49]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep50 : Instruction 40 := ⟨.inv 0,⟨⟨1209763706487,1211969648412⟩,⟨1095390726512,1110579835117⟩,⟨0,0⟩,⟨6548852253375,6631113750635⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50
theorem wholeAccepted50 : StepValid wholeStep50.shape wholeBoxes50 wholeStep50.proposed := by
  dsimp only [StepValid,wholeStep50]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 5 0,⟨⟨11852974451,12671482028⟩,⟨120482138892,127863551819⟩,⟨112885470978,115195291144⟩,⟨771012532781,815650431863⟩,⟨1147448941873,1162395925589⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51
theorem wholeAccepted51 : StepValid wholeStep51.shape wholeBoxes51 wholeStep51.proposed := by
  dsimp only [StepValid,wholeStep51]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep52 : Instruction 40 := ⟨.add 54 18,⟨⟨1206176972800,1208048680960⟩,⟨487974902707,525488777298⟩,⟨-123258295150,-113924613956⟩,⟨-378454813061,686083500890⟩,⟨-668418736374,-410963368572⟩,⟨-34424825274,29672982779⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52
theorem wholeAccepted52 : StepValid wholeStep52.shape wholeBoxes52 wholeStep52.proposed := by
  dsimp only [StepValid,wholeStep52]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep53 : Instruction 40 := ⟨.log 0,⟨⟨101803478848,103508344640⟩,⟨444132830112,479018447488⟩,⟨-112358245758,-103689064611⟩,⟨-553678523868,446009923557⟩,⟨-567424947852,-325089866196⟩,⟨-42862351594,17270562819⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53
theorem wholeAccepted53 : StepValid wholeStep53.shape wholeBoxes53 wholeStep53.proposed := by
  dsimp only [StepValid,wholeStep53]
  exact ⟨by decide,by decide,lc50,by decide⟩
noncomputable def wholeStep54 : Instruction 40 := ⟨.mul 1 0,⟨⟨111679593771,113726054416⟩,⟨532400313415,575773880982⟩,⟨-135053135344,-124296351797⟩,⟨-249740417103,1012499254884⟩,⟨-793761383732,-486714937983⟩,⟨-28846980669,46960170584⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54
theorem wholeAccepted54 : StepValid wholeStep54.shape wholeBoxes54 wholeStep54.proposed := by
  dsimp only [StepValid,wholeStep54]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep55 : Instruction 40 := ⟨.neg 21,⟨⟨-108537053184,-106665345024⟩,⟨-525488777298,-487974902707⟩,⟨113924613956,123258295150⟩,⟨-686083500890,378454813061⟩,⟨410963368572,668418736374⟩,⟨-29672982779,34424825274⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55
theorem wholeAccepted55 : StepValid wholeStep55.shape wholeBoxes55 wholeStep55.proposed := by
  dsimp only [StepValid,wholeStep55]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep56 : Instruction 40 := ⟨.add 58 0,⟨⟨990974574592,992846282752⟩,⟨-525488777298,-487974902707⟩,⟨113924613956,123258295150⟩,⟨-686083500890,378454813061⟩,⟨410963368572,668418736374⟩,⟨-29672982779,34424825274⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56
theorem wholeAccepted56 : StepValid wholeStep56.shape wholeBoxes56 wholeStep56.proposed := by
  dsimp only [StepValid,wholeStep56]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep57 : Instruction 40 := ⟨.log 0,⟨⟨-114275000832,-112200251456⟩,⟨-583043234125,-540399948017⟩,⟨126163979168,136758229941⟩,⟨-1070400280961,154303640266⟩,⟨517123211027,814147111935⟩,⟨-49933042820,23718478654⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57
theorem wholeAccepted57 : StepValid wholeStep57.shape wholeBoxes57 wholeStep57.proposed := by
  dsimp only [StepValid,wholeStep57]
  exact ⟨by decide,by decide,lc51,by decide⟩
noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 1 0,⟨⟨-103189004029,-101124529879⟩,⟨-476685637203,-432439608750⟩,⟨100899300199,111865601776⟩,⟨-526222393069,767947622730⟩,⟨265884020634,581242629313⟩,⟨-22522151671,55163451214⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58
theorem wholeAccepted58 : StepValid wholeStep58.shape wholeBoxes58 wholeStep58.proposed := by
  dsimp only [StepValid,wholeStep58]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨8490589742,12601524537⟩,⟨55714676212,143334272232⟩,⟨-34153835145,-12430750021⟩,⟨-775962810172,1780446877614⟩,⟨-527877363098,94527691330⟩,⟨-51369132340,102123621798⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59
theorem wholeAccepted59 : StepValid wholeStep59.shape wholeBoxes59 wholeStep59.proposed := by
  dsimp only [StepValid,wholeStep59]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 0 49,⟨⟨4245294871,6300762269⟩,⟨27857338106,71667136116⟩,⟨-17076917573,-6215375010⟩,⟨-387981405086,890223438807⟩,⟨-263938681549,47263845665⟩,⟨-25684566170,51061810899⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60
theorem wholeAccepted60 : StepValid wholeStep60.shape wholeBoxes60 wholeStep60.proposed := by
  dsimp only [StepValid,wholeStep60]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep61 : Instruction 40 := ⟨.neg 0,⟨⟨-6300762269,-4245294871⟩,⟨-71667136116,-27857338106⟩,⟨6215375010,17076917573⟩,⟨-890223438807,387981405086⟩,⟨-47263845665,263938681549⟩,⟨-51061810899,25684566170⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61
theorem wholeAccepted61 : StepValid wholeStep61.shape wholeBoxes61 wholeStep61.proposed := by
  dsimp only [StepValid,wholeStep61]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep62 : Instruction 40 := ⟨.add 61 0,⟨⟨755822621347,757878108009⟩,⟨-71667136116,-27857338106⟩,⟨6215375010,17076917573⟩,⟨-890223438807,387981405086⟩,⟨-47263845665,263938681549⟩,⟨-51061810899,25684566170⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62
theorem wholeAccepted62 : StepValid wholeStep62.shape wholeBoxes62 wholeStep62.proposed := by
  dsimp only [StepValid,wholeStep62]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep63 : Instruction 40 := ⟨.mul 29 29,⟨⟨10347772176,10714113081⟩,⟨94678419118,103746066760⟩,⟨-24334607836,-22104010448⟩,⟨358419375512,637744845319⟩,⟨-249781898220,-180858299992⟩,⟨16811916017,33493461950⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63
theorem wholeAccepted63 : StepValid wholeStep63.shape wholeBoxes63 wholeStep63.proposed := by
  dsimp only [StepValid,wholeStep63]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep64 : Instruction 40 := ⟨.neg 0,⟨⟨-10714113081,-10347772176⟩,⟨-103746066760,-94678419118⟩,⟨22104010448,24334607836⟩,⟨-637744845319,-358419375512⟩,⟨180858299992,249781898220⟩,⟨-33493461950,-16811916017⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64
theorem wholeAccepted64 : StepValid wholeStep64.shape wholeBoxes64 wholeStep64.proposed := by
  dsimp only [StepValid,wholeStep64]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep65 : Instruction 40 := ⟨.add 67 0,⟨⟨1088797514695,1089163855600⟩,⟨-103746066760,-94678419118⟩,⟨22104010448,24334607836⟩,⟨-637744845319,-358419375512⟩,⟨180858299992,249781898220⟩,⟨-33493461950,-16811916017⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65
theorem wholeAccepted65 : StepValid wholeStep65.shape wholeBoxes65 wholeStep65.proposed := by
  dsimp only [StepValid,wholeStep65]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep66 : Instruction 40 := ⟨.log 0,⟨⟨-10766656192,-10396772544⟩,⟨-104766960982,-95577926300⟩,⟨22314013068,24574068100⟩,⟨-654003176442,-370132956475⟩,⟨184516276654,254581371348⟩,⟨-34372278292,-17424491481⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66
theorem wholeAccepted66 : StepValid wholeStep66.shape wholeBoxes66 wholeStep66.proposed := by
  dsimp only [StepValid,wholeStep66]
  exact ⟨by decide,by decide,lc40,by decide⟩
noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 0 56,⟨⟨-5383328096,-5198386272⟩,⟨-52383480491,-47788963150⟩,⟨11157006534,12287034050⟩,⟨-327001588221,-185066478237⟩,⟨92258138327,127290685674⟩,⟨-17186139146,-8712245740⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67
theorem wholeAccepted67 : StepValid wholeStep67.shape wholeBoxes67 wholeStep67.proposed := by
  dsimp only [StepValid,wholeStep67]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep68 : Instruction 40 := ⟨.neg 0,⟨⟨5198386272,5383328096⟩,⟨47788963150,52383480491⟩,⟨-12287034050,-11157006534⟩,⟨185066478237,327001588221⟩,⟨-127290685674,-92258138327⟩,⟨8712245740,17186139146⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68
theorem wholeAccepted68 : StepValid wholeStep68.shape wholeBoxes68 wholeStep68.proposed := by
  dsimp only [StepValid,wholeStep68]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep69 : Instruction 40 := ⟨.add 68 0,⟨⟨767321769888,767506730976⟩,⟨47788963150,52383480491⟩,⟨-12287034050,-11157006534⟩,⟨185066478237,327001588221⟩,⟨-127290685674,-92258138327⟩,⟨8712245740,17186139146⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69
theorem wholeAccepted69 : StepValid wholeStep69.shape wholeBoxes69 wholeStep69.proposed := by
  dsimp only [StepValid,wholeStep69]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep70 : Instruction 40 := ⟨.mul 73 0,⟨⟨1534643539776,1535013461952⟩,⟨95577926300,104766960982⟩,⟨-24574068100,-22314013068⟩,⟨370132956474,654003176442⟩,⟨-254581371348,-184516276654⟩,⟨17424491480,34372278292⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70
theorem wholeAccepted70 : StepValid wholeStep70.shape wholeBoxes70 wholeStep70.proposed := by
  dsimp only [StepValid,wholeStep70]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep71 : Instruction 40 := ⟨.add 0 6,⟨⟨1523929426695,1524665689776⟩,⟨-8168140460,10088541864⟩,⟨-2470057652,2020594768⟩,⟨-267611888845,295583800930⟩,⟨-73723071356,65265621566⟩,⟨-16068970470,17560362275⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71
theorem wholeAccepted71 : StepValid wholeStep71.shape wholeBoxes71 wholeStep71.proposed := by
  dsimp only [StepValid,wholeStep71]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 9 0,⟨⟨1047574491196,1050930903433⟩,⟨-105009238141,-31656538583⟩,⟨6911968971,25072908876⟩,⟨-1420227235204,742810882805⟩,⟨-116614467145,411301644736⟩,⟨-81959000470,47783034456⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72
theorem wholeAccepted72 : StepValid wholeStep72.shape wholeBoxes72 wholeStep72.proposed := by
  dsimp only [StepValid,wholeStep72]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep73 : Instruction 40 := ⟨.mul 39 29,⟨⟨23408405537,24046965227⟩,⟨218506074755,230856725365⟩,⟨-27308535200,-25001499442⟩,⟨982669143656,1315883758574⟩,⟨-278044399083,-209188027686⟩,⟨-7627004346,6574208200⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73
theorem wholeAccepted73 : StepValid wholeStep73.shape wholeBoxes73 wholeStep73.proposed := by
  dsimp only [StepValid,wholeStep73]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep74 : Instruction 40 := ⟨.add 11 0,⟨⟨779231026884,781925073236⟩,⟨146838938639,202999387259⟩,⟨-21093160190,-7924581869⟩,⟨92445704849,1703865163660⟩,⟨-325308244748,54750653863⟩,⟨-58688815245,32258774370⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74
theorem wholeAccepted74 : StepValid wholeStep74.shape wholeBoxes74 wholeStep74.proposed := by
  dsimp only [StepValid,wholeStep74]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep75 : Instruction 40 := ⟨.mul 0 0,⟨⟨552246086280,556071263559⟩,⟨208131417716,288728753276⟩,⟨-30001084864,-11232405208⟩,⟨170254198419,2498388574363⟩,⟨-470479011154,75755946168⟩,⟨-83359658969,46691395109⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75
theorem wholeAccepted75 : StepValid wholeStep75.shape wholeBoxes75 wholeStep75.proposed := by
  dsimp only [StepValid,wholeStep75]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep76 : Instruction 40 := ⟨.mul 3 0,⟨⟨526159886112,531501860119⟩,⟨145192229208,260071619770⟩,⟨-25203880258,1978644787⟩,⟨-611209516830,2751687231702⟩,⟨-507036665444,289871378324⟩,⟨-122495035245,68653140552⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76
theorem wholeAccepted76 : StepValid wholeStep76.shape wholeBoxes76 wholeStep76.proposed := by
  dsimp only [StepValid,wholeStep76]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 80 50,⟨⟨1495780717592,1499927396524⟩,⟨-251712611464,-238702468798⟩,⟨-7158764160,-3977402730⟩,⟨-1174715050700,-1158405572702⟩,⟨-55679785830,-46963755932⟩,⟨-53404714802,-50202930162⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77
theorem wholeAccepted77 : StepValid wholeStep77.shape wholeBoxes77 wholeStep77.proposed := by
  dsimp only [StepValid,wholeStep77]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep78 : Instruction 40 := ⟨.mul 12 12,⟨⟨1078187804529,1078913468833⟩,⟨-205539374430,-187511663954⟩,⟨43777238970,48211177810⟩,⟨-1247180319425,-690275335558⟩,⟨353599621472,491055548190⟩,⟨-65467758537,-32219030321⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78
theorem wholeAccepted78 : StepValid wholeStep78.shape wholeBoxes78 wholeStep78.proposed := by
  dsimp only [StepValid,wholeStep78]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 1 0,⟨⟨1466771689554,1471827882035⟩,⟨-527388934239,-489164833229⟩,⟨52530106447,61868267312⟩,⟨-2772664470764,-1980884546855⟩,⟨416043142291,615667517136⟩,⟨-142341573904,-93376939516⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79
theorem wholeAccepted79 : StepValid wholeStep79.shape wholeBoxes79 wholeStep79.proposed := by
  dsimp only [StepValid,wholeStep79]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 10 10,⟨⟨535494744821,535752935406⟩,⟨66701453370,73131875742⟩,⟨-17153763724,-15572393750⟩,⟨262460748901,461513898752⟩,⟨-178879591940,-129739164114⟩,⟨12386544066,24267953778⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80
theorem wholeAccepted80 : StepValid wholeStep80.shape wholeBoxes80 wholeStep80.proposed := by
  dsimp only [StepValid,wholeStep80]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep81 : Instruction 40 := ⟨.mul 11 0,⟨⟨373708440167,373978749908⟩,⟨69823923586,76573824409⟩,⟨-17961104895,-16301378400⟩,⟨279095874707,488461308920⟩,⟨-188524424670,-136827848448⟩,⟨13203415911,25697663775⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81
theorem wholeAccepted81 : StepValid wholeStep81.shape wholeBoxes81 wholeStep81.proposed := by
  dsimp only [StepValid,wholeStep81]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 2 0,⟨⟨498534937091,500615307286⟩,⟨-86235104366,-63756976497⟩,⟨-6188848452,-703024005⟩,⟨-644209685827,-81539034239⟩,⟨-100367062026,39800699397⟩,⟨-32822547004,1104273314⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82
theorem wholeAccepted82 : StepValid wholeStep82.shape wholeBoxes82 wholeStep82.proposed := by
  dsimp only [StepValid,wholeStep82]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep83 : Instruction 40 := ⟨.inv 0,⟨⟨2414879852892,2424957068544⟩,⟨307552397585,419461928003⟩,⟨3391263673,30103590909⟩,⟨471667944507,3278657915305⟩,⟨-192733435077,498616587570⟩,⟨-5361844709,160401758312⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83
theorem wholeAccepted83 : StepValid wholeStep83.shape wholeBoxes83 wholeStep83.proposed := by
  dsimp only [StepValid,wholeStep83]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 7 0,⟨⟨1155615708168,1172219701985⟩,⟨466064669669,776351323723⟩,⟨-53963941064,18915892022⟩,⟨-1041076438766,7852137486873⟩,⟨-1220596466924,888212841731⟩,⟨-274133059627,229059769478⟩⟩⟩
noncomputable def wholeBoxes85 := wholeStep84.proposed :: wholeBoxes84
theorem wholeAccepted84 : StepValid wholeStep84.shape wholeBoxes84 wholeStep84.proposed := by
  dsimp only [StepValid,wholeStep84]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep85 : Instruction 40 := ⟨.mul 36 19,⟨⟨1037053501606,1038347826754⟩,⟨-573781131314,-560539448274⟩,⟨21053539455,23199252373⟩,⟨-2704515778900,-2428514312283⟩,⟨161653301126,228579141464⟩,⟨-31930790990,-16012946520⟩⟩⟩
noncomputable def wholeBoxes86 := wholeStep85.proposed :: wholeBoxes85
theorem wholeAccepted85 : StepValid wholeStep85.shape wholeBoxes85 wholeStep85.proposed := by
  dsimp only [StepValid,wholeStep85]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep86 : Instruction 40 := ⟨.mul 0 16,⟨⟨723733799823,724811749140⟩,⟨-355449782382,-341717030473⟩,⟨3089211580,5670853768⟩,⟨-1767988151595,-1434714895274⟩,⟨-792934407,80058025664⟩,⟨-14590234121,4627799002⟩⟩⟩
noncomputable def wholeBoxes87 := wholeStep86.proposed :: wholeBoxes86
theorem wholeAccepted86 : StepValid wholeStep86.shape wholeBoxes86 wholeStep86.proposed := by
  dsimp only [StepValid,wholeStep86]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep87 : Instruction 40 := ⟨.inv 0,⟨⟨1667916974371,1670401216456⟩,⟨786349884964,820389691660⟩,⟨-13088515467,-7108809201⟩,⟨4042985817891,4886415743895⟩,⟨-197632946589,-4872866606⟩,⟨-10620514302,33879847736⟩⟩⟩
noncomputable def wholeBoxes88 := wholeStep87.proposed :: wholeBoxes87
theorem wholeAccepted87 : StepValid wholeStep87.shape wholeBoxes87 wholeStep87.proposed := by
  dsimp only [StepValid,wholeStep87]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep88 : Instruction 40 := ⟨.mul 24 0,⟨⟨15697173566,16277106192⟩,⟨151024061609,165607438290⟩,⟨-37097188730,-33597838924⟩,⟨717182396763,1171308925852⟩,⟨-400791752140,-290821470766⟩,⟨25685364643,51793467617⟩⟩⟩
noncomputable def wholeBoxes89 := wholeStep88.proposed :: wholeBoxes88
theorem wholeAccepted88 : StepValid wholeStep88.shape wholeBoxes88 wholeStep88.proposed := by
  dsimp only [StepValid,wholeStep88]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep89 : Instruction 40 := ⟨.add 4 0,⟨⟨1171312881734,1188496808177⟩,⟨617088731278,941958762013⟩,⟨-91061129794,-14681946902⟩,⟨-323894042003,9023446412725⟩,⟨-1621388219064,597391370965⟩,⟨-248447694984,280853237095⟩⟩⟩
noncomputable def wholeBoxes90 := wholeStep89.proposed :: wholeBoxes89
theorem wholeAccepted89 : StepValid wholeStep89.shape wholeBoxes89 wholeStep89.proposed := by
  dsimp only [StepValid,wholeStep89]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep90 : Instruction 40 := ⟨.add 38 0,⟨⟨1183165856185,1201168290205⟩,⟨737570870170,1069822313832⟩,⟨21824341184,100513344242⟩,⟨447118490778,9839096844588⟩,⟨-473939277191,1759787296554⟩,⟨-248447694984,280853237095⟩⟩⟩
noncomputable def wholeBoxes91 := wholeStep90.proposed :: wholeBoxes90
theorem wholeAccepted90 : StepValid wholeStep90.shape wholeBoxes90 wholeStep90.proposed := by
  dsimp only [StepValid,wholeStep90]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep91 : Instruction 40 := ⟨.add 93 51,⟨⟨1231463383040,1233617158144⟩,⟨600515556011,643137380134⟩,⟨113759991762,122547748786⟩,⟨-476220901024,724093847192⟩,⟨414587920686,652742321120⟩,⟨-25521902192,23255688567⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91
theorem wholeAccepted91 : StepValid wholeStep91.shape wholeBoxes91 wholeStep91.proposed := by
  dsimp only [StepValid,wholeStep91]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep92 : Instruction 40 := ⟨.log 0,⟨⟨124615457152,126536774848⟩,⟨535233992276,574224972869⟩,⟨101393234434,109416712348⟩,⟨-725085272550,385959042073⟩,⟨312375022735,533443276826⟩,⟨-33675706946,11413692661⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92
theorem wholeAccepted92 : StepValid wholeStep92.shape wholeBoxes92 wholeStep92.proposed := by
  dsimp only [StepValid,wholeStep92]
  exact ⟨by decide,by decide,lc53,by decide⟩
noncomputable def wholeStep93 : Instruction 40 := ⟨.mul 1 0,⟨⟨139570486174,141970246286⟩,⟨667527804930,718277359768⟩,⟨126454605262,136865429010⟩,⟨-283675411385,1188128668283⟩,⟨507606177637,801629214726⟩,⟨-19739129190,39872584684⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93
theorem wholeAccepted93 : StepValid wholeStep93.shape wholeBoxes93 wholeStep93.proposed := by
  dsimp only [StepValid,wholeStep93]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep94 : Instruction 40 := ⟨.neg 54,⟨⟨-134105530368,-131951755264⟩,⟨-643137380134,-600515556011⟩,⟨-122547748786,-113759991762⟩,⟨-724093847192,476220901024⟩,⟨-652742321120,-414587920686⟩,⟨-23255688567,25521902192⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94
theorem wholeAccepted94 : StepValid wholeStep94.shape wholeBoxes94 wholeStep94.proposed := by
  dsimp only [StepValid,wholeStep94]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep95 : Instruction 40 := ⟨.add 97 0,⟨⟨965406097408,967559872512⟩,⟨-643137380134,-600515556011⟩,⟨-122547748786,-113759991762⟩,⟨-724093847192,476220901024⟩,⟨-652742321120,-414587920686⟩,⟨-23255688567,25521902192⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95
theorem wholeAccepted95 : StepValid wholeStep95.shape wholeBoxes95 wholeStep95.proposed := by
  dsimp only [StepValid,wholeStep95]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep96 : Instruction 40 := ⟨.log 0,⟨⟨-143016277120,-140566051072⟩,⟨-732476239392,-682411347609⟩,⟨-139570979622,-129274102069⟩,⟨-1312641858805,118834959412⟩,⟨-836395262428,-551361589052⟩,⟨-44203169480,13867887639⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96
theorem wholeAccepted96 : StepValid wholeStep96.shape wholeBoxes96 wholeStep96.proposed := by
  dsimp only [StepValid,wholeStep96]
  exact ⟨by decide,by decide,lc54,by decide⟩
noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 1 0,⟨⟨-125852976324,-123421453093⟩,⟨-567799831051,-515524299897⟩,⟨-108277605649,-97566665839⟩,⟨-471636367581,1055653086694⟩,⟨-541807174240,-235930597142⟩,⟨-15467611676,46340730747⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97
theorem wholeAccepted97 : StepValid wholeStep97.shape wholeBoxes97 wholeStep97.proposed := by
  dsimp only [StepValid,wholeStep97]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep98 : Instruction 40 := ⟨.add 4 0,⟨⟨13717509850,18548793193⟩,⟨99727973879,202753059871⟩,⟨18176999613,39298763171⟩,⟨-755311778966,2243781754977⟩,⟨-34200996603,565698617584⟩,⟨-35206740866,86213315431⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98
theorem wholeAccepted98 : StepValid wholeStep98.shape wholeBoxes98 wholeStep98.proposed := by
  dsimp only [StepValid,wholeStep98]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep99 : Instruction 40 := ⟨.mul 0 88,⟨⟨6858754925,9274396597⟩,⟨49863986939,101376529936⟩,⟨9088499806,19649381586⟩,⟨-377655889483,1121890877489⟩,⟨-17100498302,282849308792⟩,⟨-17603370433,43106657716⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99
theorem wholeAccepted99 : StepValid wholeStep99.shape wholeBoxes99 wholeStep99.proposed := by
  dsimp only [StepValid,wholeStep99]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep100 : Instruction 40 := ⟨.neg 0,⟨⟨-9274396597,-6858754925⟩,⟨-101376529936,-49863986939⟩,⟨-19649381586,-9088499806⟩,⟨-1121890877489,377655889483⟩,⟨-282849308792,17100498302⟩,⟨-43106657716,17603370433⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100
theorem wholeAccepted100 : StepValid wholeStep100.shape wholeBoxes100 wholeStep100.proposed := by
  dsimp only [StepValid,wholeStep100]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep101 : Instruction 40 := ⟨.add 100 0,⟨⟨752848987019,755264647955⟩,⟨-101376529936,-49863986939⟩,⟨-19649381586,-9088499806⟩,⟨-1121890877489,377655889483⟩,⟨-282849308792,17100498302⟩,⟨-43106657716,17603370433⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101
theorem wholeAccepted101 : StepValid wholeStep101.shape wholeBoxes101 wholeStep101.proposed := by
  dsimp only [StepValid,wholeStep101]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep102 : Instruction 40 := ⟨.mul 62 62,⟨⟨15835453921,16356619449⟩,⟨144135049920,156884706418⟩,⟨27304541784,29893873664⟩,⟨539794339613,929013693422⟩,⟨223772528534,302591421612⟩,⟨17314428070,32990405422⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102
theorem wholeAccepted102 : StepValid wholeStep102.shape wholeBoxes102 wholeStep102.proposed := by
  dsimp only [StepValid,wholeStep102]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep103 : Instruction 40 := ⟨.neg 0,⟨⟨-16356619449,-15835453921⟩,⟨-156884706418,-144135049920⟩,⟨-29893873664,-27304541784⟩,⟨-929013693422,-539794339613⟩,⟨-302591421612,-223772528534⟩,⟨-32990405422,-17314428070⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103
theorem wholeAccepted103 : StepValid wholeStep103.shape wholeBoxes103 wholeStep103.proposed := by
  dsimp only [StepValid,wholeStep103]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep104 : Instruction 40 := ⟨.add 106 0,⟨⟨1083155008327,1083676173855⟩,⟨-156884706418,-144135049920⟩,⟨-29893873664,-27304541784⟩,⟨-929013693422,-539794339613⟩,⟨-302591421612,-223772528534⟩,⟨-32990405422,-17314428070⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104
theorem wholeAccepted104 : StepValid wholeStep104.shape wholeBoxes104 wholeStep104.proposed := by
  dsimp only [StepValid,wholeStep104]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep105 : Instruction 40 := ⟨.log 0,⟨⟨-16479502336,-15950593920⟩,⟨-159253807259,-146241254703⟩,⟨-30345298171,-27703535342⟩,⟨-966109039829,-567133114472⟩,⟨-311556053500,-230727179927⟩,⟨-34326086840,-18265463250⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105
theorem wholeAccepted105 : StepValid wholeStep105.shape wholeBoxes105 wholeStep105.proposed := by
  dsimp only [StepValid,wholeStep105]
  exact ⟨by decide,by decide,lc48,by decide⟩
noncomputable def wholeStep106 : Instruction 40 := ⟨.mul 0 95,⟨⟨-8239751168,-7975296960⟩,⟨-79626903630,-73120627351⟩,⟨-15172649086,-13851767671⟩,⟨-483054519915,-283566557236⟩,⟨-155778026750,-115363589963⟩,⟨-17163043420,-9132731625⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106
theorem wholeAccepted106 : StepValid wholeStep106.shape wholeBoxes106 wholeStep106.proposed := by
  dsimp only [StepValid,wholeStep106]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep107 : Instruction 40 := ⟨.neg 0,⟨⟨7975296960,8239751168⟩,⟨73120627351,79626903630⟩,⟨13851767671,15172649086⟩,⟨283566557236,483054519915⟩,⟨115363589963,155778026750⟩,⟨9132731625,17163043420⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107
theorem wholeAccepted107 : StepValid wholeStep107.shape wholeBoxes107 wholeStep107.proposed := by
  dsimp only [StepValid,wholeStep107]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep108 : Instruction 40 := ⟨.add 107 0,⟨⟨770098680576,770363154048⟩,⟨73120627351,79626903630⟩,⟨13851767671,15172649086⟩,⟨283566557236,483054519915⟩,⟨115363589963,155778026750⟩,⟨9132731625,17163043420⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108
theorem wholeAccepted108 : StepValid wholeStep108.shape wholeBoxes108 wholeStep108.proposed := by
  dsimp only [StepValid,wholeStep108]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep109 : Instruction 40 := ⟨.mul 112 0,⟨⟨1540197361152,1540726308096⟩,⟨146241254702,159253807260⟩,⟨27703535342,30345298172⟩,⟨567133114472,966109039830⟩,⟨230727179926,311556053500⟩,⟨18265463250,34326086840⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109
theorem wholeAccepted109 : StepValid wholeStep109.shape wholeBoxes109 wholeStep109.proposed := by
  dsimp only [StepValid,wholeStep109]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep110 : Instruction 40 := ⟨.add 0 6,⟨⟨1523840741703,1524890854175⟩,⟨-10643451716,15118757340⟩,⟨-2190338322,3040756388⟩,⟨-361880578950,426314700217⟩,⟨-71864241686,87783524966⟩,⟨-14724942172,17011658770⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110
theorem wholeAccepted110 : StepValid wholeStep110.shape wholeBoxes110 wholeStep110.proposed := by
  dsimp only [StepValid,wholeStep110]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep111 : Instruction 40 := ⟨.mul 9 0,⟨⟨1043392293258,1047461550251⟩,⟨-147908182173,-58722536687⟩,⟨-28755900870,-10507256304⟩,⟨-1807295230575,818565628179⟩,⟨-442192850505,84407813744⟩,⟨-70007148986,36177517029⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111
theorem wholeAccepted111 : StepValid wholeStep111.shape wholeBoxes111 wholeStep111.proposed := by
  dsimp only [StepValid,wholeStep111]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep112 : Instruction 40 := ⟨.mul 72 68,⟨⟨28957673158,29711798237⟩,⟨269616659634,283879545089⟩,⟨24965372028,27151109849⟩,⟨1207280422146,1585531560770⟩,⟨209811503920,273822068086⟩,⟨-5654514072,5152422310⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112
theorem wholeAccepted112 : StepValid wholeStep112.shape wholeBoxes112 wholeStep112.proposed := by
  dsimp only [StepValid,wholeStep112]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep113 : Instruction 40 := ⟨.add 11 0,⟨⟨781806660177,784976446192⟩,⟨168240129698,234015558150⟩,⟨5315990442,18062610043⟩,⟨85389544657,1963187450253⟩,⟨-73037804872,290922566388⟩,⟨-48761171788,22755792743⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113
theorem wholeAccepted113 : StepValid wholeStep113.shape wholeBoxes113 wholeStep113.proposed := by
  dsimp only [StepValid,wholeStep113]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 0,⟨⟨555902855828,560419740465⟩,⟨239253957090,334142352932⟩,⟨7559859536,25790947696⟩,⟨172918327667,2902778195431⟩,⟨-102661203684,423086556206⟩,⟨-69572909685,33085633186⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114
theorem wholeAccepted114 : StepValid wholeStep114.shape wholeBoxes114 wholeStep114.proposed := by
  dsimp only [StepValid,wholeStep114]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep115 : Instruction 40 := ⟨.mul 3 0,⟨⟨527529442089,533889879206⟩,⟨151653757613,288634729406⟩,⟨-7482845218,19257651976⟩,⟨-846982447575,3157028629152⟩,⟨-335394836517,443390370811⟩,⟨-103310976531,49814531458⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115
theorem wholeAccepted115 : StepValid wholeStep115.shape wholeBoxes115 wholeStep115.proposed := by
  dsimp only [StepValid,wholeStep115]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep116 : Instruction 40 := ⟨.mul 11 11,⟨⟨1067041714180,1068068786282⟩,⟨-309250423722,-283981719250⟩,⟨-58926668560,-53796704710⟩,⟨-1793478244747,-1018757996117⟩,⟨-589308133426,-432356397892⟩,⟨-63674412233,-32488179926⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116
theorem wholeAccepted116 : StepValid wholeStep116.shape wholeBoxes116 wholeStep116.proposed := by
  dsimp only [StepValid,wholeStep116]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 39 0,⟨⟨1451608496551,1457033826152⟩,⟨-666386373583,-617983342897⟩,⟨-87340392481,-77045231775⟩,⟨-3464437539004,-2368525357261⟩,⟨-845301055689,-618252864340⟩,⟨-138351389948,-92150120956⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117
theorem wholeAccepted117 : StepValid wholeStep117.shape wholeBoxes117 wholeStep117.proposed := by
  dsimp only [StepValid,wholeStep117]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 9 9,⟨⟨539377631707,539748170118⟩,⟨102427472748,111579779746⟩,⟨19403574710,21261166340⟩,⟨406945869557,688429003861⟩,⟨163443834676,220486623376⟩,⟨13142154860,24469019160⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118
theorem wholeAccepted118 : StepValid wholeStep118.shape wholeBoxes118 wholeStep118.proposed := by
  dsimp only [StepValid,wholeStep118]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 10 0,⟨⟨377780454536,378169809414⟩,⟨107610405782,117266087346⟩,⟨20385415084,22344673872⟩,⟨437755313591,735633545158⟩,⟨173649845675,234032629289⟩,⟨14173833632,26156093090⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119
theorem wholeAccepted119 : StepValid wholeStep119.shape wholeBoxes119 wholeStep119.proposed := by
  dsimp only [StepValid,wholeStep119]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep120 : Instruction 40 := ⟨.mul 2 0,⟨⟨498757178898,501137223497⟩,⟨-87128708897,-56935616386⟩,⟨-3126713490,3138450653⟩,⟨-755776815472,40070059469⟩,⟨-84335624713,78708484195⟩,⟨-32422255220,142426646⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120
theorem wholeAccepted120 : StepValid wholeStep120.shape wholeBoxes120 wholeStep120.proposed := by
  dsimp only [StepValid,wholeStep120]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep121 : Instruction 40 := ⟨.inv 0,⟨⟨2412364843263,2423876529028⟩,⟨274075588200,423430962872⟩,⟨-15252345625,15195304975⟩,⟨-132456787404,3820888703041⟩,⟨-387838992649,415166026018⟩,⟨-883403895,157758693496⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121
theorem wholeAccepted121 : StepValid wholeStep121.shape wholeBoxes121 wholeStep121.proposed := by
  dsimp only [StepValid,wholeStep121]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 6 0,⟨⟨1157417027463,1176961766117⟩,⟨464230775239,841901466347⟩,⟨-23902035408,49831933363⟩,⟨-1855886719353,9037298847562⟩,⟨-934587487916,1190452741273⟩,⟨-228712579276,186951451915⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122
theorem wholeAccepted122 : StepValid wholeStep122.shape wholeBoxes122 wholeStep122.proposed := by
  dsimp only [StepValid,wholeStep122]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 74 18,⟨⟨1031679149710,1033116178289⟩,⟨-622047905359,-605208139403⟩,⟨-28499145095,-26006920740⟩,⟨-2928489295123,-2543647706073⟩,⟨-276678154196,-200104233969⟩,⟨-31451205067,-16491577190⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123
theorem wholeAccepted123 : StepValid wholeStep123.shape wholeBoxes123 wholeStep123.proposed := by
  dsimp only [StepValid,wholeStep123]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 0 15,⟨⟨722588767502,723843766177⟩,⟨-367222819196,-349069657441⟩,⟨-6970468723,-3958835904⟩,⟨-1875845594040,-1408184016725⟩,⟨-96253514482,-3135984841⟩,⟨-14253251533,3920642798⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124
theorem wholeAccepted124 : StepValid wholeStep124.shape wholeBoxes124 wholeStep124.proposed := by
  dsimp only [StepValid,wholeStep124]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep125 : Instruction 40 := ⟨.inv 0,⟨⟨1670147449082,1673048176204⟩,⟨805419380767,850250509762⟩,⟨9134346381,16139096688⟩,⟨4025965290055,5207447164442⟩,⟨16045732448,239264798740⟩,⟨-8977757767,33312683096⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125
theorem wholeAccepted125 : StepValid wholeStep125.shape wholeBoxes125 wholeStep125.proposed := by
  dsimp only [StepValid,wholeStep125]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep126 : Instruction 40 := ⟨.mul 23 0,⟨⟨24053900207,24888697534⟩,⟨230539596884,251368779548⟩,⟨41606888161,45727458088⟩,⟨1089090303574,1733718363750⟩,⟨361338057489,489410784296⟩,⟨26620564667,51572297471⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126
theorem wholeAccepted126 : StepValid wholeStep126.shape wholeBoxes126 wholeStep126.proposed := by
  dsimp only [StepValid,wholeStep126]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep127 : Instruction 40 := ⟨.add 4 0,⟨⟨1181470927670,1201850463651⟩,⟨694770372123,1093270245895⟩,⟨17704852753,95559391451⟩,⟨-766796415779,10771017211312⟩,⟨-573249430427,1679863525569⟩,⟨-202092014609,238523749386⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127
theorem wholeAccepted127 : StepValid wholeStep127.shape wholeBoxes127 wholeStep127.proposed := by
  dsimp only [StepValid,wholeStep127]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep128 : Instruction 40 := ⟨.neg 0,⟨⟨-1201850463651,-1181470927670⟩,⟨-1093270245895,-694770372123⟩,⟨-95559391451,-17704852753⟩,⟨-10771017211312,766796415779⟩,⟨-1679863525569,573249430427⟩,⟨-238523749386,202092014609⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128
theorem wholeAccepted128 : StepValid wholeStep128.shape wholeBoxes128 wholeStep128.proposed := by
  dsimp only [StepValid,wholeStep128]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep129 : Instruction 40 := ⟨.add 38 0,⟨⟨-18684607466,19697362535⟩,⟨-355699375725,375051941709⟩,⟨-73735050267,82808491489⟩,⟨-10323898720534,10605893260367⟩,⟨-2153802802760,2333036726981⟩,⟨-486971444370,482945251704⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129
theorem wholeAccepted129 : StepValid wholeStep129.shape wholeBoxes129 wholeStep129.proposed := by
  dsimp only [StepValid,wholeStep129]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep130 : Instruction 40 := ⟨.mul 130 83,⟨⟨11080543933,11391195551⟩,⟨153896443515,156759571797⟩,⟨0,0⟩,⟨1424967069594,1438161209136⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130
theorem wholeAccepted130 : StepValid wholeStep130.shape wholeBoxes130 wholeStep130.proposed := by
  dsimp only [StepValid,wholeStep130]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 0 129,⟨⟨251306736,273160870⟩,⟨4653828450,5012126043⟩,⟨2393397489,2483280631⟩,⟨64636506275,68974211593⟩,⟨44322175732,45564782203⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131
theorem wholeAccepted131 : StepValid wholeStep131.shape wholeBoxes131 wholeStep131.proposed := by
  dsimp only [StepValid,wholeStep131]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep132 : Instruction 40 := ⟨.inv 0,⟨⟨4425691789657241,4810558757225788⟩,⟨-95943018528851081,-75400295663278126⟩,⟨-47535404646321263,-38777294919486655⟩,⟨1248865567779153440,2779798043356936082⟩,⟨449084513991956844,1178018567118752512⟩,⟨679522512067792155,939439598984382166⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132
theorem wholeAccepted132 : StepValid wholeStep132.shape wholeBoxes132 wholeStep132.proposed := by
  dsimp only [StepValid,wholeStep132]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 3 0,⟨⟨-81748477960803,86179461356547⟩,⟨-3275033273438246,3271331518515139⟩,⟨-1174183935602664,1170097212215344⟩,⟨-157861347778627959,158278186179554297⟩,⟨-52882525682643405,53123354608880095⟩,⟨-25255153735483654,25318304117620803⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133
theorem wholeAccepted133 : StepValid wholeStep133.shape wholeBoxes133 wholeStep133.proposed := by
  dsimp only [StepValid,wholeStep133]
  exact ⟨by decide,by decide⟩
noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133]
theorem wholeAccepted : Accepted wholeProgram wholeInitial :=
  ⟨wholeAccepted0,⟨wholeAccepted1,⟨wholeAccepted2,⟨wholeAccepted3,⟨wholeAccepted4,⟨wholeAccepted5,⟨wholeAccepted6,⟨wholeAccepted7,⟨wholeAccepted8,⟨wholeAccepted9,⟨wholeAccepted10,⟨wholeAccepted11,⟨wholeAccepted12,⟨wholeAccepted13,⟨wholeAccepted14,⟨wholeAccepted15,⟨wholeAccepted16,⟨wholeAccepted17,⟨wholeAccepted18,⟨wholeAccepted19,⟨wholeAccepted20,⟨wholeAccepted21,⟨wholeAccepted22,⟨wholeAccepted23,⟨wholeAccepted24,⟨wholeAccepted25,⟨wholeAccepted26,⟨wholeAccepted27,⟨wholeAccepted28,⟨wholeAccepted29,⟨wholeAccepted30,⟨wholeAccepted31,⟨wholeAccepted32,⟨wholeAccepted33,⟨wholeAccepted34,⟨wholeAccepted35,⟨wholeAccepted36,⟨wholeAccepted37,⟨wholeAccepted38,⟨wholeAccepted39,⟨wholeAccepted40,⟨wholeAccepted41,⟨wholeAccepted42,⟨wholeAccepted43,⟨wholeAccepted44,⟨wholeAccepted45,⟨wholeAccepted46,⟨wholeAccepted47,⟨wholeAccepted48,⟨wholeAccepted49,⟨wholeAccepted50,⟨wholeAccepted51,⟨wholeAccepted52,⟨wholeAccepted53,⟨wholeAccepted54,⟨wholeAccepted55,⟨wholeAccepted56,⟨wholeAccepted57,⟨wholeAccepted58,⟨wholeAccepted59,⟨wholeAccepted60,⟨wholeAccepted61,⟨wholeAccepted62,⟨wholeAccepted63,⟨wholeAccepted64,⟨wholeAccepted65,⟨wholeAccepted66,⟨wholeAccepted67,⟨wholeAccepted68,⟨wholeAccepted69,⟨wholeAccepted70,⟨wholeAccepted71,⟨wholeAccepted72,⟨wholeAccepted73,⟨wholeAccepted74,⟨wholeAccepted75,⟨wholeAccepted76,⟨wholeAccepted77,⟨wholeAccepted78,⟨wholeAccepted79,⟨wholeAccepted80,⟨wholeAccepted81,⟨wholeAccepted82,⟨wholeAccepted83,⟨wholeAccepted84,⟨wholeAccepted85,⟨wholeAccepted86,⟨wholeAccepted87,⟨wholeAccepted88,⟨wholeAccepted89,⟨wholeAccepted90,⟨wholeAccepted91,⟨wholeAccepted92,⟨wholeAccepted93,⟨wholeAccepted94,⟨wholeAccepted95,⟨wholeAccepted96,⟨wholeAccepted97,⟨wholeAccepted98,⟨wholeAccepted99,⟨wholeAccepted100,⟨wholeAccepted101,⟨wholeAccepted102,⟨wholeAccepted103,⟨wholeAccepted104,⟨wholeAccepted105,⟨wholeAccepted106,⟨wholeAccepted107,⟨wholeAccepted108,⟨wholeAccepted109,⟨wholeAccepted110,⟨wholeAccepted111,⟨wholeAccepted112,⟨wholeAccepted113,⟨wholeAccepted114,⟨wholeAccepted115,⟨wholeAccepted116,⟨wholeAccepted117,⟨wholeAccepted118,⟨wholeAccepted119,⟨wholeAccepted120,⟨wholeAccepted121,⟨wholeAccepted122,⟨wholeAccepted123,⟨wholeAccepted124,⟨wholeAccepted125,⟨wholeAccepted126,⟨wholeAccepted127,⟨wholeAccepted128,⟨wholeAccepted129,⟨wholeAccepted130,⟨wholeAccepted131,⟨wholeAccepted132,⟨wholeAccepted133,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
noncomputable def wholeOutput : DyadicBivariateJetEnclosure 40 := ⟨⟨-81748477960803,86179461356547⟩,⟨-3275033273438246,3271331518515139⟩,⟨-1174183935602664,1170097212215344⟩,⟨-157861347778627959,158278186179554297⟩,⟨-52882525682643405,53123354608880095⟩,⟨-25255153735483654,25318304117620803⟩⟩
theorem wholeOutput_eq : (finalBoxes wholeProgram wholeInitial).getD 0 (zeroBox 40)=wholeOutput := rfl
theorem sameShape : shapes centerProgram=shapes wholeProgram := by decide
noncomputable def scalarCore (a z : ℝ) : ℝ :=
  let v0 : ℝ := Real.log (2:ℝ)
  let v1 : ℝ := a*z
  let v2 : ℝ := (1:ℝ)+a
  let v3 : ℝ := Real.log v2
  let v4 : ℝ := v2*v3
  let v5 : ℝ := -a
  let v6 : ℝ := (1:ℝ)+v5
  let v7 : ℝ := Real.log v6
  let v8 : ℝ := v6*v7
  let v9 : ℝ := v4+v8
  let v10 : ℝ := (2:ℝ)⁻¹
  let v11 : ℝ := v9*v10
  let v12 : ℝ := -v11
  let v13 : ℝ := v0+v12
  let v14 : ℝ := (1:ℝ)+v1
  let v15 : ℝ := Real.log v14
  let v16 : ℝ := v14*v15
  let v17 : ℝ := -v1
  let v18 : ℝ := (1:ℝ)+v17
  let v19 : ℝ := Real.log v18
  let v20 : ℝ := v18*v19
  let v21 : ℝ := v16+v20
  let v22 : ℝ := v21*v10
  let v23 : ℝ := -v22
  let v24 : ℝ := v0+v23
  let v25 : ℝ := v13+v24
  let v26 : ℝ := v25*v10
  let v27 : ℝ := -z
  let v28 : ℝ := (1:ℝ)+v27
  let v29 : ℝ := a*v28
  let v30 : ℝ := v29*v10
  let v31 : ℝ := v30⁻¹
  let v32 : ℝ := v26*v31
  let v33 : ℝ := GeneralCK.Reflection.biasContact v32
  let v34 : ℝ := (1:ℝ)+z
  let v35 : ℝ := a*v34
  let v36 : ℝ := v35*v10
  let v37 : ℝ := v36⁻¹
  let v38 : ℝ := v26*v37
  let v39 : ℝ := GeneralCK.Reflection.biasContact v38
  let v40 : ℝ := v6⁻¹
  let v41 : ℝ := v2*v40
  let v42 : ℝ := Real.log v41
  let v43 : ℝ := v42*v10
  let v44 : ℝ := (2:ℝ)*a
  let v45 : ℝ := v44*v1
  let v46 : ℝ := a*a
  let v47 : ℝ := -v46
  let v48 : ℝ := (1:ℝ)+v47
  let v49 : ℝ := v48*v48
  let v50 : ℝ := v49⁻¹
  let v51 : ℝ := v45*v50
  let v52 : ℝ := (1:ℝ)+v33
  let v53 : ℝ := Real.log v52
  let v54 : ℝ := v52*v53
  let v55 : ℝ := -v33
  let v56 : ℝ := (1:ℝ)+v55
  let v57 : ℝ := Real.log v56
  let v58 : ℝ := v56*v57
  let v59 : ℝ := v54+v58
  let v60 : ℝ := v59*v10
  let v61 : ℝ := -v60
  let v62 : ℝ := v0+v61
  let v63 : ℝ := v33*v33
  let v64 : ℝ := -v63
  let v65 : ℝ := (1:ℝ)+v64
  let v66 : ℝ := Real.log v65
  let v67 : ℝ := v66*v10
  let v68 : ℝ := -v67
  let v69 : ℝ := v0+v68
  let v70 : ℝ := (2:ℝ)*v69
  let v71 : ℝ := v70+v64
  let v72 : ℝ := v62*v71
  let v73 : ℝ := v33*v43
  let v74 : ℝ := v62+v73
  let v75 : ℝ := v74*v74
  let v76 : ℝ := v72*v75
  let v77 : ℝ := (2:ℝ)*v26
  let v78 : ℝ := v65*v65
  let v79 : ℝ := v77*v78
  let v80 : ℝ := v69*v69
  let v81 : ℝ := v69*v80
  let v82 : ℝ := v79*v81
  let v83 : ℝ := v82⁻¹
  let v84 : ℝ := v76*v83
  let v85 : ℝ := v48*v65
  let v86 : ℝ := v85*v69
  let v87 : ℝ := v86⁻¹
  let v88 : ℝ := v63*v87
  let v89 : ℝ := v84+v88
  let v90 : ℝ := v51+v89
  let v91 : ℝ := (1:ℝ)+v39
  let v92 : ℝ := Real.log v91
  let v93 : ℝ := v91*v92
  let v94 : ℝ := -v39
  let v95 : ℝ := (1:ℝ)+v94
  let v96 : ℝ := Real.log v95
  let v97 : ℝ := v95*v96
  let v98 : ℝ := v93+v97
  let v99 : ℝ := v98*v10
  let v100 : ℝ := -v99
  let v101 : ℝ := v0+v100
  let v102 : ℝ := v39*v39
  let v103 : ℝ := -v102
  let v104 : ℝ := (1:ℝ)+v103
  let v105 : ℝ := Real.log v104
  let v106 : ℝ := v105*v10
  let v107 : ℝ := -v106
  let v108 : ℝ := v0+v107
  let v109 : ℝ := (2:ℝ)*v108
  let v110 : ℝ := v109+v103
  let v111 : ℝ := v101*v110
  let v112 : ℝ := v39*v43
  let v113 : ℝ := v101+v112
  let v114 : ℝ := v113*v113
  let v115 : ℝ := v111*v114
  let v116 : ℝ := v104*v104
  let v117 : ℝ := v77*v116
  let v118 : ℝ := v108*v108
  let v119 : ℝ := v108*v118
  let v120 : ℝ := v117*v119
  let v121 : ℝ := v120⁻¹
  let v122 : ℝ := v115*v121
  let v123 : ℝ := v48*v104
  let v124 : ℝ := v123*v108
  let v125 : ℝ := v124⁻¹
  let v126 : ℝ := v102*v125
  let v127 : ℝ := v122+v126
  let v128 : ℝ := -v127
  let v129 : ℝ := v90+v128
  let v130 : ℝ := a*v46
  let v131 : ℝ := v130*v1
  let v132 : ℝ := v131⁻¹
  let v133 : ℝ := v129*v132
  v133

theorem scalarCore_eq (a z : ℝ) : scalarCore a z=ReflectionExpression.normalizedValue a z := by
  simp only [scalarCore,ReflectionExpression.normalizedValue,Reflection.biasS,Reflection.biasE,
    Reflection.biasB,div_eq_mul_inv,sub_eq_add_neg,pow_succ,pow_zero,one_mul,mul_assoc]

theorem scalar_program (a z : ℝ) :
    (evalRealProgram wholeProgram [a,z,1,2]).getD 0 0=scalarCore a z := by rfl

noncomputable def inputJets (a z : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (217/1000) a,BivariateJet2.affineZ (43/400) z,
    BivariateJet2.const 1,BivariateJet2.const 2]

noncomputable def outputJet (a z : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets a z)).getD 0 zeroJet

theorem output_value (a z t : ℝ) : (outputJet a z).value t =
    ReflectionExpression.normalizedValue (217/1000+t*(a-217/1000)) (43/400+t*(z-43/400)) := by
  rw [outputJet,finalJet_value]
  change (evalRealProgram wholeProgram
    [217/1000+t*(a-217/1000),43/400+t*(z-43/400),1,2]).getD 0 0=_
  rw [scalar_program,scalarCore_eq]

@[simp] theorem output_value_one (a z : ℝ) :
    (outputJet a z).value 1=ReflectionExpression.normalizedValue a z := by
  simp [output_value]

private theorem center_A (x : ℝ) :
    (⟨⟨238594023227,238594023228⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩ : DyadicBivariateJetEnclosure 40).Contains (BivariateJet2.affineA (217/1000) x) 0 := by
  apply DyadicBivariateJetEnclosure.contains_coordinateA
  norm_num [DyadicInterval.Contains,DyadicInterval.scale]

private theorem whole_A {x t : ℝ} (hx : x ∈ Icc (27/125:ℝ) (109/500))
    (ht : t ∈ Icc (0:ℝ) 1) :
    (⟨⟨237494511599,239693534856⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩ : DyadicBivariateJetEnclosure 40).Contains (BivariateJet2.affineA (217/1000) x) t := by
  apply DyadicBivariateJetEnclosure.contains_coordinateA
  change (⟨237494511599,239693534856⟩ : DyadicInterval 40).Contains ((Jet2.segment (217/1000) x).value t)
  apply DyadicInterval.contains_segment _ _ ht
  · norm_num [DyadicInterval.Contains,DyadicInterval.scale]
  · norm_num [DyadicInterval.Contains,DyadicInterval.scale]
    constructor <;> linarith [hx.1,hx.2]

private theorem center_Z (x : ℝ) :
    (⟨⟨118197499985,118197499986⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩ : DyadicBivariateJetEnclosure 40).Contains (BivariateJet2.affineZ (43/400) x) 0 := by
  apply DyadicBivariateJetEnclosure.contains_coordinateZ
  norm_num [DyadicInterval.Contains,DyadicInterval.scale]

private theorem whole_Z {x t : ℝ} (hx : x ∈ Icc (21/200:ℝ) (11/100))
    (ht : t ∈ Icc (0:ℝ) 1) :
    (⟨⟨115448720916,120946279056⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩ : DyadicBivariateJetEnclosure 40).Contains (BivariateJet2.affineZ (43/400) x) t := by
  apply DyadicBivariateJetEnclosure.contains_coordinateZ
  change (⟨115448720916,120946279056⟩ : DyadicInterval 40).Contains ((Jet2.segment (43/400) x).value t)
  apply DyadicInterval.contains_segment _ _ ht
  · norm_num [DyadicInterval.Contains,DyadicInterval.scale]
  · norm_num [DyadicInterval.Contains,DyadicInterval.scale]
    constructor <;> linarith [hx.1,hx.2]

theorem initial_center (a z : ℝ) : RegistersContain centerInitial (inputJets a z) 0 := by
  simpa [centerInitial,inputJets,DyadicBivariateJetEnclosure.const,DyadicInterval.ofInt,DyadicInterval.scale] using
    ((((RegistersContain.nil 40 0).cons (DyadicBivariateJetEnclosure.contains_const 40 2 0)).cons
      (DyadicBivariateJetEnclosure.contains_const 40 1 0)).cons (center_Z z)).cons (center_A a)

theorem initial_whole {a z : ℝ} (ha : a ∈ Icc (27/125:ℝ) (109/500))
    (hz : z ∈ Icc (21/200:ℝ) (11/100)) :
    ∀ t ∈ Icc (0:ℝ) 1, RegistersContain wholeInitial (inputJets a z) t := by
  intro t ht
  simpa [wholeInitial,inputJets,DyadicBivariateJetEnclosure.const,DyadicInterval.ofInt,DyadicInterval.scale] using
    ((((RegistersContain.nil 40 t).cons (DyadicBivariateJetEnclosure.contains_const 40 2 t)).cons
      (DyadicBivariateJetEnclosure.contains_const 40 1 t)).cons (whole_Z hz ht)).cons (whole_A ha ht)

theorem initial_sound (a z : ℝ) : ∀ i, ((inputJets a z).getD i zeroJet).DirectionalSoundOn
    (a-217/1000) (z-43/400) (Icc (0:ℝ) 1) := by
  intro i t ht
  have hconst (c : ℝ) : (BivariateJet2.const c).DirectionalSoundAt (a-217/1000) (z-43/400) t := by
    simpa only [BivariateJet2.DirectionalSoundAt,BivariateJet2.projection_const] using Jet2.soundAt_const c t
  have h : RegistersSound (inputJets a z) (a-217/1000) (z-43/400) t :=
    ((((RegistersSound.nil _ _ t).cons (hconst 2)).cons (hconst 1)).cons
      (BivariateJet2.soundOn_affineZ (43/400) z (a-217/1000) _ t ht)).cons
      (BivariateJet2.soundOn_affineA (217/1000) a (z-43/400) _ t ht)
  exact h i

theorem taylor_positive : 0 < BivariateJetEnclosure.taylorLower
    centerOutput.toReal wholeOutput.toReal (1/1000) (1/400) := by
  norm_num [BivariateJetEnclosure.taylorLower,JetBounds.Interval.magnitude,
    DyadicBivariateJetEnclosure.toReal,DyadicInterval.toReal,DyadicInterval.scale,centerOutput,wholeOutput]

/-- Original compact source box 23951, certified without subdivision by retaining
coordinate derivatives through the complete nonlinear computation. -/
theorem curvature_pos {a z : ℝ} (ha : a ∈ Icc (27/125:ℝ) (109/500))
    (hz : z ∈ Icc (21/200:ℝ) (11/100)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  have hc := (Accepted.encloses centerProgram (initial_center a z) centerAccepted).2 0
  rw [centerOutput_eq,finalJets_eq_of_shapes_eq sameShape (inputJets a z)] at hc
  have hw : wholeOutput.toReal.ContainsOn (outputJet a z) (Icc (0:ℝ) 1) := by
    intro t ht
    have h := (Accepted.encloses wholeProgram (initial_whole ha hz t ht) wholeAccepted).2 0
    rw [wholeOutput_eq] at h
    exact DyadicBivariateJetEnclosure.contains_toReal_iff.mpr h
  have hs := Accepted.preserves_soundOn wholeProgram (initial_whole ha hz) (initial_sound a z) wholeAccepted 0
  have hp : 0 < (outputJet a z).value 1 := BivariateJetEnclosure.value_pos_of_taylor hs
    (DyadicBivariateJetEnclosure.contains_toReal_iff.mpr hc) hw (by norm_num) (by norm_num)
    (by rw [abs_le]; constructor <;> linarith [ha.1,ha.2])
    (by rw [abs_le]; constructor <;> linarith [hz.1,hz.2]) taylor_positive
  apply GeneralCK.Reflection.curvature_pos_of_normalizedValue_pos
    (by linarith [ha.1]) (by linarith [ha.2]) (by linarith [hz.1]) (by linarith [hz.2])
  simpa only [output_value_one] using hp

#print axioms curvature_pos
#print axioms centerAccepted
#print axioms wholeAccepted
end GeneralCK.Certificates.BivariateFastPilot

end


