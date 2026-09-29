-- Prove2me | Definitions.Def_CK_CKLaneC2R_EpCells_B020
-- name    : CK_CKLaneC2R_EpCells_B020
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T15:44:35.247484+00:00
-- url     : https://prove2.me/theorems/094a00ba-a9f6-4073-997c-e6c2b571fbd3
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EpCells.B020` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EpCells.B020` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EpCells.B020` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EpCells.B020 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EpCells/B020.lean)

import Definitions.Def_CK_CKLaneC2R_EndpointCheckT

-- ===== source module CKLaneC2R.EpCells.B020 =====
section

namespace CKLaneC2R.EpCells.B020

open GeneralCK GeneralCK.Certificates CKLaneC2R CKLaneC2R.Endpoint

-- box ['829197/4096000', '415023/2048000', '3997/4000', '1999/2000']  interval_lower 559474475/1099511627776
noncomputable def e1200 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1322097502584,0,true,202698691584,202698691648⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨876925752968,0,false,-248708493312,-248708493248⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1322325404287,0,true,202888207872,202888207936⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨876697851265,0,false,-248994279360,-248994279296⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1321930563177,0,true,202559849024,202559849088⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨877092692375,0,false,-248499200384,-248499200320⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1322213997399,0,true,202795569280,202795569344⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨876809258153,0,false,-248854567104,-248854567040⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568979948,0,true,57350656,57350720⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454275604,0,false,-57353728,-57353664⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099597750878,0,true,86119680,86119744⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099425504674,0,false,-86126528,-86126464⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621030,0,false,-6784,-6720⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624785,0,false,-3008,-2944⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1322014028164,0,true,202629268608,202629268672⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨877009227388,0,false,-248603835968,-248603835904⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1322269709795,0,true,202841896960,202841897024⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨876753545757,0,false,-248924432256,-248924432192⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1054381442836,0,false,-46082535232,-46082535168⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1054484984194,0,false,-45974567360,-45974567296⟩
    { al := (829197/4096000), au := (415023/2048000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨222585874808,222813776511⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202698691584,202698691648⟩ : DyadicInterval 40),(⟨-248708493312,-248708493248⟩ : DyadicInterval 40),(⟨739436697075,739436716404⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202888207872,202888207936⟩ : DyadicInterval 40),(⟨-248994279360,-248994279296⟩ : DyadicInterval 40),(⟨739389889633,739389908962⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202559849024,202559849088⟩ : DyadicInterval 40),(⟨-248499200384,-248499200320⟩ : DyadicInterval 40),(⟨739470952544,739470971874⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202795569280,202795569344⟩ : DyadicInterval 40),(⟨-248854567104,-248854567040⟩ : DyadicInterval 40),(⟨739412777005,739412796335⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨57352172,86123102⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57350656,57350720⟩ : DyadicInterval 40),(⟨-57353728,-57353664⟩ : DyadicInterval 40),(⟨762123382096,762123401425⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨86119680,86119744⟩ : DyadicInterval 40),(⟨-86126528,-86126464⟩ : DyadicInterval 40),(⟨762123380229,762123399559⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6784,-2944⟩ : DyadicInterval 40),(⟨762123385088,762123406272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨222502400388,222758082019⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202629268608,202629268672⟩ : DyadicInterval 40),(⟨-248603835968,-248603835904⟩ : DyadicInterval 40),(⟨739453829065,739453848395⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202841896960,202841897024⟩ : DyadicInterval 40),(⟨-248924432256,-248924432192⟩ : DyadicInterval 40),(⟨739401332979,739401352309⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-46082535232,-45974567296⟩ : DyadicInterval 40),(⟨785110667264,785164670496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨202698691584,202888207936⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-248994279360,-248708493248⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1200_ok : ecellOkT e1200 = true := by decide +kernel
theorem e1200_pos {a z : ℝ} (ha1 : ((829197/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((415023/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1200 e1200_ok ha1 ha2 hz1 hz2 hz

-- box ['415023/2048000', '166179/819200', '999/1000', '3997/4000']  interval_lower 565372039/1099511627776
noncomputable def e1201 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1322325404286,0,true,202888207872,202888207936⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨876697851266,0,false,-248994279360,-248994279296⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1322553305990,0,true,203077691456,203077691520⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨876469949562,0,false,-249280139648,-249280139584⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1322102590509,0,true,202702922944,202702923008⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨876920665043,0,false,-248714872704,-248714872640⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1322386024732,0,true,202938612480,202938612544⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨876637230820,0,false,-249070309184,-249070309120⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099597749029,0,true,86117824,86117888⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099425506523,0,false,-86124672,-86124608⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099626582335,0,true,114948544,114948608⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099396673217,0,false,-114960576,-114960512⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511615757,0,false,-12032,-11968⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621031,0,false,-6784,-6720⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1322213993413,0,true,202795565952,202795566016⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨876809262139,0,false,-248854562112,-248854562048⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1322469674836,0,true,203008162048,203008162112⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨876553580716,0,false,-249175231296,-249175231232⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1054300381716,0,false,-46167069184,-46167069120⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1054404015990,0,false,-46058996160,-46058996096⟩
    { al := (415023/2048000), au := (166179/819200), zl := (999/1000), zu := (3997/4000),
      A := ⟨222813776510,223041678214⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202888207872,202888207936⟩ : DyadicInterval 40),(⟨-248994279360,-248994279296⟩ : DyadicInterval 40),(⟨739389889633,739389908962⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203077691456,203077691520⟩ : DyadicInterval 40),(⟨-249280139648,-249280139584⟩ : DyadicInterval 40),(⟨739343032931,739343052260⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202702922944,202702923008⟩ : DyadicInterval 40),(⟨-248714872704,-248714872640⟩ : DyadicInterval 40),(⟨739435652612,739435671942⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202938612480,202938612544⟩ : DyadicInterval 40),(⟨-249070309184,-249070309120⟩ : DyadicInterval 40),(⟨739377430877,739377450207⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨86121253,114954559⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨86117824,86117888⟩ : DyadicInterval 40),(⟨-86124672,-86124608⟩ : DyadicInterval 40),(⟨762123380230,762123399559⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨114948544,114948608⟩ : DyadicInterval 40),(⟨-114960576,-114960512⟩ : DyadicInterval 40),(⟨762123377549,762123396878⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-12032,-6720⟩ : DyadicInterval 40),(⟨762123386976,762123408896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨222702365637,222958047060⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202795565952,202795566016⟩ : DyadicInterval 40),(⟨-248854562112,-248854562048⟩ : DyadicInterval 40),(⟨739412777835,739412797164⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203008162048,203008162112⟩ : DyadicInterval 40),(⟨-249175231296,-249175231232⟩ : DyadicInterval 40),(⟨739360233272,739360252601⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-46167069184,-46058996096⟩ : DyadicInterval 40),(⟨785152881664,785206937472⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨202888207872,203077691520⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-249280139648,-248994279296⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1201_ok : ecellOkT e1201 = true := by decide +kernel
theorem e1201_pos {a z : ℝ} (ha1 : ((415023/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((166179/819200 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1201 e1201_ok ha1 ha2 hz1 hz2 hz

-- box ['166179/819200', '3249/16000', '999/1000', '3997/4000']  interval_lower 570375395/1099511627776
noncomputable def e1202 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1322553305989,0,true,203077691456,203077691520⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨876469949563,0,false,-249280139648,-249280139584⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1322781207692,0,true,203267142400,203267142464⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨876242047860,0,false,-249566074368,-249566074304⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1322330264310,0,true,202892248960,202892249024⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨876692991242,0,false,-249000374528,-249000374464⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1322613755508,0,true,203127945344,203127945408⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨876409500044,0,false,-249355974848,-249355974784⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099597842575,0,true,86211392,86211456⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099425412977,0,false,-86218240,-86218176⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099626707088,0,true,115073280,115073344⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099396548464,0,false,-115085376,-115085312⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511615731,0,false,-12096,-12032⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621016,0,false,-6784,-6720⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1322441781168,0,true,202984970816,202984970880⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨876581474384,0,false,-249140243200,-249140243136⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1322697491079,0,true,203197553920,203197553984⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨876325764473,0,false,-249461031488,-249461031424⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1054207941739,0,false,-46263477504,-46263477440⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1054311693519,0,false,-46155272384,-46155272320⟩
    { al := (166179/819200), au := (3249/16000), zl := (999/1000), zu := (3997/4000),
      A := ⟨223041678213,223269579916⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203077691456,203077691520⟩ : DyadicInterval 40),(⟨-249280139648,-249280139584⟩ : DyadicInterval 40),(⟨739343032931,739343052261⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203267142400,203267142464⟩ : DyadicInterval 40),(⟨-249566074368,-249566074304⟩ : DyadicInterval 40),(⟨739296126995,739296146325⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202892248960,202892249024⟩ : DyadicInterval 40),(⟨-249000374528,-249000374464⟩ : DyadicInterval 40),(⟨739388890907,739388910236⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203127945344,203127945408⟩ : DyadicInterval 40),(⟨-249355974848,-249355974784⟩ : DyadicInterval 40),(⟨739330596224,739330615554⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨86214799,115079312⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨86211392,86211456⟩ : DyadicInterval 40),(⟨-86218240,-86218176⟩ : DyadicInterval 40),(⟨762123380215,762123399545⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨115073280,115073344⟩ : DyadicInterval 40),(⟨-115085376,-115085312⟩ : DyadicInterval 40),(⟨762123377554,762123396884⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-12096,-6720⟩ : DyadicInterval 40),(⟨762123386976,762123408928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨222930153392,223185863303⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202984970816,202984970880⟩ : DyadicInterval 40),(⟨-249140243200,-249140243136⟩ : DyadicInterval 40),(⟨739365968632,739365987961⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203197553920,203197553984⟩ : DyadicInterval 40),(⟨-249461031488,-249461031424⟩ : DyadicInterval 40),(⟨739313363006,739313382336⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-46263477504,-46155272320⟩ : DyadicInterval 40),(⟨785201019776,785255141632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨203077691456,203267142464⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-249566074368,-249280139584⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1202_ok : ecellOkT e1202 = true := by decide +kernel
theorem e1202_pos {a z : ℝ} (ha1 : ((166179/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3249/16000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1202 e1202_ok ha1 ha2 hz1 hz2 hz

-- box ['415023/2048000', '166179/819200', '3997/4000', '1999/2000']  interval_lower 564454769/1099511627776
noncomputable def e1203 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1322325404286,0,true,202888207872,202888207936⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨876697851266,0,false,-248994279360,-248994279296⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1322553305990,0,true,203077691456,203077691520⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨876469949562,0,false,-249280139648,-249280139584⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1322158293953,0,true,202749247104,202749247168⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨876864961599,0,false,-248784717696,-248784717632⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1322441785152,0,true,202984974144,202984974208⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨876581470400,0,false,-249140248192,-249140248128⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569042303,0,true,57412992,57413056⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454213249,0,false,-57416064,-57416000⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099597844428,0,true,86213248,86213312⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099425411124,0,false,-86220096,-86220032⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621015,0,false,-6784,-6720⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624778,0,false,-3008,-2944⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1322241844405,0,true,202818725760,202818725824⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨876781411147,0,false,-248889487616,-248889487552⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1322497554530,0,true,203031341184,203031341248⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨876525701022,0,false,-249210202944,-249210202880⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1054289074167,0,false,-46178861696,-46178861632⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1054392733036,0,false,-46070761856,-46070761792⟩
    { al := (415023/2048000), au := (166179/819200), zl := (3997/4000), zu := (1999/2000),
      A := ⟨222813776510,223041678214⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202888207872,202888207936⟩ : DyadicInterval 40),(⟨-248994279360,-248994279296⟩ : DyadicInterval 40),(⟨739389889633,739389908962⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203077691456,203077691520⟩ : DyadicInterval 40),(⟨-249280139648,-249280139584⟩ : DyadicInterval 40),(⟨739343032931,739343052260⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202749247104,202749247168⟩ : DyadicInterval 40),(⟨-248784717696,-248784717632⟩ : DyadicInterval 40),(⟨739424216275,739424235604⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202984974144,202984974208⟩ : DyadicInterval 40),(⟨-249140248192,-249140248128⟩ : DyadicInterval 40),(⟨739365967801,739365987131⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨57414527,86216652⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57412992,57413056⟩ : DyadicInterval 40),(⟨-57416064,-57416000⟩ : DyadicInterval 40),(⟨762123382089,762123401418⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨86213248,86213312⟩ : DyadicInterval 40),(⟨-86220096,-86220032⟩ : DyadicInterval 40),(⟨762123380215,762123399544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6784,-2944⟩ : DyadicInterval 40),(⟨762123385088,762123406272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨222730216629,222985926754⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202818725760,202818725824⟩ : DyadicInterval 40),(⟨-248889487616,-248889487552⟩ : DyadicInterval 40),(⟨739407057232,739407076562⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203031341184,203031341248⟩ : DyadicInterval 40),(⟨-249210202944,-249210202880⟩ : DyadicInterval 40),(⟨739354500027,739354519357⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-46178861696,-46070761792⟩ : DyadicInterval 40),(⟨785158764512,785212833728⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨202888207872,203077691520⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-249280139648,-248994279296⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1203_ok : ecellOkT e1203 = true := by decide +kernel
theorem e1203_pos {a z : ℝ} (ha1 : ((415023/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((166179/819200 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1203 e1203_ok ha1 ha2 hz1 hz2 hz

-- box ['166179/819200', '3249/16000', '3997/4000', '1999/2000']  interval_lower 284727321/549755813888
noncomputable def e1204 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1322553305989,0,true,203077691456,203077691520⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨876469949563,0,false,-249280139648,-249280139584⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1322781207692,0,true,203267142400,203267142464⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨876242047860,0,false,-249566074368,-249566074304⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1322386024730,0,true,202938612480,202938612544⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨876637230822,0,false,-249070309184,-249070309120⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1322669572903,0,true,203174346304,203174346368⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨876353682649,0,false,-249426003520,-249426003456⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569104668,0,true,57475328,57475392⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454150884,0,false,-57478400,-57478336⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099597937996,0,true,86306816,86306880⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099425317556,0,false,-86313664,-86313600⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621000,0,false,-6784,-6720⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624772,0,false,-3008,-2944⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1322469660639,0,true,203008150272,203008150336⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨876553594913,0,false,-249175213504,-249175213440⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1322725399252,0,true,203220752768,203220752832⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨876297856300,0,false,-249496047936,-249496047872⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1054196611074,0,false,-46275295168,-46275295104⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1054300387475,0,false,-46167063232,-46167063168⟩
    { al := (166179/819200), au := (3249/16000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨223041678213,223269579916⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203077691456,203077691520⟩ : DyadicInterval 40),(⟨-249280139648,-249280139584⟩ : DyadicInterval 40),(⟨739343032931,739343052261⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203267142400,203267142464⟩ : DyadicInterval 40),(⟨-249566074368,-249566074304⟩ : DyadicInterval 40),(⟨739296126995,739296146325⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202938612480,202938612544⟩ : DyadicInterval 40),(⟨-249070309184,-249070309120⟩ : DyadicInterval 40),(⟨739377430878,739377450207⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203174346304,203174346368⟩ : DyadicInterval 40),(⟨-249426003520,-249426003456⟩ : DyadicInterval 40),(⟨739319109430,739319128760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨57476892,86310220⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57475328,57475392⟩ : DyadicInterval 40),(⟨-57478400,-57478336⟩ : DyadicInterval 40),(⟨762123382083,762123401412⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨86306816,86306880⟩ : DyadicInterval 40),(⟨-86313664,-86313600⟩ : DyadicInterval 40),(⟨762123380200,762123399530⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6784,-2944⟩ : DyadicInterval 40),(⟨762123385088,762123406272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨222958032863,223213771476⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203008150272,203008150336⟩ : DyadicInterval 40),(⟨-249175213504,-249175213440⟩ : DyadicInterval 40),(⟨739360236181,739360255510⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203220752768,203220752832⟩ : DyadicInterval 40),(⟨-249496047936,-249496047872⟩ : DyadicInterval 40),(⟨739307617846,739307637175⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-46275295168,-46167063168⟩ : DyadicInterval 40),(⟨785206915200,785261050464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨203077691456,203267142464⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-249566074368,-249280139584⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1204_ok : ecellOkT e1204 = true := by decide +kernel
theorem e1204_pos {a z : ℝ} (ha1 : ((166179/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3249/16000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1204 e1204_ok ha1 ha2 hz1 hz2 hz

-- box ['207087/1024000', '829197/4096000', '1999/2000', '3999/4000']  interval_lower 69200295/137438953472
noncomputable def e1205 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1321869600882,0,true,202509142656,202509142720⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨877153654670,0,false,-248422781504,-248422781440⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1322097502585,0,true,202698691584,202698691648⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨876925752967,0,false,-248708493312,-248708493248⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1321758421895,0,true,202416661696,202416661760⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨877264833657,0,false,-248283427520,-248283427456⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1322041856117,0,true,202652412672,202652412736⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨876981399435,0,false,-248638724544,-248638724480⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540272783,0,true,28644608,28644672⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482982769,0,false,-28645440,-28645376⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099568981350,0,true,57352064,57352128⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454274202,0,false,-57355072,-57355008⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624784,0,false,-3008,-2944⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627030,0,false,-768,-704⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1321814006156,0,true,202462898816,202462898880⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨877209249396,0,false,-248353095744,-248353095680⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1322069687987,0,true,202675559552,202675559616⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨876953567565,0,false,-248673619200,-248673619136⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1054462454203,0,false,-45998059584,-45998059520⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1054565902615,0,false,-45890196928,-45890196864⟩
    { al := (207087/1024000), au := (829197/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨222357973106,222585874809⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202509142656,202509142720⟩ : DyadicInterval 40),(⟨-248422781504,-248422781440⟩ : DyadicInterval 40),(⟨739483455232,739483474562⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202698691584,202698691648⟩ : DyadicInterval 40),(⟨-248708493312,-248708493248⟩ : DyadicInterval 40),(⟨739436697075,739436716404⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202416661696,202416661760⟩ : DyadicInterval 40),(⟨-248283427520,-248283427456⟩ : DyadicInterval 40),(⟨739506247757,739506267086⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202652412672,202652412736⟩ : DyadicInterval 40),(⟨-248638724544,-248638724480⟩ : DyadicInterval 40),(⟨739448118492,739448137822⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨28645007,57353574⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28644608,28644672⟩ : DyadicInterval 40),(⟨-28645440,-28645376⟩ : DyadicInterval 40),(⟨762123383221,762123402550⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57352064,57352128⟩ : DyadicInterval 40),(⟨-57355072,-57355008⟩ : DyadicInterval 40),(⟨762123382064,762123401393⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3008,-704⟩ : DyadicInterval 40),(⟨762123383968,762123404384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨222302378380,222558060211⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202462898816,202462898880⟩ : DyadicInterval 40),(⟨-248353095744,-248353095680⟩ : DyadicInterval 40),(⟨739494854019,739494873349⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202675559552,202675559616⟩ : DyadicInterval 40),(⟨-248673619200,-248673619136⟩ : DyadicInterval 40),(⟨739442406378,739442425707⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-45998059584,-45890196864⟩ : DyadicInterval 40),(⟨785068482048,785122432672⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨202509142656,202698691648⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-248708493312,-248422781440⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1205_ok : ecellOkT e1205 = true := by decide +kernel
theorem e1205_pos {a z : ℝ} (ha1 : ((207087/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((829197/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1205 e1205_ok ha1 ha2 hz1 hz2 hz

-- box ['829197/4096000', '415023/2048000', '1999/2000', '3999/4000']  interval_lower 558559535/1099511627776
noncomputable def e1206 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1322097502584,0,true,202698691584,202698691648⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨876925752968,0,false,-248708493312,-248708493248⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1322325404287,0,true,202888207872,202888207936⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨876697851265,0,false,-248994279360,-248994279296⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1321986209646,0,true,202606131840,202606131904⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨877037045906,0,false,-248568960256,-248568960192⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1322269700844,0,true,202841889536,202841889600⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨876753554708,0,false,-248924420992,-248924420928⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540303955,0,true,28675776,28675840⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482951597,0,false,-28676608,-28676544⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569043708,0,true,57414400,57414464⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454211844,0,false,-57417472,-57417408⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624777,0,false,-3008,-2944⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627029,0,false,-768,-704⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1322041850879,0,true,202652408320,202652408384⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨876981404673,0,false,-248638718016,-248638717952⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1322297561205,0,true,202865056128,202865056192⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨876725694347,0,false,-248959360448,-248959360384⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1054370156890,0,false,-46094304320,-46094304256⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1054473722816,0,false,-45986309632,-45986309568⟩
    { al := (829197/4096000), au := (415023/2048000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨222585874808,222813776511⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202698691584,202698691648⟩ : DyadicInterval 40),(⟨-248708493312,-248708493248⟩ : DyadicInterval 40),(⟨739436697075,739436716404⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202888207872,202888207936⟩ : DyadicInterval 40),(⟨-248994279360,-248994279296⟩ : DyadicInterval 40),(⟨739389889633,739389908962⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202606131840,202606131904⟩ : DyadicInterval 40),(⟨-248568960256,-248568960192⟩ : DyadicInterval 40),(⟨739459536978,739459556307⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202841889536,202841889600⟩ : DyadicInterval 40),(⟨-248924420992,-248924420928⟩ : DyadicInterval 40),(⟨739401334791,739401354121⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨28676179,57415932⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28675776,28675840⟩ : DyadicInterval 40),(⟨-28676608,-28676544⟩ : DyadicInterval 40),(⟨762123383220,762123402549⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57414400,57414464⟩ : DyadicInterval 40),(⟨-57417472,-57417408⟩ : DyadicInterval 40),(⟨762123382089,762123401418⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3008,-704⟩ : DyadicInterval 40),(⟨762123383968,762123404384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨222530223103,222785933429⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202652408320,202652408384⟩ : DyadicInterval 40),(⟨-248638718016,-248638717952⟩ : DyadicInterval 40),(⟨739448119580,739448138909⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202865056128,202865056192⟩ : DyadicInterval 40),(⟨-248959360448,-248959360384⟩ : DyadicInterval 40),(⟨739395610803,739395630133⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-46094304320,-45986309568⟩ : DyadicInterval 40),(⟨785116538400,785170555040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨202698691584,202888207936⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-248994279360,-248708493248⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1206_ok : ecellOkT e1206 = true := by decide +kernel
theorem e1206_pos {a z : ℝ} (ha1 : ((829197/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((415023/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1206 e1206_ok ha1 ha2 hz1 hz2 hz

-- box ['207087/1024000', '829197/4096000', '3999/4000', '1']  interval_lower 552690505/1099511627776
noncomputable def e1207 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1321869600882,0,true,202509142656,202509142720⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨877153654670,0,false,-248422781504,-248422781440⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1322097502585,0,true,202698691584,202698691648⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨876925752967,0,false,-248708493312,-248708493248⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1321814011388,0,true,202462903168,202462903232⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨877209244164,0,false,-248353102336,-248353102272⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540304913,0,true,28676736,28676800⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482950639,0,false,-28677568,-28677504⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627028,0,false,-768,-704⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1321841800592,0,true,202486018560,202486018624⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨877181454960,0,false,-248387934400,-248387934336⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1322097511115,0,true,202698698688,202698698752⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨876925744437,0,false,-248708504000,-248708503936⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1054451189841,0,false,-46009805248,-46009805184⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1054554662797,0,false,-45901915840,-45901915776⟩
    { al := (207087/1024000), au := (829197/4096000), zl := (3999/4000), zu := 1,
      A := ⟨222357973106,222585874809⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202509142656,202509142720⟩ : DyadicInterval 40),(⟨-248422781504,-248422781440⟩ : DyadicInterval 40),(⟨739483455232,739483474562⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202698691584,202698691648⟩ : DyadicInterval 40),(⟨-248708493312,-248708493248⟩ : DyadicInterval 40),(⟨739436697075,739436716404⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202462903168,202462903232⟩ : DyadicInterval 40),(⟨-248353102336,-248353102272⟩ : DyadicInterval 40),(⟨739494852961,739494872290⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202698691584,202698691648⟩ : DyadicInterval 40),(⟨-248708493312,-248708493248⟩ : DyadicInterval 40),(⟨739436697075,739436716404⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,28677137⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28676736,28676800⟩ : DyadicInterval 40),(⟨-28677568,-28677504⟩ : DyadicInterval 40),(⟨762123383220,762123402549⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-768,0⟩ : DyadicInterval 40),(⟨762123383616,762123403264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨222330172816,222585883339⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202486018560,202486018624⟩ : DyadicInterval 40),(⟨-248387934400,-248387934336⟩ : DyadicInterval 40),(⟨739489155582,739489174911⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202698698688,202698698752⟩ : DyadicInterval 40),(⟨-248708504000,-248708503936⟩ : DyadicInterval 40),(⟨739436695314,739436714644⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-46009805248,-45901915776⟩ : DyadicInterval 40),(⟨785074341504,785128305504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨202509142656,202698691648⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-248708493312,-248422781440⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1207_ok : ecellOkT e1207 = true := by decide +kernel
theorem e1207_pos {a z : ℝ} (ha1 : ((207087/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((829197/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1207 e1207_ok ha1 ha2 hz1 hz2 hz

-- box ['829197/4096000', '415023/2048000', '3999/4000', '1']  interval_lower 557644197/1099511627776
noncomputable def e1208 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1322097502584,0,true,202698691584,202698691648⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨876925752968,0,false,-248708493312,-248708493248⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1322325404287,0,true,202888207872,202888207936⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨876697851265,0,false,-248994279360,-248994279296⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1322041856115,0,true,202652412672,202652412736⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨876981399437,0,false,-248638724544,-248638724480⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540336093,0,true,28707904,28707968⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482919459,0,false,-28708736,-28708672⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627026,0,false,-768,-704⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1322069673800,0,true,202675547776,202675547840⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨876953581752,0,false,-248673601408,-248673601344⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1322325412821,0,true,202888214976,202888215040⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨876697842731,0,false,-248994290048,-248994289984⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1054358869449,0,false,-46106075072,-46106075008⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1054462459947,0,false,-45998053632,-45998053568⟩
    { al := (829197/4096000), au := (415023/2048000), zl := (3999/4000), zu := 1,
      A := ⟨222585874808,222813776511⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202698691584,202698691648⟩ : DyadicInterval 40),(⟨-248708493312,-248708493248⟩ : DyadicInterval 40),(⟨739436697075,739436716404⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202888207872,202888207936⟩ : DyadicInterval 40),(⟨-248994279360,-248994279296⟩ : DyadicInterval 40),(⟨739389889633,739389908962⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202652412672,202652412736⟩ : DyadicInterval 40),(⟨-248638724544,-248638724480⟩ : DyadicInterval 40),(⟨739448118492,739448137822⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202888207872,202888207936⟩ : DyadicInterval 40),(⟨-248994279360,-248994279296⟩ : DyadicInterval 40),(⟨739389889633,739389908962⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,28708317⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28707904,28707968⟩ : DyadicInterval 40),(⟨-28708736,-28708672⟩ : DyadicInterval 40),(⟨762123383218,762123402547⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-768,0⟩ : DyadicInterval 40),(⟨762123383616,762123403264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨222558046024,222813785045⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202675547776,202675547840⟩ : DyadicInterval 40),(⟨-248673601408,-248673601344⟩ : DyadicInterval 40),(⟨739442409274,739442428604⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202888214976,202888215040⟩ : DyadicInterval 40),(⟨-248994290048,-248994289984⟩ : DyadicInterval 40),(⟨739389887868,739389907197⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-46106075072,-45998053568⟩ : DyadicInterval 40),(⟨785122410400,785176440416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨202698691584,202888207936⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-248994279360,-248708493248⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1208_ok : ecellOkT e1208 = true := by decide +kernel
theorem e1208_pos {a z : ℝ} (ha1 : ((829197/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((415023/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1208 e1208_ok ha1 ha2 hz1 hz2 hz

-- box ['415023/2048000', '166179/819200', '1999/2000', '3999/4000']  interval_lower 563536377/1099511627776
noncomputable def e1209 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1322325404286,0,true,202888207872,202888207936⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨876697851266,0,false,-248994279360,-248994279296⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1322553305990,0,true,203077691456,203077691520⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨876469949562,0,false,-249280139648,-249280139584⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1322213997397,0,true,202795569280,202795569344⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨876809258155,0,false,-248854567104,-248854567040⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1322497545571,0,true,203031333760,203031333824⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨876525709981,0,false,-249210191744,-249210191680⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540335132,0,true,28706944,28707008⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482920420,0,false,-28707776,-28707712⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569106076,0,true,57476736,57476800⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454149476,0,false,-57479808,-57479744⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624771,0,false,-3008,-2944⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627027,0,false,-768,-704⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1322269695604,0,true,202841885184,202841885248⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨876753559948,0,false,-248924414464,-248924414400⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1322525434420,0,true,203054520064,203054520128⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨876497821132,0,false,-249245176000,-249245175936⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1054277765125,0,false,-46190655936,-46190655872⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1054381448587,0,false,-46082529216,-46082529152⟩
    { al := (415023/2048000), au := (166179/819200), zl := (1999/2000), zu := (3999/4000),
      A := ⟨222813776510,223041678214⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202888207872,202888207936⟩ : DyadicInterval 40),(⟨-248994279360,-248994279296⟩ : DyadicInterval 40),(⟨739389889633,739389908962⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203077691456,203077691520⟩ : DyadicInterval 40),(⟨-249280139648,-249280139584⟩ : DyadicInterval 40),(⟨739343032931,739343052260⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202795569280,202795569344⟩ : DyadicInterval 40),(⟨-248854567104,-248854567040⟩ : DyadicInterval 40),(⟨739412777006,739412796335⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203031333760,203031333824⟩ : DyadicInterval 40),(⟨-249210191744,-249210191680⟩ : DyadicInterval 40),(⟨739354501870,739354521200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨28707356,57478300⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28706944,28707008⟩ : DyadicInterval 40),(⟨-28707776,-28707712⟩ : DyadicInterval 40),(⟨762123383218,762123402547⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57476736,57476800⟩ : DyadicInterval 40),(⟨-57479808,-57479744⟩ : DyadicInterval 40),(⟨762123382083,762123401412⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3008,-704⟩ : DyadicInterval 40),(⟨762123383968,762123404384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨222758067828,223013806644⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202841885184,202841885248⟩ : DyadicInterval 40),(⟨-248924414464,-248924414400⟩ : DyadicInterval 40),(⟨739401335882,739401355211⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203054520064,203054520128⟩ : DyadicInterval 40),(⟨-249245176000,-249245175936⟩ : DyadicInterval 40),(⟨739348765984,739348785313⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-46190655936,-46082529152⟩ : DyadicInterval 40),(⟨785164648192,785218730848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨202888207872,203077691520⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-249280139648,-248994279296⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1209_ok : ecellOkT e1209 = true := by decide +kernel
theorem e1209_pos {a z : ℝ} (ha1 : ((415023/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((166179/819200 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1209 e1209_ok ha1 ha2 hz1 hz2 hz

-- box ['166179/819200', '3249/16000', '1999/2000', '3999/4000']  interval_lower 284266329/549755813888
noncomputable def e1210 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1322553305989,0,true,203077691456,203077691520⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨876469949563,0,false,-249280139648,-249280139584⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1322781207692,0,true,203267142400,203267142464⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨876242047860,0,false,-249566074368,-249566074304⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1322441785149,0,true,202984974080,202984974144⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨876581470403,0,false,-249140248192,-249140248128⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1322725390298,0,true,203220745344,203220745408⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨876297865254,0,false,-249496036736,-249496036672⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540366316,0,true,28738112,28738176⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482889236,0,false,-28738944,-28738880⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569168455,0,true,57539136,57539200⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454087097,0,false,-57542208,-57542144⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624764,0,false,-3072,-3008⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627025,0,false,-768,-704⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1322497540327,0,true,203031329408,203031329472⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨876525715225,0,false,-249210185152,-249210185088⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1322753307633,0,true,203243951296,203243951360⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨876269947919,0,false,-249531065792,-249531065728⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1054185278907,0,false,-46287114496,-46287114432⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1054289079929,0,false,-46178855680,-46178855616⟩
    { al := (166179/819200), au := (3249/16000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨223041678213,223269579916⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203077691456,203077691520⟩ : DyadicInterval 40),(⟨-249280139648,-249280139584⟩ : DyadicInterval 40),(⟨739343032931,739343052261⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203267142400,203267142464⟩ : DyadicInterval 40),(⟨-249566074368,-249566074304⟩ : DyadicInterval 40),(⟨739296126995,739296146325⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202984974080,202984974144⟩ : DyadicInterval 40),(⟨-249140248192,-249140248128⟩ : DyadicInterval 40),(⟨739365967841,739365987170⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203220745344,203220745408⟩ : DyadicInterval 40),(⟨-249496036736,-249496036672⟩ : DyadicInterval 40),(⟨739307619692,739307639021⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨28738540,57540679⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28738112,28738176⟩ : DyadicInterval 40),(⟨-28738944,-28738880⟩ : DyadicInterval 40),(⟨762123383216,762123402545⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57539136,57539200⟩ : DyadicInterval 40),(⟨-57542208,-57542144⟩ : DyadicInterval 40),(⟨762123382076,762123401405⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3072,-704⟩ : DyadicInterval 40),(⟨762123383968,762123404416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨222985912551,223241679857⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203031329408,203031329472⟩ : DyadicInterval 40),(⟨-249210185152,-249210185088⟩ : DyadicInterval 40),(⟨739354502939,739354522268⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203243951296,203243951360⟩ : DyadicInterval 40),(⟨-249531065792,-249531065728⟩ : DyadicInterval 40),(⟨739301871919,739301891248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-46287114496,-46178855616⟩ : DyadicInterval 40),(⟨785212811424,785266960128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨203077691456,203267142464⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-249566074368,-249280139584⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1210_ok : ecellOkT e1210 = true := by decide +kernel
theorem e1210_pos {a z : ℝ} (ha1 : ((166179/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3249/16000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1210 e1210_ok ha1 ha2 hz1 hz2 hz

-- box ['415023/2048000', '166179/819200', '3999/4000', '1']  interval_lower 281308783/549755813888
noncomputable def e1211 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1322325404286,0,true,202888207872,202888207936⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨876697851266,0,false,-248994279360,-248994279296⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1322553305990,0,true,203077691456,203077691520⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨876469949562,0,false,-249280139648,-249280139584⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1322269700841,0,true,202841889536,202841889600⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨876753554711,0,false,-248924420992,-248924420928⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540367277,0,true,28739072,28739136⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482888275,0,false,-28739904,-28739840⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627024,0,false,-768,-704⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1322297547011,0,true,202865044352,202865044416⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨876725708541,0,false,-248959342656,-248959342592⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1322553314528,0,true,203077698560,203077698624⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨876469941024,0,false,-249280150400,-249280150336⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1054266454580,0,false,-46202451776,-46202451712⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1054370162643,0,false,-46094298304,-46094298240⟩
    { al := (415023/2048000), au := (166179/819200), zl := (3999/4000), zu := 1,
      A := ⟨222813776510,223041678214⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202888207872,202888207936⟩ : DyadicInterval 40),(⟨-248994279360,-248994279296⟩ : DyadicInterval 40),(⟨739389889633,739389908962⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203077691456,203077691520⟩ : DyadicInterval 40),(⟨-249280139648,-249280139584⟩ : DyadicInterval 40),(⟨739343032931,739343052260⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202841889536,202841889600⟩ : DyadicInterval 40),(⟨-248924420992,-248924420928⟩ : DyadicInterval 40),(⟨739401334792,739401354121⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203077691456,203077691520⟩ : DyadicInterval 40),(⟨-249280139648,-249280139584⟩ : DyadicInterval 40),(⟨739343032931,739343052260⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,28739501⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28739072,28739136⟩ : DyadicInterval 40),(⟨-28739904,-28739840⟩ : DyadicInterval 40),(⟨762123383216,762123402545⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-768,0⟩ : DyadicInterval 40),(⟨762123383616,762123403264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨222785919235,223041686752⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨202865044352,202865044416⟩ : DyadicInterval 40),(⟨-248959342656,-248959342592⟩ : DyadicInterval 40),(⟨739395613707,739395633037⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203077698560,203077698624⟩ : DyadicInterval 40),(⟨-249280150400,-249280150336⟩ : DyadicInterval 40),(⟨739343031188,739343050517⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-46202451776,-46094298240⟩ : DyadicInterval 40),(⟨785170532736,785224628768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨202888207872,203077691520⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-249280139648,-248994279296⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1211_ok : ecellOkT e1211 = true := by decide +kernel
theorem e1211_pos {a z : ℝ} (ha1 : ((415023/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((166179/819200 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1211 e1211_ok ha1 ha2 hz1 hz2 hz

-- box ['166179/819200', '3249/16000', '3999/4000', '1']  interval_lower 567610341/1099511627776
noncomputable def e1212 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1322553305989,0,true,203077691456,203077691520⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨876469949563,0,false,-249280139648,-249280139584⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1322781207692,0,true,203267142400,203267142464⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨876242047860,0,false,-249566074368,-249566074304⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1322497545569,0,true,203031333760,203031333824⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨876525709983,0,false,-249210191744,-249210191680⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540398468,0,true,28770304,28770368⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482857084,0,false,-28771072,-28771008⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627023,0,false,-768,-704⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1322525420223,0,true,203054508224,203054508288⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨876497835329,0,false,-249245158144,-249245158080⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1322781216224,0,true,203267149504,203267149568⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨876242039328,0,false,-249566085056,-249566084992⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1054173945239,0,false,-46298935552,-46298935488⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1054277770885,0,false,-46190649920,-46190649856⟩
    { al := (166179/819200), au := (3249/16000), zl := (3999/4000), zu := 1,
      A := ⟨223041678213,223269579916⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203077691456,203077691520⟩ : DyadicInterval 40),(⟨-249280139648,-249280139584⟩ : DyadicInterval 40),(⟨739343032931,739343052261⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203267142400,203267142464⟩ : DyadicInterval 40),(⟨-249566074368,-249566074304⟩ : DyadicInterval 40),(⟨739296126995,739296146325⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203031333760,203031333824⟩ : DyadicInterval 40),(⟨-249210191744,-249210191680⟩ : DyadicInterval 40),(⟨739354501871,739354521201⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203267142400,203267142464⟩ : DyadicInterval 40),(⟨-249566074368,-249566074304⟩ : DyadicInterval 40),(⟨739296126995,739296146325⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,28770692⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28770304,28770368⟩ : DyadicInterval 40),(⟨-28771072,-28771008⟩ : DyadicInterval 40),(⟨762123383183,762123402512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-768,0⟩ : DyadicInterval 40),(⟨762123383616,762123403264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨223013792447,223269588448⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203054508224,203054508288⟩ : DyadicInterval 40),(⟨-249245158144,-249245158080⟩ : DyadicInterval 40),(⟨739348768907,739348788237⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203267149504,203267149568⟩ : DyadicInterval 40),(⟨-249566085056,-249566084992⟩ : DyadicInterval 40),(⟨739296125224,739296144553⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-46298935552,-46190649856⟩ : DyadicInterval 40),(⟨785218708544,785272870656⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨203077691456,203267142464⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-249566074368,-249280139584⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1212_ok : ecellOkT e1212 = true := by decide +kernel
theorem e1212_pos {a z : ℝ} (ha1 : ((166179/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3249/16000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1212 e1212_ok ha1 ha2 hz1 hz2 hz

-- box ['3249/16000', '832593/4096000', '999/1000', '3997/4000']  interval_lower 575398401/1099511627776
noncomputable def e1213 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1322781207691,0,true,203267142400,203267142464⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨876242047861,0,false,-249566074368,-249566074304⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1323009109394,0,true,203456560704,203456560768⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨876014146158,0,false,-249852083392,-249852083328⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1322557938111,0,true,203081542400,203081542464⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨876465317441,0,false,-249285950592,-249285950528⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1322841486283,0,true,203317245568,203317245632⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨876181769269,0,false,-249641714752,-249641714688⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099597936138,0,true,86304960,86305024⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099425319414,0,false,-86311808,-86311744⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099626831866,0,true,115198016,115198080⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099396423686,0,false,-115210176,-115210112⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511615705,0,false,-12096,-12032⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621002,0,false,-6784,-6720⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1322669568915,0,true,203174342976,203174343040⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨876353686637,0,false,-249425998528,-249425998464⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1322925307322,0,true,203386913216,203386913280⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨876097948230,0,false,-249746905920,-249746905856⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1054115407356,0,false,-46359992704,-46359992640⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1054219276668,0,false,-46251655488,-46251655424⟩
    { al := (3249/16000), au := (832593/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨223269579915,223497481618⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203267142400,203267142464⟩ : DyadicInterval 40),(⟨-249566074368,-249566074304⟩ : DyadicInterval 40),(⟨739296126995,739296146325⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203456560704,203456560768⟩ : DyadicInterval 40),(⟨-249852083392,-249852083328⟩ : DyadicInterval 40),(⟨739249171761,739249191090⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203081542400,203081542464⟩ : DyadicInterval 40),(⟨-249285950592,-249285950528⟩ : DyadicInterval 40),(⟨739342080062,739342099391⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203317245568,203317245632⟩ : DyadicInterval 40),(⟨-249641714752,-249641714688⟩ : DyadicInterval 40),(⟨739283712405,739283731735⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨86308362,115204090⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨86304960,86305024⟩ : DyadicInterval 40),(⟨-86311808,-86311744⟩ : DyadicInterval 40),(⟨762123380200,762123399530⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨115198016,115198080⟩ : DyadicInterval 40),(⟨-115210176,-115210112⟩ : DyadicInterval 40),(⟨762123377560,762123396890⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-12096,-6720⟩ : DyadicInterval 40),(⟨762123386976,762123408928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨223157941139,223413679546⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203174342976,203174343040⟩ : DyadicInterval 40),(⟨-249425998528,-249425998464⟩ : DyadicInterval 40),(⟨739319110264,739319129593⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203386913216,203386913280⟩ : DyadicInterval 40),(⟨-249746905920,-249746905856⟩ : DyadicInterval 40),(⟨739266443457,739266462786⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-46359992704,-46251655424⟩ : DyadicInterval 40),(⟨785249211328,785303399232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨203267142400,203456560768⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-249852083392,-249566074304⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1213_ok : ecellOkT e1213 = true := by decide +kernel
theorem e1213_pos {a z : ℝ} (ha1 : ((3249/16000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((832593/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1213 e1213_ok ha1 ha2 hz1 hz2 hz

-- box ['832593/4096000', '416721/2048000', '999/1000', '3997/4000']  interval_lower 580441289/1099511627776
noncomputable def e1214 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1323009109393,0,true,203456560704,203456560768⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨876014146159,0,false,-249852083392,-249852083328⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1323237011096,0,true,203645946432,203645946496⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨875786244456,0,false,-250138166912,-250138166848⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1322785611911,0,true,203270803264,203270803328⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨876237643641,0,false,-249571600768,-249571600704⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1323069217059,0,true,203506513216,203506513280⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨875954038493,0,false,-249927528960,-249927528896⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099598029719,0,true,86398528,86398592⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099425225833,0,false,-86405376,-86405312⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099626956668,0,true,115322816,115322880⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099396298884,0,false,-115334976,-115334912⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511615679,0,false,-12160,-12096⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620987,0,false,-6848,-6784⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1322897356671,0,true,203363682624,203363682688⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨876125898881,0,false,-249711828160,-249711828096⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1323153123565,0,true,203576239872,203576239936⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨875870131987,0,false,-250032854784,-250032854720⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1054022778567,0,false,-46456614848,-46456614784⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1054126765431,0,false,-46348145536,-46348145472⟩
    { al := (832593/4096000), au := (416721/2048000), zl := (999/1000), zu := (3997/4000),
      A := ⟨223497481617,223725383320⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203456560704,203456560768⟩ : DyadicInterval 40),(⟨-249852083392,-249852083328⟩ : DyadicInterval 40),(⟨739249171762,739249191091⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203645946432,203645946496⟩ : DyadicInterval 40),(⟨-250138166912,-250138166848⟩ : DyadicInterval 40),(⟨739202167254,739202186583⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203270803264,203270803328⟩ : DyadicInterval 40),(⟨-249571600768,-249571600704⟩ : DyadicInterval 40),(⟨739295220013,739295239342⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203506513216,203506513280⟩ : DyadicInterval 40),(⟨-249927528960,-249927528896⟩ : DyadicInterval 40),(⟨739236779393,739236798723⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨86401943,115328892⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨86398528,86398592⟩ : DyadicInterval 40),(⟨-86405376,-86405312⟩ : DyadicInterval 40),(⟨762123380186,762123399515⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨115322816,115322880⟩ : DyadicInterval 40),(⟨-115334976,-115334912⟩ : DyadicInterval 40),(⟨762123377534,762123396864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-12160,-6784⟩ : DyadicInterval 40),(⟨762123387008,762123408960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨223385728895,223641495789⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203363682624,203363682688⟩ : DyadicInterval 40),(⟨-249711828160,-249711828096⟩ : DyadicInterval 40),(⟨739272202623,739272221952⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203576239872,203576239936⟩ : DyadicInterval 40),(⟨-250032854784,-250032854720⟩ : DyadicInterval 40),(⟨739219474726,739219494055⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-46456614848,-46348145472⟩ : DyadicInterval 40),(⟨785297456352,785351710304⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨203456560704,203645946496⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-250138166912,-249852083328⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1214_ok : ecellOkT e1214 = true := by decide +kernel
theorem e1214_pos {a z : ℝ} (ha1 : ((832593/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((416721/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1214 e1214_ok ha1 ha2 hz1 hz2 hz

-- box ['3249/16000', '832593/4096000', '3997/4000', '1999/2000']  interval_lower 574474147/1099511627776
noncomputable def e1215 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1322781207691,0,true,203267142400,203267142464⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨876242047861,0,false,-249566074368,-249566074304⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1323009109394,0,true,203456560704,203456560768⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨876014146158,0,false,-249852083392,-249852083328⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1322613755506,0,true,203127945344,203127945408⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨876409500046,0,false,-249355974848,-249355974784⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1322897360654,0,true,203363685888,203363685952⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨876125894898,0,false,-249711833152,-249711833088⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569167045,0,true,57537728,57537792⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454088507,0,false,-57540800,-57540736⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099598031581,0,true,86400384,86400448⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099425223971,0,false,-86407232,-86407168⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620986,0,false,-6848,-6784⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624765,0,false,-3072,-3008⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1322697476877,0,true,203197542144,203197542208⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨876325778675,0,false,-249461013632,-249461013568⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1322953243979,0,true,203410131712,203410131776⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨876070011573,0,false,-249781967296,-249781967232⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1054104053549,0,false,-46371835520,-46371835456⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1054207947506,0,false,-46263471488,-46263471424⟩
    { al := (3249/16000), au := (832593/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨223269579915,223497481618⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203267142400,203267142464⟩ : DyadicInterval 40),(⟨-249566074368,-249566074304⟩ : DyadicInterval 40),(⟨739296126995,739296146325⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203456560704,203456560768⟩ : DyadicInterval 40),(⟨-249852083392,-249852083328⟩ : DyadicInterval 40),(⟨739249171761,739249191090⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203127945344,203127945408⟩ : DyadicInterval 40),(⟨-249355974848,-249355974784⟩ : DyadicInterval 40),(⟨739330596225,739330615554⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203363685888,203363685952⟩ : DyadicInterval 40),(⟨-249711833152,-249711833088⟩ : DyadicInterval 40),(⟨739272201828,739272221157⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨57539269,86403805⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57537728,57537792⟩ : DyadicInterval 40),(⟨-57540800,-57540736⟩ : DyadicInterval 40),(⟨762123382076,762123401405⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨86400384,86400448⟩ : DyadicInterval 40),(⟨-86407232,-86407168⟩ : DyadicInterval 40),(⟨762123380185,762123399515⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6848,-3008⟩ : DyadicInterval 40),(⟨762123385120,762123406304⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨223185849101,223441616203⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203197542144,203197542208⟩ : DyadicInterval 40),(⟨-249461013632,-249461013568⟩ : DyadicInterval 40),(⟨739313365897,739313385227⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203410131712,203410131776⟩ : DyadicInterval 40),(⟨-249781967296,-249781967232⟩ : DyadicInterval 40),(⟨739260686442,739260705772⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-46371835520,-46263471424⟩ : DyadicInterval 40),(⟨785255119328,785309320640⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨203267142400,203456560768⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-249852083392,-249566074304⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1215_ok : ecellOkT e1215 = true := by decide +kernel
theorem e1215_pos {a z : ℝ} (ha1 : ((3249/16000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((832593/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1215 e1215_ok ha1 ha2 hz1 hz2 hz

-- box ['832593/4096000', '416721/2048000', '3997/4000', '1999/2000']  interval_lower 579513589/1099511627776
noncomputable def e1216 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1323009109393,0,true,203456560704,203456560768⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨876014146159,0,false,-249852083392,-249852083328⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1323237011096,0,true,203645946432,203645946496⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨875786244456,0,false,-250138166912,-250138166848⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1322841486281,0,true,203317245568,203317245632⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨876181769271,0,false,-249641714752,-249641714688⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1323125148405,0,true,203552992896,203552992960⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨875898107147,0,false,-249997737088,-249997737024⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569229434,0,true,57600128,57600192⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454026118,0,false,-57603200,-57603136⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099598125184,0,true,86493952,86494016⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099425130368,0,false,-86500864,-86500800⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620971,0,false,-6848,-6784⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624759,0,false,-3072,-3008⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1322925293116,0,true,203386901440,203386901504⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨876097962436,0,false,-249746888128,-249746888064⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1323181088710,0,true,203599478080,203599478144⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨875842166842,0,false,-250067961024,-250067960960⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1054011401593,0,false,-46468482880,-46468482816⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1054115413130,0,false,-46359986688,-46359986624⟩
    { al := (832593/4096000), au := (416721/2048000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨223497481617,223725383320⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203456560704,203456560768⟩ : DyadicInterval 40),(⟨-249852083392,-249852083328⟩ : DyadicInterval 40),(⟨739249171762,739249191091⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203645946432,203645946496⟩ : DyadicInterval 40),(⟨-250138166912,-250138166848⟩ : DyadicInterval 40),(⟨739202167254,739202186583⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203317245568,203317245632⟩ : DyadicInterval 40),(⟨-249641714752,-249641714688⟩ : DyadicInterval 40),(⟨739283712405,739283731735⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203552992896,203552992960⟩ : DyadicInterval 40),(⟨-249997737088,-249997737024⟩ : DyadicInterval 40),(⟨739225244980,739225264309⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨57601658,86497408⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57600128,57600192⟩ : DyadicInterval 40),(⟨-57603200,-57603136⟩ : DyadicInterval 40),(⟨762123382070,762123401399⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨86493952,86494016⟩ : DyadicInterval 40),(⟨-86500864,-86500800⟩ : DyadicInterval 40),(⟨762123380203,762123399532⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6848,-3008⟩ : DyadicInterval 40),(⟨762123385120,762123406304⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨223413665340,223669460934⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203386901440,203386901504⟩ : DyadicInterval 40),(⟨-249746888128,-249746888064⟩ : DyadicInterval 40),(⟨739266446380,739266465709⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203599478080,203599478144⟩ : DyadicInterval 40),(⟨-250067961024,-250067960960⟩ : DyadicInterval 40),(⟨739213705766,739213725096⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-46468482880,-46359986624⟩ : DyadicInterval 40),(⟨785303376928,785357644320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨203456560704,203645946496⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-250138166912,-249852083328⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1216_ok : ecellOkT e1216 = true := by decide +kernel
theorem e1216_pos {a z : ℝ} (ha1 : ((832593/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((416721/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1216 e1216_ok ha1 ha2 hz1 hz2 hz

-- box ['416721/2048000', '834291/4096000', '999/1000', '3997/4000']  interval_lower 146375969/274877906944
noncomputable def e1217 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1323237011095,0,true,203645946432,203645946496⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨875786244457,0,false,-250138166912,-250138166848⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1323464912798,0,true,203835299456,203835299520⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨875558342754,0,false,-250424324800,-250424324736⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1323013285711,0,true,203460031552,203460031616⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨876009969841,0,false,-249857325248,-249857325184⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1323296947835,0,true,203695748288,203695748352⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨875726307717,0,false,-250213417472,-250213417408⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099598123318,0,true,86492096,86492160⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099425132234,0,false,-86499008,-86498944⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099627081493,0,true,115447616,115447680⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099396174059,0,false,-115459840,-115459776⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511615652,0,false,-12160,-12096⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620972,0,false,-6848,-6784⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1323125144422,0,true,203552989568,203552989632⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨875898111130,0,false,-249997732096,-249997732032⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1323380939806,0,true,203765533952,203765534016⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨875642315746,0,false,-250318878016,-250318877952⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1053930055373,0,false,-46553344000,-46553343936⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1054034159814,0,false,-46444742464,-46444742400⟩
    { al := (416721/2048000), au := (834291/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨223725383319,223953285022⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203645946432,203645946496⟩ : DyadicInterval 40),(⟨-250138166912,-250138166848⟩ : DyadicInterval 40),(⟨739202167254,739202186584⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203835299456,203835299520⟩ : DyadicInterval 40),(⟨-250424324800,-250424324736⟩ : DyadicInterval 40),(⟨739155113487,739155132816⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203460031552,203460031616⟩ : DyadicInterval 40),(⟨-249857325248,-249857325184⟩ : DyadicInterval 40),(⟨739248310824,739248330154⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203695748288,203695748352⟩ : DyadicInterval 40),(⟨-250213417472,-250213417408⟩ : DyadicInterval 40),(⟨739189797176,739189816506⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨86495542,115453717⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨86492096,86492160⟩ : DyadicInterval 40),(⟨-86499008,-86498944⟩ : DyadicInterval 40),(⟨762123380203,762123399532⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨115447616,115447680⟩ : DyadicInterval 40),(⟨-115459840,-115459776⟩ : DyadicInterval 40),(⟨762123377540,762123396870⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-12160,-6784⟩ : DyadicInterval 40),(⟨762123387008,762123408960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨223613516646,223869312030⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203552989568,203552989632⟩ : DyadicInterval 40),(⟨-249997732096,-249997732032⟩ : DyadicInterval 40),(⟨739225245816,739225265145⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203765533952,203765534016⟩ : DyadicInterval 40),(⟨-250318878016,-250318877952⟩ : DyadicInterval 40),(⟨739172456737,739172476067⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-46553344000,-46444742400⟩ : DyadicInterval 40),(⟨785345754816,785400074880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨203645946432,203835299520⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-250424324800,-250138166848⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1217_ok : ecellOkT e1217 = true := by decide +kernel
theorem e1217_pos {a z : ℝ} (ha1 : ((416721/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((834291/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1217 e1217_ok ha1 ha2 hz1 hz2 hz

-- box ['834291/4096000', '41757/204800', '999/1000', '3997/4000']  interval_lower 590586383/1099511627776
noncomputable def e1218 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1323464912797,0,true,203835299456,203835299520⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨875558342755,0,false,-250424324800,-250424324736⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1323692814500,0,true,204024619968,204024620032⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨875330441052,0,false,-250710557248,-250710557184⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1323240959511,0,true,203649227264,203649227328⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨875782296041,0,false,-250143123968,-250143123904⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1323524678611,0,true,203884950784,203884950848⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨875498576941,0,false,-250499380288,-250499380224⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099598216934,0,true,86585728,86585792⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099425038618,0,false,-86592576,-86592512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099627206342,0,true,115572480,115572544⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099396049210,0,false,-115584704,-115584640⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511615626,0,false,-12160,-12096⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620957,0,false,-6848,-6784⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1323352932171,0,true,203742264000,203742264064⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨875670323381,0,false,-250283710400,-250283710336⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1323608756053,0,true,203954795456,203954795520⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨875414499499,0,false,-250604975616,-250604975552⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1053837237771,0,false,-46650180160,-46650180096⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1053941459815,0,false,-46541446400,-46541446336⟩
    { al := (834291/4096000), au := (41757/204800), zl := (999/1000), zu := (3997/4000),
      A := ⟨223953285021,224181186724⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203835299456,203835299520⟩ : DyadicInterval 40),(⟨-250424324800,-250424324736⟩ : DyadicInterval 40),(⟨739155113487,739155132816⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204024619968,204024620032⟩ : DyadicInterval 40),(⟨-250710557248,-250710557184⟩ : DyadicInterval 40),(⟨739108010407,739108029736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203649227264,203649227328⟩ : DyadicInterval 40),(⟨-250143123968,-250143123904⟩ : DyadicInterval 40),(⟨739201352457,739201371787⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203884950784,203884950848⟩ : DyadicInterval 40),(⟨-250499380288,-250499380224⟩ : DyadicInterval 40),(⟨739142765740,739142785070⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨86589158,115578566⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨86585728,86585792⟩ : DyadicInterval 40),(⟨-86592576,-86592512⟩ : DyadicInterval 40),(⟨762123380156,762123399486⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨115572480,115572544⟩ : DyadicInterval 40),(⟨-115584704,-115584640⟩ : DyadicInterval 40),(⟨762123377514,762123396843⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-12160,-6784⟩ : DyadicInterval 40),(⟨762123387008,762123408960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨223841304395,224097128277⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203742264000,203742264064⟩ : DyadicInterval 40),(⟨-250283710400,-250283710336⟩ : DyadicInterval 40),(⟨739178239737,739178259067⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203954795456,203954795520⟩ : DyadicInterval 40),(⟨-250604975616,-250604975552⟩ : DyadicInterval 40),(⟨739125389475,739125408805⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-46650180160,-46541446336⟩ : DyadicInterval 40),(⟨785394106784,785448492960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨203835299456,204024620032⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-250710557248,-250424324736⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1218_ok : ecellOkT e1218 = true := by decide +kernel
theorem e1218_pos {a z : ℝ} (ha1 : ((834291/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((41757/204800 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1218 e1218_ok ha1 ha2 hz1 hz2 hz

-- box ['416721/2048000', '834291/4096000', '3997/4000', '1999/2000']  interval_lower 584572691/1099511627776
noncomputable def e1219 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1323237011095,0,true,203645946432,203645946496⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨875786244457,0,false,-250138166912,-250138166848⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1323464912798,0,true,203835299456,203835299520⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨875558342754,0,false,-250424324800,-250424324736⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1323069217057,0,true,203506513216,203506513280⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨875954038495,0,false,-249927528960,-249927528896⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1323352936156,0,true,203742267328,203742267392⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨875670319396,0,false,-250283715392,-250283715328⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569291834,0,true,57662528,57662592⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453963718,0,false,-57665600,-57665536⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099598218805,0,true,86587584,86587648⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099425036747,0,false,-86594496,-86594432⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620956,0,false,-6848,-6784⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624752,0,false,-3072,-3008⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1323153109353,0,true,203576228096,203576228160⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨875870146199,0,false,-250032836928,-250032836864⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1323408933438,0,true,203788791808,203788791872⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨875614322114,0,false,-250354029120,-250354029056⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1053918655208,0,false,-46565237248,-46565237184⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1054022784350,0,false,-46456608832,-46456608768⟩
    { al := (416721/2048000), au := (834291/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨223725383319,223953285022⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203645946432,203645946496⟩ : DyadicInterval 40),(⟨-250138166912,-250138166848⟩ : DyadicInterval 40),(⟨739202167254,739202186584⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203835299456,203835299520⟩ : DyadicInterval 40),(⟨-250424324800,-250424324736⟩ : DyadicInterval 40),(⟨739155113487,739155132816⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203506513216,203506513280⟩ : DyadicInterval 40),(⟨-249927528960,-249927528896⟩ : DyadicInterval 40),(⟨739236779394,739236798723⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203742267328,203742267392⟩ : DyadicInterval 40),(⟨-250283715392,-250283715328⟩ : DyadicInterval 40),(⟨739178238900,739178258229⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨57664058,86591029⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57662528,57662592⟩ : DyadicInterval 40),(⟨-57665600,-57665536⟩ : DyadicInterval 40),(⟨762123382063,762123401392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨86587584,86587648⟩ : DyadicInterval 40),(⟨-86594496,-86594432⟩ : DyadicInterval 40),(⟨762123380188,762123399517⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6848,-3008⟩ : DyadicInterval 40),(⟨762123385120,762123406304⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨223641481577,223897305662⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203576228096,203576228160⟩ : DyadicInterval 40),(⟨-250032836928,-250032836864⟩ : DyadicInterval 40),(⟨739219477631,739219496961⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203788791808,203788791872⟩ : DyadicInterval 40),(⟨-250354029120,-250354029056⟩ : DyadicInterval 40),(⟨739166675845,739166695174⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-46565237248,-46456608768⟩ : DyadicInterval 40),(⟨785351688000,785406021504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨203645946432,203835299520⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-250424324800,-250138166848⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1219_ok : ecellOkT e1219 = true := by decide +kernel
theorem e1219_pos {a z : ℝ} (ha1 : ((416721/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((834291/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1219 e1219_ok ha1 ha2 hz1 hz2 hz

-- box ['834291/4096000', '41757/204800', '3997/4000', '1999/2000']  interval_lower 147412863/274877906944
noncomputable def e1220 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1323464912797,0,true,203835299456,203835299520⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨875558342755,0,false,-250424324800,-250424324736⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1323692814500,0,true,204024619968,204024620032⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨875330441052,0,false,-250710557248,-250710557184⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1323296947833,0,true,203695748288,203695748352⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨875726307719,0,false,-250213417408,-250213417344⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1323580723907,0,true,203931509120,203931509184⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨875442531645,0,false,-250569768128,-250569768064⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569354247,0,true,57724928,57724992⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453901305,0,false,-57728000,-57727936⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099598312445,0,true,86681216,86681280⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099424943107,0,false,-86688128,-86688064⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620941,0,false,-6848,-6784⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624746,0,false,-3072,-3008⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1323380925592,0,true,203765522176,203765522240⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨875642329960,0,false,-250318860160,-250318860096⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1323636778165,0,true,203978072960,203978073024⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨875386477387,0,false,-250640171712,-250640171648⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1053825814394,0,false,-46662098688,-46662098624⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1053930061162,0,false,-46553337920,-46553337856⟩
    { al := (834291/4096000), au := (41757/204800), zl := (3997/4000), zu := (1999/2000),
      A := ⟨223953285021,224181186724⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203835299456,203835299520⟩ : DyadicInterval 40),(⟨-250424324800,-250424324736⟩ : DyadicInterval 40),(⟨739155113487,739155132816⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204024619968,204024620032⟩ : DyadicInterval 40),(⟨-250710557248,-250710557184⟩ : DyadicInterval 40),(⟨739108010407,739108029736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203695748288,203695748352⟩ : DyadicInterval 40),(⟨-250213417408,-250213417344⟩ : DyadicInterval 40),(⟨739189797151,739189816480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203931509120,203931509184⟩ : DyadicInterval 40),(⟨-250569768128,-250569768064⟩ : DyadicInterval 40),(⟨739131183638,739131202968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨57726471,86684669⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57724928,57724992⟩ : DyadicInterval 40),(⟨-57728000,-57727936⟩ : DyadicInterval 40),(⟨762123382057,762123401386⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨86681216,86681280⟩ : DyadicInterval 40),(⟨-86688128,-86688064⟩ : DyadicInterval 40),(⟨762123380173,762123399503⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6848,-3008⟩ : DyadicInterval 40),(⟨762123385120,762123406304⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨223869297816,224125150389⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203765522176,203765522240⟩ : DyadicInterval 40),(⟨-250318860160,-250318860096⟩ : DyadicInterval 40),(⟨739172459649,739172478979⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203978072960,203978073024⟩ : DyadicInterval 40),(⟨-250640171712,-250640171648⟩ : DyadicInterval 40),(⟨739119596677,739119616006⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-46662098688,-46553337856⟩ : DyadicInterval 40),(⟨785400052544,785454452224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨203835299456,204024620032⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-250710557248,-250424324736⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1220_ok : ecellOkT e1220 = true := by decide +kernel
theorem e1220_pos {a z : ℝ} (ha1 : ((834291/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((41757/204800 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1220 e1220_ok ha1 ha2 hz1 hz2 hz

-- box ['3249/16000', '832593/4096000', '1999/2000', '3999/4000']  interval_lower 286774439/549755813888
noncomputable def e1221 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1322781207691,0,true,203267142400,203267142464⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨876242047861,0,false,-249566074368,-249566074304⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1323009109394,0,true,203456560704,203456560768⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨876014146158,0,false,-249852083392,-249852083328⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1322669572901,0,true,203174346304,203174346368⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨876353682651,0,false,-249426003520,-249426003456⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1322953235024,0,true,203410124288,203410124352⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨876070020528,0,false,-249781956032,-249781955968⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540397505,0,true,28769344,28769408⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482858047,0,false,-28770112,-28770048⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569230848,0,true,57601536,57601600⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099454024704,0,false,-57604608,-57604544⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624758,0,false,-3072,-3008⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627024,0,false,-768,-704⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1322725385050,0,true,203220740992,203220741056⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨876297870502,0,false,-249496030144,-249496030080⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1322981180850,0,true,203433349952,203433350016⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨876042074702,0,false,-249817030016,-249817029952⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1054092698235,0,false,-46383680064,-46383680000⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1054196616841,0,false,-46275289152,-46275289088⟩
    { al := (3249/16000), au := (832593/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨223269579915,223497481618⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203267142400,203267142464⟩ : DyadicInterval 40),(⟨-249566074368,-249566074304⟩ : DyadicInterval 40),(⟨739296126995,739296146325⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203456560704,203456560768⟩ : DyadicInterval 40),(⟨-249852083392,-249852083328⟩ : DyadicInterval 40),(⟨739249171761,739249191090⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203174346304,203174346368⟩ : DyadicInterval 40),(⟨-249426003520,-249426003456⟩ : DyadicInterval 40),(⟨739319109431,739319128761⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203410124288,203410124352⟩ : DyadicInterval 40),(⟨-249781956032,-249781955968⟩ : DyadicInterval 40),(⟨739260688267,739260707597⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨28769729,57603072⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28769344,28769408⟩ : DyadicInterval 40),(⟨-28770112,-28770048⟩ : DyadicInterval 40),(⟨762123383183,762123402512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57601536,57601600⟩ : DyadicInterval 40),(⟨-57604608,-57604544⟩ : DyadicInterval 40),(⟨762123382070,762123401399⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3072,-704⟩ : DyadicInterval 40),(⟨762123383968,762123404416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨223213757274,223469553074⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203220740992,203220741056⟩ : DyadicInterval 40),(⟨-249496030144,-249496030080⟩ : DyadicInterval 40),(⟨739307620763,739307640092⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203433349952,203433350016⟩ : DyadicInterval 40),(⟨-249817030016,-249817029952⟩ : DyadicInterval 40),(⟨739254928592,739254947922⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-46383680064,-46275289088⟩ : DyadicInterval 40),(⟨785261028160,785315242912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨203267142400,203456560768⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-249852083392,-249566074304⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1221_ok : ecellOkT e1221 = true := by decide +kernel
theorem e1221_pos {a z : ℝ} (ha1 : ((3249/16000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((832593/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1221 e1221_ok ha1 ha2 hz1 hz2 hz

-- box ['832593/4096000', '416721/2048000', '1999/2000', '3999/4000']  interval_lower 578584609/1099511627776
noncomputable def e1222 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1323009109393,0,true,203456560704,203456560768⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨876014146159,0,false,-249852083392,-249852083328⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1323237011096,0,true,203645946432,203645946496⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨875786244456,0,false,-250138166912,-250138166848⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1322897360652,0,true,203363685888,203363685952⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨876125894900,0,false,-249711833152,-249711833088⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1323181079751,0,true,203599470656,203599470720⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨875842175801,0,false,-250067949760,-250067949696⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540428701,0,true,28800512,28800576⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482826851,0,false,-28801344,-28801280⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569293250,0,true,57663936,57664000⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453962302,0,false,-57667008,-57666944⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624751,0,false,-3072,-3008⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627022,0,false,-768,-704⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1322953229772,0,true,203410119936,203410120000⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨876070025780,0,false,-249781949440,-249781949376⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1323209054067,0,true,203622715968,203622716032⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨875814201485,0,false,-250103068608,-250103068544⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1054000023109,0,false,-46480352640,-46480352576⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1054104059324,0,false,-46371829504,-46371829440⟩
    { al := (832593/4096000), au := (416721/2048000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨223497481617,223725383320⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203456560704,203456560768⟩ : DyadicInterval 40),(⟨-249852083392,-249852083328⟩ : DyadicInterval 40),(⟨739249171762,739249191091⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203645946432,203645946496⟩ : DyadicInterval 40),(⟨-250138166912,-250138166848⟩ : DyadicInterval 40),(⟨739202167254,739202186583⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203363685888,203363685952⟩ : DyadicInterval 40),(⟨-249711833152,-249711833088⟩ : DyadicInterval 40),(⟨739272201828,739272221158⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203599470656,203599470720⟩ : DyadicInterval 40),(⟨-250067949760,-250067949696⟩ : DyadicInterval 40),(⟨739213707595,739213726925⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨28800925,57665474⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28800512,28800576⟩ : DyadicInterval 40),(⟨-28801344,-28801280⟩ : DyadicInterval 40),(⟨762123383213,762123402542⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57663936,57664000⟩ : DyadicInterval 40),(⟨-57667008,-57666944⟩ : DyadicInterval 40),(⟨762123382063,762123401392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3072,-704⟩ : DyadicInterval 40),(⟨762123383968,762123404416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨223441601996,223697426291⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203410119936,203410120000⟩ : DyadicInterval 40),(⟨-249781949440,-249781949376⟩ : DyadicInterval 40),(⟨739260689341,739260708671⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203622715968,203622716032⟩ : DyadicInterval 40),(⟨-250103068608,-250103068544⟩ : DyadicInterval 40),(⟨739207936007,739207955337⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-46480352640,-46371829440⟩ : DyadicInterval 40),(⟨785309298336,785363579200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨203456560704,203645946496⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-250138166912,-249852083328⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1222_ok : ecellOkT e1222 = true := by decide +kernel
theorem e1222_pos {a z : ℝ} (ha1 : ((832593/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((416721/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1222 e1222_ok ha1 ha2 hz1 hz2 hz

-- box ['3249/16000', '832593/4096000', '3999/4000', '1']  interval_lower 286311549/549755813888
noncomputable def e1223 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1322781207691,0,true,203267142400,203267142464⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨876242047861,0,false,-249566074368,-249566074304⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1323009109394,0,true,203456560704,203456560768⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨876014146158,0,false,-249852083392,-249852083328⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1322725390296,0,true,203220745344,203220745408⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨876297865256,0,false,-249496036736,-249496036672⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540429665,0,true,28801472,28801536⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482825887,0,false,-28802304,-28802240⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627021,0,false,-768,-704⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1322753293430,0,true,203243939520,203243939584⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨876269962122,0,false,-249531048000,-249531047936⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1323009117928,0,true,203456567808,203456567872⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨876014137624,0,false,-249852094144,-249852094080⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1054081341417,0,false,-46395526272,-46395526208⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1054185284676,0,false,-46287108480,-46287108416⟩
    { al := (3249/16000), au := (832593/4096000), zl := (3999/4000), zu := 1,
      A := ⟨223269579915,223497481618⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203267142400,203267142464⟩ : DyadicInterval 40),(⟨-249566074368,-249566074304⟩ : DyadicInterval 40),(⟨739296126995,739296146325⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203456560704,203456560768⟩ : DyadicInterval 40),(⟨-249852083392,-249852083328⟩ : DyadicInterval 40),(⟨739249171761,739249191090⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203220745344,203220745408⟩ : DyadicInterval 40),(⟨-249496036736,-249496036672⟩ : DyadicInterval 40),(⟨739307619692,739307639021⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203456560704,203456560768⟩ : DyadicInterval 40),(⟨-249852083392,-249852083328⟩ : DyadicInterval 40),(⟨739249171761,739249191090⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,28801889⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28801472,28801536⟩ : DyadicInterval 40),(⟨-28802304,-28802240⟩ : DyadicInterval 40),(⟨762123383213,762123402542⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-768,0⟩ : DyadicInterval 40),(⟨762123383616,762123403264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨223241665654,223497490152⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203243939520,203243939584⟩ : DyadicInterval 40),(⟨-249531048000,-249531047936⟩ : DyadicInterval 40),(⟨739301874836,739301894166⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203456567808,203456567872⟩ : DyadicInterval 40),(⟨-249852094144,-249852094080⟩ : DyadicInterval 40),(⟨739249170011,739249189341⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-46395526272,-46287108416⟩ : DyadicInterval 40),(⟨785266937824,785321166016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨203267142400,203456560768⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-249852083392,-249566074304⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1223_ok : ecellOkT e1223 = true := by decide +kernel
theorem e1223_pos {a z : ℝ} (ha1 : ((3249/16000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((832593/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1223 e1223_ok ha1 ha2 hz1 hz2 hz

-- box ['832593/4096000', '416721/2048000', '3999/4000', '1']  interval_lower 577655191/1099511627776
noncomputable def e1224 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1323009109393,0,true,203456560704,203456560768⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨876014146159,0,false,-249852083392,-249852083328⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1323237011096,0,true,203645946432,203645946496⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨875786244456,0,false,-250138166912,-250138166848⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1322953235022,0,true,203410124288,203410124352⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨876070020530,0,false,-249781956032,-249781955968⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540460867,0,true,28832704,28832768⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482794685,0,false,-28833472,-28833408⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627019,0,false,-768,-704⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1322981166642,0,true,203433338112,203433338176⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨876042088910,0,false,-249817012160,-249817012096⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1323237019632,0,true,203645953536,203645953600⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨875786235920,0,false,-250138177600,-250138177536⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1053988643119,0,false,-46492224064,-46492224000⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1054092704011,0,false,-46383674048,-46383673984⟩
    { al := (832593/4096000), au := (416721/2048000), zl := (3999/4000), zu := 1,
      A := ⟨223497481617,223725383320⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203456560704,203456560768⟩ : DyadicInterval 40),(⟨-249852083392,-249852083328⟩ : DyadicInterval 40),(⟨739249171762,739249191091⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203645946432,203645946496⟩ : DyadicInterval 40),(⟨-250138166912,-250138166848⟩ : DyadicInterval 40),(⟨739202167254,739202186583⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203410124288,203410124352⟩ : DyadicInterval 40),(⟨-249781956032,-249781955968⟩ : DyadicInterval 40),(⟨739260688267,739260707597⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203645946432,203645946496⟩ : DyadicInterval 40),(⟨-250138166912,-250138166848⟩ : DyadicInterval 40),(⟨739202167254,739202186583⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,28833091⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28832704,28832768⟩ : DyadicInterval 40),(⟨-28833472,-28833408⟩ : DyadicInterval 40),(⟨762123383179,762123402508⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-768,0⟩ : DyadicInterval 40),(⟨762123383616,762123403264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨223469538866,223725391856⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203433338112,203433338176⟩ : DyadicInterval 40),(⟨-249817012160,-249817012096⟩ : DyadicInterval 40),(⟨739254931531,739254950860⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203645953536,203645953600⟩ : DyadicInterval 40),(⟨-250138177600,-250138177536⟩ : DyadicInterval 40),(⟨739202165474,739202184804⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-46492224064,-46383673984⟩ : DyadicInterval 40),(⟨785315220608,785369514912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨203456560704,203645946496⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-250138166912,-249852083328⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1224_ok : ecellOkT e1224 = true := by decide +kernel
theorem e1224_pos {a z : ℝ} (ha1 : ((832593/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((416721/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1224 e1224_ok ha1 ha2 hz1 hz2 hz

-- box ['416721/2048000', '834291/4096000', '1999/2000', '3999/4000']  interval_lower 583640121/1099511627776
noncomputable def e1225 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1323237011095,0,true,203645946432,203645946496⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨875786244457,0,false,-250138166912,-250138166848⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1323464912798,0,true,203835299456,203835299520⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨875558342754,0,false,-250424324800,-250424324736⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1323125148403,0,true,203552992896,203552992960⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨875898107149,0,false,-249997737088,-249997737024⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1323408924477,0,true,203788784384,203788784448⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨875614331075,0,false,-250354017856,-250354017792⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540459901,0,true,28831744,28831808⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482795651,0,false,-28832512,-28832448⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569355666,0,true,57726336,57726400⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453899886,0,false,-57729408,-57729344⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624745,0,false,-3072,-3008⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627020,0,false,-768,-704⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1323181074497,0,true,203599466240,203599466304⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨875842181055,0,false,-250067943168,-250067943104⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1323436927280,0,true,203812049344,203812049408⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨875586328272,0,false,-250389181632,-250389181568⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1053907253532,0,false,-46577132224,-46577132160⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1054011407376,0,false,-46468476864,-46468476800⟩
    { al := (416721/2048000), au := (834291/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨223725383319,223953285022⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203645946432,203645946496⟩ : DyadicInterval 40),(⟨-250138166912,-250138166848⟩ : DyadicInterval 40),(⟨739202167254,739202186584⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203835299456,203835299520⟩ : DyadicInterval 40),(⟨-250424324800,-250424324736⟩ : DyadicInterval 40),(⟨739155113487,739155132816⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203552992896,203552992960⟩ : DyadicInterval 40),(⟨-249997737088,-249997737024⟩ : DyadicInterval 40),(⟨739225244980,739225264310⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203788784384,203788784448⟩ : DyadicInterval 40),(⟨-250354017856,-250354017792⟩ : DyadicInterval 40),(⟨739166677678,739166697008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨28832125,57727890⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28831744,28831808⟩ : DyadicInterval 40),(⟨-28832512,-28832448⟩ : DyadicInterval 40),(⟨762123383179,762123402508⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57726336,57726400⟩ : DyadicInterval 40),(⟨-57729408,-57729344⟩ : DyadicInterval 40),(⟨762123382057,762123401386⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3072,-704⟩ : DyadicInterval 40),(⟨762123383968,762123404416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨223669446721,223925299504⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203599466240,203599466304⟩ : DyadicInterval 40),(⟨-250067943168,-250067943104⟩ : DyadicInterval 40),(⟨739213708711,739213728041⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203812049344,203812049408⟩ : DyadicInterval 40),(⟨-250389181632,-250389181568⟩ : DyadicInterval 40),(⟨739160894176,739160913505⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-46577132224,-46468476800⟩ : DyadicInterval 40),(⟨785357622016,785411968992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨203645946432,203835299520⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-250424324800,-250138166848⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1225_ok : ecellOkT e1225 = true := by decide +kernel
theorem e1225_pos {a z : ℝ} (ha1 : ((416721/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((834291/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1225 e1225_ok ha1 ha2 hz1 hz2 hz

-- box ['834291/4096000', '41757/204800', '1999/2000', '3999/4000']  interval_lower 294357879/549755813888
noncomputable def e1226 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1323464912797,0,true,203835299456,203835299520⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨875558342755,0,false,-250424324800,-250424324736⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1323692814500,0,true,204024619968,204024620032⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨875330441052,0,false,-250710557248,-250710557184⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1323352936154,0,true,203742267328,203742267392⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨875670319398,0,false,-250283715392,-250283715328⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1323636769204,0,true,203978065536,203978065600⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨875386486348,0,false,-250640160448,-250640160384⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540491109,0,true,28862912,28862976⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482764443,0,false,-28863744,-28863680⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569418093,0,true,57788736,57788800⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453837459,0,false,-57791872,-57791808⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624738,0,false,-3072,-3008⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627019,0,false,-768,-704⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1323408919220,0,true,203788780032,203788780096⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨875614336332,0,false,-250354011264,-250354011200⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1323664800495,0,true,204001350144,204001350208⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨875358455057,0,false,-250675369152,-250675369088⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1053814389501,0,false,-46674018944,-46674018880⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1053918661000,0,false,-46565231232,-46565231168⟩
    { al := (834291/4096000), au := (41757/204800), zl := (1999/2000), zu := (3999/4000),
      A := ⟨223953285021,224181186724⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203835299456,203835299520⟩ : DyadicInterval 40),(⟨-250424324800,-250424324736⟩ : DyadicInterval 40),(⟨739155113487,739155132816⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204024619968,204024620032⟩ : DyadicInterval 40),(⟨-250710557248,-250710557184⟩ : DyadicInterval 40),(⟨739108010407,739108029736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203742267328,203742267392⟩ : DyadicInterval 40),(⟨-250283715392,-250283715328⟩ : DyadicInterval 40),(⟨739178238900,739178258230⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203978065536,203978065600⟩ : DyadicInterval 40),(⟨-250640160448,-250640160384⟩ : DyadicInterval 40),(⟨739119598514,739119617844⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨28863333,57790317⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28862912,28862976⟩ : DyadicInterval 40),(⟨-28863744,-28863680⟩ : DyadicInterval 40),(⟨762123383210,762123402539⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57788736,57788800⟩ : DyadicInterval 40),(⟨-57791872,-57791808⟩ : DyadicInterval 40),(⟨762123382082,762123401411⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3072,-704⟩ : DyadicInterval 40),(⟨762123383968,762123404416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨223897291444,224153172719⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203788780032,203788780096⟩ : DyadicInterval 40),(⟨-250354011264,-250354011200⟩ : DyadicInterval 40),(⟨739166678759,739166698088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204001350144,204001350208⟩ : DyadicInterval 40),(⟨-250675369152,-250675369088⟩ : DyadicInterval 40),(⟨739113803071,739113822400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-46674018944,-46565231168⟩ : DyadicInterval 40),(⟨785405999200,785460412352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨203835299456,204024620032⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-250710557248,-250424324736⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1226_ok : ecellOkT e1226 = true := by decide +kernel
theorem e1226_pos {a z : ℝ} (ha1 : ((834291/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((41757/204800 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1226 e1226_ok ha1 ha2 hz1 hz2 hz

-- box ['416721/2048000', '834291/4096000', '3999/4000', '1']  interval_lower 72838431/137438953472
noncomputable def e1227 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1323237011095,0,true,203645946432,203645946496⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨875786244457,0,false,-250138166912,-250138166848⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1323464912798,0,true,203835299456,203835299520⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨875558342754,0,false,-250424324800,-250424324736⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1323181079749,0,true,203599470656,203599470720⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨875842175803,0,false,-250067949760,-250067949696⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540492076,0,true,28863872,28863936⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482763476,0,false,-28864704,-28864640⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627018,0,false,-768,-704⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1323209039853,0,true,203622704128,203622704192⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨875814215699,0,false,-250103050752,-250103050688⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1323464921331,0,true,203835306560,203835306624⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨875558334221,0,false,-250424335552,-250424335488⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1053895850346,0,false,-46589028928,-46589028864⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1054000028894,0,false,-46480346624,-46480346560⟩
    { al := (416721/2048000), au := (834291/4096000), zl := (3999/4000), zu := 1,
      A := ⟨223725383319,223953285022⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203645946432,203645946496⟩ : DyadicInterval 40),(⟨-250138166912,-250138166848⟩ : DyadicInterval 40),(⟨739202167254,739202186584⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203835299456,203835299520⟩ : DyadicInterval 40),(⟨-250424324800,-250424324736⟩ : DyadicInterval 40),(⟨739155113487,739155132816⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203599470656,203599470720⟩ : DyadicInterval 40),(⟨-250067949760,-250067949696⟩ : DyadicInterval 40),(⟨739213707596,739213726926⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203835299456,203835299520⟩ : DyadicInterval 40),(⟨-250424324800,-250424324736⟩ : DyadicInterval 40),(⟨739155113487,739155132816⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,28864300⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28863872,28863936⟩ : DyadicInterval 40),(⟨-28864704,-28864640⟩ : DyadicInterval 40),(⟨762123383210,762123402539⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-768,0⟩ : DyadicInterval 40),(⟨762123383616,762123403264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨223697412077,223953293555⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203622704128,203622704192⟩ : DyadicInterval 40),(⟨-250103050752,-250103050688⟩ : DyadicInterval 40),(⟨739207938953,739207958282⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203835306560,203835306624⟩ : DyadicInterval 40),(⟨-250424335552,-250424335488⟩ : DyadicInterval 40),(⟨739155111729,739155131059⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-46589028928,-46480346560⟩ : DyadicInterval 40),(⟨785363556896,785417917344⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨203645946432,203835299520⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-250424324800,-250138166848⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1227_ok : ecellOkT e1227 = true := by decide +kernel
theorem e1227_pos {a z : ℝ} (ha1 : ((416721/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((834291/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1227 e1227_ok ha1 ha2 hz1 hz2 hz

-- box ['834291/4096000', '41757/204800', '3999/4000', '1']  interval_lower 293889607/549755813888
noncomputable def e1228 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1323464912797,0,true,203835299456,203835299520⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨875558342755,0,false,-250424324800,-250424324736⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1323692814500,0,true,204024619968,204024620032⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨875330441052,0,false,-250710557248,-250710557184⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1323408924475,0,true,203788784384,203788784448⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨875614331077,0,false,-250354017856,-250354017792⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540523290,0,true,28895104,28895168⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482732262,0,false,-28895936,-28895872⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627016,0,false,-768,-704⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1323436913061,0,true,203812037568,203812037632⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨875586342491,0,false,-250389163776,-250389163712⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1323692823038,0,true,204024627072,204024627136⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨875330432514,0,false,-250710568000,-250710567936⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1053802963092,0,false,-46685940928,-46685940864⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1053907259325,0,false,-46577126208,-46577126144⟩
    { al := (834291/4096000), au := (41757/204800), zl := (3999/4000), zu := 1,
      A := ⟨223953285021,224181186724⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203835299456,203835299520⟩ : DyadicInterval 40),(⟨-250424324800,-250424324736⟩ : DyadicInterval 40),(⟨739155113487,739155132816⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204024619968,204024620032⟩ : DyadicInterval 40),(⟨-250710557248,-250710557184⟩ : DyadicInterval 40),(⟨739108010407,739108029736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203788784384,203788784448⟩ : DyadicInterval 40),(⟨-250354017856,-250354017792⟩ : DyadicInterval 40),(⟨739166677679,739166697008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204024619968,204024620032⟩ : DyadicInterval 40),(⟨-250710557248,-250710557184⟩ : DyadicInterval 40),(⟨739108010407,739108029736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,28895514⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28895104,28895168⟩ : DyadicInterval 40),(⟨-28895936,-28895872⟩ : DyadicInterval 40),(⟨762123383208,762123402537⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-768,0⟩ : DyadicInterval 40),(⟨762123383616,762123403264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨223925285285,224181195262⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203812037568,203812037632⟩ : DyadicInterval 40),(⟨-250389163776,-250389163712⟩ : DyadicInterval 40),(⟨739160897090,739160916419⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204024627072,204024627136⟩ : DyadicInterval 40),(⟨-250710568000,-250710567936⟩ : DyadicInterval 40),(⟨739108008645,739108027974⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-46685940928,-46577126144⟩ : DyadicInterval 40),(⟨785411946688,785466373344⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨203835299456,204024620032⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-250710557248,-250424324736⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1228_ok : ecellOkT e1228 = true := by decide +kernel
theorem e1228_pos {a z : ℝ} (ha1 : ((834291/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((41757/204800 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1228 e1228_ok ha1 ha2 hz1 hz2 hz

-- box ['41757/204800', '835989/4096000', '999/1000', '3997/4000']  interval_lower 297844271/549755813888
noncomputable def e1229 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1323692814499,0,true,204024619968,204024620032⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨875330441053,0,false,-250710557248,-250710557184⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1323920716202,0,true,204213907840,204213907904⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨875102539350,0,false,-250996864192,-250996864128⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1323468633312,0,true,203838390400,203838390464⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨875554622240,0,false,-250428996992,-250428996928⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1323752409386,0,true,204074120704,204074120768⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨875270846166,0,false,-250785417536,-250785417472⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099598310568,0,true,86679360,86679424⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099424944984,0,false,-86686272,-86686208⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099627331214,0,true,115697344,115697408⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099395924338,0,false,-115709568,-115709504⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511615600,0,false,-12224,-12160⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620943,0,false,-6848,-6784⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1323580719921,0,true,203931505792,203931505856⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨875442535631,0,false,-250569763072,-250569763008⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1323836572292,0,true,204144024384,204144024448⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨875186683260,0,false,-250891147712,-250891147648⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1053744325765,0,false,-46747123328,-46747123264⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1053848665434,0,false,-46638257280,-46638257216⟩
    { al := (41757/204800), au := (835989/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨224181186723,224409088426⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204024619968,204024620032⟩ : DyadicInterval 40),(⟨-250710557248,-250710557184⟩ : DyadicInterval 40),(⟨739108010407,739108029736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204213907840,204213907904⟩ : DyadicInterval 40),(⟨-250996864192,-250996864128⟩ : DyadicInterval 40),(⟨739060858053,739060877382⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203838390400,203838390464⟩ : DyadicInterval 40),(⟨-250428996992,-250428996928⟩ : DyadicInterval 40),(⟨739154344924,739154364253⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204074120704,204074120768⟩ : DyadicInterval 40),(⟨-250785417536,-250785417472⟩ : DyadicInterval 40),(⟨739095685125,739095704454⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨86682792,115703438⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨86679360,86679424⟩ : DyadicInterval 40),(⟨-86686272,-86686208⟩ : DyadicInterval 40),(⟨762123380173,762123399503⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨115697344,115697408⟩ : DyadicInterval 40),(⟨-115709568,-115709504⟩ : DyadicInterval 40),(⟨762123377487,762123396817⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-12224,-6784⟩ : DyadicInterval 40),(⟨762123387008,762123408992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨224069092145,224324944516⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203931505792,203931505856⟩ : DyadicInterval 40),(⟨-250569763072,-250569763008⟩ : DyadicInterval 40),(⟨739131184452,739131203782⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204144024384,204144024448⟩ : DyadicInterval 40),(⟨-250891147712,-250891147648⟩ : DyadicInterval 40),(⟨739078272982,739078292311⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-46747123328,-46638257216⟩ : DyadicInterval 40),(⟨785442512224,785496964544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨204024619968,204213907904⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-250996864192,-250710557184⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1229_ok : ecellOkT e1229 = true := by decide +kernel
theorem e1229_pos {a z : ℝ} (ha1 : ((41757/204800 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((835989/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1229 e1229_ok ha1 ha2 hz1 hz2 hz

-- box ['835989/4096000', '418419/2048000', '999/1000', '3997/4000']  interval_lower 300405427/549755813888
noncomputable def e1230 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1323920716201,0,true,204213907840,204213907904⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨875102539351,0,false,-250996864192,-250996864128⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1324148617905,0,true,204403163136,204403163200⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨874874637647,0,false,-251283245760,-251283245696⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1323696307112,0,true,204027521024,204027521088⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨875326948440,0,false,-250714944384,-250714944320⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1323980140163,0,true,204263258112,204263258176⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨875043115389,0,false,-251071529216,-251071529152⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099598404221,0,true,86772992,86773056⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099424851331,0,false,-86779904,-86779840⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099627456110,0,true,115822208,115822272⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099395799442,0,false,-115834496,-115834432⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511615574,0,false,-12224,-12160⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620928,0,false,-6912,-6848⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1323808507671,0,true,204120715072,204120715136⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨875214747881,0,false,-250855890240,-250855890176⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1324064388534,0,true,204333220736,204333220800⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨874958867018,0,false,-251177394304,-251177394240⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1053651319353,0,false,-46844173568,-46844173504⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1053755776670,0,false,-46735175104,-46735175040⟩
    { al := (835989/4096000), au := (418419/2048000), zl := (999/1000), zu := (3997/4000),
      A := ⟨224409088425,224636990129⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204213907840,204213907904⟩ : DyadicInterval 40),(⟨-250996864192,-250996864128⟩ : DyadicInterval 40),(⟨739060858053,739060877382⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204403163136,204403163200⟩ : DyadicInterval 40),(⟨-251283245760,-251283245696⟩ : DyadicInterval 40),(⟨739013656425,739013675754⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204027521024,204027521088⟩ : DyadicInterval 40),(⟨-250714944384,-250714944320⟩ : DyadicInterval 40),(⟨739107288198,739107307528⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204263258112,204263258176⟩ : DyadicInterval 40),(⟨-251071529216,-251071529152⟩ : DyadicInterval 40),(⟨739048555276,739048574606⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨86776445,115828334⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨86772992,86773056⟩ : DyadicInterval 40),(⟨-86779904,-86779840⟩ : DyadicInterval 40),(⟨762123380159,762123399488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨115822208,115822272⟩ : DyadicInterval 40),(⟨-115834496,-115834432⟩ : DyadicInterval 40),(⟨762123377493,762123396823⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-12224,-6848⟩ : DyadicInterval 40),(⟨762123387040,762123408992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨224296879895,224552760758⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204120715072,204120715136⟩ : DyadicInterval 40),(⟨-250855890240,-250855890176⟩ : DyadicInterval 40),(⟨739084079922,739084099251⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204333220736,204333220800⟩ : DyadicInterval 40),(⟨-251177394304,-251177394240⟩ : DyadicInterval 40),(⟨739031107241,739031126571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-46844173568,-46735175040⟩ : DyadicInterval 40),(⟨785490971136,785545489664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨204213907840,204403163200⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-251283245760,-250996864128⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1230_ok : ecellOkT e1230 = true := by decide +kernel
theorem e1230_pos {a z : ℝ} (ha1 : ((835989/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((418419/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1230 e1230_ok ha1 ha2 hz1 hz2 hz

-- box ['41757/204800', '835989/4096000', '3997/4000', '1999/2000']  interval_lower 74343779/137438953472
noncomputable def e1231 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1323692814499,0,true,204024619968,204024620032⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨875330441053,0,false,-250710557248,-250710557184⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1323920716202,0,true,204213907840,204213907904⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨875102539350,0,false,-250996864192,-250996864128⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1323524678608,0,true,203884950784,203884950848⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨875498576944,0,false,-250499380288,-250499380224⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1323808511658,0,true,204120718400,204120718464⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨875214743894,0,false,-250855895232,-250855895168⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569416671,0,true,57787328,57787392⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453838881,0,false,-57790464,-57790400⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099598406101,0,true,86774848,86774912⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099424849451,0,false,-86781760,-86781696⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620927,0,false,-6912,-6848⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624739,0,false,-3072,-3008⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1323608741829,0,true,203954783680,203954783744⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨875414513723,0,false,-250604957760,-250604957696⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1323864622897,0,true,204167321536,204167321600⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨875158632655,0,false,-250926388736,-250926388672⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1053732879149,0,false,-46759067136,-46759067072⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1053837243570,0,false,-46650174080,-46650174016⟩
    { al := (41757/204800), au := (835989/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨224181186723,224409088426⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204024619968,204024620032⟩ : DyadicInterval 40),(⟨-250710557248,-250710557184⟩ : DyadicInterval 40),(⟨739108010407,739108029736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204213907840,204213907904⟩ : DyadicInterval 40),(⟨-250996864192,-250996864128⟩ : DyadicInterval 40),(⟨739060858053,739060877382⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203884950784,203884950848⟩ : DyadicInterval 40),(⟨-250499380288,-250499380224⟩ : DyadicInterval 40),(⟨739142765741,739142785070⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204120718400,204120718464⟩ : DyadicInterval 40),(⟨-250855895232,-250855895168⟩ : DyadicInterval 40),(⟨739084079080,739084098410⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨57788895,86778325⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57787328,57787392⟩ : DyadicInterval 40),(⟨-57790464,-57790400⟩ : DyadicInterval 40),(⟨762123382082,762123401411⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨86774848,86774912⟩ : DyadicInterval 40),(⟨-86781760,-86781696⟩ : DyadicInterval 40),(⟨762123380158,762123399488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6912,-3008⟩ : DyadicInterval 40),(⟨762123385120,762123406336⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨224097114053,224352995121⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203954783680,203954783744⟩ : DyadicInterval 40),(⟨-250604957760,-250604957696⟩ : DyadicInterval 40),(⟨739125392396,739125411725⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204167321536,204167321600⟩ : DyadicInterval 40),(⟨-250926388736,-250926388672⟩ : DyadicInterval 40),(⟨739072468223,739072487552⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-46759067136,-46650174016⟩ : DyadicInterval 40),(⟨785448470624,785502936448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨204024619968,204213907904⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-250996864192,-250710557184⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1231_ok : ecellOkT e1231 = true := by decide +kernel
theorem e1231_pos {a z : ℝ} (ha1 : ((41757/204800 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((835989/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1231 e1231_ok ha1 ha2 hz1 hz2 hz

-- box ['835989/4096000', '418419/2048000', '3997/4000', '1999/2000']  interval_lower 599868775/1099511627776
noncomputable def e1232 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1323920716201,0,true,204213907840,204213907904⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨875102539351,0,false,-250996864192,-250996864128⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1324148617905,0,true,204403163136,204403163200⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨874874637647,0,false,-251283245760,-251283245696⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1323752409384,0,true,204074120704,204074120768⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨875270846168,0,false,-250785417536,-250785417472⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1324036299411,0,true,204309895104,204309895168⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨874986956141,0,false,-251142096896,-251142096832⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569479108,0,true,57849792,57849856⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453776444,0,false,-57852864,-57852800⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099598499775,0,true,86868544,86868608⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099424755777,0,false,-86875456,-86875392⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620912,0,false,-6912,-6848⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624733,0,false,-3072,-3008⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1323836558064,0,true,204144012544,204144012608⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨875186697488,0,false,-250891129856,-250891129792⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1324092467622,0,true,204356537536,204356537600⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨874930787930,0,false,-251212680320,-251212680256⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1053639849477,0,false,-46856142720,-46856142656⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1053744331572,0,false,-46747117248,-46747117184⟩
    { al := (835989/4096000), au := (418419/2048000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨224409088425,224636990129⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204213907840,204213907904⟩ : DyadicInterval 40),(⟨-250996864192,-250996864128⟩ : DyadicInterval 40),(⟨739060858053,739060877382⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204403163136,204403163200⟩ : DyadicInterval 40),(⟨-251283245760,-251283245696⟩ : DyadicInterval 40),(⟨739013656425,739013675754⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204074120704,204074120768⟩ : DyadicInterval 40),(⟨-250785417536,-250785417472⟩ : DyadicInterval 40),(⟨739095685125,739095704454⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204309895104,204309895168⟩ : DyadicInterval 40),(⟨-251142096896,-251142096832⟩ : DyadicInterval 40),(⟨739036925327,739036944656⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨57851332,86871999⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57849792,57849856⟩ : DyadicInterval 40),(⟨-57852864,-57852800⟩ : DyadicInterval 40),(⟨762123382044,762123401373⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨86868544,86868608⟩ : DyadicInterval 40),(⟨-86875456,-86875392⟩ : DyadicInterval 40),(⟨762123380144,762123399473⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6912,-3008⟩ : DyadicInterval 40),(⟨762123385120,762123406336⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨224324930288,224580839846⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204144012544,204144012608⟩ : DyadicInterval 40),(⟨-250891129856,-250891129792⟩ : DyadicInterval 40),(⟨739078275947,739078295277⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204356537536,204356537600⟩ : DyadicInterval 40),(⟨-251212680320,-251212680256⟩ : DyadicInterval 40),(⟨739025290522,739025309851⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-46856142720,-46747117184⟩ : DyadicInterval 40),(⟨785496942208,785551474240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨204213907840,204403163200⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-251283245760,-250996864128⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1232_ok : ecellOkT e1232 = true := by decide +kernel
theorem e1232_pos {a z : ℝ} (ha1 : ((835989/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((418419/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1232 e1232_ok ha1 ha2 hz1 hz2 hz

-- box ['418419/2048000', '837687/4096000', '999/1000', '3997/4000']  interval_lower 605953091/1099511627776
noncomputable def e1233 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1324148617904,0,true,204403163136,204403163200⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨874874637648,0,false,-251283245760,-251283245696⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1324376519607,0,true,204592385856,204592385920⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨874646735945,0,false,-251569701888,-251569701824⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1323923980913,0,true,204216619136,204216619200⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨875099274639,0,false,-251000966144,-251000966080⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1324207870939,0,true,204452363008,204452363072⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨874815384613,0,false,-251357715392,-251357715328⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099598497890,0,true,86866624,86866688⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099424757662,0,false,-86873600,-86873536⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099627581028,0,true,115947136,115947200⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099395674524,0,false,-115959424,-115959360⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511615547,0,false,-12288,-12224⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620913,0,false,-6912,-6848⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1324036295422,0,true,204309891776,204309891840⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨874986960130,0,false,-251142091840,-251142091776⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1324292204776,0,true,204522384576,204522384640⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨874731050776,0,false,-251463715456,-251463715392⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1053558218534,0,false,-46941330880,-46941330816⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1053662793523,0,false,-46832200064,-46832200000⟩
    { al := (418419/2048000), au := (837687/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨224636990128,224864891831⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204403163136,204403163200⟩ : DyadicInterval 40),(⟨-251283245760,-251283245696⟩ : DyadicInterval 40),(⟨739013656425,739013675754⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204592385856,204592385920⟩ : DyadicInterval 40),(⟨-251569701888,-251569701824⟩ : DyadicInterval 40),(⟨738966405484,738966424813⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204216619136,204216619200⟩ : DyadicInterval 40),(⟨-251000966144,-251000966080⟩ : DyadicInterval 40),(⟨739060182268,739060201598⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204452363008,204452363072⟩ : DyadicInterval 40),(⟨-251357715392,-251357715328⟩ : DyadicInterval 40),(⟨739001376209,739001395538⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨86870114,115953252⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨86866624,86866688⟩ : DyadicInterval 40),(⟨-86873600,-86873536⟩ : DyadicInterval 40),(⟨762123380176,762123399505⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨115947136,115947200⟩ : DyadicInterval 40),(⟨-115959424,-115959360⟩ : DyadicInterval 40),(⟨762123377467,762123396797⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-12288,-6848⟩ : DyadicInterval 40),(⟨762123387040,762123409024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨224524667646,224780577000⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204309891776,204309891840⟩ : DyadicInterval 40),(⟨-251142091840,-251142091776⟩ : DyadicInterval 40),(⟨739036926145,739036945474⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204522384576,204522384640⟩ : DyadicInterval 40),(⟨-251463715456,-251463715392⟩ : DyadicInterval 40),(⟨738983892227,738983911557⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-46941330880,-46832200000⟩ : DyadicInterval 40),(⟨785539483616,785594068320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨204403163136,204592385920⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-251569701888,-251283245696⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1233_ok : ecellOkT e1233 = true := by decide +kernel
theorem e1233_pos {a z : ℝ} (ha1 : ((418419/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((837687/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1233 e1233_ok ha1 ha2 hz1 hz2 hz

-- box ['837687/4096000', '104817/512000', '999/1000', '3997/4000']  interval_lower 305557723/549755813888
noncomputable def e1234 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1324376519606,0,true,204592385856,204592385920⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨874646735946,0,false,-251569701888,-251569701824⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1324604421309,0,true,204781576000,204781576064⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨874418834243,0,false,-251856232704,-251856232640⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1324151654714,0,true,204405684736,204405684800⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨874871600838,0,false,-251287062336,-251287062272⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1324435601715,0,true,204641435328,204641435392⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨874587653837,0,false,-251643976064,-251643976000⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099598591578,0,true,86960320,86960384⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099424663974,0,false,-86967296,-86967232⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099627705971,0,true,116072064,116072128⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099395549581,0,false,-116084352,-116084288⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511615521,0,false,-12288,-12224⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620898,0,false,-6912,-6848⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1324264083174,0,true,204499035968,204499036032⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨874759172378,0,false,-251428368000,-251428367936⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1324520021012,0,true,204711515776,204711515840⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨874503234540,0,false,-251750111168,-251750111104⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1053465023313,0,false,-47038595328,-47038595264⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1053569715994,0,false,-46929332032,-46929331968⟩
    { al := (837687/4096000), au := (104817/512000), zl := (999/1000), zu := (3997/4000),
      A := ⟨224864891830,225092793533⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204592385856,204592385920⟩ : DyadicInterval 40),(⟨-251569701888,-251569701824⟩ : DyadicInterval 40),(⟨738966405484,738966424813⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204781576000,204781576064⟩ : DyadicInterval 40),(⟨-251856232704,-251856232640⟩ : DyadicInterval 40),(⟨738919105268,738919124597⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204405684736,204405684800⟩ : DyadicInterval 40),(⟨-251287062336,-251287062272⟩ : DyadicInterval 40),(⟨739013027146,739013046475⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204641435328,204641435392⟩ : DyadicInterval 40),(⟨-251643976064,-251643976000⟩ : DyadicInterval 40),(⟨738954147947,738954167277⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨86963802,116078195⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨86960320,86960384⟩ : DyadicInterval 40),(⟨-86967296,-86967232⟩ : DyadicInterval 40),(⟨762123380161,762123399491⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨116072064,116072128⟩ : DyadicInterval 40),(⟨-116084352,-116084288⟩ : DyadicInterval 40),(⟨762123377440,762123396770⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-12288,-6848⟩ : DyadicInterval 40),(⟨762123387040,762123409024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨224752455398,225008393236⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204499035968,204499036032⟩ : DyadicInterval 40),(⟨-251428368000,-251428367936⟩ : DyadicInterval 40),(⟨738989723121,738989742450⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204711515776,204711515840⟩ : DyadicInterval 40),(⟨-251750111168,-251750111104⟩ : DyadicInterval 40),(⟨738936628006,738936647335⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-47038595328,-46929331968⟩ : DyadicInterval 40),(⟨785588049600,785642700544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨204592385856,204781576064⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-251856232704,-251569701824⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1234_ok : ecellOkT e1234 = true := by decide +kernel
theorem e1234_pos {a z : ℝ} (ha1 : ((837687/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((104817/512000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1234 e1234_ok ha1 ha2 hz1 hz2 hz

-- box ['418419/2048000', '837687/4096000', '3997/4000', '1999/2000']  interval_lower 302503699/549755813888
noncomputable def e1235 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1324148617904,0,true,204403163136,204403163200⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨874874637648,0,false,-251283245760,-251283245696⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1324376519607,0,true,204592385856,204592385920⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨874646735945,0,false,-251569701888,-251569701824⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1323980140161,0,true,204263258112,204263258176⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨875043115391,0,false,-251071529216,-251071529152⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1324264087162,0,true,204499039296,204499039360⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨874759168390,0,false,-251428372992,-251428372928⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569541555,0,true,57912192,57912256⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453713997,0,false,-57915328,-57915264⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099598593466,0,true,86962240,86962304⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099424662086,0,false,-86969152,-86969088⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620897,0,false,-6912,-6848⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624726,0,false,-3072,-3008⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1324064374300,0,true,204333208896,204333208960⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨874958881252,0,false,-251177376448,-251177376384⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1324320312355,0,true,204545721024,204545721088⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨874702943197,0,false,-251499046464,-251499046400⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1053546725372,0,false,-46953325440,-46953325376⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1053651325168,0,false,-46844167488,-46844167424⟩
    { al := (418419/2048000), au := (837687/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨224636990128,224864891831⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204403163136,204403163200⟩ : DyadicInterval 40),(⟨-251283245760,-251283245696⟩ : DyadicInterval 40),(⟨739013656425,739013675754⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204592385856,204592385920⟩ : DyadicInterval 40),(⟨-251569701888,-251569701824⟩ : DyadicInterval 40),(⟨738966405484,738966424813⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204263258112,204263258176⟩ : DyadicInterval 40),(⟨-251071529216,-251071529152⟩ : DyadicInterval 40),(⟨739048555277,739048574606⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204499039296,204499039360⟩ : DyadicInterval 40),(⟨-251428372992,-251428372928⟩ : DyadicInterval 40),(⟨738989722276,738989741605⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨57913779,86965690⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57912192,57912256⟩ : DyadicInterval 40),(⟨-57915328,-57915264⟩ : DyadicInterval 40),(⟨762123382069,762123401398⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨86962240,86962304⟩ : DyadicInterval 40),(⟨-86969152,-86969088⟩ : DyadicInterval 40),(⟨762123380129,762123399458⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6912,-3008⟩ : DyadicInterval 40),(⟨762123385120,762123406336⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨224552746524,224808684579⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204333208896,204333208960⟩ : DyadicInterval 40),(⟨-251177376448,-251177376384⟩ : DyadicInterval 40),(⟨739031110214,739031129543⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204545721024,204545721088⟩ : DyadicInterval 40),(⟨-251499046464,-251499046400⟩ : DyadicInterval 40),(⟨738978063521,738978082850⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-46953325440,-46844167424⟩ : DyadicInterval 40),(⟨785545467328,785600065600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨204403163136,204592385920⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-251569701888,-251283245696⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1235_ok : ecellOkT e1235 = true := by decide +kernel
theorem e1235_pos {a z : ℝ} (ha1 : ((418419/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((837687/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1235 e1235_ok ha1 ha2 hz1 hz2 hz

-- box ['837687/4096000', '104817/512000', '3997/4000', '1999/2000']  interval_lower 152541543/274877906944
noncomputable def e1236 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1324376519606,0,true,204592385856,204592385920⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨874646735946,0,false,-251569701888,-251569701824⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1324604421309,0,true,204781576000,204781576064⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨874418834243,0,false,-251856232704,-251856232640⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1324207870937,0,true,204452363008,204452363072⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨874815384615,0,false,-251357715392,-251357715328⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1324491874913,0,true,204688150912,204688150976⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨874531380639,0,false,-251714723712,-251714723648⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569604015,0,true,57974656,57974720⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453651537,0,false,-57977792,-57977728⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099598687175,0,true,87055936,87056000⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099424568377,0,false,-87062848,-87062784⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620882,0,false,-6912,-6848⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624719,0,false,-3072,-3008⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1324292190538,0,true,204522372736,204522372800⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨874731065014,0,false,-251463697600,-251463697536⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1324548157077,0,true,204734871872,204734871936⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨874475098475,0,false,-251785487168,-251785487104⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1053453506842,0,false,-47050615296,-47050615232⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1053558224357,0,false,-46941324800,-46941324736⟩
    { al := (837687/4096000), au := (104817/512000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨224864891830,225092793533⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204592385856,204592385920⟩ : DyadicInterval 40),(⟨-251569701888,-251569701824⟩ : DyadicInterval 40),(⟨738966405484,738966424813⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204781576000,204781576064⟩ : DyadicInterval 40),(⟨-251856232704,-251856232640⟩ : DyadicInterval 40),(⟨738919105268,738919124597⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204452363008,204452363072⟩ : DyadicInterval 40),(⟨-251357715392,-251357715328⟩ : DyadicInterval 40),(⟨739001376209,739001395539⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204688150912,204688150976⟩ : DyadicInterval 40),(⟨-251714723712,-251714723648⟩ : DyadicInterval 40),(⟨738942470030,738942489359⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨57976239,87059399⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57974656,57974720⟩ : DyadicInterval 40),(⟨-57977792,-57977728⟩ : DyadicInterval 40),(⟨762123382062,762123401392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨87055936,87056000⟩ : DyadicInterval 40),(⟨-87062848,-87062784⟩ : DyadicInterval 40),(⟨762123380114,762123399443⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6912,-3008⟩ : DyadicInterval 40),(⟨762123385120,762123406336⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨224780562762,225036529301⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204522372736,204522372800⟩ : DyadicInterval 40),(⟨-251463697600,-251463697536⟩ : DyadicInterval 40),(⟨738983895207,738983914537⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204734871872,204734871936⟩ : DyadicInterval 40),(⟨-251785487168,-251785487104⟩ : DyadicInterval 40),(⟨738930787287,738930806617⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-47050615296,-46941324736⟩ : DyadicInterval 40),(⟨785594045984,785648710528⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨204592385856,204781576064⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-251856232704,-251569701824⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1236_ok : ecellOkT e1236 = true := by decide +kernel
theorem e1236_pos {a z : ℝ} (ha1 : ((837687/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((104817/512000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1236 e1236_ok ha1 ha2 hz1 hz2 hz

-- box ['41757/204800', '835989/4096000', '1999/2000', '3999/4000']  interval_lower 296905477/549755813888
noncomputable def e1237 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1323692814499,0,true,204024619968,204024620032⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨875330441053,0,false,-250710557248,-250710557184⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1323920716202,0,true,204213907840,204213907904⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨875102539350,0,false,-250996864192,-250996864128⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1323580723905,0,true,203931509120,203931509184⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨875442531647,0,false,-250569768128,-250569768064⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1323864613931,0,true,204167314112,204167314176⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨875158641621,0,false,-250926377472,-250926377408⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540522322,0,true,28894144,28894208⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482733230,0,false,-28894976,-28894912⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569480532,0,true,57851200,57851264⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453775020,0,false,-57854336,-57854272⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624731,0,false,-3072,-3008⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627017,0,false,-768,-704⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1323636763941,0,true,203978061184,203978061248⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨875386491611,0,false,-250640153792,-250640153728⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1323892673713,0,true,204190618368,204190618432⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨875130581839,0,false,-250961631168,-250961631104⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1053721431015,0,false,-46771012736,-46771012672⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1053825820194,0,false,-46662092608,-46662092544⟩
    { al := (41757/204800), au := (835989/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨224181186723,224409088426⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204024619968,204024620032⟩ : DyadicInterval 40),(⟨-250710557248,-250710557184⟩ : DyadicInterval 40),(⟨739108010407,739108029736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204213907840,204213907904⟩ : DyadicInterval 40),(⟨-250996864192,-250996864128⟩ : DyadicInterval 40),(⟨739060858053,739060877382⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203931509120,203931509184⟩ : DyadicInterval 40),(⟨-250569768128,-250569768064⟩ : DyadicInterval 40),(⟨739131183639,739131202968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204167314112,204167314176⟩ : DyadicInterval 40),(⟨-250926377472,-250926377408⟩ : DyadicInterval 40),(⟨739072470064,739072489394⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨28894546,57852756⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28894144,28894208⟩ : DyadicInterval 40),(⟨-28894976,-28894912⟩ : DyadicInterval 40),(⟨762123383208,762123402537⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57851200,57851264⟩ : DyadicInterval 40),(⟨-57854336,-57854272⟩ : DyadicInterval 40),(⟨762123382075,762123401405⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3072,-704⟩ : DyadicInterval 40),(⟨762123383968,762123404416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨224125136165,224381045937⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203978061184,203978061248⟩ : DyadicInterval 40),(⟨-250640153792,-250640153728⟩ : DyadicInterval 40),(⟨739119599572,739119618902⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204190618368,204190618432⟩ : DyadicInterval 40),(⟨-250961631168,-250961631104⟩ : DyadicInterval 40),(⟨739066662679,739066682008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-46771012736,-46662092544⟩ : DyadicInterval 40),(⟨785454429888,785508909248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨204024619968,204213907904⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-250996864192,-250710557184⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1237_ok : ecellOkT e1237 = true := by decide +kernel
theorem e1237_pos {a z : ℝ} (ha1 : ((41757/204800 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((835989/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1237 e1237_ok ha1 ha2 hz1 hz2 hz

-- box ['835989/4096000', '418419/2048000', '1999/2000', '3999/4000']  interval_lower 37432879/68719476736
noncomputable def e1238 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1323920716201,0,true,204213907840,204213907904⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨875102539351,0,false,-250996864192,-250996864128⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1324148617905,0,true,204403163136,204403163200⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨874874637647,0,false,-251283245760,-251283245696⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1323808511656,0,true,204120718400,204120718464⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨875214743896,0,false,-250855895232,-250855895168⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1324092458658,0,true,204356530112,204356530176⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨874930796894,0,false,-251212669056,-251212668992⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540553540,0,true,28925376,28925440⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482702012,0,false,-28926208,-28926144⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569542983,0,true,57913664,57913728⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453712569,0,false,-57916736,-57916672⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624725,0,false,-3072,-3008⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627016,0,false,-768,-704⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1323864608668,0,true,204167309760,204167309824⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨875158646884,0,false,-250926370880,-250926370816⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1324120546925,0,true,204379854016,204379854080⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨874902708627,0,false,-251247967680,-251247967616⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1053628378079,0,false,-46868113600,-46868113536⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1053732884957,0,false,-46759061120,-46759061056⟩
    { al := (835989/4096000), au := (418419/2048000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨224409088425,224636990129⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204213907840,204213907904⟩ : DyadicInterval 40),(⟨-250996864192,-250996864128⟩ : DyadicInterval 40),(⟨739060858053,739060877382⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204403163136,204403163200⟩ : DyadicInterval 40),(⟨-251283245760,-251283245696⟩ : DyadicInterval 40),(⟨739013656425,739013675754⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204120718400,204120718464⟩ : DyadicInterval 40),(⟨-250855895232,-250855895168⟩ : DyadicInterval 40),(⟨739084079080,739084098410⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204356530112,204356530176⟩ : DyadicInterval 40),(⟨-251212669056,-251212668992⟩ : DyadicInterval 40),(⟨739025292368,739025311697⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨28925764,57915207⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28925376,28925440⟩ : DyadicInterval 40),(⟨-28926208,-28926144⟩ : DyadicInterval 40),(⟨762123383207,762123402536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57913664,57913728⟩ : DyadicInterval 40),(⟨-57916736,-57916672⟩ : DyadicInterval 40),(⟨762123382037,762123401366⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3072,-704⟩ : DyadicInterval 40),(⟨762123383968,762123404416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨224352980892,224608919149⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204167309760,204167309824⟩ : DyadicInterval 40),(⟨-250926370880,-250926370816⟩ : DyadicInterval 40),(⟨739072471150,739072490480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204379854016,204379854080⟩ : DyadicInterval 40),(⟨-251247967680,-251247967616⟩ : DyadicInterval 40),(⟨739019472990,739019492319⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-46868113600,-46759061056⟩ : DyadicInterval 40),(⟨785502914144,785557459680⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨204213907840,204403163200⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-251283245760,-250996864128⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1238_ok : ecellOkT e1238 = true := by decide +kernel
theorem e1238_pos {a z : ℝ} (ha1 : ((835989/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((418419/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1238 e1238_ok ha1 ha2 hz1 hz2 hz

-- box ['41757/204800', '835989/4096000', '3999/4000', '1']  interval_lower 592870799/1099511627776
noncomputable def e1239 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1323692814499,0,true,204024619968,204024620032⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨875330441053,0,false,-250710557248,-250710557184⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1323920716202,0,true,204213907840,204213907904⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨875102539350,0,false,-250996864192,-250996864128⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1323636769202,0,true,203978065536,203978065600⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨875386486350,0,false,-250640160448,-250640160384⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540554511,0,true,28926336,28926400⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482701041,0,false,-28927168,-28927104⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627014,0,false,-768,-704⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1323664786271,0,true,204001338368,204001338432⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨875358469281,0,false,-250675351296,-250675351232⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1323920724742,0,true,204213914944,204213915008⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨875102530810,0,false,-250996874944,-250996874880⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1053709981364,0,false,-46782960000,-46782959936⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1053814395302,0,false,-46674012864,-46674012800⟩
    { al := (41757/204800), au := (835989/4096000), zl := (3999/4000), zu := 1,
      A := ⟨224181186723,224409088426⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204024619968,204024620032⟩ : DyadicInterval 40),(⟨-250710557248,-250710557184⟩ : DyadicInterval 40),(⟨739108010407,739108029736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204213907840,204213907904⟩ : DyadicInterval 40),(⟨-250996864192,-250996864128⟩ : DyadicInterval 40),(⟨739060858053,739060877382⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨203978065536,203978065600⟩ : DyadicInterval 40),(⟨-250640160448,-250640160384⟩ : DyadicInterval 40),(⟨739119598515,739119617844⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204213907840,204213907904⟩ : DyadicInterval 40),(⟨-250996864192,-250996864128⟩ : DyadicInterval 40),(⟨739060858053,739060877382⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,28926735⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28926336,28926400⟩ : DyadicInterval 40),(⟨-28927168,-28927104⟩ : DyadicInterval 40),(⟨762123383206,762123402535⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-768,0⟩ : DyadicInterval 40),(⟨762123383616,762123403264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨224153158495,224409096966⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204001338368,204001338432⟩ : DyadicInterval 40),(⟨-250675351296,-250675351232⟩ : DyadicInterval 40),(⟨739113805992,739113825322⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204213914944,204213915008⟩ : DyadicInterval 40),(⟨-250996874944,-250996874880⟩ : DyadicInterval 40),(⟨739060856287,739060875616⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-46782960000,-46674012800⟩ : DyadicInterval 40),(⟨785460390016,785514882880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨204024619968,204213907904⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-250996864192,-250710557184⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1239_ok : ecellOkT e1239 = true := by decide +kernel
theorem e1239_pos {a z : ℝ} (ha1 : ((41757/204800 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((835989/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1239 e1239_ok ha1 ha2 hz1 hz2 hz

-- box ['835989/4096000', '418419/2048000', '3999/4000', '1']  interval_lower 597982591/1099511627776
noncomputable def e1240 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1323920716201,0,true,204213907840,204213907904⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨875102539351,0,false,-250996864192,-250996864128⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1324148617905,0,true,204403163136,204403163200⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨874874637647,0,false,-251283245760,-251283245696⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1323864613928,0,true,204167314112,204167314176⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨875158641624,0,false,-250926377472,-250926377408⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540585736,0,true,28957568,28957632⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482669816,0,false,-28958400,-28958336⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627013,0,false,-768,-704⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1323892659483,0,true,204190606592,204190606656⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨875130596069,0,false,-250961613248,-250961613184⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1324148626441,0,true,204403170240,204403170304⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨874874629111,0,false,-251283256448,-251283256384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1053616905160,0,false,-46880086208,-46880086144⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1053721436824,0,false,-46771006656,-46771006592⟩
    { al := (835989/4096000), au := (418419/2048000), zl := (3999/4000), zu := 1,
      A := ⟨224409088425,224636990129⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204213907840,204213907904⟩ : DyadicInterval 40),(⟨-250996864192,-250996864128⟩ : DyadicInterval 40),(⟨739060858053,739060877382⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204403163136,204403163200⟩ : DyadicInterval 40),(⟨-251283245760,-251283245696⟩ : DyadicInterval 40),(⟨739013656425,739013675754⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204167314112,204167314176⟩ : DyadicInterval 40),(⟨-250926377472,-250926377408⟩ : DyadicInterval 40),(⟨739072470065,739072489395⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204403163136,204403163200⟩ : DyadicInterval 40),(⟨-251283245760,-251283245696⟩ : DyadicInterval 40),(⟨739013656425,739013675754⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,28957960⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28957568,28957632⟩ : DyadicInterval 40),(⟨-28958400,-28958336⟩ : DyadicInterval 40),(⟨762123383205,762123402534⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-768,0⟩ : DyadicInterval 40),(⟨762123383616,762123403264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨224381031707,224636998665⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204190606592,204190606656⟩ : DyadicInterval 40),(⟨-250961613248,-250961613184⟩ : DyadicInterval 40),(⟨739066665583,739066684912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204403170240,204403170304⟩ : DyadicInterval 40),(⟨-251283256448,-251283256384⟩ : DyadicInterval 40),(⟨739013654630,739013673960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-46880086208,-46771006592⟩ : DyadicInterval 40),(⟨785508886912,785563445984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨204213907840,204403163200⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-251283245760,-250996864128⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1240_ok : ecellOkT e1240 = true := by decide +kernel
theorem e1240_pos {a z : ℝ} (ha1 : ((835989/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((418419/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1240 e1240_ok ha1 ha2 hz1 hz2 hz

-- box ['418419/2048000', '837687/4096000', '1999/2000', '3999/4000']  interval_lower 604060979/1099511627776
noncomputable def e1241 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1324148617904,0,true,204403163136,204403163200⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨874874637648,0,false,-251283245760,-251283245696⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1324376519607,0,true,204592385856,204592385920⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨874646735945,0,false,-251569701888,-251569701824⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1324036299408,0,true,204309895104,204309895168⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨874986956144,0,false,-251142096896,-251142096832⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1324320303385,0,true,204545713536,204545713600⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨874702952167,0,false,-251499035200,-251499035136⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540584765,0,true,28956544,28956608⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482670787,0,false,-28957376,-28957312⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569605445,0,true,57976128,57976192⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453650107,0,false,-57979200,-57979136⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624718,0,false,-3072,-3008⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627014,0,false,-768,-704⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1324092453387,0,true,204356525696,204356525760⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨874930802165,0,false,-251212662400,-251212662336⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1324348420138,0,true,204569057152,204569057216⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨874674835414,0,false,-251534378816,-251534378752⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1053535230689,0,false,-46965321664,-46965321600⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1053639855293,0,false,-46856136640,-46856136576⟩
    { al := (418419/2048000), au := (837687/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨224636990128,224864891831⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204403163136,204403163200⟩ : DyadicInterval 40),(⟨-251283245760,-251283245696⟩ : DyadicInterval 40),(⟨739013656425,739013675754⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204592385856,204592385920⟩ : DyadicInterval 40),(⟨-251569701888,-251569701824⟩ : DyadicInterval 40),(⟨738966405484,738966424813⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204309895104,204309895168⟩ : DyadicInterval 40),(⟨-251142096896,-251142096832⟩ : DyadicInterval 40),(⟨739036925327,739036944657⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204545713536,204545713600⟩ : DyadicInterval 40),(⟨-251499035200,-251499035136⟩ : DyadicInterval 40),(⟨738978065410,738978084740⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨28956989,57977669⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28956544,28956608⟩ : DyadicInterval 40),(⟨-28957376,-28957312⟩ : DyadicInterval 40),(⟨762123383205,762123402534⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨57976128,57976192⟩ : DyadicInterval 40),(⟨-57979200,-57979136⟩ : DyadicInterval 40),(⟨762123382030,762123401359⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3072,-704⟩ : DyadicInterval 40),(⟨762123383968,762123404416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨224580825611,224836792362⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204356525696,204356525760⟩ : DyadicInterval 40),(⟨-251212662400,-251212662336⟩ : DyadicInterval 40),(⟨739025293470,739025312800⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204569057152,204569057216⟩ : DyadicInterval 40),(⟨-251534378816,-251534378752⟩ : DyadicInterval 40),(⟨738972234000,738972253329⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-46965321664,-46856136576⟩ : DyadicInterval 40),(⟨785551451904,785606063712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨204403163136,204592385920⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-251569701888,-251283245696⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1241_ok : ecellOkT e1241 = true := by decide +kernel
theorem e1241_pos {a z : ℝ} (ha1 : ((418419/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((837687/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1241 e1241_ok ha1 ha2 hz1 hz2 hz

-- box ['837687/4096000', '104817/512000', '1999/2000', '3999/4000']  interval_lower 609216413/1099511627776
noncomputable def e1242 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1324376519606,0,true,204592385856,204592385920⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨874646735946,0,false,-251569701888,-251569701824⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1324604421309,0,true,204781576000,204781576064⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨874418834243,0,false,-251856232704,-251856232640⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1324264087160,0,true,204499039232,204499039296⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨874759168392,0,false,-251428372992,-251428372928⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1324548148111,0,true,204734864448,204734864512⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨874475107441,0,false,-251785475904,-251785475840⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540615996,0,true,28987776,28987840⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482639556,0,false,-28988608,-28988544⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569667921,0,true,58038592,58038656⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453587631,0,false,-58041728,-58041664⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624712,0,false,-3072,-3008⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627012,0,false,-768,-704⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1324320298111,0,true,204545709184,204545709248⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨874702957441,0,false,-251499028544,-251499028480⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1324576293353,0,true,204758227648,204758227712⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨874446962199,0,false,-251820864576,-251820864512⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1053441988845,0,false,-47062636928,-47062636864⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1053546731198,0,false,-46953319360,-46953319296⟩
    { al := (837687/4096000), au := (104817/512000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨224864891830,225092793533⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204592385856,204592385920⟩ : DyadicInterval 40),(⟨-251569701888,-251569701824⟩ : DyadicInterval 40),(⟨738966405484,738966424813⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204781576000,204781576064⟩ : DyadicInterval 40),(⟨-251856232704,-251856232640⟩ : DyadicInterval 40),(⟨738919105268,738919124597⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204499039232,204499039296⟩ : DyadicInterval 40),(⟨-251428372992,-251428372928⟩ : DyadicInterval 40),(⟨738989722315,738989741645⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204734864448,204734864512⟩ : DyadicInterval 40),(⟨-251785475904,-251785475840⟩ : DyadicInterval 40),(⟨738930789141,738930808470⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨28988220,58040145⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28987776,28987840⟩ : DyadicInterval 40),(⟨-28988608,-28988544⟩ : DyadicInterval 40),(⟨762123383203,762123402532⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58038592,58038656⟩ : DyadicInterval 40),(⟨-58041728,-58041664⟩ : DyadicInterval 40),(⟨762123382056,762123401385⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3072,-704⟩ : DyadicInterval 40),(⟨762123383968,762123404416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨224808670335,225064665577⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204545709184,204545709248⟩ : DyadicInterval 40),(⟨-251499028544,-251499028480⟩ : DyadicInterval 40),(⟨738978066477,738978085807⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204758227648,204758227712⟩ : DyadicInterval 40),(⟨-251820864576,-251820864512⟩ : DyadicInterval 40),(⟨738924945774,738924965103⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-47062636928,-46953319296⟩ : DyadicInterval 40),(⟨785600043264,785654721344⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨204592385856,204781576064⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-251856232704,-251569701824⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1242_ok : ecellOkT e1242 = true := by decide +kernel
theorem e1242_pos {a z : ℝ} (ha1 : ((837687/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((104817/512000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1242 e1242_ok ha1 ha2 hz1 hz2 hz

-- box ['418419/2048000', '837687/4096000', '3999/4000', '1']  interval_lower 603114007/1099511627776
noncomputable def e1243 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1324148617904,0,true,204403163136,204403163200⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨874874637648,0,false,-251283245760,-251283245696⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1324376519607,0,true,204592385856,204592385920⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨874646735945,0,false,-251569701888,-251569701824⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1324092458656,0,true,204356530112,204356530176⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨874930796896,0,false,-251212669056,-251212668992⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540616968,0,true,28988800,28988864⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482638584,0,false,-28989632,-28989568⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627011,0,false,-768,-704⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1324120532691,0,true,204379842240,204379842304⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨874902722861,0,false,-251247949824,-251247949760⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1324376528145,0,true,204592392960,204592393024⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨874646727407,0,false,-251569712640,-251569712576⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1053523734478,0,false,-46977319616,-46977319552⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1053628383896,0,false,-46868107520,-46868107456⟩
    { al := (418419/2048000), au := (837687/4096000), zl := (3999/4000), zu := 1,
      A := ⟨224636990128,224864891831⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204403163136,204403163200⟩ : DyadicInterval 40),(⟨-251283245760,-251283245696⟩ : DyadicInterval 40),(⟨739013656425,739013675754⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204592385856,204592385920⟩ : DyadicInterval 40),(⟨-251569701888,-251569701824⟩ : DyadicInterval 40),(⟨738966405484,738966424813⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204356530112,204356530176⟩ : DyadicInterval 40),(⟨-251212669056,-251212668992⟩ : DyadicInterval 40),(⟨739025292368,739025311697⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204592385856,204592385920⟩ : DyadicInterval 40),(⟨-251569701888,-251569701824⟩ : DyadicInterval 40),(⟨738966405484,738966424813⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,28989192⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨28988800,28988864⟩ : DyadicInterval 40),(⟨-28989632,-28989568⟩ : DyadicInterval 40),(⟨762123383203,762123402532⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-768,0⟩ : DyadicInterval 40),(⟨762123383616,762123403264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨224608904915,224864900369⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204379842240,204379842304⟩ : DyadicInterval 40),(⟨-251247949824,-251247949760⟩ : DyadicInterval 40),(⟨739019475925,739019495255⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204592392960,204592393024⟩ : DyadicInterval 40),(⟨-251569712640,-251569712576⟩ : DyadicInterval 40),(⟨738966403711,738966423040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-46977319616,-46868107456⟩ : DyadicInterval 40),(⟨785557437344,785612062688⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨204403163136,204592385920⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-251569701888,-251283245696⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1243_ok : ecellOkT e1243 = true := by decide +kernel
theorem e1243_pos {a z : ℝ} (ha1 : ((418419/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((837687/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1243 e1243_ok ha1 ha2 hz1 hz2 hz

-- box ['837687/4096000', '104817/512000', '3999/4000', '1']  interval_lower 76033197/137438953472
noncomputable def e1244 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1324376519606,0,true,204592385856,204592385920⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨874646735946,0,false,-251569701888,-251569701824⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1324604421309,0,true,204781576000,204781576064⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨874418834243,0,false,-251856232704,-251856232640⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1324320303383,0,true,204545713536,204545713600⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨874702952169,0,false,-251499035200,-251499035136⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540648206,0,true,29020032,29020096⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482607346,0,false,-29020864,-29020800⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627010,0,false,-768,-704⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1324348405898,0,true,204569045312,204569045376⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨874674849654,0,false,-251534360960,-251534360896⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1324604429840,0,true,204781583104,204781583168⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨874418825712,0,false,-251856243392,-251856243328⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1053430469322,0,false,-47074660288,-47074660224⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1053535236514,0,false,-46965315584,-46965315520⟩
    { al := (837687/4096000), au := (104817/512000), zl := (3999/4000), zu := 1,
      A := ⟨224864891830,225092793533⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204592385856,204592385920⟩ : DyadicInterval 40),(⟨-251569701888,-251569701824⟩ : DyadicInterval 40),(⟨738966405484,738966424813⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204781576000,204781576064⟩ : DyadicInterval 40),(⟨-251856232704,-251856232640⟩ : DyadicInterval 40),(⟨738919105268,738919124597⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204545713536,204545713600⟩ : DyadicInterval 40),(⟨-251499035200,-251499035136⟩ : DyadicInterval 40),(⟨738978065410,738978084740⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204781576000,204781576064⟩ : DyadicInterval 40),(⟨-251856232704,-251856232640⟩ : DyadicInterval 40),(⟨738919105268,738919124597⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,29020430⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29020032,29020096⟩ : DyadicInterval 40),(⟨-29020864,-29020800⟩ : DyadicInterval 40),(⟨762123383202,762123402531⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-768,0⟩ : DyadicInterval 40),(⟨762123383616,762123403264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨224836778122,225092802064⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204569045312,204569045376⟩ : DyadicInterval 40),(⟨-251534360960,-251534360896⟩ : DyadicInterval 40),(⟨738972236981,738972256311⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204781583104,204781583168⟩ : DyadicInterval 40),(⟨-251856243392,-251856243328⟩ : DyadicInterval 40),(⟨738919103467,738919122796⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-47074660288,-46965315520⟩ : DyadicInterval 40),(⟨785606041376,785660733024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨204592385856,204781576064⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-251856232704,-251569701824⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1244_ok : ecellOkT e1244 = true := by decide +kernel
theorem e1244_pos {a z : ℝ} (ha1 : ((837687/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((104817/512000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1244 e1244_ok ha1 ha2 hz1 hz2 hz

-- box ['104817/512000', '167877/819200', '999/1000', '3997/4000']  interval_lower 616297735/1099511627776
noncomputable def e1245 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1324604421308,0,true,204781576000,204781576064⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨874418834244,0,false,-251856232704,-251856232640⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1324832323011,0,true,204970733632,204970733696⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨874190932541,0,false,-252142838144,-252142838080⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1324379328514,0,true,204594717824,204594717888⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨874643927038,0,false,-251573232960,-251573232896⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1324663332490,0,true,204830475200,204830475264⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨874359923062,0,false,-251930311296,-251930311232⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099598685283,0,true,87054016,87054080⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099424570269,0,false,-87060992,-87060928⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099627830938,0,true,116196992,116197056⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099395424614,0,false,-116209344,-116209280⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511615494,0,false,-12288,-12224⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620883,0,false,-6912,-6848⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1324491870924,0,true,204688147584,204688147648⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨874531384628,0,false,-251714718720,-251714718656⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1324747837258,0,true,204900614528,204900614592⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨874275418294,0,false,-252036581504,-252036581440⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1053371733680,0,false,-47135966976,-47135966912⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1053476544083,0,false,-47026571072,-47026571008⟩
    { al := (104817/512000), au := (167877/819200), zl := (999/1000), zu := (3997/4000),
      A := ⟨225092793532,225320695235⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204781576000,204781576064⟩ : DyadicInterval 40),(⟨-251856232704,-251856232640⟩ : DyadicInterval 40),(⟨738919105268,738919124597⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204970733632,204970733696⟩ : DyadicInterval 40),(⟨-252142838144,-252142838080⟩ : DyadicInterval 40),(⟨738871755699,738871775028⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204594717824,204594717888⟩ : DyadicInterval 40),(⟨-251573232960,-251573232896⟩ : DyadicInterval 40),(⟨738965822817,738965842147⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204830475200,204830475264⟩ : DyadicInterval 40),(⟨-251930311296,-251930311232⟩ : DyadicInterval 40),(⟨738906870428,738906889757⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨87057507,116203162⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨87054016,87054080⟩ : DyadicInterval 40),(⟨-87060992,-87060928⟩ : DyadicInterval 40),(⟨762123380146,762123399476⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨116196992,116197056⟩ : DyadicInterval 40),(⟨-116209344,-116209280⟩ : DyadicInterval 40),(⟨762123377446,762123396776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-12288,-6848⟩ : DyadicInterval 40),(⟨762123387040,762123409024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨224980243148,225236209482⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204688147584,204688147648⟩ : DyadicInterval 40),(⟨-251714718720,-251714718656⟩ : DyadicInterval 40),(⟨738942470877,738942490206⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204900614528,204900614592⟩ : DyadicInterval 40),(⟨-252036581504,-252036581440⟩ : DyadicInterval 40),(⟨738889314471,738889333801⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-47135966976,-47026571008⟩ : DyadicInterval 40),(⟨785636669120,785691386368⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨204781576000,204970733696⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-252142838144,-251856232640⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1245_ok : ecellOkT e1245 = true := by decide +kernel
theorem e1245_pos {a z : ℝ} (ha1 : ((104817/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((167877/819200 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1245 e1245_ok ha1 ha2 hz1 hz2 hz

-- box ['167877/819200', '420117/2048000', '999/1000', '3997/4000']  interval_lower 155375043/274877906944
noncomputable def e1246 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1324832323010,0,true,204970733632,204970733696⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨874190932542,0,false,-252142838144,-252142838080⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1325060224713,0,true,205159858688,205159858752⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨873963030839,0,false,-252429518400,-252429518336⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1324607002314,0,true,204783718400,204783718464⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨874416253238,0,false,-251859478080,-251859478016⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1324891063266,0,true,205019482560,205019482624⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨874132192286,0,false,-252216721088,-252216721024⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099598779005,0,true,87147712,87147776⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099424476547,0,false,-87154688,-87154624⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099627955929,0,true,116321984,116322048⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099395299623,0,false,-116334336,-116334272⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511615468,0,false,-12352,-12288⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620869,0,false,-6912,-6848⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1324719658679,0,true,204877226688,204877226752⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨874303596873,0,false,-252001144000,-252001143936⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1324975653496,0,true,205089680768,205089680832⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨874047602056,0,false,-252323126528,-252323126464⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1053278349646,0,false,-47233445696,-47233445632⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1053383277787,0,false,-47123917248,-47123917184⟩
    { al := (167877/819200), au := (420117/2048000), zl := (999/1000), zu := (3997/4000),
      A := ⟨225320695234,225548596937⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204970733632,204970733696⟩ : DyadicInterval 40),(⟨-252142838144,-252142838080⟩ : DyadicInterval 40),(⟨738871755699,738871775029⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205159858688,205159858752⟩ : DyadicInterval 40),(⟨-252429518400,-252429518336⟩ : DyadicInterval 40),(⟨738824356880,738824376210⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204783718400,204783718464⟩ : DyadicInterval 40),(⟨-251859478080,-251859478016⟩ : DyadicInterval 40),(⟨738918569296,738918588626⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205019482560,205019482624⟩ : DyadicInterval 40),(⟨-252216721088,-252216721024⟩ : DyadicInterval 40),(⟨738859543674,738859563003⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨87151229,116328153⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨87147712,87147776⟩ : DyadicInterval 40),(⟨-87154688,-87154624⟩ : DyadicInterval 40),(⟨762123380131,762123399461⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨116321984,116322048⟩ : DyadicInterval 40),(⟨-116334336,-116334272⟩ : DyadicInterval 40),(⟨762123377420,762123396749⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-12352,-6848⟩ : DyadicInterval 40),(⟨762123387040,762123409056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨225208030903,225464025720⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204877226688,204877226752⟩ : DyadicInterval 40),(⟨-252001144000,-252001143936⟩ : DyadicInterval 40),(⟨738895169359,738895188689⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205089680768,205089680832⟩ : DyadicInterval 40),(⟨-252323126528,-252323126464⟩ : DyadicInterval 40),(⟨738841951676,738841971006⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-47233445696,-47123917184⟩ : DyadicInterval 40),(⟨785685342208,785740125728⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨204970733632,205159858752⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-252429518400,-252142838080⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1246_ok : ecellOkT e1246 = true := by decide +kernel
theorem e1246_pos {a z : ℝ} (ha1 : ((167877/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((420117/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1246 e1246_ok ha1 ha2 hz1 hz2 hz

-- box ['104817/512000', '167877/819200', '3997/4000', '1999/2000']  interval_lower 615345045/1099511627776
noncomputable def e1247 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1324604421308,0,true,204781576000,204781576064⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨874418834244,0,false,-251856232704,-251856232640⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1324832323011,0,true,204970733632,204970733696⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨874190932541,0,false,-252142838144,-252142838080⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1324435601712,0,true,204641435328,204641435392⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨874587653840,0,false,-251643976064,-251643976000⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1324719662664,0,true,204877230016,204877230080⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨874303592888,0,false,-252001148992,-252001148928⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569666486,0,true,58037120,58037184⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453589066,0,false,-58040256,-58040192⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099598780903,0,true,87149632,87149696⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099424474649,0,false,-87156608,-87156544⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620867,0,false,-6912,-6848⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624713,0,false,-3072,-3008⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1324520006768,0,true,204711504000,204711504064⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨874503248784,0,false,-251750093312,-251750093248⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1324776001809,0,true,204923990272,204923990336⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨874247253743,0,false,-252072002560,-252072002496⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1053360193878,0,false,-47148012288,-47148012224⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1053465029143,0,false,-47038589248,-47038589184⟩
    { al := (104817/512000), au := (167877/819200), zl := (3997/4000), zu := (1999/2000),
      A := ⟨225092793532,225320695235⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204781576000,204781576064⟩ : DyadicInterval 40),(⟨-251856232704,-251856232640⟩ : DyadicInterval 40),(⟨738919105268,738919124597⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204970733632,204970733696⟩ : DyadicInterval 40),(⟨-252142838144,-252142838080⟩ : DyadicInterval 40),(⟨738871755699,738871775028⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204641435328,204641435392⟩ : DyadicInterval 40),(⟨-251643976064,-251643976000⟩ : DyadicInterval 40),(⟨738954147948,738954167278⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204877230016,204877230080⟩ : DyadicInterval 40),(⟨-252001148992,-252001148928⟩ : DyadicInterval 40),(⟨738895168511,738895187841⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨58038710,87153127⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58037120,58037184⟩ : DyadicInterval 40),(⟨-58040256,-58040192⟩ : DyadicInterval 40),(⟨762123382056,762123401385⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨87149632,87149696⟩ : DyadicInterval 40),(⟨-87156608,-87156544⟩ : DyadicInterval 40),(⟨762123380131,762123399461⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6912,-3008⟩ : DyadicInterval 40),(⟨762123385120,762123406336⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨225008378992,225264374033⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204711504000,204711504064⟩ : DyadicInterval 40),(⟨-251750093312,-251750093248⟩ : DyadicInterval 40),(⟨738936630955,738936650284⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204923990272,204923990336⟩ : DyadicInterval 40),(⟨-252072002560,-252072002496⟩ : DyadicInterval 40),(⟨738883461738,738883481068⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-47148012288,-47038589184⟩ : DyadicInterval 40),(⟨785642678208,785697409024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨204781576000,204970733696⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-252142838144,-251856232640⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1247_ok : ecellOkT e1247 = true := by decide +kernel
theorem e1247_pos {a z : ℝ} (ha1 : ((104817/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((167877/819200 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1247 e1247_ok ha1 ha2 hz1 hz2 hz

-- box ['167877/819200', '420117/2048000', '3997/4000', '1999/2000']  interval_lower 155135981/274877906944
noncomputable def e1248 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1324832323010,0,true,204970733632,204970733696⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨874190932542,0,false,-252142838144,-252142838080⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1325060224713,0,true,205159858688,205159858752⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨873963030839,0,false,-252429518400,-252429518336⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1324663332488,0,true,204830475200,204830475264⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨874359923064,0,false,-251930311232,-251930311168⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1324947450415,0,true,205066276608,205066276672⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨874075805137,0,false,-252287648896,-252287648832⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569728970,0,true,58099648,58099712⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453526582,0,false,-58102784,-58102720⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099598874647,0,true,87243392,87243456⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099424380905,0,false,-87250368,-87250304⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620852,0,false,-6976,-6912⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624706,0,false,-3072,-3008⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1324747823013,0,true,204900602752,204900602816⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨874275432539,0,false,-252036563648,-252036563584⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1325003846532,0,true,205113076096,205113076160⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨874019409020,0,false,-252358592640,-252358592576⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1053266786489,0,false,-47245516480,-47245516416⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1053371739518,0,false,-47135960832,-47135960768⟩
    { al := (167877/819200), au := (420117/2048000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨225320695234,225548596937⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204970733632,204970733696⟩ : DyadicInterval 40),(⟨-252142838144,-252142838080⟩ : DyadicInterval 40),(⟨738871755699,738871775029⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205159858688,205159858752⟩ : DyadicInterval 40),(⟨-252429518400,-252429518336⟩ : DyadicInterval 40),(⟨738824356880,738824376210⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204830475200,204830475264⟩ : DyadicInterval 40),(⟨-251930311232,-251930311168⟩ : DyadicInterval 40),(⟨738906870402,738906889732⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205066276608,205066276672⟩ : DyadicInterval 40),(⟨-252287648896,-252287648832⟩ : DyadicInterval 40),(⟨738847817732,738847837061⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨58101194,87246871⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58099648,58099712⟩ : DyadicInterval 40),(⟨-58102784,-58102720⟩ : DyadicInterval 40),(⟨762123382049,762123401378⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨87243392,87243456⟩ : DyadicInterval 40),(⟨-87250368,-87250304⟩ : DyadicInterval 40),(⟨762123380116,762123399446⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6976,-3008⟩ : DyadicInterval 40),(⟨762123385120,762123406368⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨225236195237,225492218756⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204900602752,204900602816⟩ : DyadicInterval 40),(⟨-252036563648,-252036563584⟩ : DyadicInterval 40),(⟨738889317426,738889336756⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205113076096,205113076160⟩ : DyadicInterval 40),(⟨-252358592640,-252358592576⟩ : DyadicInterval 40),(⟨738836086943,738836106272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-47245516480,-47135960768⟩ : DyadicInterval 40),(⟨785691364000,785746161120⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨204970733632,205159858752⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-252429518400,-252142838080⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1248_ok : ecellOkT e1248 = true := by decide +kernel
theorem e1248_pos {a z : ℝ} (ha1 : ((167877/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((420117/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1248 e1248_ok ha1 ha2 hz1 hz2 hz

-- box ['420117/2048000', '841083/4096000', '999/1000', '3997/4000']  interval_lower 78340365/137438953472
noncomputable def e1249 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1325060224712,0,true,205159858688,205159858752⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨873963030840,0,false,-252429518400,-252429518336⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1325288126415,0,true,205348951296,205348951360⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨873735129137,0,false,-252716273344,-252716273280⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1324834676115,0,true,204972686528,204972686592⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨874188579437,0,false,-252145797760,-252145797696⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1325118794042,0,true,205208457472,205208457536⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨873904461510,0,false,-252503205504,-252503205440⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099598872746,0,true,87241472,87241536⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099424382806,0,false,-87248448,-87248384⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099628080944,0,true,116446976,116447040⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099395174608,0,false,-116459392,-116459328⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511615442,0,false,-12352,-12288⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620854,0,false,-6976,-6912⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1324947446428,0,true,205066273280,205066273344⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨874075809124,0,false,-252287643904,-252287643840⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1325203469749,0,true,205278714496,205278714560⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨873819785803,0,false,-252609746240,-252609746176⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1053184871199,0,false,-47331031680,-47331031616⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1053289917112,0,false,-47221370560,-47221370496⟩
    { al := (420117/2048000), au := (841083/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨225548596936,225776498639⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205159858688,205159858752⟩ : DyadicInterval 40),(⟨-252429518400,-252429518336⟩ : DyadicInterval 40),(⟨738824356880,738824376210⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205348951296,205348951360⟩ : DyadicInterval 40),(⟨-252716273344,-252716273280⟩ : DyadicInterval 40),(⟨738776908670,738776928000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204972686528,204972686592⟩ : DyadicInterval 40),(⟨-252145797760,-252145797696⟩ : DyadicInterval 40),(⟨738871266556,738871285885⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205208457472,205208457536⟩ : DyadicInterval 40),(⟨-252503205504,-252503205440⟩ : DyadicInterval 40),(⟨738812167662,738812186991⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨87244970,116453168⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨87241472,87241536⟩ : DyadicInterval 40),(⟨-87248448,-87248384⟩ : DyadicInterval 40),(⟨762123380116,762123399446⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨116446976,116447040⟩ : DyadicInterval 40),(⟨-116459392,-116459328⟩ : DyadicInterval 40),(⟨762123377425,762123396755⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-12352,-6912⟩ : DyadicInterval 40),(⟨762123387072,762123409056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨225435818652,225691841973⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205066273280,205066273344⟩ : DyadicInterval 40),(⟨-252287643904,-252287643840⟩ : DyadicInterval 40),(⟨738847818582,738847837911⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205278714496,205278714560⟩ : DyadicInterval 40),(⟨-252609746240,-252609746176⟩ : DyadicInterval 40),(⟨738794539604,738794558934⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-47331031680,-47221370496⟩ : DyadicInterval 40),(⟨785734068864,785788918720⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨205159858688,205348951360⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-252716273344,-252429518336⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1249_ok : ecellOkT e1249 = true := by decide +kernel
theorem e1249_pos {a z : ℝ} (ha1 : ((420117/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((841083/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1249 e1249_ok ha1 ha2 hz1 hz2 hz

-- box ['841083/4096000', '210483/1024000', '999/1000', '3997/4000']  interval_lower 631966039/1099511627776
noncomputable def e1250 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1325288126414,0,true,205348951296,205348951360⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨873735129138,0,false,-252716273344,-252716273280⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1325516028117,0,true,205538011328,205538011392⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨873507227435,0,false,-253003103104,-253003103040⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1325062349915,0,true,205161622144,205161622208⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨873960905637,0,false,-252432192064,-252432192000⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1325346524817,0,true,205397399808,205397399872⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨873676730735,0,false,-252789764608,-252789764544⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099598966504,0,true,87335232,87335296⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099424289048,0,false,-87342208,-87342144⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099628205982,0,true,116571968,116572032⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099395049570,0,false,-116584448,-116584384⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511615415,0,false,-12416,-12352⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620839,0,false,-6976,-6912⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1325175234181,0,true,205255287424,205255287488⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨873848021371,0,false,-252574218496,-252574218432⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1325431285984,0,true,205467715712,205467715776⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨873591969568,0,false,-252896440640,-252896440576⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1053091298353,0,false,-47428724928,-47428724864⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1053196462053,0,false,-47318931072,-47318931008⟩
    { al := (841083/4096000), au := (210483/1024000), zl := (999/1000), zu := (3997/4000),
      A := ⟨225776498638,226004400341⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205348951296,205348951360⟩ : DyadicInterval 40),(⟨-252716273344,-252716273280⟩ : DyadicInterval 40),(⟨738776908670,738776928000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205538011328,205538011392⟩ : DyadicInterval 40),(⟨-253003103104,-253003103040⟩ : DyadicInterval 40),(⟨738729411183,738729430512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205161622144,205161622208⟩ : DyadicInterval 40),(⟨-252432192064,-252432192000⟩ : DyadicInterval 40),(⟨738823914647,738823933976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205397399808,205397399872⟩ : DyadicInterval 40),(⟨-252789764608,-252789764544⟩ : DyadicInterval 40),(⟨738764742479,738764761808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨87338728,116578206⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨87335232,87335296⟩ : DyadicInterval 40),(⟨-87342208,-87342144⟩ : DyadicInterval 40),(⟨762123380102,762123399431⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨116571968,116572032⟩ : DyadicInterval 40),(⟨-116584448,-116584384⟩ : DyadicInterval 40),(⟨762123377431,762123396760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-12416,-6912⟩ : DyadicInterval 40),(⟨762123387072,762123409088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨225663606405,225919658208⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205255287424,205255287488⟩ : DyadicInterval 40),(⟨-252574218496,-252574218432⟩ : DyadicInterval 40),(⟨738800418518,738800437847⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205467715712,205467715776⟩ : DyadicInterval 40),(⟨-252896440640,-252896440576⟩ : DyadicInterval 40),(⟨738747078249,738747097578⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-47428724928,-47318931008⟩ : DyadicInterval 40),(⟨785782849120,785837765344⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨205348951296,205538011392⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-253003103104,-252716273280⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1250_ok : ecellOkT e1250 = true := by decide +kernel
theorem e1250_pos {a z : ℝ} (ha1 : ((841083/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((210483/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1250 e1250_ok ha1 ha2 hz1 hz2 hz

-- box ['420117/2048000', '841083/4096000', '3997/4000', '1999/2000']  interval_lower 156440739/274877906944
noncomputable def e1251 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1325060224712,0,true,205159858688,205159858752⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨873963030840,0,false,-252429518400,-252429518336⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1325288126415,0,true,205348951296,205348951360⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨873735129137,0,false,-252716273344,-252716273280⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1324891063264,0,true,205019482560,205019482624⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨874132192288,0,false,-252216721088,-252216721024⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1325175238166,0,true,205255290688,205255290752⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨873848017386,0,false,-252574223552,-252574223488⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569791466,0,true,58162112,58162176⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453464086,0,false,-58165248,-58165184⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099598968411,0,true,87337152,87337216⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099424287141,0,false,-87344128,-87344064⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620838,0,false,-6976,-6912⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624700,0,false,-3136,-3072⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1324975639242,0,true,205089668928,205089668992⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨874047616310,0,false,-252323108608,-252323108544⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1325231691262,0,true,205302129408,205302129472⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨873791564290,0,false,-252645257408,-252645257344⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1053173284667,0,false,-47343127936,-47343127872⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1053278355493,0,false,-47233439616,-47233439552⟩
    { al := (420117/2048000), au := (841083/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨225548596936,225776498639⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205159858688,205159858752⟩ : DyadicInterval 40),(⟨-252429518400,-252429518336⟩ : DyadicInterval 40),(⟨738824356880,738824376210⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205348951296,205348951360⟩ : DyadicInterval 40),(⟨-252716273344,-252716273280⟩ : DyadicInterval 40),(⟨738776908670,738776928000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205019482560,205019482624⟩ : DyadicInterval 40),(⟨-252216721088,-252216721024⟩ : DyadicInterval 40),(⟨738859543675,738859563004⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205255290688,205255290752⟩ : DyadicInterval 40),(⟨-252574223552,-252574223488⟩ : DyadicInterval 40),(⟨738800417730,738800437060⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨58163690,87340635⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58162112,58162176⟩ : DyadicInterval 40),(⟨-58165248,-58165184⟩ : DyadicInterval 40),(⟨762123382043,762123401372⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨87337152,87337216⟩ : DyadicInterval 40),(⟨-87344128,-87344064⟩ : DyadicInterval 40),(⟨762123380101,762123399431⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6976,-3072⟩ : DyadicInterval 40),(⟨762123385152,762123406368⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨225464011466,225720063486⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205089668928,205089668992⟩ : DyadicInterval 40),(⟨-252323108608,-252323108544⟩ : DyadicInterval 40),(⟨738841954652,738841973982⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205302129408,205302129472⟩ : DyadicInterval 40),(⟨-252645257408,-252645257344⟩ : DyadicInterval 40),(⟨738788662845,738788682175⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-47343127936,-47233439552⟩ : DyadicInterval 40),(⟨785740103392,785794966848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨205159858688,205348951360⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-252716273344,-252429518336⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1251_ok : ecellOkT e1251 = true := by decide +kernel
theorem e1251_pos {a z : ℝ} (ha1 : ((420117/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((841083/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1251 e1251_ok ha1 ha2 hz1 hz2 hz

-- box ['841083/4096000', '210483/1024000', '3997/4000', '1999/2000']  interval_lower 315501273/549755813888
noncomputable def e1252 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1325288126414,0,true,205348951296,205348951360⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨873735129138,0,false,-252716273344,-252716273280⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1325516028117,0,true,205538011328,205538011392⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨873507227435,0,false,-253003103104,-253003103040⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1325118794039,0,true,205208457408,205208457472⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨873904461513,0,false,-252503205504,-252503205440⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1325403025918,0,true,205444272320,205444272384⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨873620229634,0,false,-252860872832,-252860872768⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569853972,0,true,58224640,58224704⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453401580,0,false,-58227776,-58227712⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099599062192,0,true,87430912,87430976⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099424193360,0,false,-87437952,-87437888⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620823,0,false,-6976,-6912⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624693,0,false,-3136,-3072⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1325203455482,0,true,205278702656,205278702720⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨873819800070,0,false,-252609728256,-252609728192⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1325459535994,0,true,205491150272,205491150336⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨873563719558,0,false,-252931996992,-252931996928⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1053079688414,0,false,-47440846656,-47440846592⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1053184877057,0,false,-47331025600,-47331025536⟩
    { al := (841083/4096000), au := (210483/1024000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨225776498638,226004400341⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205348951296,205348951360⟩ : DyadicInterval 40),(⟨-252716273344,-252716273280⟩ : DyadicInterval 40),(⟨738776908670,738776928000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205538011328,205538011392⟩ : DyadicInterval 40),(⟨-253003103104,-253003103040⟩ : DyadicInterval 40),(⟨738729411183,738729430512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205208457408,205208457472⟩ : DyadicInterval 40),(⟨-252503205504,-252503205440⟩ : DyadicInterval 40),(⟨738812167700,738812187030⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205444272320,205444272384⟩ : DyadicInterval 40),(⟨-252860872832,-252860872768⟩ : DyadicInterval 40),(⟨738752968404,738752987733⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨58226196,87434416⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58224640,58224704⟩ : DyadicInterval 40),(⟨-58227776,-58227712⟩ : DyadicInterval 40),(⟨762123382036,762123401365⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨87430912,87430976⟩ : DyadicInterval 40),(⟨-87437952,-87437888⟩ : DyadicInterval 40),(⟨762123380118,762123399448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6976,-3072⟩ : DyadicInterval 40),(⟨762123385152,762123406368⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨225691827706,225947908218⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205278702656,205278702720⟩ : DyadicInterval 40),(⟨-252609728256,-252609728192⟩ : DyadicInterval 40),(⟨738794542564,738794561893⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205491150272,205491150336⟩ : DyadicInterval 40),(⟨-252931996992,-252931996928⟩ : DyadicInterval 40),(⟨738741189446,738741208776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-47440846656,-47331025536⟩ : DyadicInterval 40),(⟨785788896384,785843826208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨205348951296,205538011392⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-253003103104,-252716273280⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1252_ok : ecellOkT e1252 = true := by decide +kernel
theorem e1252_pos {a z : ℝ} (ha1 : ((841083/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((210483/1024000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1252 e1252_ok ha1 ha2 hz1 hz2 hz

-- box ['104817/512000', '167877/819200', '1999/2000', '3999/4000']  interval_lower 614391483/1099511627776
noncomputable def e1253 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1324604421308,0,true,204781576000,204781576064⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨874418834244,0,false,-251856232704,-251856232640⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1324832323011,0,true,204970733632,204970733696⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨874190932541,0,false,-252142838144,-252142838080⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1324491874911,0,true,204688150912,204688150976⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨874531380641,0,false,-251714723712,-251714723648⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1324775992838,0,true,204923982848,204923982912⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨874247262714,0,false,-252071991296,-252071991232⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540647232,0,true,29019072,29019136⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482608320,0,false,-29019840,-29019776⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569730406,0,true,58101056,58101120⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453525146,0,false,-58104192,-58104128⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624705,0,false,-3072,-3008⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627011,0,false,-768,-704⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1324548142833,0,true,204734860096,204734860160⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨874475112719,0,false,-251785469312,-251785469248⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1324804166574,0,true,204947365632,204947365696⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨874219088978,0,false,-252107425024,-252107424960⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1053348652546,0,false,-47160059328,-47160059264⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1053453512674,0,false,-47050609152,-47050609088⟩
    { al := (104817/512000), au := (167877/819200), zl := (1999/2000), zu := (3999/4000),
      A := ⟨225092793532,225320695235⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204781576000,204781576064⟩ : DyadicInterval 40),(⟨-251856232704,-251856232640⟩ : DyadicInterval 40),(⟨738919105268,738919124597⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204970733632,204970733696⟩ : DyadicInterval 40),(⟨-252142838144,-252142838080⟩ : DyadicInterval 40),(⟨738871755699,738871775028⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204688150912,204688150976⟩ : DyadicInterval 40),(⟨-251714723712,-251714723648⟩ : DyadicInterval 40),(⟨738942470030,738942489360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204923982848,204923982912⟩ : DyadicInterval 40),(⟨-252071991296,-252071991232⟩ : DyadicInterval 40),(⟨738883463597,738883482926⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨29019456,58102630⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29019072,29019136⟩ : DyadicInterval 40),(⟨-29019840,-29019776⟩ : DyadicInterval 40),(⟨762123383170,762123402499⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58101056,58101120⟩ : DyadicInterval 40),(⟨-58104192,-58104128⟩ : DyadicInterval 40),(⟨762123382049,762123401378⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3072,-704⟩ : DyadicInterval 40),(⟨762123383968,762123404416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨225036515057,225292538798⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204734860096,204734860160⟩ : DyadicInterval 40),(⟨-251785469312,-251785469248⟩ : DyadicInterval 40),(⟨738930790236,738930809566⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204947365632,204947365696⟩ : DyadicInterval 40),(⟨-252107425024,-252107424960⟩ : DyadicInterval 40),(⟨738877608246,738877627576⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-47160059328,-47050609088⟩ : DyadicInterval 40),(⟨785648688160,785703432544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨204781576000,204970733696⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-252142838144,-251856232640⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1253_ok : ecellOkT e1253 = true := by decide +kernel
theorem e1253_pos {a z : ℝ} (ha1 : ((104817/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((167877/819200 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1253 e1253_ok ha1 ha2 hz1 hz2 hz

-- box ['167877/819200', '420117/2048000', '1999/2000', '3999/4000']  interval_lower 619586799/1099511627776
noncomputable def e1254 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1324832323010,0,true,204970733632,204970733696⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨874190932542,0,false,-252142838144,-252142838080⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1325060224713,0,true,205159858688,205159858752⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨873963030839,0,false,-252429518400,-252429518336⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1324719662662,0,true,204877230016,204877230080⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨874303592890,0,false,-252001148992,-252001148928⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1325003837564,0,true,205113068672,205113068736⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨874019417988,0,false,-252358581376,-252358581312⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540678474,0,true,29050304,29050368⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482577078,0,false,-29051136,-29051072⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569792905,0,true,58163584,58163648⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453462647,0,false,-58166720,-58166656⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624699,0,false,-3136,-3072⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627009,0,false,-768,-704⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1324775987560,0,true,204923978432,204923978496⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨874247267992,0,false,-252071984640,-252071984576⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1325032039781,0,true,205136471104,205136471168⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨873991215771,0,false,-252394060160,-252394060096⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1053255221798,0,false,-47257589056,-47257588992⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1053360199718,0,false,-47148006208,-47148006144⟩
    { al := (167877/819200), au := (420117/2048000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨225320695234,225548596937⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204970733632,204970733696⟩ : DyadicInterval 40),(⟨-252142838144,-252142838080⟩ : DyadicInterval 40),(⟨738871755699,738871775029⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205159858688,205159858752⟩ : DyadicInterval 40),(⟨-252429518400,-252429518336⟩ : DyadicInterval 40),(⟨738824356880,738824376210⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204877230016,204877230080⟩ : DyadicInterval 40),(⟨-252001148992,-252001148928⟩ : DyadicInterval 40),(⟨738895168511,738895187841⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205113068672,205113068736⟩ : DyadicInterval 40),(⟨-252358581376,-252358581312⟩ : DyadicInterval 40),(⟨738836088805,738836108134⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨29050698,58165129⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29050304,29050368⟩ : DyadicInterval 40),(⟨-29051136,-29051072⟩ : DyadicInterval 40),(⟨762123383200,762123402529⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58163584,58163648⟩ : DyadicInterval 40),(⟨-58166720,-58166656⟩ : DyadicInterval 40),(⟨762123382042,762123401372⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3136,-704⟩ : DyadicInterval 40),(⟨762123383968,762123404448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨225264359784,225520412005⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204923978432,204923978496⟩ : DyadicInterval 40),(⟨-252071984640,-252071984576⟩ : DyadicInterval 40),(⟨738883464708,738883484038⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205136471104,205136471168⟩ : DyadicInterval 40),(⟨-252394060160,-252394060096⟩ : DyadicInterval 40),(⟨738830221408,738830240738⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-47257589056,-47148006144⟩ : DyadicInterval 40),(⟨785697386688,785752197408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨204970733632,205159858752⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-252429518400,-252142838080⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1254_ok : ecellOkT e1254 = true := by decide +kernel
theorem e1254_pos {a z : ℝ} (ha1 : ((167877/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((420117/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1254 e1254_ok ha1 ha2 hz1 hz2 hz

-- box ['104817/512000', '167877/819200', '3999/4000', '1']  interval_lower 613437089/1099511627776
noncomputable def e1255 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1324604421308,0,true,204781576000,204781576064⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨874418834244,0,false,-251856232704,-251856232640⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1324832323011,0,true,204970733632,204970733696⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨874190932541,0,false,-252142838144,-252142838080⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1324548148109,0,true,204734864448,204734864512⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨874475107443,0,false,-251785475904,-251785475840⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540679450,0,true,29051264,29051328⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482576102,0,false,-29052096,-29052032⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627008,0,false,-832,-768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1324576279107,0,true,204758215808,204758215872⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨874446976445,0,false,-251820846656,-251820846592⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1324832331550,0,true,204970740736,204970740800⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨874190924002,0,false,-252142848896,-252142848832⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1053337109683,0,false,-47172108160,-47172108096⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1053441994678,0,false,-47062630848,-47062630784⟩
    { al := (104817/512000), au := (167877/819200), zl := (3999/4000), zu := 1,
      A := ⟨225092793532,225320695235⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204781576000,204781576064⟩ : DyadicInterval 40),(⟨-251856232704,-251856232640⟩ : DyadicInterval 40),(⟨738919105268,738919124597⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204970733632,204970733696⟩ : DyadicInterval 40),(⟨-252142838144,-252142838080⟩ : DyadicInterval 40),(⟨738871755699,738871775028⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204734864448,204734864512⟩ : DyadicInterval 40),(⟨-251785475904,-251785475840⟩ : DyadicInterval 40),(⟨738930789141,738930808471⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204970733632,204970733696⟩ : DyadicInterval 40),(⟨-252142838144,-252142838080⟩ : DyadicInterval 40),(⟨738871755699,738871775028⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,29051674⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29051264,29051328⟩ : DyadicInterval 40),(⟨-29052096,-29052032⟩ : DyadicInterval 40),(⟨762123383200,762123402529⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-832,0⟩ : DyadicInterval 40),(⟨762123383616,762123403296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨225064651331,225320703774⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204758215808,204758215872⟩ : DyadicInterval 40),(⟨-251820846656,-251820846592⟩ : DyadicInterval 40),(⟨738924948738,738924968067⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204970740736,204970740800⟩ : DyadicInterval 40),(⟨-252142848896,-252142848832⟩ : DyadicInterval 40),(⟨738871753919,738871773248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-47172108160,-47062630784⟩ : DyadicInterval 40),(⟨785654699008,785709456960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨204781576000,204970733696⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-252142838144,-251856232640⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1255_ok : ecellOkT e1255 = true := by decide +kernel
theorem e1255_pos {a z : ℝ} (ha1 : ((104817/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((167877/819200 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1255 e1255_ok ha1 ha2 hz1 hz2 hz

-- box ['167877/819200', '420117/2048000', '3999/4000', '1']  interval_lower 154657183/274877906944
noncomputable def e1256 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1324832323010,0,true,204970733632,204970733696⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨874190932542,0,false,-252142838144,-252142838080⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1325060224713,0,true,205159858688,205159858752⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨873963030839,0,false,-252429518400,-252429518336⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1324775992836,0,true,204923982784,204923982848⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨874247262716,0,false,-252071991296,-252071991232⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540710700,0,true,29082496,29082560⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482544852,0,false,-29083328,-29083264⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627006,0,false,-832,-768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1324804152318,0,true,204947353792,204947353856⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨874219103234,0,false,-252107407104,-252107407040⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1325060233243,0,true,205159865792,205159865856⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨873963022309,0,false,-252429529088,-252429529024⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1053243655575,0,false,-47269663296,-47269663232⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1053348658389,0,false,-47160053248,-47160053184⟩
    { al := (167877/819200), au := (420117/2048000), zl := (3999/4000), zu := 1,
      A := ⟨225320695234,225548596937⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204970733632,204970733696⟩ : DyadicInterval 40),(⟨-252142838144,-252142838080⟩ : DyadicInterval 40),(⟨738871755699,738871775029⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205159858688,205159858752⟩ : DyadicInterval 40),(⟨-252429518400,-252429518336⟩ : DyadicInterval 40),(⟨738824356880,738824376210⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204923982784,204923982848⟩ : DyadicInterval 40),(⟨-252071991296,-252071991232⟩ : DyadicInterval 40),(⟨738883463636,738883482966⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205159858688,205159858752⟩ : DyadicInterval 40),(⟨-252429518400,-252429518336⟩ : DyadicInterval 40),(⟨738824356880,738824376210⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,29082924⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29082496,29082560⟩ : DyadicInterval 40),(⟨-29083328,-29083264⟩ : DyadicInterval 40),(⟨762123383198,762123402527⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-832,0⟩ : DyadicInterval 40),(⟨762123383616,762123403296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨225292524542,225548605467⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨204947353792,204947353856⟩ : DyadicInterval 40),(⟨-252107407104,-252107407040⟩ : DyadicInterval 40),(⟨738877611218,738877630548⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205159865792,205159865856⟩ : DyadicInterval 40),(⟨-252429529088,-252429529024⟩ : DyadicInterval 40),(⟨738824355072,738824374402⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-47269663296,-47160053184⟩ : DyadicInterval 40),(⟨785703410208,785758234528⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨204970733632,205159858752⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-252429518400,-252142838080⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1256_ok : ecellOkT e1256 = true := by decide +kernel
theorem e1256_pos {a z : ℝ} (ha1 : ((167877/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((420117/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1256 e1256_ok ha1 ha2 hz1 hz2 hz

-- box ['420117/2048000', '841083/4096000', '1999/2000', '3999/4000']  interval_lower 312401057/549755813888
noncomputable def e1257 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1325060224712,0,true,205159858688,205159858752⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨873963030840,0,false,-252429518400,-252429518336⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1325288126415,0,true,205348951296,205348951360⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨873735129137,0,false,-252716273344,-252716273280⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1324947450413,0,true,205066276608,205066276672⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨874075805139,0,false,-252287648896,-252287648832⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1325231682291,0,true,205302121984,205302122048⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨873791573261,0,false,-252645246144,-252645246080⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540709722,0,true,29081536,29081600⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482545830,0,false,-29082368,-29082304⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569855415,0,true,58226048,58226112⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453400137,0,false,-58229184,-58229120⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624692,0,false,-3136,-3072⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627007,0,false,-832,-768⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1325003832278,0,true,205113064256,205113064320⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨874019423274,0,false,-252358574720,-252358574656⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1325259913002,0,true,205325544064,205325544128⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨873763342550,0,false,-252680770048,-252680769984⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1053161696592,0,false,-47355225984,-47355225920⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1053266792336,0,false,-47245510400,-47245510336⟩
    { al := (420117/2048000), au := (841083/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨225548596936,225776498639⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205159858688,205159858752⟩ : DyadicInterval 40),(⟨-252429518400,-252429518336⟩ : DyadicInterval 40),(⟨738824356880,738824376210⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205348951296,205348951360⟩ : DyadicInterval 40),(⟨-252716273344,-252716273280⟩ : DyadicInterval 40),(⟨738776908670,738776928000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205066276608,205066276672⟩ : DyadicInterval 40),(⟨-252287648896,-252287648832⟩ : DyadicInterval 40),(⟨738847817732,738847837062⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205302121984,205302122048⟩ : DyadicInterval 40),(⟨-252645246144,-252645246080⟩ : DyadicInterval 40),(⟨738788664712,738788684041⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨29081946,58227639⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29081536,29081600⟩ : DyadicInterval 40),(⟨-29082368,-29082304⟩ : DyadicInterval 40),(⟨762123383198,762123402527⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58226048,58226112⟩ : DyadicInterval 40),(⟨-58229184,-58229120⟩ : DyadicInterval 40),(⟨762123382036,762123401365⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3136,-768⟩ : DyadicInterval 40),(⟨762123384000,762123404448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨225492204502,225748285226⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205113064256,205113064320⟩ : DyadicInterval 40),(⟨-252358574720,-252358574656⟩ : DyadicInterval 40),(⟨738836089920,738836109249⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205325544064,205325544128⟩ : DyadicInterval 40),(⟨-252680770048,-252680769984⟩ : DyadicInterval 40),(⟨738782785266,738782804595⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-47355225984,-47245510336⟩ : DyadicInterval 40),(⟨785746138784,785801015872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨205159858688,205348951360⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-252716273344,-252429518336⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1257_ok : ecellOkT e1257 = true := by decide +kernel
theorem e1257_pos {a z : ℝ} (ha1 : ((420117/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((841083/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1257 e1257_ok ha1 ha2 hz1 hz2 hz

-- box ['841083/4096000', '210483/1024000', '1999/2000', '3999/4000']  interval_lower 630037991/1099511627776
noncomputable def e1258 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1325288126414,0,true,205348951296,205348951360⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨873735129138,0,false,-252716273344,-252716273280⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1325516028117,0,true,205538011328,205538011392⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨873507227435,0,false,-253003103104,-253003103040⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1325175238164,0,true,205255290688,205255290752⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨873848017388,0,false,-252574223488,-252574223424⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1325459527018,0,true,205491142848,205491142912⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨873563728534,0,false,-252931985664,-252931985600⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540740977,0,true,29112768,29112832⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482514575,0,false,-29113600,-29113536⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099569917937,0,true,58288576,58288640⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099453337615,0,false,-58291712,-58291648⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624685,0,false,-3136,-3072⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627006,0,false,-832,-768⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1325231677006,0,true,205302117632,205302117696⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨873791578546,0,false,-252645239488,-252645239424⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1325487786222,0,true,205514584512,205514584576⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨873535469330,0,false,-252967554752,-252967554688⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1053068076933,0,false,-47452970176,-47452970112⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1053173290521,0,false,-47343121856,-47343121792⟩
    { al := (841083/4096000), au := (210483/1024000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨225776498638,226004400341⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205348951296,205348951360⟩ : DyadicInterval 40),(⟨-252716273344,-252716273280⟩ : DyadicInterval 40),(⟨738776908670,738776928000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205538011328,205538011392⟩ : DyadicInterval 40),(⟨-253003103104,-253003103040⟩ : DyadicInterval 40),(⟨738729411183,738729430512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205255290688,205255290752⟩ : DyadicInterval 40),(⟨-252574223488,-252574223424⟩ : DyadicInterval 40),(⟨738800417705,738800437035⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205491142848,205491142912⟩ : DyadicInterval 40),(⟨-252931985664,-252931985600⟩ : DyadicInterval 40),(⟨738741191292,738741210622⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨29113201,58290161⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29112768,29112832⟩ : DyadicInterval 40),(⟨-29113600,-29113536⟩ : DyadicInterval 40),(⟨762123383197,762123402526⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58288576,58288640⟩ : DyadicInterval 40),(⟨-58291712,-58291648⟩ : DyadicInterval 40),(⟨762123382029,762123401358⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3136,-768⟩ : DyadicInterval 40),(⟨762123384000,762123404448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨225720049230,225976158446⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205302117632,205302117696⟩ : DyadicInterval 40),(⟨-252645239488,-252645239424⟩ : DyadicInterval 40),(⟨738788665790,738788685120⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205514584512,205514584576⟩ : DyadicInterval 40),(⟨-252967554752,-252967554688⟩ : DyadicInterval 40),(⟨738735299835,738735319164⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-47452970176,-47343121792⟩ : DyadicInterval 40),(⟨785794944512,785849887968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨205348951296,205538011392⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-253003103104,-252716273280⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1258_ok : ecellOkT e1258 = true := by decide +kernel
theorem e1258_pos {a z : ℝ} (ha1 : ((841083/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((210483/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1258 e1258_ok ha1 ha2 hz1 hz2 hz

-- box ['420117/2048000', '841083/4096000', '3999/4000', '1']  interval_lower 311920257/549755813888
noncomputable def e1259 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1325060224712,0,true,205159858688,205159858752⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨873963030840,0,false,-252429518400,-252429518336⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1325288126415,0,true,205348951296,205348951360⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨873735129137,0,false,-252716273344,-252716273280⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1325003837562,0,true,205113068672,205113068736⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨874019417990,0,false,-252358581376,-252358581312⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099540741956,0,true,29113792,29113856⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482513596,0,false,-29114624,-29114560⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627005,0,false,-832,-768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1325032025526,0,true,205136459264,205136459328⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨873991230026,0,false,-252394042240,-252394042176⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1325288134958,0,true,205348958336,205348958400⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨873735120594,0,false,-252716284096,-252716284032⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1053150106981,0,false,-47367325696,-47367325632⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1053255227647,0,false,-47257582912,-47257582848⟩
    { al := (420117/2048000), au := (841083/4096000), zl := (3999/4000), zu := 1,
      A := ⟨225548596936,225776498639⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205159858688,205159858752⟩ : DyadicInterval 40),(⟨-252429518400,-252429518336⟩ : DyadicInterval 40),(⟨738824356880,738824376210⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205348951296,205348951360⟩ : DyadicInterval 40),(⟨-252716273344,-252716273280⟩ : DyadicInterval 40),(⟨738776908670,738776928000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205113068672,205113068736⟩ : DyadicInterval 40),(⟨-252358581376,-252358581312⟩ : DyadicInterval 40),(⟨738836088805,738836108135⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205348951296,205348951360⟩ : DyadicInterval 40),(⟨-252716273344,-252716273280⟩ : DyadicInterval 40),(⟨738776908670,738776928000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,29114180⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29113792,29113856⟩ : DyadicInterval 40),(⟨-29114624,-29114560⟩ : DyadicInterval 40),(⟨762123383197,762123402526⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-832,0⟩ : DyadicInterval 40),(⟨762123383616,762123403296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨225520397750,225776507182⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205136459264,205136459328⟩ : DyadicInterval 40),(⟨-252394042240,-252394042176⟩ : DyadicInterval 40),(⟨738830224386,738830243716⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨205348958336,205348958400⟩ : DyadicInterval 40),(⟨-252716284096,-252716284032⟩ : DyadicInterval 40),(⟨738776906920,738776926249⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-47367325696,-47257582848⟩ : DyadicInterval 40),(⟨785752175040,785807065728⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨205159858688,205348951360⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-252716273344,-252429518336⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1259_ok : ecellOkT e1259 = true := by decide +kernel
theorem e1259_pos {a z : ℝ} (ha1 : ((420117/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((841083/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1259 e1259_ok ha1 ha2 hz1 hz2 hz

end CKLaneC2R.EpCells.B020

end


