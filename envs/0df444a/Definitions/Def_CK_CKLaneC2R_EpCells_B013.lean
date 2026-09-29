-- Prove2me | Definitions.Def_CK_CKLaneC2R_EpCells_B013
-- name    : CK_CKLaneC2R_EpCells_B013
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T14:45:55.51672+00:00
-- url     : https://prove2.me/theorems/395cdc9e-21ee-4b39-b1c3-94ac9b38f271
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EpCells.B013` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EpCells.B013` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EpCells.B013` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EpCells.B013 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EpCells/B013.lean)

import Definitions.Def_CK_CKLaneC2R_EndpointCheckT

-- ===== source module CKLaneC2R.EpCells.B013 =====
section

namespace CKLaneC2R.EpCells.B013

open GeneralCK GeneralCK.Certificates CKLaneC2R CKLaneC2R.Endpoint

-- box ['739203/4096000', '185013/1024000', '3999/4000', '1']  interval_lower 4128037/34359738368
noncomputable def e780 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1297939922157,0,true,182422421440,182422421504⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨901083333395,0,false,-218828808832,-218828808768⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1298167823860,0,true,182615464704,182615464768⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨900855431692,0,false,-219106932160,-219106932096⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1297890315083,0,true,182380397440,182380397504⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨901132940469,0,false,-218768279424,-218768279360⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537062279,0,true,25434176,25434240⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486193273,0,false,-25434816,-25434752⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627187,0,false,-640,-576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1297915113573,0,true,182401405376,182401405440⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨901108141979,0,false,-218798537600,-218798537536⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1298167832357,0,true,182615471936,182615472000⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨900855423195,0,false,-219106942528,-219106942464⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1063619067277,0,false,-36491470592,-36491470528⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1063710330017,0,false,-36397132160,-36397132096⟩
    { al := (739203/4096000), au := (185013/1024000), zl := (3999/4000), zu := 1,
      A := ⟨198428294381,198656196084⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182422421440,182422421504⟩ : DyadicInterval 40),(⟨-218828808832,-218828808768⟩ : DyadicInterval 40),(⟨744119776323,744119795653⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182615464704,182615464768⟩ : DyadicInterval 40),(⟨-219106932160,-219106932096⟩ : DyadicInterval 40),(⟨744078167176,744078186506⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182380397440,182380397504⟩ : DyadicInterval 40),(⟨-218768279424,-218768279360⟩ : DyadicInterval 40),(⟨744128826886,744128846216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182615464704,182615464768⟩ : DyadicInterval 40),(⟨-219106932160,-219106932096⟩ : DyadicInterval 40),(⟨744078167176,744078186506⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,25434503⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25434176,25434240⟩ : DyadicInterval 40),(⟨-25434816,-25434752⟩ : DyadicInterval 40),(⟨762123383283,762123402612⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-640,0⟩ : DyadicInterval 40),(⟨762123383616,762123403200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨198403485797,198656204581⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182401405376,182401405440⟩ : DyadicInterval 40),(⟨-218798537600,-218798537536⟩ : DyadicInterval 40),(⟨744124302828,744124322157⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182615471936,182615472000⟩ : DyadicInterval 40),(⟨-219106942528,-219106942464⟩ : DyadicInterval 40),(⟨744078165602,744078184931⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-36491470592,-36397132096⟩ : DyadicInterval 40),(⟨780321949664,780369138176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨182422421440,182615464768⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-219106932160,-218828808768⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e780_ok : ecellOkT e780 = true := by decide +kernel
theorem e780_pos {a z : ℝ} (ha1 : ((739203/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((185013/1024000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e780 e780_ok ha1 ha2 hz1 hz2 hz

-- box ['185013/1024000', '740901/4096000', '999/1000', '3997/4000']  interval_lower 17134707/137438953472
noncomputable def e781 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1298167823859,0,true,182615464704,182615464768⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨900855431693,0,false,-219106932160,-219106932096⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1298395725562,0,true,182808474112,182808474176⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨900627529990,0,false,-219385125824,-219385125760⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1297969167662,0,true,182447195648,182447195712⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨901054087890,0,false,-218864495104,-218864495040⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1298246562489,0,true,182682152064,182682152128⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨900776693063,0,false,-219203038400,-219203038336⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587928392,0,true,76297920,76297984⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435327160,0,false,-76303296,-76303232⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099613485564,0,true,101853056,101853120⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099409769988,0,false,-101862528,-101862464⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511618339,0,false,-9472,-9408⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622482,0,false,-5312,-5248⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1298068491817,0,true,182531330048,182531330112⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨900954763735,0,false,-218985702144,-218985702080⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1298321153190,0,true,182745322688,182745322752⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨900702102362,0,false,-219294089536,-219294089472⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1063563642873,0,false,-36548766848,-36548766784⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1063654955358,0,false,-36454372096,-36454372032⟩
    { al := (185013/1024000), au := (740901/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨198656196083,198884097786⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182615464704,182615464768⟩ : DyadicInterval 40),(⟨-219106932160,-219106932096⟩ : DyadicInterval 40),(⟨744078167176,744078186506⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182808474112,182808474176⟩ : DyadicInterval 40),(⟨-219385125824,-219385125760⟩ : DyadicInterval 40),(⟨744036509165,744036528494⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182447195648,182447195712⟩ : DyadicInterval 40),(⟨-218864495104,-218864495040⟩ : DyadicInterval 40),(⟨744114439548,744114458878⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182682152064,182682152128⟩ : DyadicInterval 40),(⟨-219203038400,-219203038336⟩ : DyadicInterval 40),(⟨744063780132,744063799461⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨76300616,101857788⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76297920,76297984⟩ : DyadicInterval 40),(⟨-76303296,-76303232⟩ : DyadicInterval 40),(⟨762123380944,762123400274⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨101853056,101853120⟩ : DyadicInterval 40),(⟨-101862528,-101862464⟩ : DyadicInterval 40),(⟨762123378851,762123398181⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-9472,-5248⟩ : DyadicInterval 40),(⟨762123386240,762123407616⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨198556864041,198809525414⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182531330048,182531330112⟩ : DyadicInterval 40),(⟨-218985702144,-218985702080⟩ : DyadicInterval 40),(⟨744096308727,744096328057⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182745322688,182745322752⟩ : DyadicInterval 40),(⟨-219294089536,-219294089472⟩ : DyadicInterval 40),(⟨744050145576,744050164905⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-36548766848,-36454372032⟩ : DyadicInterval 40),(⟨780350569632,780397786304⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨182615464704,182808474176⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-219385125824,-219106932096⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e781_ok : ecellOkT e781 = true := by decide +kernel
theorem e781_pos {a z : ℝ} (ha1 : ((185013/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((740901/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e781 e781_ok ha1 ha2 hz1 hz2 hz

-- box ['740901/4096000', '2967/16384', '999/1000', '3997/4000']  interval_lower 70128197/549755813888
noncomputable def e782 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1298395725561,0,true,182808474112,182808474176⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨900627529991,0,false,-219385125824,-219385125760⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1298623627264,0,true,183001449600,183001449664⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨900399628288,0,false,-219663389888,-219663389824⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1298196841463,0,true,182640041536,182640041600⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨900826414089,0,false,-219142349248,-219142349184⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1298474293265,0,true,182875005056,182875005120⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨900548962287,0,false,-219481047680,-219481047616⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588020198,0,true,76389760,76389824⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435235354,0,false,-76395136,-76395072⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099613607994,0,true,101975488,101975552⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099409647558,0,false,-101984960,-101984896⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511618317,0,false,-9472,-9408⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622469,0,false,-5312,-5248⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1298296279569,0,true,182724257728,182724257792⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨900726975983,0,false,-219263726016,-219263725952⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1298548969434,0,true,182938236928,182938236992⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨900474286118,0,false,-219572226176,-219572226112⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1063481209930,0,false,-36633989248,-36633989184⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1063572637419,0,false,-36539468288,-36539468224⟩
    { al := (740901/4096000), au := (2967/16384), zl := (999/1000), zu := (3997/4000),
      A := ⟨198884097785,199111999488⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182808474112,182808474176⟩ : DyadicInterval 40),(⟨-219385125824,-219385125760⟩ : DyadicInterval 40),(⟨744036509165,744036528495⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183001449600,183001449664⟩ : DyadicInterval 40),(⟨-219663389888,-219663389824⟩ : DyadicInterval 40),(⟨743994802341,743994821671⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182640041536,182640041600⟩ : DyadicInterval 40),(⟨-219142349248,-219142349184⟩ : DyadicInterval 40),(⟨744072865760,744072885089⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182875005056,182875005120⟩ : DyadicInterval 40),(⟨-219481047680,-219481047616⟩ : DyadicInterval 40),(⟨744022136502,744022155831⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨76392422,101980218⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76389760,76389824⟩ : DyadicInterval 40),(⟨-76395136,-76395072⟩ : DyadicInterval 40),(⟨762123380932,762123400261⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨101975488,101975552⟩ : DyadicInterval 40),(⟨-101984960,-101984896⟩ : DyadicInterval 40),(⟨762123378828,762123398158⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-9472,-5248⟩ : DyadicInterval 40),(⟨762123386240,762123407616⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨198784651793,199037341658⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182724257728,182724257792⟩ : DyadicInterval 40),(⟨-219263726016,-219263725952⟩ : DyadicInterval 40),(⟨744054692819,744054712148⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182938236928,182938236992⟩ : DyadicInterval 40),(⟨-219572226176,-219572226112⟩ : DyadicInterval 40),(⟨744008470344,744008489673⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-36633989248,-36539468224⟩ : DyadicInterval 40),(⟨780393117728,780440397504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨182808474112,183001449664⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-219663389888,-219385125760⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e782_ok : ecellOkT e782 = true := by decide +kernel
theorem e782_pos {a z : ℝ} (ha1 : ((740901/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((2967/16384 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e782 e782_ok ha1 ha2 hz1 hz2 hz

-- box ['185013/1024000', '740901/4096000', '3997/4000', '1999/2000']  interval_lower 34117533/274877906944
noncomputable def e783 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1298167823859,0,true,182615464704,182615464768⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨900855431693,0,false,-219106932160,-219106932096⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1298395725562,0,true,182808474112,182808474176⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨900627529990,0,false,-219385125824,-219385125760⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1298018831711,0,true,182489265280,182489265344⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨901004423841,0,false,-218925099392,-218925099328⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1298296283514,0,true,182724261056,182724261120⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨900726972038,0,false,-219263730880,-219263730816⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099562495077,0,true,50866112,50866176⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099460760475,0,false,-50868480,-50868416⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588021648,0,true,76391168,76391232⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435233904,0,false,-76396544,-76396480⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622468,0,false,-5312,-5248⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625423,0,false,-2368,-2304⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1298093323319,0,true,182552363008,182552363072⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨900929932233,0,false,-219016006528,-219016006464⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1298346013334,0,true,182766375808,182766375872⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨900677242218,0,false,-219324437376,-219324437312⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1063554652077,0,false,-36558061568,-36558061504⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1063645986333,0,false,-36463643456,-36463643392⟩
    { al := (185013/1024000), au := (740901/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨198656196083,198884097786⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182615464704,182615464768⟩ : DyadicInterval 40),(⟨-219106932160,-219106932096⟩ : DyadicInterval 40),(⟨744078167176,744078186506⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182808474112,182808474176⟩ : DyadicInterval 40),(⟨-219385125824,-219385125760⟩ : DyadicInterval 40),(⟨744036509165,744036528494⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182489265280,182489265344⟩ : DyadicInterval 40),(⟨-218925099392,-218925099328⟩ : DyadicInterval 40),(⟨744105374975,744105394305⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182724261056,182724261120⟩ : DyadicInterval 40),(⟨-219263730880,-219263730816⟩ : DyadicInterval 40),(⟨744054692125,744054711455⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨50867301,76393872⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨50866112,50866176⟩ : DyadicInterval 40),(⟨-50868480,-50868416⟩ : DyadicInterval 40),(⟨762123382382,762123401711⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76391168,76391232⟩ : DyadicInterval 40),(⟨-76396544,-76396480⟩ : DyadicInterval 40),(⟨762123380931,762123400261⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5312,-2304⟩ : DyadicInterval 40),(⟨762123384768,762123405536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨198581695543,198834385558⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182552363008,182552363072⟩ : DyadicInterval 40),(⟨-219016006528,-219016006464⟩ : DyadicInterval 40),(⟨744091774492,744091793821⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182766375808,182766375872⟩ : DyadicInterval 40),(⟨-219324437376,-219324437312⟩ : DyadicInterval 40),(⟨744045600201,744045619531⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-36558061568,-36463643392⟩ : DyadicInterval 40),(⟨780355205312,780402433664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨182615464704,182808474176⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-219385125824,-219106932096⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e783_ok : ecellOkT e783 = true := by decide +kernel
theorem e783_pos {a z : ℝ} (ha1 : ((185013/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((740901/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e783 e783_ok ha1 ha2 hz1 hz2 hz

-- box ['740901/4096000', '2967/16384', '3997/4000', '1999/2000']  interval_lower 139646319/1099511627776
noncomputable def e784 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1298395725561,0,true,182808474112,182808474176⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨900627529991,0,false,-219385125824,-219385125760⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1298623627264,0,true,183001449600,183001449664⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨900399628288,0,false,-219663389888,-219663389824⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1298246562487,0,true,182682152064,182682152128⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨900776693065,0,false,-219203038400,-219203038336⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1298524071265,0,true,182917154880,182917154944⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨900499184287,0,false,-219541825088,-219541825024⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099562556283,0,true,50927296,50927360⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099460699269,0,false,-50929728,-50929664⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588113472,0,true,76483008,76483072⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435142080,0,false,-76488384,-76488320⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622455,0,false,-5376,-5312⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625418,0,false,-2368,-2304⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1298321139557,0,true,182745311104,182745311168⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨900702115995,0,false,-219294072896,-219294072832⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1298573858062,0,true,182959310464,182959310528⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨900449397490,0,false,-219602616512,-219602616448⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1063472198519,0,false,-36643306048,-36643305984⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1063563647804,0,false,-36548761728,-36548761664⟩
    { al := (740901/4096000), au := (2967/16384), zl := (3997/4000), zu := (1999/2000),
      A := ⟨198884097785,199111999488⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182808474112,182808474176⟩ : DyadicInterval 40),(⟨-219385125824,-219385125760⟩ : DyadicInterval 40),(⟨744036509165,744036528495⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183001449600,183001449664⟩ : DyadicInterval 40),(⟨-219663389888,-219663389824⟩ : DyadicInterval 40),(⟨743994802341,743994821671⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182682152064,182682152128⟩ : DyadicInterval 40),(⟨-219203038400,-219203038336⟩ : DyadicInterval 40),(⟨744063780132,744063799462⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182917154880,182917154944⟩ : DyadicInterval 40),(⟨-219541825088,-219541825024⟩ : DyadicInterval 40),(⟨744013027442,744013046771⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨50928507,76485696⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨50927296,50927360⟩ : DyadicInterval 40),(⟨-50929728,-50929664⟩ : DyadicInterval 40),(⟨762123382408,762123401738⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76483008,76483072⟩ : DyadicInterval 40),(⟨-76488384,-76488320⟩ : DyadicInterval 40),(⟨762123380919,762123400248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5376,-2304⟩ : DyadicInterval 40),(⟨762123384768,762123405568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨198809511781,199062230286⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182745311104,182745311168⟩ : DyadicInterval 40),(⟨-219294072896,-219294072832⟩ : DyadicInterval 40),(⟨744050148092,744050167421⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182959310464,182959310528⟩ : DyadicInterval 40),(⟨-219602616512,-219602616448⟩ : DyadicInterval 40),(⟨744003914450,744003933779⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-36643306048,-36548761664⟩ : DyadicInterval 40),(⟨780397764448,780445055904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨182808474112,183001449664⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-219663389888,-219385125760⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e784_ok : ecellOkT e784 = true := by decide +kernel
theorem e784_pos {a z : ℝ} (ha1 : ((740901/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((2967/16384 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e784 e784_ok ha1 ha2 hz1 hz2 hz

-- box ['2967/16384', '742599/4096000', '999/1000', '3997/4000']  interval_lower 143449875/1099511627776
noncomputable def e785 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1298623627264,0,true,183001449600,183001449664⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨900399628288,0,false,-219663389888,-219663389824⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1298851528967,0,true,183194391296,183194391360⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨900171726585,0,false,-219941724416,-219941724352⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1298424515264,0,true,182832853632,182832853696⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨900598740288,0,false,-219420273664,-219420273600⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1298702024042,0,true,183067824192,183067824256⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨900321231510,0,false,-219759127296,-219759127232⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588112019,0,true,76481536,76481600⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435143533,0,false,-76486912,-76486848⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099613730446,0,true,102097920,102097984⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099409525106,0,false,-102107456,-102107392⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511618294,0,false,-9536,-9472⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622456,0,false,-5376,-5312⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1298524067317,0,true,182917151488,182917151552⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨900499188235,0,false,-219541820224,-219541820160⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1298776785679,0,true,183131117312,183131117376⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨900246469873,0,false,-219850433280,-219850433216⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1063398682581,0,false,-36719315904,-36719315840⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1063490225100,0,false,-36624668672,-36624668608⟩
    { al := (2967/16384), au := (742599/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨199111999488,199339901191⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183001449600,183001449664⟩ : DyadicInterval 40),(⟨-219663389888,-219663389824⟩ : DyadicInterval 40),(⟨743994802341,743994821671⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183194391296,183194391360⟩ : DyadicInterval 40),(⟨-219941724416,-219941724352⟩ : DyadicInterval 40),(⟨743953046645,743953065975⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182832853632,182832853696⟩ : DyadicInterval 40),(⟨-219420273664,-219420273600⟩ : DyadicInterval 40),(⟨744031243236,744031262565⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183067824192,183067824256⟩ : DyadicInterval 40),(⟨-219759127296,-219759127232⟩ : DyadicInterval 40),(⟨743980444138,743980463468⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨76484243,102102670⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76481536,76481600⟩ : DyadicInterval 40),(⟨-76486912,-76486848⟩ : DyadicInterval 40),(⟨762123380919,762123400248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨102097920,102097984⟩ : DyadicInterval 40),(⟨-102107456,-102107392⟩ : DyadicInterval 40),(⟨762123378838,762123398167⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-9536,-5312⟩ : DyadicInterval 40),(⟨762123386272,762123407648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨199012439541,199265157903⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182917151488,182917151552⟩ : DyadicInterval 40),(⟨-219541820224,-219541820160⟩ : DyadicInterval 40),(⟨744013028176,744013047505⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183131117312,183131117376⟩ : DyadicInterval 40),(⟨-219850433280,-219850433216⟩ : DyadicInterval 40),(⟨743966746354,743966765683⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-36719315904,-36624668608⟩ : DyadicInterval 40),(⟨780435717920,780483060832⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨183001449600,183194391360⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-219941724416,-219663389824⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e785_ok : ecellOkT e785 = true := by decide +kernel
theorem e785_pos {a z : ℝ} (ha1 : ((2967/16384 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((742599/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e785 e785_ok ha1 ha2 hz1 hz2 hz

-- box ['742599/4096000', '92931/512000', '999/1000', '3997/4000']  interval_lower 146658793/1099511627776
noncomputable def e786 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1298851528966,0,true,183194391296,183194391360⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨900171726586,0,false,-219941724416,-219941724352⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1299079430669,0,true,183387299072,183387299136⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨899943824883,0,false,-220220129408,-220220129344⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1298652189064,0,true,183025631872,183025631936⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨900371066488,0,false,-219698268352,-219698268288⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1298929754817,0,true,183260609472,183260609536⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨900093500735,0,false,-220037277248,-220037277184⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588203856,0,true,76573376,76573440⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435051696,0,false,-76578752,-76578688⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099613852918,0,true,102220352,102220416⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099409402634,0,false,-102229952,-102229888⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511618271,0,false,-9536,-9472⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622443,0,false,-5376,-5312⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1298751855065,0,true,183110011456,183110011520⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨900271400487,0,false,-219819984768,-219819984704⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1299004601915,0,true,183323963840,183323963904⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨900018653637,0,false,-220128710720,-220128710656⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1063316060830,0,false,-36804746816,-36804746752⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1063407718398,0,false,-36709973312,-36709973248⟩
    { al := (742599/4096000), au := (92931/512000), zl := (999/1000), zu := (3997/4000),
      A := ⟨199339901190,199567802893⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183194391296,183194391360⟩ : DyadicInterval 40),(⟨-219941724416,-219941724352⟩ : DyadicInterval 40),(⟨743953046645,743953065975⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183387299072,183387299136⟩ : DyadicInterval 40),(⟨-220220129408,-220220129344⟩ : DyadicInterval 40),(⟨743911242141,743911261470⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183025631872,183025631936⟩ : DyadicInterval 40),(⟨-219698268352,-219698268288⟩ : DyadicInterval 40),(⟨743989572004,743989591334⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183260609472,183260609536⟩ : DyadicInterval 40),(⟨-220037277248,-220037277184⟩ : DyadicInterval 40),(⟨743938703031,743938722360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨76576080,102225142⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76573376,76573440⟩ : DyadicInterval 40),(⟨-76578752,-76578688⟩ : DyadicInterval 40),(⟨762123380906,762123400236⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨102220352,102220416⟩ : DyadicInterval 40),(⟨-102229952,-102229888⟩ : DyadicInterval 40),(⟨762123378847,762123398177⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-9536,-5312⟩ : DyadicInterval 40),(⟨762123386272,762123407648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨199240227289,199492974139⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183110011456,183110011520⟩ : DyadicInterval 40),(⟨-219819984768,-219819984704⟩ : DyadicInterval 40),(⟨743971314710,743971334040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183323963840,183323963904⟩ : DyadicInterval 40),(⟨-220128710720,-220128710656⟩ : DyadicInterval 40),(⟨743924973544,743924992873⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-36804746816,-36709973248⟩ : DyadicInterval 40),(⟨780478370240,780525776288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨183194391296,183387299136⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-220220129408,-219941724352⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e786_ok : ecellOkT e786 = true := by decide +kernel
theorem e786_pos {a z : ℝ} (ha1 : ((742599/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((92931/512000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e786 e786_ok ha1 ha2 hz1 hz2 hz

-- box ['2967/16384', '742599/4096000', '3997/4000', '1999/2000']  interval_lower 142837537/1099511627776
noncomputable def e787 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1298623627264,0,true,183001449600,183001449664⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨900399628288,0,false,-219663389888,-219663389824⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1298851528967,0,true,183194391296,183194391360⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨900171726585,0,false,-219941724416,-219941724352⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1298474293264,0,true,182875005056,182875005120⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨900548962288,0,false,-219481047680,-219481047616⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1298751859017,0,true,183110014848,183110014912⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨900271396535,0,false,-219819989632,-219819989568⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099562617498,0,true,50988480,50988544⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099460638054,0,false,-50990912,-50990848⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588205312,0,true,76574848,76574912⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435050240,0,false,-76580224,-76580160⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622442,0,false,-5376,-5312⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625412,0,false,-2368,-2304⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1298548955797,0,true,182938225344,182938225408⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨900474299755,0,false,-219572209536,-219572209472⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1298801702793,0,true,183152211328,183152211392⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨900221552759,0,false,-219880866048,-219880865984⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1063389650529,0,false,-36728654720,-36728654656⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1063481214869,0,false,-36633984128,-36633984064⟩
    { al := (2967/16384), au := (742599/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨199111999488,199339901191⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183001449600,183001449664⟩ : DyadicInterval 40),(⟨-219663389888,-219663389824⟩ : DyadicInterval 40),(⟨743994802341,743994821671⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183194391296,183194391360⟩ : DyadicInterval 40),(⟨-219941724416,-219941724352⟩ : DyadicInterval 40),(⟨743953046645,743953065975⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182875005056,182875005120⟩ : DyadicInterval 40),(⟨-219481047680,-219481047616⟩ : DyadicInterval 40),(⟨744022136502,744022155831⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183110014848,183110014912⟩ : DyadicInterval 40),(⟨-219819989632,-219819989568⟩ : DyadicInterval 40),(⟨743971313974,743971333304⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨50989722,76577536⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨50988480,50988544⟩ : DyadicInterval 40),(⟨-50990912,-50990848⟩ : DyadicInterval 40),(⟨762123382403,762123401732⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76574848,76574912⟩ : DyadicInterval 40),(⟨-76580224,-76580160⟩ : DyadicInterval 40),(⟨762123380906,762123400235⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5376,-2304⟩ : DyadicInterval 40),(⟨762123384768,762123405568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨199037328021,199290075017⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182938225344,182938225408⟩ : DyadicInterval 40),(⟨-219572209536,-219572209472⟩ : DyadicInterval 40),(⟨744008472867,744008492196⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183152211328,183152211392⟩ : DyadicInterval 40),(⟨-219880866048,-219880865984⟩ : DyadicInterval 40),(⟨743962179850,743962199180⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-36728654720,-36633984064⟩ : DyadicInterval 40),(⟨780440375648,780487730240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨183001449600,183194391360⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-219941724416,-219663389824⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e787_ok : ecellOkT e787 = true := by decide +kernel
theorem e787_pos {a z : ℝ} (ha1 : ((2967/16384 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((742599/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e787 e787_ok ha1 ha2 hz1 hz2 hz

-- box ['742599/4096000', '92931/512000', '3997/4000', '1999/2000']  interval_lower 18255495/137438953472
noncomputable def e788 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1298851528966,0,true,183194391296,183194391360⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨900171726586,0,false,-219941724416,-219941724352⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1299079430669,0,true,183387299072,183387299136⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨899943824883,0,false,-220220129408,-220220129344⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1298702024040,0,true,183067824192,183067824256⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨900321231512,0,false,-219759127296,-219759127232⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1298979646768,0,true,183302840960,183302841024⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨900043608784,0,false,-220098224576,-220098224512⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099562678724,0,true,51049728,51049792⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099460576828,0,false,-51052160,-51052096⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588297169,0,true,76666688,76666752⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434958383,0,false,-76672128,-76672064⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622429,0,false,-5376,-5312⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625406,0,false,-2432,-2368⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1298776772036,0,true,183131105728,183131105792⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨900246483516,0,false,-219850416576,-219850416512⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1299029547517,0,true,183345078272,183345078336⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨899993708035,0,false,-220159186048,-220159185984⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1063307008113,0,false,-36814107712,-36814107648⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1063398687527,0,false,-36719310784,-36719310720⟩
    { al := (742599/4096000), au := (92931/512000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨199339901190,199567802893⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183194391296,183194391360⟩ : DyadicInterval 40),(⟨-219941724416,-219941724352⟩ : DyadicInterval 40),(⟨743953046645,743953065975⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183387299072,183387299136⟩ : DyadicInterval 40),(⟨-220220129408,-220220129344⟩ : DyadicInterval 40),(⟨743911242141,743911261470⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183067824192,183067824256⟩ : DyadicInterval 40),(⟨-219759127296,-219759127232⟩ : DyadicInterval 40),(⟨743980444139,743980463468⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183302840960,183302841024⟩ : DyadicInterval 40),(⟨-220098224576,-220098224512⟩ : DyadicInterval 40),(⟨743929551737,743929571066⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨51050948,76669393⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨51049728,51049792⟩ : DyadicInterval 40),(⟨-51052160,-51052096⟩ : DyadicInterval 40),(⟨762123382397,762123401726⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76666688,76666752⟩ : DyadicInterval 40),(⟨-76672128,-76672064⟩ : DyadicInterval 40),(⟨762123380925,762123400255⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5376,-2368⟩ : DyadicInterval 40),(⟨762123384800,762123405568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨199265144260,199517919741⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183131105728,183131105792⟩ : DyadicInterval 40),(⟨-219850416576,-219850416512⟩ : DyadicInterval 40),(⟨743966748857,743966768187⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183345078272,183345078336⟩ : DyadicInterval 40),(⟨-220159186048,-220159185984⟩ : DyadicInterval 40),(⟨743920396495,743920415824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-36814107712,-36719310720⟩ : DyadicInterval 40),(⟨780483038976,780530456736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨183194391296,183387299136⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-220220129408,-219941724352⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e788_ok : ecellOkT e788 = true := by decide +kernel
theorem e788_pos {a z : ℝ} (ha1 : ((742599/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((92931/512000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e788 e788_ok ha1 ha2 hz1 hz2 hz

-- box ['185013/1024000', '740901/4096000', '1999/2000', '3999/4000']  interval_lower 135862373/1099511627776
noncomputable def e789 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1298167823859,0,true,182615464704,182615464768⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨900855431693,0,false,-219106932160,-219106932096⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1298395725562,0,true,182808474112,182808474176⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨900627529990,0,false,-219385125824,-219385125760⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1298068495760,0,true,182531333376,182531333440⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨900954759792,0,false,-218985706944,-218985706880⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1298346004538,0,true,182766368384,182766368448⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨900677251014,0,false,-219324426688,-219324426624⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537061453,0,true,25433344,25433408⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486194099,0,false,-25433984,-25433920⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099562557421,0,true,50928448,50928512⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099460698131,0,false,-50930880,-50930816⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625416,0,false,-2368,-2304⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627188,0,false,-640,-576⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1298118154977,0,true,182573395776,182573395840⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨900905100575,0,false,-219046312000,-219046311936⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1298370873623,0,true,182787428672,182787428736⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨900652381929,0,false,-219354786304,-219354786240⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1063545660104,0,false,-36567357568,-36567357504⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1063637016130,0,false,-36472916224,-36472916160⟩
    { al := (185013/1024000), au := (740901/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨198656196083,198884097786⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182615464704,182615464768⟩ : DyadicInterval 40),(⟨-219106932160,-219106932096⟩ : DyadicInterval 40),(⟨744078167176,744078186506⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182808474112,182808474176⟩ : DyadicInterval 40),(⟨-219385125824,-219385125760⟩ : DyadicInterval 40),(⟨744036509165,744036528494⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182531333376,182531333440⟩ : DyadicInterval 40),(⟨-218985706944,-218985706880⟩ : DyadicInterval 40),(⟨744096308009,744096327339⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182766368384,182766368448⟩ : DyadicInterval 40),(⟨-219324426688,-219324426624⟩ : DyadicInterval 40),(⟨744045601815,744045621145⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨25433677,50929645⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25433344,25433408⟩ : DyadicInterval 40),(⟨-25433984,-25433920⟩ : DyadicInterval 40),(⟨762123383283,762123402612⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨50928448,50928512⟩ : DyadicInterval 40),(⟨-50930880,-50930816⟩ : DyadicInterval 40),(⟨762123382408,762123401737⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2368,-576⟩ : DyadicInterval 40),(⟨762123383904,762123404064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨198606527201,198859245847⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182573395776,182573395840⟩ : DyadicInterval 40),(⟨-219046312000,-219046311936⟩ : DyadicInterval 40),(⟨744087239627,744087258957⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182787428672,182787428736⟩ : DyadicInterval 40),(⟨-219354786304,-219354786240⟩ : DyadicInterval 40),(⟨744041054236,744041073565⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-36567357568,-36472916160⟩ : DyadicInterval 40),(⟨780359841696,780407081664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨182615464704,182808474176⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-219385125824,-219106932096⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e789_ok : ecellOkT e789 = true := by decide +kernel
theorem e789_pos {a z : ℝ} (ha1 : ((185013/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((740901/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e789 e789_ok ha1 ha2 hz1 hz2 hz

-- box ['740901/4096000', '2967/16384', '1999/2000', '3999/4000']  interval_lower 139036293/1099511627776
noncomputable def e790 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1298395725561,0,true,182808474112,182808474176⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨900627529991,0,false,-219385125824,-219385125760⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1298623627264,0,true,183001449600,183001449664⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨900399628288,0,false,-219663389888,-219663389824⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1298296283512,0,true,182724261056,182724261120⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨900726972040,0,false,-219263730816,-219263730752⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1298573849265,0,true,182959303040,182959303104⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨900449406287,0,false,-219602605824,-219602605760⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537092056,0,true,25463936,25464000⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486163496,0,false,-25464576,-25464512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099562618638,0,true,50989632,50989696⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099460636914,0,false,-50992064,-50992000⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625411,0,false,-2368,-2304⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627187,0,false,-640,-576⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1298345999704,0,true,182766364288,182766364352⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨900677255848,0,false,-219324420736,-219324420672⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1298598746837,0,true,182980383808,182980383872⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨900424508715,0,false,-219633007872,-219633007808⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1063463185927,0,false,-36652624064,-36652624000⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1063554657008,0,false,-36558056448,-36558056384⟩
    { al := (740901/4096000), au := (2967/16384), zl := (1999/2000), zu := (3999/4000),
      A := ⟨198884097785,199111999488⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182808474112,182808474176⟩ : DyadicInterval 40),(⟨-219385125824,-219385125760⟩ : DyadicInterval 40),(⟨744036509165,744036528495⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183001449600,183001449664⟩ : DyadicInterval 40),(⟨-219663389888,-219663389824⟩ : DyadicInterval 40),(⟨743994802341,743994821671⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182724261056,182724261120⟩ : DyadicInterval 40),(⟨-219263730816,-219263730752⟩ : DyadicInterval 40),(⟨744054692099,744054711429⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182959303040,182959303104⟩ : DyadicInterval 40),(⟨-219602605824,-219602605760⟩ : DyadicInterval 40),(⟨744003916068,744003935397⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨25464280,50990862⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25463936,25464000⟩ : DyadicInterval 40),(⟨-25464576,-25464512⟩ : DyadicInterval 40),(⟨762123383282,762123402611⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨50989632,50989696⟩ : DyadicInterval 40),(⟨-50992064,-50992000⟩ : DyadicInterval 40),(⟨762123382403,762123401732⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2368,-576⟩ : DyadicInterval 40),(⟨762123383904,762123404064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨198834371928,199087119061⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182766364288,182766364352⟩ : DyadicInterval 40),(⟨-219324420736,-219324420672⟩ : DyadicInterval 40),(⟨744045602680,744045622009⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182980383808,182980383872⟩ : DyadicInterval 40),(⟨-219633007872,-219633007808⟩ : DyadicInterval 40),(⟨743999357897,743999377227⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-36652624064,-36558056384⟩ : DyadicInterval 40),(⟨780402411808,780449714912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨182808474112,183001449664⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-219663389888,-219385125760⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e790_ok : ecellOkT e790 = true := by decide +kernel
theorem e790_pos {a z : ℝ} (ha1 : ((740901/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((2967/16384 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e790 e790_ok ha1 ha2 hz1 hz2 hz

-- box ['185013/1024000', '740901/4096000', '3999/4000', '1']  interval_lower 135253855/1099511627776
noncomputable def e791 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1298167823859,0,true,182615464704,182615464768⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨900855431693,0,false,-219106932160,-219106932096⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1298395725562,0,true,182808474112,182808474176⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨900627529990,0,false,-219385125824,-219385125760⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1298118159809,0,true,182573399872,182573399936⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨900905095743,0,false,-219046317888,-219046317824⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537092883,0,true,25464768,25464832⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486162669,0,false,-25465408,-25465344⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627186,0,false,-640,-576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1298142986781,0,true,182594428224,182594428288⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨900880268771,0,false,-219076618432,-219076618368⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1298395734062,0,true,182808481280,182808481344⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨900627521490,0,false,-219385136192,-219385136128⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1063536666953,0,false,-36576654848,-36576654784⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1063628044753,0,false,-36482190208,-36482190144⟩
    { al := (185013/1024000), au := (740901/4096000), zl := (3999/4000), zu := 1,
      A := ⟨198656196083,198884097786⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182615464704,182615464768⟩ : DyadicInterval 40),(⟨-219106932160,-219106932096⟩ : DyadicInterval 40),(⟨744078167176,744078186506⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182808474112,182808474176⟩ : DyadicInterval 40),(⟨-219385125824,-219385125760⟩ : DyadicInterval 40),(⟨744036509165,744036528494⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182573399872,182573399936⟩ : DyadicInterval 40),(⟨-219046317888,-219046317824⟩ : DyadicInterval 40),(⟨744087238739,744087258069⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182808474112,182808474176⟩ : DyadicInterval 40),(⟨-219385125824,-219385125760⟩ : DyadicInterval 40),(⟨744036509165,744036528494⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,25465107⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25464768,25464832⟩ : DyadicInterval 40),(⟨-25465408,-25465344⟩ : DyadicInterval 40),(⟨762123383282,762123402611⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-640,0⟩ : DyadicInterval 40),(⟨762123383616,762123403200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨198631359005,198884106286⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182594428224,182594428288⟩ : DyadicInterval 40),(⟨-219076618432,-219076618368⟩ : DyadicInterval 40),(⟨744082704159,744082723488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182808481280,182808481344⟩ : DyadicInterval 40),(⟨-219385136192,-219385136128⟩ : DyadicInterval 40),(⟨744036507624,744036526954⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-36576654848,-36482190144⟩ : DyadicInterval 40),(⟨780364478688,780411730304⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨182615464704,182808474176⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-219385125824,-219106932096⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e791_ok : ecellOkT e791 = true := by decide +kernel
theorem e791_pos {a z : ℝ} (ha1 : ((185013/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((740901/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e791 e791_ok ha1 ha2 hz1 hz2 hz

-- box ['740901/4096000', '2967/16384', '3999/4000', '1']  interval_lower 69212645/549755813888
noncomputable def e792 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1298395725561,0,true,182808474112,182808474176⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨900627529991,0,false,-219385125824,-219385125760⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1298623627264,0,true,183001449600,183001449664⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨900399628288,0,false,-219663389888,-219663389824⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1298346004536,0,true,182766368384,182766368448⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨900677251016,0,false,-219324426688,-219324426624⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537123492,0,true,25495360,25495424⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486132060,0,false,-25496064,-25496000⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627184,0,false,-640,-576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1298370859990,0,true,182787417152,182787417216⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨900652395562,0,false,-219354769664,-219354769600⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1298623635762,0,true,183001456832,183001456896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨900399619790,0,false,-219663400256,-219663400192⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1063454172154,0,false,-36661943424,-36661943360⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1063545665037,0,false,-36567352448,-36567352384⟩
    { al := (740901/4096000), au := (2967/16384), zl := (3999/4000), zu := 1,
      A := ⟨198884097785,199111999488⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182808474112,182808474176⟩ : DyadicInterval 40),(⟨-219385125824,-219385125760⟩ : DyadicInterval 40),(⟨744036509165,744036528495⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183001449600,183001449664⟩ : DyadicInterval 40),(⟨-219663389888,-219663389824⟩ : DyadicInterval 40),(⟨743994802341,743994821671⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182766368384,182766368448⟩ : DyadicInterval 40),(⟨-219324426688,-219324426624⟩ : DyadicInterval 40),(⟨744045601816,744045621145⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183001449600,183001449664⟩ : DyadicInterval 40),(⟨-219663389888,-219663389824⟩ : DyadicInterval 40),(⟨743994802341,743994821671⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,25495716⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25495360,25495424⟩ : DyadicInterval 40),(⟨-25496064,-25496000⟩ : DyadicInterval 40),(⟨762123383312,762123402641⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-640,0⟩ : DyadicInterval 40),(⟨762123383616,762123403200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨198859232214,199112007986⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182787417152,182787417216⟩ : DyadicInterval 40),(⟨-219354769664,-219354769600⟩ : DyadicInterval 40),(⟨744041056715,744041076045⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183001456832,183001456896⟩ : DyadicInterval 40),(⟨-219663400256,-219663400192⟩ : DyadicInterval 40),(⟨743994800760,743994820089⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-36661943424,-36567352384⟩ : DyadicInterval 40),(⟨780407059808,780454374592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨182808474112,183001449664⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-219663389888,-219385125760⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e792_ok : ecellOkT e792 = true := by decide +kernel
theorem e792_pos {a z : ℝ} (ha1 : ((740901/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((2967/16384 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e792 e792_ok ha1 ha2 hz1 hz2 hz

-- box ['2967/16384', '742599/4096000', '1999/2000', '3999/4000']  interval_lower 71112411/549755813888
noncomputable def e793 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1298623627264,0,true,183001449600,183001449664⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨900399628288,0,false,-219663389888,-219663389824⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1298851528967,0,true,183194391296,183194391360⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨900171726585,0,false,-219941724416,-219941724352⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1298524071264,0,true,182917154816,182917154880⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨900499184288,0,false,-219541825088,-219541825024⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1298801693992,0,true,183152203840,183152203904⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨900221561560,0,false,-219880855360,-219880855296⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537122664,0,true,25494592,25494656⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486132888,0,false,-25495232,-25495168⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099562679867,0,true,51050880,51050944⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099460575685,0,false,-51053312,-51053248⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625405,0,false,-2432,-2368⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627185,0,false,-640,-576⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1298573844420,0,true,182959298944,182959299008⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨900449411132,0,false,-219602599872,-219602599808⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1298826620053,0,true,183173305024,183173305088⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨900196635499,0,false,-219911299904,-219911299840⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1063380617295,0,false,-36737994880,-36737994816⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1063472203459,0,false,-36643300928,-36643300864⟩
    { al := (2967/16384), au := (742599/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨199111999488,199339901191⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183001449600,183001449664⟩ : DyadicInterval 40),(⟨-219663389888,-219663389824⟩ : DyadicInterval 40),(⟨743994802341,743994821671⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183194391296,183194391360⟩ : DyadicInterval 40),(⟨-219941724416,-219941724352⟩ : DyadicInterval 40),(⟨743953046645,743953065975⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182917154816,182917154880⟩ : DyadicInterval 40),(⟨-219541825088,-219541825024⟩ : DyadicInterval 40),(⟨744013027480,744013046810⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183152203840,183152203904⟩ : DyadicInterval 40),(⟨-219880855360,-219880855296⟩ : DyadicInterval 40),(⟨743962181511,743962200840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨25494888,51052091⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25494592,25494656⟩ : DyadicInterval 40),(⟨-25495232,-25495168⟩ : DyadicInterval 40),(⟨762123383280,762123402609⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨51050880,51050944⟩ : DyadicInterval 40),(⟨-51053312,-51053248⟩ : DyadicInterval 40),(⟨762123382397,762123401726⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2432,-576⟩ : DyadicInterval 40),(⟨762123383904,762123404096⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨199062216644,199314992277⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182959298944,182959299008⟩ : DyadicInterval 40),(⟨-219602599872,-219602599808⟩ : DyadicInterval 40),(⟨744003916937,744003936266⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183173305024,183173305088⟩ : DyadicInterval 40),(⟨-219911299904,-219911299840⟩ : DyadicInterval 40),(⟨743957612786,743957632116⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-36737994880,-36643300864⟩ : DyadicInterval 40),(⟨780445034048,780492400320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨183001449600,183194391360⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-219941724416,-219663389824⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e793_ok : ecellOkT e793 = true := by decide +kernel
theorem e793_pos {a z : ℝ} (ha1 : ((2967/16384 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((742599/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e793 e793_ok ha1 ha2 hz1 hz2 hz

-- box ['742599/4096000', '92931/512000', '1999/2000', '3999/4000']  interval_lower 72714235/549755813888
noncomputable def e794 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1298851528966,0,true,183194391296,183194391360⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨900171726586,0,false,-219941724416,-219941724352⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1299079430669,0,true,183387299072,183387299136⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨899943824883,0,false,-220220129408,-220220129344⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1298751859015,0,true,183110014848,183110014912⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨900271396537,0,false,-219819989632,-219819989568⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1299029538719,0,true,183345070848,183345070912⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨899993716833,0,false,-220159175296,-220159175232⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537153278,0,true,25525184,25525248⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486102274,0,false,-25525824,-25525760⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099562741104,0,true,51112128,51112192⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099460514448,0,false,-51114560,-51114496⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625399,0,false,-2432,-2368⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627184,0,false,-640,-576⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1298801689150,0,true,183152199744,183152199808⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨900221566402,0,false,-219880849408,-219880849344⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1299054493270,0,true,183366192384,183366192448⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨899968762282,0,false,-220189662400,-220189662336⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1063297954210,0,false,-36823469952,-36823469888⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1063389655476,0,false,-36728649600,-36728649536⟩
    { al := (742599/4096000), au := (92931/512000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨199339901190,199567802893⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183194391296,183194391360⟩ : DyadicInterval 40),(⟨-219941724416,-219941724352⟩ : DyadicInterval 40),(⟨743953046645,743953065975⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183387299072,183387299136⟩ : DyadicInterval 40),(⟨-220220129408,-220220129344⟩ : DyadicInterval 40),(⟨743911242141,743911261470⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183110014848,183110014912⟩ : DyadicInterval 40),(⟨-219819989632,-219819989568⟩ : DyadicInterval 40),(⟨743971313975,743971333304⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183345070848,183345070912⟩ : DyadicInterval 40),(⟨-220159175296,-220159175232⟩ : DyadicInterval 40),(⟨743920398094,743920417424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨25525502,51113328⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25525184,25525248⟩ : DyadicInterval 40),(⟨-25525824,-25525760⟩ : DyadicInterval 40),(⟨762123383279,762123402608⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨51112128,51112192⟩ : DyadicInterval 40),(⟨-51114560,-51114496⟩ : DyadicInterval 40),(⟨762123382391,762123401720⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2432,-576⟩ : DyadicInterval 40),(⟨762123383904,762123404096⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨199290061374,199542865494⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183152199744,183152199808⟩ : DyadicInterval 40),(⟨-219880849408,-219880849344⟩ : DyadicInterval 40),(⟨743962182381,743962201710⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183366192384,183366192448⟩ : DyadicInterval 40),(⟨-220189662400,-220189662336⟩ : DyadicInterval 40),(⟨743915818855,743915838185⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-36823469952,-36728649536⟩ : DyadicInterval 40),(⟨780487708384,780535137856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨183194391296,183387299136⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-220220129408,-219941724352⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e794_ok : ecellOkT e794 = true := by decide +kernel
theorem e794_pos {a z : ℝ} (ha1 : ((742599/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((92931/512000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e794 e794_ok ha1 ha2 hz1 hz2 hz

-- box ['2967/16384', '742599/4096000', '3999/4000', '1']  interval_lower 17701421/137438953472
noncomputable def e795 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1298623627264,0,true,183001449600,183001449664⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨900399628288,0,false,-219663389888,-219663389824⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1298851528967,0,true,183194391296,183194391360⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨900171726585,0,false,-219941724416,-219941724352⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1298573849264,0,true,182959303040,182959303104⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨900449406288,0,false,-219602605824,-219602605760⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537154106,0,true,25526016,25526080⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486101446,0,false,-25526656,-25526592⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627183,0,false,-640,-576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1298598733199,0,true,182980372224,182980372288⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨900424522353,0,false,-219632991232,-219632991168⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1298851537470,0,true,183194398464,183194398528⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨900171718082,0,false,-219941734784,-219941734720⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1063371582875,0,false,-36747336320,-36747336256⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1063463190866,0,false,-36652618944,-36652618880⟩
    { al := (2967/16384), au := (742599/4096000), zl := (3999/4000), zu := 1,
      A := ⟨199111999488,199339901191⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183001449600,183001449664⟩ : DyadicInterval 40),(⟨-219663389888,-219663389824⟩ : DyadicInterval 40),(⟨743994802341,743994821671⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183194391296,183194391360⟩ : DyadicInterval 40),(⟨-219941724416,-219941724352⟩ : DyadicInterval 40),(⟨743953046645,743953065975⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182959303040,182959303104⟩ : DyadicInterval 40),(⟨-219602605824,-219602605760⟩ : DyadicInterval 40),(⟨744003916068,744003935398⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183194391296,183194391360⟩ : DyadicInterval 40),(⟨-219941724416,-219941724352⟩ : DyadicInterval 40),(⟨743953046645,743953065975⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,25526330⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25526016,25526080⟩ : DyadicInterval 40),(⟨-25526656,-25526592⟩ : DyadicInterval 40),(⟨762123383279,762123402608⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-640,0⟩ : DyadicInterval 40),(⟨762123383616,762123403200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨199087105423,199339909694⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182980372224,182980372288⟩ : DyadicInterval 40),(⟨-219632991232,-219632991168⟩ : DyadicInterval 40),(⟨743999360421,743999379751⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183194398464,183194398528⟩ : DyadicInterval 40),(⟨-219941734784,-219941734720⟩ : DyadicInterval 40),(⟨743953045097,743953064426⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-36747336320,-36652618880⟩ : DyadicInterval 40),(⟨780449693056,780497071040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨183001449600,183194391360⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-219941724416,-219663389824⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e795_ok : ecellOkT e795 = true := by decide +kernel
theorem e795_pos {a z : ℝ} (ha1 : ((2967/16384 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((742599/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e795 e795_ok ha1 ha2 hz1 hz2 hz

-- box ['742599/4096000', '92931/512000', '3999/4000', '1']  interval_lower 72406529/549755813888
noncomputable def e796 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1298851528966,0,true,183194391296,183194391360⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨900171726586,0,false,-219941724416,-219941724352⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1299079430669,0,true,183387299072,183387299136⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨899943824883,0,false,-220220129408,-220220129344⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1298801693990,0,true,183152203840,183152203904⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨900221561562,0,false,-219880855296,-219880855232⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537184727,0,true,25556608,25556672⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486070825,0,false,-25557312,-25557248⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627181,0,false,-640,-576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1298826606413,0,true,183173293504,183173293568⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨900196649139,0,false,-219911283264,-219911283200⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1299079439168,0,true,183387306240,183387306304⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨899943816384,0,false,-220220139776,-220220139712⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1063288899122,0,false,-36832833472,-36832833408⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1063380622241,0,false,-36737989760,-36737989696⟩
    { al := (742599/4096000), au := (92931/512000), zl := (3999/4000), zu := 1,
      A := ⟨199339901190,199567802893⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183194391296,183194391360⟩ : DyadicInterval 40),(⟨-219941724416,-219941724352⟩ : DyadicInterval 40),(⟨743953046645,743953065975⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183387299072,183387299136⟩ : DyadicInterval 40),(⟨-220220129408,-220220129344⟩ : DyadicInterval 40),(⟨743911242141,743911261470⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183152203840,183152203904⟩ : DyadicInterval 40),(⟨-219880855296,-219880855232⟩ : DyadicInterval 40),(⟨743962181485,743962200814⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183387299072,183387299136⟩ : DyadicInterval 40),(⟨-220220129408,-220220129344⟩ : DyadicInterval 40),(⟨743911242141,743911261470⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,25556951⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25556608,25556672⟩ : DyadicInterval 40),(⟨-25557312,-25557248⟩ : DyadicInterval 40),(⟨762123383309,762123402638⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-640,0⟩ : DyadicInterval 40),(⟨762123383616,762123403200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨199314978637,199567811392⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183173293504,183173293568⟩ : DyadicInterval 40),(⟨-219911283264,-219911283200⟩ : DyadicInterval 40),(⟨743957615279,743957634609⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183387306240,183387306304⟩ : DyadicInterval 40),(⟨-220220139776,-220220139712⟩ : DyadicInterval 40),(⟨743911240590,743911259919⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-36832833472,-36737989696⟩ : DyadicInterval 40),(⟨780492378464,780539819616⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨183194391296,183387299136⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-220220129408,-219941724352⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e796_ok : ecellOkT e796 = true := by decide +kernel
theorem e796_pos {a z : ℝ} (ha1 : ((742599/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((92931/512000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e796 e796_ok ha1 ha2 hz1 hz2 hz

-- box ['92931/512000', '744297/4096000', '999/1000', '3997/4000']  interval_lower 149882277/1099511627776
noncomputable def e797 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1299079430668,0,true,183387299072,183387299136⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨899943824884,0,false,-220220129408,-220220129344⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1299307332371,0,true,183580173056,183580173120⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨899715923181,0,false,-220498604864,-220498604800⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1298879862865,0,true,183218376384,183218376448⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨900143392687,0,false,-219976333312,-219976333248⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1299157485593,0,true,183453361024,183453361088⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨899865769959,0,false,-220315497600,-220315497536⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588295709,0,true,76665216,76665280⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434959843,0,false,-76670656,-76670592⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099613975410,0,true,102342848,102342912⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099409280142,0,false,-102352448,-102352384⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511618249,0,false,-9536,-9472⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622431,0,false,-5376,-5312⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1298979642815,0,true,183302837632,183302837696⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨900043612737,0,false,-220098219776,-220098219712⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1299232418162,0,true,183516776640,183516776704⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨899790837390,0,false,-220407058624,-220407058560⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1063233344668,0,false,-36890281984,-36890281920⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1063325117313,0,false,-36795382080,-36795382016⟩
    { al := (92931/512000), au := (744297/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨199567802892,199795704595⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183387299072,183387299136⟩ : DyadicInterval 40),(⟨-220220129408,-220220129344⟩ : DyadicInterval 40),(⟨743911242141,743911261471⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183580173056,183580173120⟩ : DyadicInterval 40),(⟨-220498604864,-220498604800⟩ : DyadicInterval 40),(⟨743869388741,743869408071⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183218376384,183218376448⟩ : DyadicInterval 40),(⟨-219976333312,-219976333248⟩ : DyadicInterval 40),(⟨743947851977,743947871307⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183453361024,183453361088⟩ : DyadicInterval 40),(⟨-220315497600,-220315497536⟩ : DyadicInterval 40),(⟨743896913118,743896932447⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨76667933,102347634⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76665216,76665280⟩ : DyadicInterval 40),(⟨-76670656,-76670592⟩ : DyadicInterval 40),(⟨762123380925,762123400255⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨102342848,102342912⟩ : DyadicInterval 40),(⟨-102352448,-102352384⟩ : DyadicInterval 40),(⟨762123378824,762123398154⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-9536,-5312⟩ : DyadicInterval 40),(⟨762123386272,762123407648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨199468015039,199720790386⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183302837632,183302837696⟩ : DyadicInterval 40),(⟨-220098219776,-220098219712⟩ : DyadicInterval 40),(⟨743929552463,743929571793⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183516776640,183516776704⟩ : DyadicInterval 40),(⟨-220407058624,-220407058560⟩ : DyadicInterval 40),(⟨743883151875,743883171205⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-36890281984,-36795382016⟩ : DyadicInterval 40),(⟨780521074624,780568543872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨183387299072,183580173120⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-220498604864,-220220129344⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e797_ok : ecellOkT e797 = true := by decide +kernel
theorem e797_pos {a z : ℝ} (ha1 : ((92931/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((744297/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e797 e797_ok ha1 ha2 hz1 hz2 hz

-- box ['744297/4096000', '372573/2048000', '999/1000', '3997/4000']  interval_lower 76560407/549755813888
noncomputable def e798 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1299307332370,0,true,183580172992,183580173056⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨899715923182,0,false,-220498604864,-220498604800⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1299535234073,0,true,183773013184,183773013248⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨899488021479,0,false,-220777150912,-220777150848⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1299107536665,0,true,183411087104,183411087168⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨899915718887,0,false,-220254468608,-220254468544⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1299385216369,0,true,183646078720,183646078784⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨899638039183,0,false,-220593788352,-220593788288⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588387577,0,true,76757120,76757184⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434867975,0,false,-76762496,-76762432⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099614097922,0,true,102465344,102465408⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099409157630,0,false,-102474944,-102474880⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511618226,0,false,-9600,-9536⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622418,0,false,-5376,-5312⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1299207430566,0,true,183495629952,183495630016⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨899815824986,0,false,-220376525120,-220376525056⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1299460234399,0,true,183709555520,183709555584⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨899563021153,0,false,-220685477056,-220685476992⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1063150534104,0,false,-36975921472,-36975921408⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1063242421845,0,false,-36880895104,-36880895040⟩
    { al := (744297/4096000), au := (372573/2048000), zl := (999/1000), zu := (3997/4000),
      A := ⟨199795704594,200023606297⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183580172992,183580173056⟩ : DyadicInterval 40),(⟨-220498604864,-220498604800⟩ : DyadicInterval 40),(⟨743869388779,743869408108⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183773013184,183773013248⟩ : DyadicInterval 40),(⟨-220777150912,-220777150848⟩ : DyadicInterval 40),(⟨743827486525,743827505854⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183411087104,183411087168⟩ : DyadicInterval 40),(⟨-220254468608,-220254468544⟩ : DyadicInterval 40),(⟨743906083207,743906102537⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183646078720,183646078784⟩ : DyadicInterval 40),(⟨-220593788352,-220593788288⟩ : DyadicInterval 40),(⟨743855074463,743855093793⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨76759801,102470146⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76757120,76757184⟩ : DyadicInterval 40),(⟨-76762496,-76762432⟩ : DyadicInterval 40),(⟨762123380881,762123400210⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨102465344,102465408⟩ : DyadicInterval 40),(⟨-102474944,-102474880⟩ : DyadicInterval 40),(⟨762123378801,762123398131⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-9600,-5312⟩ : DyadicInterval 40),(⟨762123386272,762123407680⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨199695802790,199948606623⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183495629952,183495630016⟩ : DyadicInterval 40),(⟨-220376525120,-220376525056⟩ : DyadicInterval 40),(⟨743887741409,743887760738⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183709555520,183709555584⟩ : DyadicInterval 40),(⟨-220685477056,-220685476992⟩ : DyadicInterval 40),(⟨743841281481,743841300811⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-36975921472,-36880895040⟩ : DyadicInterval 40),(⟨780563831136,780611363616⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨183580172992,183773013248⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-220777150912,-220498604800⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e798_ok : ecellOkT e798 = true := by decide +kernel
theorem e798_pos {a z : ℝ} (ha1 : ((744297/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((372573/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e798 e798_ok ha1 ha2 hz1 hz2 hz

-- box ['92931/512000', '744297/4096000', '3997/4000', '1999/2000']  interval_lower 149265237/1099511627776
noncomputable def e799 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1299079430668,0,true,183387299072,183387299136⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨899943824884,0,false,-220220129408,-220220129344⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1299307332371,0,true,183580173056,183580173120⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨899715923181,0,false,-220498604864,-220498604800⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1298929754815,0,true,183260609472,183260609536⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨900093500737,0,false,-220037277248,-220037277184⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1299207434519,0,true,183495633280,183495633344⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨899815821033,0,false,-220376529984,-220376529920⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099562739960,0,true,51110976,51111040⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099460515592,0,false,-51113408,-51113344⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588389039,0,true,76758528,76758592⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434866513,0,false,-76763968,-76763904⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622416,0,false,-5376,-5312⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625400,0,false,-2432,-2368⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1299004588266,0,true,183323952320,183323952384⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨900018667286,0,false,-220128694016,-220128693952⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1299257392246,0,true,183537911424,183537911488⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨899765863306,0,false,-220437576512,-220437576448⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1063224271266,0,false,-36899665024,-36899664960⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1063316065784,0,false,-36804741696,-36804741632⟩
    { al := (92931/512000), au := (744297/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨199567802892,199795704595⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183387299072,183387299136⟩ : DyadicInterval 40),(⟨-220220129408,-220220129344⟩ : DyadicInterval 40),(⟨743911242141,743911261471⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183580173056,183580173120⟩ : DyadicInterval 40),(⟨-220498604864,-220498604800⟩ : DyadicInterval 40),(⟨743869388741,743869408071⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183260609472,183260609536⟩ : DyadicInterval 40),(⟨-220037277248,-220037277184⟩ : DyadicInterval 40),(⟨743938703031,743938722361⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183495633280,183495633344⟩ : DyadicInterval 40),(⟨-220376529984,-220376529920⟩ : DyadicInterval 40),(⟨743887740707,743887760036⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨51112184,76761263⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨51110976,51111040⟩ : DyadicInterval 40),(⟨-51113408,-51113344⟩ : DyadicInterval 40),(⟨762123382391,762123401721⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76758528,76758592⟩ : DyadicInterval 40),(⟨-76763968,-76763904⟩ : DyadicInterval 40),(⟨762123380912,762123400242⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5376,-2368⟩ : DyadicInterval 40),(⟨762123384800,762123405568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨199492960490,199745764470⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183323952320,183323952384⟩ : DyadicInterval 40),(⟨-220128694016,-220128693952⟩ : DyadicInterval 40),(⟨743924976017,743924995346⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183537911424,183537911488⟩ : DyadicInterval 40),(⟨-220437576512,-220437576448⟩ : DyadicInterval 40),(⟨743878564294,743878583624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-36899665024,-36804741632⟩ : DyadicInterval 40),(⟨780525754432,780573235392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨183387299072,183580173120⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-220498604864,-220220129344⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e799_ok : ecellOkT e799 = true := by decide +kernel
theorem e799_pos {a z : ℝ} (ha1 : ((92931/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((744297/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e799 e799_ok ha1 ha2 hz1 hz2 hz

-- box ['744297/4096000', '372573/2048000', '3997/4000', '1999/2000']  interval_lower 4765669/34359738368
noncomputable def e800 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1299307332370,0,true,183580172992,183580173056⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨899715923182,0,false,-220498604864,-220498604800⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1299535234073,0,true,183773013184,183773013248⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨899488021479,0,false,-220777150912,-220777150848⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1299157485591,0,true,183453361024,183453361088⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨899865769961,0,false,-220315497600,-220315497536⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1299435222271,0,true,183688391872,183688391936⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨899588033281,0,false,-220654905792,-220654905728⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099562801206,0,true,51172224,51172288⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099460454346,0,false,-51174656,-51174592⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588480926,0,true,76850432,76850496⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434774626,0,false,-76855872,-76855808⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622404,0,false,-5376,-5312⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625395,0,false,-2432,-2368⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1299232404503,0,true,183516765056,183516765120⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨899790851049,0,false,-220407041920,-220407041856⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1299485236980,0,true,183730710784,183730710848⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨899538018572,0,false,-220716037440,-220716037376⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1063141439987,0,false,-36985326656,-36985326592⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1063233349631,0,false,-36890276864,-36890276800⟩
    { al := (744297/4096000), au := (372573/2048000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨199795704594,200023606297⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183580172992,183580173056⟩ : DyadicInterval 40),(⟨-220498604864,-220498604800⟩ : DyadicInterval 40),(⟨743869388779,743869408108⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183773013184,183773013248⟩ : DyadicInterval 40),(⟨-220777150912,-220777150848⟩ : DyadicInterval 40),(⟨743827486525,743827505854⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183453361024,183453361088⟩ : DyadicInterval 40),(⟨-220315497600,-220315497536⟩ : DyadicInterval 40),(⟨743896913118,743896932448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183688391872,183688391936⟩ : DyadicInterval 40),(⟨-220654905792,-220654905728⟩ : DyadicInterval 40),(⟨743845880808,743845900138⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨51173430,76853150⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨51172224,51172288⟩ : DyadicInterval 40),(⟨-51174656,-51174592⟩ : DyadicInterval 40),(⟨762123382386,762123401715⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76850432,76850496⟩ : DyadicInterval 40),(⟨-76855872,-76855808⟩ : DyadicInterval 40),(⟨762123380899,762123400229⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5376,-2368⟩ : DyadicInterval 40),(⟨762123384800,762123405568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨199720776727,199973609204⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183516765056,183516765120⟩ : DyadicInterval 40),(⟨-220407041920,-220407041856⟩ : DyadicInterval 40),(⟨743883154394,743883173723⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183730710784,183730710848⟩ : DyadicInterval 40),(⟨-220716037440,-220716037376⟩ : DyadicInterval 40),(⟨743836683237,743836702567⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-36985326656,-36890276800⟩ : DyadicInterval 40),(⟨780568522016,780616066208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨183580172992,183773013248⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-220777150912,-220498604800⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e800_ok : ecellOkT e800 = true := by decide +kernel
theorem e800_pos {a z : ℝ} (ha1 : ((744297/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((372573/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e800 e800_ok ha1 ha2 hz1 hz2 hz

-- box ['372573/2048000', '149199/819200', '999/1000', '3997/4000']  interval_lower 156374859/1099511627776
noncomputable def e801 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1299535234072,0,true,183773013184,183773013248⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨899488021480,0,false,-220777150912,-220777150848⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1299763135775,0,true,183965819456,183965819520⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨899260119777,0,false,-221055767552,-221055767488⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1299335210465,0,true,183603764032,183603764096⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨899688045087,0,false,-220532674240,-220532674176⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1299612947145,0,true,183838762688,183838762752⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨899410308407,0,false,-220872149568,-220872149504⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588479459,0,true,76848960,76849024⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434776093,0,false,-76854400,-76854336⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099614220456,0,true,102587840,102587904⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099409035096,0,false,-102597504,-102597440⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511618203,0,false,-9600,-9536⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622405,0,false,-5376,-5312⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1299435218322,0,true,183688388480,183688388544⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨899588037230,0,false,-220654900992,-220654900928⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1299688050637,0,true,183902300672,183902300736⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨899335204915,0,false,-220963965952,-220963965888⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1063067629134,0,false,-37061665216,-37061665152⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1063159631993,0,false,-36966512448,-36966512384⟩
    { al := (372573/2048000), au := (149199/819200), zl := (999/1000), zu := (3997/4000),
      A := ⟨200023606296,200251507999⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183773013184,183773013248⟩ : DyadicInterval 40),(⟨-220777150912,-220777150848⟩ : DyadicInterval 40),(⟨743827486525,743827505855⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183965819456,183965819520⟩ : DyadicInterval 40),(⟨-221055767552,-221055767488⟩ : DyadicInterval 40),(⟨743785535480,743785554809⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183603764032,183603764096⟩ : DyadicInterval 40),(⟨-220532674240,-220532674176⟩ : DyadicInterval 40),(⟨743864265684,743864285014⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183838762688,183838762752⟩ : DyadicInterval 40),(⟨-220872149568,-220872149504⟩ : DyadicInterval 40),(⟨743813187007,743813206336⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨76851683,102592680⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76848960,76849024⟩ : DyadicInterval 40),(⟨-76854400,-76854336⟩ : DyadicInterval 40),(⟨762123380900,762123400229⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨102587840,102587904⟩ : DyadicInterval 40),(⟨-102597504,-102597440⟩ : DyadicInterval 40),(⟨762123378810,762123398140⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-9600,-5312⟩ : DyadicInterval 40),(⟨762123386272,762123407680⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨199923590546,200176422861⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183688388480,183688388544⟩ : DyadicInterval 40),(⟨-220654900992,-220654900928⟩ : DyadicInterval 40),(⟨743845881575,743845900904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183902300672,183902300736⟩ : DyadicInterval 40),(⟨-220963965952,-220963965888⟩ : DyadicInterval 40),(⟨743799362208,743799381537⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-37061665216,-36966512384⟩ : DyadicInterval 40),(⟨780606639808,780654235488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨183773013184,183965819520⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-221055767552,-220777150848⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e801_ok : ecellOkT e801 = true := by decide +kernel
theorem e801_pos {a z : ℝ} (ha1 : ((372573/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((149199/819200 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e801 e801_ok ha1 ha2 hz1 hz2 hz

-- box ['149199/819200', '186711/1024000', '999/1000', '3997/4000']  interval_lower 19955489/137438953472
noncomputable def e802 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1299763135774,0,true,183965819456,183965819520⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨899260119778,0,false,-221055767552,-221055767488⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1299991037477,0,true,184158592000,184158592064⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨899032218075,0,false,-221334454784,-221334454720⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1299562884265,0,true,183796407232,183796407296⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨899460371287,0,false,-220810950336,-220810950272⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1299840677920,0,true,184031412928,184031412992⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨899182577632,0,false,-221150581248,-221150581184⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588571357,0,true,76940864,76940928⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434684195,0,false,-76946304,-76946240⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099614343009,0,true,102710400,102710464⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099408912543,0,false,-102720064,-102720000⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511618180,0,false,-9600,-9536⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622392,0,false,-5440,-5376⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1299663006070,0,true,183881113280,183881113344⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨899360249482,0,false,-220933347328,-220933347264⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1299915866886,0,true,184095012032,184095012096⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨899107388666,0,false,-221242525440,-221242525376⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1062984629753,0,false,-37147513344,-37147513280⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1063076747762,0,false,-37052234048,-37052233984⟩
    { al := (149199/819200), au := (186711/1024000), zl := (999/1000), zu := (3997/4000),
      A := ⟨200251507998,200479409701⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183965819456,183965819520⟩ : DyadicInterval 40),(⟨-221055767552,-221055767488⟩ : DyadicInterval 40),(⟨743785535480,743785554810⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184158592000,184158592064⟩ : DyadicInterval 40),(⟨-221334454784,-221334454720⟩ : DyadicInterval 40),(⟨743743535520,743743554850⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183796407232,183796407296⟩ : DyadicInterval 40),(⟨-220810950336,-220810950272⟩ : DyadicInterval 40),(⟨743822399410,743822418739⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184031412928,184031412992⟩ : DyadicInterval 40),(⟨-221150581248,-221150581184⟩ : DyadicInterval 40),(⟨743771250737,743771270066⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨76943581,102715233⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76940864,76940928⟩ : DyadicInterval 40),(⟨-76946304,-76946240⟩ : DyadicInterval 40),(⟨762123380887,762123400216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨102710400,102710464⟩ : DyadicInterval 40),(⟨-102720064,-102720000⟩ : DyadicInterval 40),(⟨762123378788,762123398117⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-9600,-5376⟩ : DyadicInterval 40),(⟨762123386304,762123407680⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨200151378294,200404239110⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183881113280,183881113344⟩ : DyadicInterval 40),(⟨-220933347328,-220933347264⟩ : DyadicInterval 40),(⟨743803972890,743803992219⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184095012032,184095012096⟩ : DyadicInterval 40),(⟨-221242525440,-221242525376⟩ : DyadicInterval 40),(⟨743757394132,743757413461⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-37147513344,-37052233984⟩ : DyadicInterval 40),(⟨780649500608,780697159552⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨183965819456,184158592064⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-221334454784,-221055767488⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e802_ok : ecellOkT e802 = true := by decide +kernel
theorem e802_pos {a z : ℝ} (ha1 : ((149199/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((186711/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e802 e802_ok ha1 ha2 hz1 hz2 hz

-- box ['372573/2048000', '149199/819200', '3997/4000', '1999/2000']  interval_lower 77876265/549755813888
noncomputable def e803 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1299535234072,0,true,183773013184,183773013248⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨899488021480,0,false,-220777150912,-220777150848⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1299763135775,0,true,183965819456,183965819520⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨899260119777,0,false,-221055767552,-221055767488⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1299385216367,0,true,183646078720,183646078784⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨899638039185,0,false,-220593788352,-220593788288⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1299663010022,0,true,183881116608,183881116672⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨899360245530,0,false,-220933352128,-220933352064⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099562862462,0,true,51233472,51233536⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099460393090,0,false,-51235904,-51235840⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588572827,0,true,76942336,76942400⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434682725,0,false,-76947776,-76947712⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622391,0,false,-5440,-5376⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625389,0,false,-2432,-2368⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1299460220741,0,true,183709544000,183709544064⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨899563034811,0,false,-220685460352,-220685460288⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1299713081703,0,true,183923476288,183923476352⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨899310173849,0,false,-220994568896,-220994568832⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1063058514282,0,false,-37071092608,-37071092544⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1063150539072,0,false,-36975916288,-36975916224⟩
    { al := (372573/2048000), au := (149199/819200), zl := (3997/4000), zu := (1999/2000),
      A := ⟨200023606296,200251507999⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183773013184,183773013248⟩ : DyadicInterval 40),(⟨-220777150912,-220777150848⟩ : DyadicInterval 40),(⟨743827486525,743827505855⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183965819456,183965819520⟩ : DyadicInterval 40),(⟨-221055767552,-221055767488⟩ : DyadicInterval 40),(⟨743785535480,743785554809⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183646078720,183646078784⟩ : DyadicInterval 40),(⟨-220593788352,-220593788288⟩ : DyadicInterval 40),(⟨743855074464,743855093793⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183881116608,183881116672⟩ : DyadicInterval 40),(⟨-220933352128,-220933352064⟩ : DyadicInterval 40),(⟨743803972158,743803991488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨51234686,76945051⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨51233472,51233536⟩ : DyadicInterval 40),(⟨-51235904,-51235840⟩ : DyadicInterval 40),(⟨762123382380,762123401709⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76942336,76942400⟩ : DyadicInterval 40),(⟨-76947776,-76947712⟩ : DyadicInterval 40),(⟨762123380887,762123400216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5440,-2368⟩ : DyadicInterval 40),(⟨762123384800,762123405600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨199948592965,200201453927⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183709544000,183709544064⟩ : DyadicInterval 40),(⟨-220685460352,-220685460288⟩ : DyadicInterval 40),(⟨743841283967,743841303297⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183923476288,183923476352⟩ : DyadicInterval 40),(⟨-220994568896,-220994568832⟩ : DyadicInterval 40),(⟨743794753379,743794772709⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-37071092608,-36975916224⟩ : DyadicInterval 40),(⟨780611341728,780658949184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨183773013184,183965819520⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-221055767552,-220777150848⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e803_ok : ecellOkT e803 = true := by decide +kernel
theorem e803_pos {a z : ℝ} (ha1 : ((372573/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((149199/819200 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e803 e803_ok ha1 ha2 hz1 hz2 hz

-- box ['149199/819200', '186711/1024000', '3997/4000', '1999/2000']  interval_lower 159019129/1099511627776
noncomputable def e804 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1299763135774,0,true,183965819456,183965819520⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨899260119778,0,false,-221055767552,-221055767488⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1299991037477,0,true,184158592000,184158592064⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨899032218075,0,false,-221334454784,-221334454720⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1299612947142,0,true,183838762688,183838762752⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨899410308410,0,false,-220872149568,-220872149504⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1299890797773,0,true,184073807552,184073807616⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨899132457779,0,false,-221211868992,-221211868928⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099562923728,0,true,51294720,51294784⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099460331824,0,false,-51297152,-51297088⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588664744,0,true,77034240,77034304⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434590808,0,false,-77039680,-77039616⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622378,0,false,-5440,-5376⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625383,0,false,-2432,-2368⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1299688036973,0,true,183902289152,183902289216⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨899335218579,0,false,-220963949248,-220963949184⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1299940926432,0,true,184116208064,184116208128⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨899082329120,0,false,-221273171008,-221273170944⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1062975494146,0,false,-37156962880,-37156962816⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1063067634110,0,false,-37061660096,-37061660032⟩
    { al := (149199/819200), au := (186711/1024000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨200251507998,200479409701⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183965819456,183965819520⟩ : DyadicInterval 40),(⟨-221055767552,-221055767488⟩ : DyadicInterval 40),(⟨743785535480,743785554810⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184158592000,184158592064⟩ : DyadicInterval 40),(⟨-221334454784,-221334454720⟩ : DyadicInterval 40),(⟨743743535520,743743554850⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183838762688,183838762752⟩ : DyadicInterval 40),(⟨-220872149568,-220872149504⟩ : DyadicInterval 40),(⟨743813187007,743813206337⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184073807552,184073807616⟩ : DyadicInterval 40),(⟨-221211868992,-221211868928⟩ : DyadicInterval 40),(⟨743762014707,743762034037⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨51295952,77036968⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨51294720,51294784⟩ : DyadicInterval 40),(⟨-51297152,-51297088⟩ : DyadicInterval 40),(⟨762123382374,762123401703⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77034240,77034304⟩ : DyadicInterval 40),(⟨-77039680,-77039616⟩ : DyadicInterval 40),(⟨762123380874,762123400203⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5440,-2368⟩ : DyadicInterval 40),(⟨762123384800,762123405600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨200176409197,200429298656⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183902289152,183902289216⟩ : DyadicInterval 40),(⟨-220963949248,-220963949184⟩ : DyadicInterval 40),(⟨743799364701,743799384030⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184116208064,184116208128⟩ : DyadicInterval 40),(⟨-221273171008,-221273170944⟩ : DyadicInterval 40),(⟨743752774683,743752794012⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-37156962880,-37061660032⟩ : DyadicInterval 40),(⟨780654213632,780701884320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨183965819456,184158592064⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-221334454784,-221055767488⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e804_ok : ecellOkT e804 = true := by decide +kernel
theorem e804_pos {a z : ℝ} (ha1 : ((149199/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((186711/1024000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e804 e804_ok ha1 ha2 hz1 hz2 hz

-- box ['92931/512000', '744297/4096000', '1999/2000', '3999/4000']  interval_lower 148647331/1099511627776
noncomputable def e805 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1299079430668,0,true,183387299072,183387299136⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨899943824884,0,false,-220220129408,-220220129344⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1299307332371,0,true,183580173056,183580173120⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨899715923181,0,false,-220498604864,-220498604800⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1298979646766,0,true,183302840960,183302841024⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨900043608786,0,false,-220098224576,-220098224512⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1299257383446,0,true,183537904000,183537904064⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨899765872106,0,false,-220437565760,-220437565696⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537183896,0,true,25555776,25555840⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486071656,0,false,-25556480,-25556416⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099562802353,0,true,51173376,51173440⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099460453199,0,false,-51175808,-51175744⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625394,0,false,-2432,-2368⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627182,0,false,-640,-576⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1299029533869,0,true,183345066752,183345066816⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨899993721683,0,false,-220159169344,-220159169280⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1299282366488,0,true,183559045952,183559046016⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨899740889064,0,false,-220468095360,-220468095296⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1063215196672,0,false,-36909049344,-36909049280⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1063307013067,0,false,-36814102592,-36814102528⟩
    { al := (92931/512000), au := (744297/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨199567802892,199795704595⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183387299072,183387299136⟩ : DyadicInterval 40),(⟨-220220129408,-220220129344⟩ : DyadicInterval 40),(⟨743911242141,743911261471⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183580173056,183580173120⟩ : DyadicInterval 40),(⟨-220498604864,-220498604800⟩ : DyadicInterval 40),(⟨743869388741,743869408071⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183302840960,183302841024⟩ : DyadicInterval 40),(⟨-220098224576,-220098224512⟩ : DyadicInterval 40),(⟨743929551737,743929571067⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183537904000,183537904064⟩ : DyadicInterval 40),(⟨-220437565760,-220437565696⟩ : DyadicInterval 40),(⟨743878565898,743878585227⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨25556120,51174577⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25555776,25555840⟩ : DyadicInterval 40),(⟨-25556480,-25556416⟩ : DyadicInterval 40),(⟨762123383309,762123402639⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨51173376,51173440⟩ : DyadicInterval 40),(⟨-51175808,-51175744⟩ : DyadicInterval 40),(⟨762123382386,762123401715⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2432,-576⟩ : DyadicInterval 40),(⟨762123383904,762123404096⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨199517906093,199770738712⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183345066752,183345066816⟩ : DyadicInterval 40),(⟨-220159169344,-220159169280⟩ : DyadicInterval 40),(⟨743920398968,743920418297⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183559045952,183559046016⟩ : DyadicInterval 40),(⟨-220468095360,-220468095296⟩ : DyadicInterval 40),(⟨743873976055,743873995384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-36909049344,-36814102528⟩ : DyadicInterval 40),(⟨780530434880,780577927552⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨183387299072,183580173120⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-220498604864,-220220129344⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e805_ok : ecellOkT e805 = true := by decide +kernel
theorem e805_pos {a z : ℝ} (ha1 : ((92931/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((744297/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e805 e805_ok ha1 ha2 hz1 hz2 hz

-- box ['744297/4096000', '372573/2048000', '1999/2000', '3999/4000']  interval_lower 151880929/1099511627776
noncomputable def e806 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1299307332370,0,true,183580172992,183580173056⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨899715923182,0,false,-220498604864,-220498604800⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1299535234073,0,true,183773013184,183773013248⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨899488021479,0,false,-220777150912,-220777150848⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1299207434517,0,true,183495633280,183495633344⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨899815821035,0,false,-220376529984,-220376529920⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1299485228172,0,true,183730703296,183730703360⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨899538027380,0,false,-220716026688,-220716026624⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537214519,0,true,25586432,25586496⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486041033,0,false,-25587072,-25587008⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099562863612,0,true,51234624,51234688⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099460391940,0,false,-51237056,-51236992⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625388,0,false,-2432,-2368⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627181,0,false,-640,-576⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1299257378587,0,true,183537899840,183537899904⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨899765876965,0,false,-220437559808,-220437559744⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1299510239700,0,true,183751865728,183751865792⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨899513015852,0,false,-220746598848,-220746598784⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1063132344682,0,false,-36994733120,-36994733056⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1063224276230,0,false,-36899659904,-36899659840⟩
    { al := (744297/4096000), au := (372573/2048000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨199795704594,200023606297⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183580172992,183580173056⟩ : DyadicInterval 40),(⟨-220498604864,-220498604800⟩ : DyadicInterval 40),(⟨743869388779,743869408108⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183773013184,183773013248⟩ : DyadicInterval 40),(⟨-220777150912,-220777150848⟩ : DyadicInterval 40),(⟨743827486525,743827505854⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183495633280,183495633344⟩ : DyadicInterval 40),(⟨-220376529984,-220376529920⟩ : DyadicInterval 40),(⟨743887740707,743887760037⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183730703296,183730703360⟩ : DyadicInterval 40),(⟨-220716026688,-220716026624⟩ : DyadicInterval 40),(⟨743836684884,743836704214⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨25586743,51235836⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25586432,25586496⟩ : DyadicInterval 40),(⟨-25587072,-25587008⟩ : DyadicInterval 40),(⟨762123383276,762123402605⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨51234624,51234688⟩ : DyadicInterval 40),(⟨-51237056,-51236992⟩ : DyadicInterval 40),(⟨762123382380,762123401709⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2432,-576⟩ : DyadicInterval 40),(⟨762123383904,762123404096⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨199745750811,199998611924⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183537899840,183537899904⟩ : DyadicInterval 40),(⟨-220437559808,-220437559744⟩ : DyadicInterval 40),(⟨743878566813,743878586143⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183751865728,183751865792⟩ : DyadicInterval 40),(⟨-220746598848,-220746598784⟩ : DyadicInterval 40),(⟨743832084400,743832103729⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-36994733120,-36899659840⟩ : DyadicInterval 40),(⟨780573213536,780620769440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨183580172992,183773013248⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-220777150912,-220498604800⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e806_ok : ecellOkT e806 = true := by decide +kernel
theorem e806_pos {a z : ℝ} (ha1 : ((744297/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((372573/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e806 e806_ok ha1 ha2 hz1 hz2 hz

-- box ['92931/512000', '744297/4096000', '3999/4000', '1']  interval_lower 148029111/1099511627776
noncomputable def e807 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1299079430668,0,true,183387299072,183387299136⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨899943824884,0,false,-220220129408,-220220129344⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1299307332371,0,true,183580173056,183580173120⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨899715923181,0,false,-220498604864,-220498604800⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1299029538717,0,true,183345070848,183345070912⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨899993716835,0,false,-220159175296,-220159175232⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537215351,0,true,25587264,25587328⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486040201,0,false,-25587904,-25587840⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627180,0,false,-640,-576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1299054479621,0,true,183366180864,183366180928⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨899968775931,0,false,-220189645696,-220189645632⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1299307340879,0,true,183580180224,183580180288⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨899715914673,0,false,-220498615296,-220498615232⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1063206120889,0,false,-36918435008,-36918434944⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1063297959165,0,false,-36823464832,-36823464768⟩
    { al := (92931/512000), au := (744297/4096000), zl := (3999/4000), zu := 1,
      A := ⟨199567802892,199795704595⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183387299072,183387299136⟩ : DyadicInterval 40),(⟨-220220129408,-220220129344⟩ : DyadicInterval 40),(⟨743911242141,743911261471⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183580173056,183580173120⟩ : DyadicInterval 40),(⟨-220498604864,-220498604800⟩ : DyadicInterval 40),(⟨743869388741,743869408071⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183345070848,183345070912⟩ : DyadicInterval 40),(⟨-220159175296,-220159175232⟩ : DyadicInterval 40),(⟨743920398095,743920417424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183580173056,183580173120⟩ : DyadicInterval 40),(⟨-220498604864,-220498604800⟩ : DyadicInterval 40),(⟨743869388741,743869408071⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,25587575⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25587264,25587328⟩ : DyadicInterval 40),(⟨-25587904,-25587840⟩ : DyadicInterval 40),(⟨762123383276,762123402605⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-640,0⟩ : DyadicInterval 40),(⟨762123383616,762123403200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨199542851845,199795713103⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183366180864,183366180928⟩ : DyadicInterval 40),(⟨-220189645696,-220189645632⟩ : DyadicInterval 40),(⟨743915821329,743915840659⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183580180224,183580180288⟩ : DyadicInterval 40),(⟨-220498615296,-220498615232⟩ : DyadicInterval 40),(⟨743869387211,743869406540⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-36918435008,-36823464768⟩ : DyadicInterval 40),(⟨780535116000,780582620384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨183387299072,183580173120⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-220498604864,-220220129344⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e807_ok : ecellOkT e807 = true := by decide +kernel
theorem e807_pos {a z : ℝ} (ha1 : ((92931/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((744297/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e807 e807_ok ha1 ha2 hz1 hz2 hz

-- box ['744297/4096000', '372573/2048000', '3999/4000', '1']  interval_lower 75630291/549755813888
noncomputable def e808 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1299307332370,0,true,183580172992,183580173056⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨899715923182,0,false,-220498604864,-220498604800⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1299535234073,0,true,183773013184,183773013248⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨899488021479,0,false,-220777150912,-220777150848⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1299257383443,0,true,183537904000,183537904064⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨899765872109,0,false,-220437565696,-220437565632⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537245981,0,true,25617856,25617920⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486009571,0,false,-25618560,-25618496⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627179,0,false,-640,-576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1299282352831,0,true,183559034432,183559034496⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨899740902721,0,false,-220468078656,-220468078592⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1299535242580,0,true,183773020352,183773020416⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨899488012972,0,false,-220777161344,-220777161280⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1063123248182,0,false,-37004140928,-37004140864⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1063215201635,0,false,-36909044224,-36909044160⟩
    { al := (744297/4096000), au := (372573/2048000), zl := (3999/4000), zu := 1,
      A := ⟨199795704594,200023606297⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183580172992,183580173056⟩ : DyadicInterval 40),(⟨-220498604864,-220498604800⟩ : DyadicInterval 40),(⟨743869388779,743869408108⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183773013184,183773013248⟩ : DyadicInterval 40),(⟨-220777150912,-220777150848⟩ : DyadicInterval 40),(⟨743827486525,743827505854⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183537904000,183537904064⟩ : DyadicInterval 40),(⟨-220437565696,-220437565632⟩ : DyadicInterval 40),(⟨743878565872,743878585202⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183773013184,183773013248⟩ : DyadicInterval 40),(⟨-220777150912,-220777150848⟩ : DyadicInterval 40),(⟨743827486525,743827505854⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,25618205⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25617856,25617920⟩ : DyadicInterval 40),(⟨-25618560,-25618496⟩ : DyadicInterval 40),(⟨762123383307,762123402636⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-640,0⟩ : DyadicInterval 40),(⟨762123383616,762123403200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨199770725055,200023614804⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183559034432,183559034496⟩ : DyadicInterval 40),(⟨-220468078656,-220468078592⟩ : DyadicInterval 40),(⟨743873978536,743873997865⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183773020352,183773020416⟩ : DyadicInterval 40),(⟨-220777161344,-220777161280⟩ : DyadicInterval 40),(⟨743827484991,743827504320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-37004140928,-36909044160⟩ : DyadicInterval 40),(⟨780577905696,780625473344⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨183580172992,183773013248⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-220777150912,-220498604800⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e808_ok : ecellOkT e808 = true := by decide +kernel
theorem e808_pos {a z : ℝ} (ha1 : ((744297/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((372573/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e808 e808_ok ha1 ha2 hz1 hz2 hz

-- box ['372573/2048000', '149199/819200', '1999/2000', '3999/4000']  interval_lower 155129851/1099511627776
noncomputable def e809 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1299535234072,0,true,183773013184,183773013248⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨899488021480,0,false,-220777150912,-220777150848⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1299763135775,0,true,183965819456,183965819520⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨899260119777,0,false,-221055767552,-221055767488⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1299435222268,0,true,183688391872,183688391936⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨899588033284,0,false,-220654905792,-220654905728⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1299713072899,0,true,183923468864,183923468928⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨899310182653,0,false,-220994558144,-220994558080⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537245148,0,true,25617024,25617088⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486010404,0,false,-25617728,-25617664⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099562924881,0,true,51295872,51295936⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099460330671,0,false,-51298304,-51298240⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625382,0,false,-2432,-2368⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627180,0,false,-640,-576⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1299485223320,0,true,183730699200,183730699264⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨899538032232,0,false,-220716020736,-220716020672⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1299738112914,0,true,183944651648,183944651712⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨899285142638,0,false,-221025172928,-221025172864⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1063049398238,0,false,-37080521280,-37080521216⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1063141444957,0,false,-36985321472,-36985321408⟩
    { al := (372573/2048000), au := (149199/819200), zl := (1999/2000), zu := (3999/4000),
      A := ⟨200023606296,200251507999⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183773013184,183773013248⟩ : DyadicInterval 40),(⟨-220777150912,-220777150848⟩ : DyadicInterval 40),(⟨743827486525,743827505855⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183965819456,183965819520⟩ : DyadicInterval 40),(⟨-221055767552,-221055767488⟩ : DyadicInterval 40),(⟨743785535480,743785554809⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183688391872,183688391936⟩ : DyadicInterval 40),(⟨-220654905792,-220654905728⟩ : DyadicInterval 40),(⟨743845880809,743845900138⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183923468864,183923468928⟩ : DyadicInterval 40),(⟨-220994558144,-220994558080⟩ : DyadicInterval 40),(⟨743794754992,743794774321⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨25617372,51297105⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25617024,25617088⟩ : DyadicInterval 40),(⟨-25617728,-25617664⟩ : DyadicInterval 40),(⟨762123383307,762123402636⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨51295872,51295936⟩ : DyadicInterval 40),(⟨-51298304,-51298240⟩ : DyadicInterval 40),(⟨762123382374,762123401703⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2432,-576⟩ : DyadicInterval 40),(⟨762123383904,762123404096⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨199973595544,200226485138⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183730699200,183730699264⟩ : DyadicInterval 40),(⟨-220716020736,-220716020672⟩ : DyadicInterval 40),(⟨743836685762,743836705091⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183944651648,183944651712⟩ : DyadicInterval 40),(⟨-221025172928,-221025172864⟩ : DyadicInterval 40),(⟨743790143942,743790163272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-37080521280,-36985321408⟩ : DyadicInterval 40),(⟨780616044320,780663663520⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨183773013184,183965819520⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-221055767552,-220777150848⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e809_ok : ecellOkT e809 = true := by decide +kernel
theorem e809_pos {a z : ℝ} (ha1 : ((372573/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((149199/819200 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e809 e809_ok ha1 ha2 hz1 hz2 hz

-- box ['149199/819200', '186711/1024000', '1999/2000', '3999/4000']  interval_lower 158394105/1099511627776
noncomputable def e810 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1299763135774,0,true,183965819456,183965819520⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨899260119778,0,false,-221055767552,-221055767488⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1299991037477,0,true,184158592000,184158592064⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨899032218075,0,false,-221334454784,-221334454720⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1299663010019,0,true,183881116608,183881116672⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨899360245533,0,false,-220933352128,-220933352064⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1299940917625,0,true,184116200576,184116200640⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨899082337927,0,false,-221273160192,-221273160128⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537275783,0,true,25647680,25647744⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485979769,0,false,-25648320,-25648256⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099562986159,0,true,51357120,51357184⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099460269393,0,false,-51359616,-51359552⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625377,0,false,-2432,-2368⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627178,0,false,-640,-576⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1299713068037,0,true,183923464768,183923464832⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨899310187515,0,false,-220994552192,-220994552128⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1299965986130,0,true,184137403776,184137403840⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨899057269422,0,false,-221303817600,-221303817536⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1062966357341,0,false,-37166413760,-37166413696⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1063058519260,0,false,-37071087424,-37071087360⟩
    { al := (149199/819200), au := (186711/1024000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨200251507998,200479409701⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183965819456,183965819520⟩ : DyadicInterval 40),(⟨-221055767552,-221055767488⟩ : DyadicInterval 40),(⟨743785535480,743785554810⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184158592000,184158592064⟩ : DyadicInterval 40),(⟨-221334454784,-221334454720⟩ : DyadicInterval 40),(⟨743743535520,743743554850⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183881116608,183881116672⟩ : DyadicInterval 40),(⟨-220933352128,-220933352064⟩ : DyadicInterval 40),(⟨743803972159,743803991488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184116200576,184116200640⟩ : DyadicInterval 40),(⟨-221273160192,-221273160128⟩ : DyadicInterval 40),(⟨743752776311,743752795640⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨25648007,51358383⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25647680,25647744⟩ : DyadicInterval 40),(⟨-25648320,-25648256⟩ : DyadicInterval 40),(⟨762123383273,762123402602⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨51357120,51357184⟩ : DyadicInterval 40),(⟨-51359616,-51359552⟩ : DyadicInterval 40),(⟨762123382400,762123401730⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2432,-576⟩ : DyadicInterval 40),(⟨762123383904,762123404096⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨200201440261,200454358354⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183923464768,183923464832⟩ : DyadicInterval 40),(⟨-220994552192,-220994552128⟩ : DyadicInterval 40),(⟨743794755874,743794775203⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184137403776,184137403840⟩ : DyadicInterval 40),(⟨-221303817600,-221303817536⟩ : DyadicInterval 40),(⟨743748154632,743748173962⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-37166413760,-37071087360⟩ : DyadicInterval 40),(⟨780658927296,780706609760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨183965819456,184158592064⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-221334454784,-221055767488⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e810_ok : ecellOkT e810 = true := by decide +kernel
theorem e810_pos {a z : ℝ} (ha1 : ((149199/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((186711/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e810 e810_ok ha1 ha2 hz1 hz2 hz

-- box ['372573/2048000', '149199/819200', '3999/4000', '1']  interval_lower 154506875/1099511627776
noncomputable def e811 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1299535234072,0,true,183773013184,183773013248⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨899488021480,0,false,-220777150912,-220777150848⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1299763135775,0,true,183965819456,183965819520⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨899260119777,0,false,-221055767552,-221055767488⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1299485228170,0,true,183730703296,183730703360⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨899538027382,0,false,-220716026688,-220716026624⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537276616,0,true,25648512,25648576⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485978936,0,false,-25649152,-25649088⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627177,0,false,-640,-576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1299510226039,0,true,183751854144,183751854208⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨899513029513,0,false,-220746582144,-220746582080⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1299763144275,0,true,183965826688,183965826752⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨899260111277,0,false,-221055777984,-221055777920⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1063040281000,0,false,-37089951232,-37089951168⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1063132349653,0,false,-36994728000,-36994727936⟩
    { al := (372573/2048000), au := (149199/819200), zl := (3999/4000), zu := 1,
      A := ⟨200023606296,200251507999⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183773013184,183773013248⟩ : DyadicInterval 40),(⟨-220777150912,-220777150848⟩ : DyadicInterval 40),(⟨743827486525,743827505855⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183965819456,183965819520⟩ : DyadicInterval 40),(⟨-221055767552,-221055767488⟩ : DyadicInterval 40),(⟨743785535480,743785554809⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183730703296,183730703360⟩ : DyadicInterval 40),(⟨-220716026688,-220716026624⟩ : DyadicInterval 40),(⟨743836684884,743836704214⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183965819456,183965819520⟩ : DyadicInterval 40),(⟨-221055767552,-221055767488⟩ : DyadicInterval 40),(⟨743785535480,743785554809⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,25648840⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25648512,25648576⟩ : DyadicInterval 40),(⟨-25649152,-25649088⟩ : DyadicInterval 40),(⟨762123383273,762123402602⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-640,0⟩ : DyadicInterval 40),(⟨762123383616,762123403200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨199998598263,200251516499⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183751854144,183751854208⟩ : DyadicInterval 40),(⟨-220746582144,-220746582080⟩ : DyadicInterval 40),(⟨743832086925,743832106255⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183965826688,183965826752⟩ : DyadicInterval 40),(⟨-221055777984,-221055777920⟩ : DyadicInterval 40),(⟨743785533906,743785553236⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-37089951232,-36994727936⟩ : DyadicInterval 40),(⟨780620747584,780668378496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨183773013184,183965819520⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-221055767552,-220777150848⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e811_ok : ecellOkT e811 = true := by decide +kernel
theorem e811_pos {a z : ℝ} (ha1 : ((372573/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((149199/819200 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e811 e811_ok ha1 ha2 hz1 hz2 hz

-- box ['149199/819200', '186711/1024000', '3999/4000', '1']  interval_lower 78884091/549755813888
noncomputable def e812 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1299763135774,0,true,183965819456,183965819520⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨899260119778,0,false,-221055767552,-221055767488⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1299991037477,0,true,184158592000,184158592064⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨899032218075,0,false,-221334454784,-221334454720⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1299713072896,0,true,183923468864,183923468928⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨899310182656,0,false,-220994558144,-220994558080⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537307256,0,true,25679168,25679232⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485948296,0,false,-25679808,-25679744⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627176,0,false,-640,-576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1299738099249,0,true,183944640064,183944640128⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨899285156303,0,false,-221025156224,-221025156160⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1299991045984,0,true,184158599168,184158599232⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨899032209568,0,false,-221334465216,-221334465152⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1062957219337,0,false,-37175865984,-37175865920⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1063049403216,0,false,-37080516096,-37080516032⟩
    { al := (149199/819200), au := (186711/1024000), zl := (3999/4000), zu := 1,
      A := ⟨200251507998,200479409701⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183965819456,183965819520⟩ : DyadicInterval 40),(⟨-221055767552,-221055767488⟩ : DyadicInterval 40),(⟨743785535480,743785554810⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184158592000,184158592064⟩ : DyadicInterval 40),(⟨-221334454784,-221334454720⟩ : DyadicInterval 40),(⟨743743535520,743743554850⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183923468864,183923468928⟩ : DyadicInterval 40),(⟨-220994558144,-220994558080⟩ : DyadicInterval 40),(⟨743794754992,743794774321⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184158592000,184158592064⟩ : DyadicInterval 40),(⟨-221334454784,-221334454720⟩ : DyadicInterval 40),(⟨743743535520,743743554850⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,25679480⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25679168,25679232⟩ : DyadicInterval 40),(⟨-25679808,-25679744⟩ : DyadicInterval 40),(⟨762123383272,762123402601⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-640,0⟩ : DyadicInterval 40),(⟨762123383616,762123403200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨200226471473,200479418208⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183944640064,183944640128⟩ : DyadicInterval 40),(⟨-221025156224,-221025156160⟩ : DyadicInterval 40),(⟨743790146474,743790165803⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184158599168,184158599232⟩ : DyadicInterval 40),(⟨-221334465216,-221334465152⟩ : DyadicInterval 40),(⟨743743533979,743743553309⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-37175865984,-37080516032⟩ : DyadicInterval 40),(⟨780663641632,780711335872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨183965819456,184158592064⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-221334454784,-221055767488⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e812_ok : ecellOkT e812 = true := by decide +kernel
theorem e812_pos {a z : ℝ} (ha1 : ((149199/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((186711/1024000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e812 e812_ok ha1 ha2 hz1 hz2 hz

-- box ['186711/1024000', '747693/4096000', '999/1000', '3997/4000']  interval_lower 162927773/1099511627776
noncomputable def e813 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1299991037476,0,true,184158592000,184158592064⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨899032218076,0,false,-221334454784,-221334454720⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1300218939180,0,true,184351330688,184351330752⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨898804316372,0,false,-221613212736,-221613212672⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1299790558066,0,true,183989016640,183989016704⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨899232697486,0,false,-221089296896,-221089296832⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1300068408697,0,true,184224029376,184224029440⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨898954846855,0,false,-221429083456,-221429083392⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588663270,0,true,77032768,77032832⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434592282,0,false,-77038208,-77038144⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099614465583,0,true,102832960,102833024⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099408789969,0,false,-102842624,-102842560⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511618157,0,false,-9664,-9600⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622379,0,false,-5440,-5376⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1299890793821,0,true,184073804224,184073804288⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨899132461731,0,false,-221211864192,-221211864128⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1300143683124,0,true,184287689664,184287689728⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨898879572428,0,false,-221521155456,-221521155392⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1062901535971,0,false,-37233465792,-37233465728⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1062993769147,0,false,-37138059904,-37138059840⟩
    { al := (186711/1024000), au := (747693/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨200479409700,200707311404⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184158592000,184158592064⟩ : DyadicInterval 40),(⟨-221334454784,-221334454720⟩ : DyadicInterval 40),(⟨743743535520,743743554850⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184351330688,184351330752⟩ : DyadicInterval 40),(⟨-221613212736,-221613212672⟩ : DyadicInterval 40),(⟨743701486762,743701506091⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨183989016640,183989016704⟩ : DyadicInterval 40),(⟨-221089296896,-221089296832⟩ : DyadicInterval 40),(⟨743780484411,743780503741⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184224029376,184224029440⟩ : DyadicInterval 40),(⟨-221429083456,-221429083392⟩ : DyadicInterval 40),(⟨743729265706,743729285035⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨77035494,102837807⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77032768,77032832⟩ : DyadicInterval 40),(⟨-77038208,-77038144⟩ : DyadicInterval 40),(⟨762123380874,762123400203⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨102832960,102833024⟩ : DyadicInterval 40),(⟨-102842624,-102842560⟩ : DyadicInterval 40),(⟨762123378765,762123398094⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-9664,-5376⟩ : DyadicInterval 40),(⟨762123386304,762123407712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨200379166045,200632055348⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184073804224,184073804288⟩ : DyadicInterval 40),(⟨-221211864192,-221211864128⟩ : DyadicInterval 40),(⟨743762015440,743762034770⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184287689664,184287689728⟩ : DyadicInterval 40),(⟨-221521155456,-221521155392⟩ : DyadicInterval 40),(⟨743715377182,743715396511⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-37233465792,-37138059840⟩ : DyadicInterval 40),(⟨780692413536,780740135776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨184158592000,184351330752⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-221613212736,-221334454720⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e813_ok : ecellOkT e813 = true := by decide +kernel
theorem e813_pos {a z : ℝ} (ha1 : ((186711/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((747693/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e813 e813_ok ha1 ha2 hz1 hz2 hz

-- box ['747693/4096000', '374271/2048000', '999/1000', '3997/4000']  interval_lower 166227221/1099511627776
noncomputable def e814 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1300218939179,0,true,184351330688,184351330752⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨898804316373,0,false,-221613212736,-221613212672⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1300446840882,0,true,184544035648,184544035712⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨898576414670,0,false,-221892041344,-221892041280⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1300018231867,0,true,184181592320,184181592384⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨899005023685,0,false,-221367713920,-221367713856⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1300296139473,0,true,184416612096,184416612160⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨898727116079,0,false,-221707656256,-221707656192⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588755199,0,true,77124672,77124736⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434500353,0,false,-77130176,-77130112⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099614588179,0,true,102955520,102955584⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099408667373,0,false,-102965248,-102965184⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511618134,0,false,-9664,-9600⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622366,0,false,-5440,-5376⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1300118581566,0,true,184266461440,184266461504⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨898904673986,0,false,-221490451648,-221490451584⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1300371499366,0,true,184480333504,184480333568⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨898651756186,0,false,-221799856192,-221799856128⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1062818347781,0,false,-37319522624,-37319522560⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1062910696152,0,false,-37223990144,-37223990080⟩
    { al := (747693/4096000), au := (374271/2048000), zl := (999/1000), zu := (3997/4000),
      A := ⟨200707311403,200935213106⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184351330688,184351330752⟩ : DyadicInterval 40),(⟨-221613212736,-221613212672⟩ : DyadicInterval 40),(⟨743701486762,743701506092⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184544035648,184544035712⟩ : DyadicInterval 40),(⟨-221892041344,-221892041280⟩ : DyadicInterval 40),(⟨743659389091,743659408421⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184181592320,184181592384⟩ : DyadicInterval 40),(⟨-221367713920,-221367713856⟩ : DyadicInterval 40),(⟨743738520639,743738539968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184416612096,184416612160⟩ : DyadicInterval 40),(⟨-221707656256,-221707656192⟩ : DyadicInterval 40),(⟨743687231891,743687251221⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨77127423,102960403⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77124672,77124736⟩ : DyadicInterval 40),(⟨-77130176,-77130112⟩ : DyadicInterval 40),(⟨762123380893,762123400222⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨102955520,102955584⟩ : DyadicInterval 40),(⟨-102965248,-102965184⟩ : DyadicInterval 40),(⟨762123378774,762123398104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-9664,-5376⟩ : DyadicInterval 40),(⟨762123386304,762123407712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨200606953790,200859871590⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184266461440,184266461504⟩ : DyadicInterval 40),(⟨-221490451648,-221490451584⟩ : DyadicInterval 40),(⟨743720009168,743720028498⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184480333504,184480333568⟩ : DyadicInterval 40),(⟨-221799856192,-221799856128⟩ : DyadicInterval 40),(⟨743673311461,743673330790⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-37319522624,-37223990080⟩ : DyadicInterval 40),(⟨780735378656,780783164192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨184351330688,184544035712⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-221892041344,-221613212672⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e814_ok : ecellOkT e814 = true := by decide +kernel
theorem e814_pos {a z : ℝ} (ha1 : ((747693/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((374271/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e814 e814_ok ha1 ha2 hz1 hz2 hz

-- box ['186711/1024000', '747693/4096000', '3997/4000', '1999/2000']  interval_lower 162300953/1099511627776
noncomputable def e815 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1299991037476,0,true,184158592000,184158592064⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨899032218076,0,false,-221334454784,-221334454720⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1300218939180,0,true,184351330688,184351330752⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨898804316372,0,false,-221613212736,-221613212672⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1299840677918,0,true,184031412928,184031412992⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨899182577634,0,false,-221150581248,-221150581184⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1300118585525,0,true,184266464768,184266464832⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨898904670027,0,false,-221490456448,-221490456384⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099562985006,0,true,51355968,51356032⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099460270546,0,false,-51358464,-51358400⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588756676,0,true,77126144,77126208⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434498876,0,false,-77131648,-77131584⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622365,0,false,-5440,-5376⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625378,0,false,-2432,-2368⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1299915853216,0,true,184095000512,184095000576⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨899107402336,0,false,-221242508672,-221242508608⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1300168771156,0,true,184308905984,184308906048⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨898854484396,0,false,-221551843648,-221551843584⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1062892379582,0,false,-37242937600,-37242937536⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1062984634737,0,false,-37147508160,-37147508096⟩
    { al := (186711/1024000), au := (747693/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨200479409700,200707311404⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184158592000,184158592064⟩ : DyadicInterval 40),(⟨-221334454784,-221334454720⟩ : DyadicInterval 40),(⟨743743535520,743743554850⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184351330688,184351330752⟩ : DyadicInterval 40),(⟨-221613212736,-221613212672⟩ : DyadicInterval 40),(⟨743701486762,743701506091⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184031412928,184031412992⟩ : DyadicInterval 40),(⟨-221150581248,-221150581184⟩ : DyadicInterval 40),(⟨743771250737,743771270067⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184266464768,184266464832⟩ : DyadicInterval 40),(⟨-221490456448,-221490456384⟩ : DyadicInterval 40),(⟨743720008433,743720027762⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨51357230,77128900⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨51355968,51356032⟩ : DyadicInterval 40),(⟨-51358464,-51358400⟩ : DyadicInterval 40),(⟨762123382401,762123401730⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77126144,77126208⟩ : DyadicInterval 40),(⟨-77131648,-77131584⟩ : DyadicInterval 40),(⟨762123380893,762123400222⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5440,-2368⟩ : DyadicInterval 40),(⟨762123384800,762123405600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨200404225440,200657143380⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184095000512,184095000576⟩ : DyadicInterval 40),(⟨-221242508672,-221242508608⟩ : DyadicInterval 40),(⟨743757396605,743757415935⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184308905984,184308906048⟩ : DyadicInterval 40),(⟨-221551843648,-221551843584⟩ : DyadicInterval 40),(⟨743710747161,743710766491⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-37242937600,-37147508096⟩ : DyadicInterval 40),(⟨780697137664,780744871680⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨184158592000,184351330752⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-221613212736,-221334454720⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e815_ok : ecellOkT e815 = true := by decide +kernel
theorem e815_pos {a z : ℝ} (ha1 : ((186711/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((747693/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e815 e815_ok ha1 ha2 hz1 hz2 hz

-- box ['747693/4096000', '374271/2048000', '3997/4000', '1999/2000']  interval_lower 82798805/549755813888
noncomputable def e816 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1300218939179,0,true,184351330688,184351330752⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨898804316373,0,false,-221613212736,-221613212672⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1300446840882,0,true,184544035648,184544035712⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨898576414670,0,false,-221892041344,-221892041280⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1300068408695,0,true,184224029376,184224029440⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨898954846857,0,false,-221429083456,-221429083392⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1300346373276,0,true,184459088256,184459088320⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨898676882276,0,false,-221769114496,-221769114432⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099563046293,0,true,51417280,51417344⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099460209259,0,false,-51419776,-51419712⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588848623,0,true,77218112,77218176⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434406929,0,false,-77223616,-77223552⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622352,0,false,-5440,-5376⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625372,0,false,-2432,-2368⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1300143669449,0,true,184287678080,184287678144⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨898879586103,0,false,-221521138752,-221521138688⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1300396615886,0,true,184501570240,184501570304⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨898626639666,0,false,-221830586944,-221830586880⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1062809170586,0,false,-37329016704,-37329016640⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1062901540963,0,false,-37233460608,-37233460544⟩
    { al := (747693/4096000), au := (374271/2048000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨200707311403,200935213106⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184351330688,184351330752⟩ : DyadicInterval 40),(⟨-221613212736,-221613212672⟩ : DyadicInterval 40),(⟨743701486762,743701506092⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184544035648,184544035712⟩ : DyadicInterval 40),(⟨-221892041344,-221892041280⟩ : DyadicInterval 40),(⟨743659389091,743659408421⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184224029376,184224029440⟩ : DyadicInterval 40),(⟨-221429083456,-221429083392⟩ : DyadicInterval 40),(⟨743729265706,743729285036⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184459088256,184459088320⟩ : DyadicInterval 40),(⟨-221769114496,-221769114432⟩ : DyadicInterval 40),(⟨743677953323,743677972652⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨51418517,77220847⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨51417280,51417344⟩ : DyadicInterval 40),(⟨-51419776,-51419712⟩ : DyadicInterval 40),(⟨762123382395,762123401724⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77218112,77218176⟩ : DyadicInterval 40),(⟨-77223616,-77223552⟩ : DyadicInterval 40),(⟨762123380880,762123400209⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5440,-2368⟩ : DyadicInterval 40),(⟨762123384800,762123405600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨200632041673,200884988110⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184287678080,184287678144⟩ : DyadicInterval 40),(⟨-221521138752,-221521138688⟩ : DyadicInterval 40),(⟨743715379726,743715399056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184501570240,184501570304⟩ : DyadicInterval 40),(⟨-221830586944,-221830586880⟩ : DyadicInterval 40),(⟨743668670741,743668690070⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-37329016704,-37233460544⟩ : DyadicInterval 40),(⟨780740113888,780787911232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨184351330688,184544035712⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-221892041344,-221613212672⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e816_ok : ecellOkT e816 = true := by decide +kernel
theorem e816_pos {a z : ℝ} (ha1 : ((747693/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((374271/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e816 e816_ok ha1 ha2 hz1 hz2 hz

-- box ['374271/2048000', '749391/4096000', '999/1000', '3997/4000']  interval_lower 42385425/274877906944
noncomputable def e817 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1300446840881,0,true,184544035648,184544035712⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨898576414671,0,false,-221892041280,-221892041216⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1300674742584,0,true,184736706816,184736706880⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨898348512968,0,false,-222170940608,-222170940544⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1300245905667,0,true,184374134272,184374134336⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨898777349885,0,false,-221646201472,-221646201408⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1300523870249,0,true,184609161088,184609161152⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨898499385303,0,false,-221986299648,-221986299584⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588847143,0,true,77216640,77216704⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434408409,0,false,-77222080,-77222016⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099614710794,0,true,103078144,103078208⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099408544758,0,false,-103087872,-103087808⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511618111,0,false,-9728,-9664⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622353,0,false,-5440,-5376⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1300346369319,0,true,184459084928,184459084992⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨898676886233,0,false,-221769109696,-221769109632⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1300599315610,0,true,184672943552,184672943616⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨898423939942,0,false,-222078627520,-222078627456⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1062735065185,0,false,-37405683904,-37405683840⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1062827528771,0,false,-37310024704,-37310024640⟩
    { al := (374271/2048000), au := (749391/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨200935213105,201163114808⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184544035648,184544035712⟩ : DyadicInterval 40),(⟨-221892041280,-221892041216⟩ : DyadicInterval 40),(⟨743659389066,743659408395⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184736706816,184736706880⟩ : DyadicInterval 40),(⟨-222170940608,-222170940544⟩ : DyadicInterval 40),(⟨743617242535,743617261865⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184374134272,184374134336⟩ : DyadicInterval 40),(⟨-221646201472,-221646201408⟩ : DyadicInterval 40),(⟨743696508108,743696527437⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184609161088,184609161152⟩ : DyadicInterval 40),(⟨-221986299648,-221986299584⟩ : DyadicInterval 40),(⟨743645149281,743645168610⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨77219367,103083018⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77216640,77216704⟩ : DyadicInterval 40),(⟨-77222080,-77222016⟩ : DyadicInterval 40),(⟨762123380848,762123400178⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨103078144,103078208⟩ : DyadicInterval 40),(⟨-103087872,-103087808⟩ : DyadicInterval 40),(⟨762123378751,762123398081⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-9728,-5376⟩ : DyadicInterval 40),(⟨762123386304,762123407744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨200834741543,201087687834⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184459084928,184459084992⟩ : DyadicInterval 40),(⟨-221769109696,-221769109632⟩ : DyadicInterval 40),(⟨743677954060,743677973389⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184672943552,184672943616⟩ : DyadicInterval 40),(⟨-222078627520,-222078627456⟩ : DyadicInterval 40),(⟨743631196904,743631216234⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-37405683904,-37310024640⟩ : DyadicInterval 40),(⟨780778395936,780826244832⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨184544035648,184736706880⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-222170940608,-221892041216⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e817_ok : ecellOkT e817 = true := by decide +kernel
theorem e817_pos {a z : ℝ} (ha1 : ((374271/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((749391/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e817 e817_ok ha1 ha2 hz1 hz2 hz

-- box ['749391/4096000', '4689/25600', '999/1000', '3997/4000']  interval_lower 10804489/68719476736
noncomputable def e818 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1300674742583,0,true,184736706816,184736706880⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨898348512969,0,false,-222170940608,-222170940544⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1300902644286,0,true,184929344256,184929344320⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨898120611266,0,false,-222449910720,-222449910656⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1300473579468,0,true,184566642560,184566642624⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨898549676084,0,false,-221924759552,-221924759488⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1300751601024,0,true,184801676352,184801676416⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨898271654528,0,false,-222265013632,-222265013568⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588939103,0,true,77308608,77308672⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434316449,0,false,-77314048,-77313984⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099614833431,0,true,103200768,103200832⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099408422121,0,false,-103210560,-103210496⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511618088,0,false,-9728,-9664⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622340,0,false,-5440,-5376⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1300574157070,0,true,184651674624,184651674688⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨898449098482,0,false,-222047838336,-222047838272⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1300827131852,0,true,184865519936,184865520000⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨898196123700,0,false,-222357469568,-222357469504⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1062651688183,0,false,-37491949632,-37491949568⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1062744267009,0,false,-37396163712,-37396163648⟩
    { al := (749391/4096000), au := (4689/25600), zl := (999/1000), zu := (3997/4000),
      A := ⟨201163114807,201391016510⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184736706816,184736706880⟩ : DyadicInterval 40),(⟨-222170940608,-222170940544⟩ : DyadicInterval 40),(⟨743617242536,743617261865⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184929344256,184929344320⟩ : DyadicInterval 40),(⟨-222449910720,-222449910656⟩ : DyadicInterval 40),(⟨743575047123,743575066453⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184566642560,184566642624⟩ : DyadicInterval 40),(⟨-221924759552,-221924759488⟩ : DyadicInterval 40),(⟨743654446769,743654466098⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184801676352,184801676416⟩ : DyadicInterval 40),(⟨-222265013632,-222265013568⟩ : DyadicInterval 40),(⟨743603017864,743603037193⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨77311327,103205655⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77308608,77308672⟩ : DyadicInterval 40),(⟨-77314048,-77313984⟩ : DyadicInterval 40),(⟨762123380835,762123400165⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨103200768,103200832⟩ : DyadicInterval 40),(⟨-103210560,-103210496⟩ : DyadicInterval 40),(⟨762123378760,762123398090⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-9728,-5376⟩ : DyadicInterval 40),(⟨762123386304,762123407744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨201062529294,201315504076⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184651674624,184651674688⟩ : DyadicInterval 40),(⟨-222047838336,-222047838272⟩ : DyadicInterval 40),(⟨743635850143,743635869472⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184865519936,184865520000⟩ : DyadicInterval 40),(⟨-222357469568,-222357469504⟩ : DyadicInterval 40),(⟨743589033479,743589052809⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-37491949632,-37396163648⟩ : DyadicInterval 40),(⟨780821465440,780869377696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨184736706816,184929344320⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-222449910720,-222170940544⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e818_ok : ecellOkT e818 = true := by decide +kernel
theorem e818_pos {a z : ℝ} (ha1 : ((749391/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((4689/25600 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e818 e818_ok ha1 ha2 hz1 hz2 hz

-- box ['374271/2048000', '749391/4096000', '3997/4000', '1999/2000']  interval_lower 84454949/549755813888
noncomputable def e819 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1300446840881,0,true,184544035648,184544035712⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨898576414671,0,false,-221892041280,-221892041216⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1300674742584,0,true,184736706816,184736706880⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨898348512968,0,false,-222170940608,-222170940544⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1300296139471,0,true,184416612096,184416612160⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨898727116081,0,false,-221707656256,-221707656192⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1300574161027,0,true,184651677952,184651678016⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨898449094525,0,false,-222047843200,-222047843136⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099563107590,0,true,51478592,51478656⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099460147962,0,false,-51481024,-51480960⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588940588,0,true,77310080,77310144⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434314964,0,false,-77315584,-77315520⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622339,0,false,-5440,-5376⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625366,0,false,-2432,-2368⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1300371485689,0,true,184480321920,184480321984⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨898651769863,0,false,-221799839424,-221799839360⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1300624460615,0,true,184694200640,184694200704⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨898398794937,0,false,-222109400960,-222109400896⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1062725867161,0,false,-37415200256,-37415200192⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1062818352779,0,false,-37319517504,-37319517440⟩
    { al := (374271/2048000), au := (749391/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨200935213105,201163114808⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184544035648,184544035712⟩ : DyadicInterval 40),(⟨-221892041280,-221892041216⟩ : DyadicInterval 40),(⟨743659389066,743659408395⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184736706816,184736706880⟩ : DyadicInterval 40),(⟨-222170940608,-222170940544⟩ : DyadicInterval 40),(⟨743617242535,743617261865⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184416612096,184416612160⟩ : DyadicInterval 40),(⟨-221707656256,-221707656192⟩ : DyadicInterval 40),(⟨743687231892,743687251221⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184651677952,184651678016⟩ : DyadicInterval 40),(⟨-222047843200,-222047843136⟩ : DyadicInterval 40),(⟨743635849430,743635868760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨51479814,77312812⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨51478592,51478656⟩ : DyadicInterval 40),(⟨-51481024,-51480960⟩ : DyadicInterval 40),(⟨762123382357,762123401686⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77310080,77310144⟩ : DyadicInterval 40),(⟨-77315584,-77315520⟩ : DyadicInterval 40),(⟨762123380867,762123400196⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5440,-2368⟩ : DyadicInterval 40),(⟨762123384800,762123405600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨200859857913,201112832839⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184480321920,184480321984⟩ : DyadicInterval 40),(⟨-221799839424,-221799839360⟩ : DyadicInterval 40),(⟨743673313985,743673333315⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184694200640,184694200704⟩ : DyadicInterval 40),(⟨-222109400960,-222109400896⟩ : DyadicInterval 40),(⟨743626545550,743626564879⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-37415200256,-37319517440⟩ : DyadicInterval 40),(⟨780783142336,780831003008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨184544035648,184736706880⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-222170940608,-221892041216⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e819_ok : ecellOkT e819 = true := by decide +kernel
theorem e819_pos {a z : ℝ} (ha1 : ((374271/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((749391/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e819 e819_ok ha1 ha2 hz1 hz2 hz

-- box ['749391/4096000', '4689/25600', '3997/4000', '1999/2000']  interval_lower 43059269/274877906944
noncomputable def e820 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1300674742583,0,true,184736706816,184736706880⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨898348512969,0,false,-222170940608,-222170940544⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1300902644286,0,true,184929344256,184929344320⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨898120611266,0,false,-222449910720,-222449910656⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1300523870246,0,true,184609161088,184609161152⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨898499385306,0,false,-221986299648,-221986299584⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1300801948778,0,true,184844233984,184844234048⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨898221306774,0,false,-222326642560,-222326642496⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099563168898,0,true,51539904,51539968⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099460086654,0,false,-51542336,-51542272⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589032567,0,true,77402048,77402112⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434222985,0,false,-77407552,-77407488⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622326,0,false,-5504,-5440⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625360,0,false,-2432,-2368⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1300599301923,0,true,184672932032,184672932096⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨898423953629,0,false,-222078610752,-222078610688⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1300852305345,0,true,184886797376,184886797440⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨898170950207,0,false,-222388285696,-222388285632⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1062642469306,0,false,-37501488320,-37501488256⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1062735070192,0,false,-37405678720,-37405678656⟩
    { al := (749391/4096000), au := (4689/25600), zl := (3997/4000), zu := (1999/2000),
      A := ⟨201163114807,201391016510⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184736706816,184736706880⟩ : DyadicInterval 40),(⟨-222170940608,-222170940544⟩ : DyadicInterval 40),(⟨743617242536,743617261865⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184929344256,184929344320⟩ : DyadicInterval 40),(⟨-222449910720,-222449910656⟩ : DyadicInterval 40),(⟨743575047123,743575066453⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184609161088,184609161152⟩ : DyadicInterval 40),(⟨-221986299648,-221986299584⟩ : DyadicInterval 40),(⟨743645149282,743645168611⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184844233984,184844234048⟩ : DyadicInterval 40),(⟨-222326642560,-222326642496⟩ : DyadicInterval 40),(⟨743593696667,743593715997⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨51541122,77404791⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨51539904,51539968⟩ : DyadicInterval 40),(⟨-51542336,-51542272⟩ : DyadicInterval 40),(⟨762123382351,762123401680⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77402048,77402112⟩ : DyadicInterval 40),(⟨-77407552,-77407488⟩ : DyadicInterval 40),(⟨762123380854,762123400183⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5504,-2368⟩ : DyadicInterval 40),(⟨762123384800,762123405632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨201087674147,201340677569⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184672932032,184672932096⟩ : DyadicInterval 40),(⟨-222078610752,-222078610688⟩ : DyadicInterval 40),(⟨743631199399,743631218729⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184886797376,184886797440⟩ : DyadicInterval 40),(⟨-222388285696,-222388285632⟩ : DyadicInterval 40),(⟨743584371464,743584390793⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-37501488320,-37405678656⟩ : DyadicInterval 40),(⟨780826222944,780874147040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨184736706816,184929344320⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-222449910720,-222170940544⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e820_ok : ecellOkT e820 = true := by decide +kernel
theorem e820_pos {a z : ℝ} (ha1 : ((749391/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((4689/25600 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e820 e820_ok ha1 ha2 hz1 hz2 hz

-- box ['186711/1024000', '747693/4096000', '1999/2000', '3999/4000']  interval_lower 80836623/549755813888
noncomputable def e821 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1299991037476,0,true,184158592000,184158592064⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨899032218076,0,false,-221334454784,-221334454720⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1300218939180,0,true,184351330688,184351330752⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨898804316372,0,false,-221613212736,-221613212672⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1299890797771,0,true,184073807552,184073807616⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨899132457781,0,false,-221211868992,-221211868928⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1300168762353,0,true,184308898560,184308898624⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨898854493199,0,false,-221551832896,-221551832832⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537306422,0,true,25678336,25678400⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485949130,0,false,-25678976,-25678912⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099563047448,0,true,51418432,51418496⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099460208104,0,false,-51420928,-51420864⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625371,0,false,-2432,-2368⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627177,0,false,-640,-576⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1299940912761,0,true,184116196480,184116196544⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨899082342791,0,false,-221273154240,-221273154176⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1300193859341,0,true,184330122112,184330122176⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨898829396211,0,false,-221582532864,-221582532800⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1062883221992,0,false,-37252410752,-37252410688⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1062975499131,0,false,-37156957760,-37156957696⟩
    { al := (186711/1024000), au := (747693/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨200479409700,200707311404⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184158592000,184158592064⟩ : DyadicInterval 40),(⟨-221334454784,-221334454720⟩ : DyadicInterval 40),(⟨743743535520,743743554850⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184351330688,184351330752⟩ : DyadicInterval 40),(⟨-221613212736,-221613212672⟩ : DyadicInterval 40),(⟨743701486762,743701506091⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184073807552,184073807616⟩ : DyadicInterval 40),(⟨-221211868992,-221211868928⟩ : DyadicInterval 40),(⟨743762014708,743762034037⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184308898560,184308898624⟩ : DyadicInterval 40),(⟨-221551832896,-221551832832⟩ : DyadicInterval 40),(⟨743710748781,743710768110⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨25678646,51419672⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25678336,25678400⟩ : DyadicInterval 40),(⟨-25678976,-25678912⟩ : DyadicInterval 40),(⟨762123383272,762123402601⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨51418432,51418496⟩ : DyadicInterval 40),(⟨-51420928,-51420864⟩ : DyadicInterval 40),(⟨762123382395,762123401724⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2432,-576⟩ : DyadicInterval 40),(⟨762123383904,762123404096⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨200429284985,200682231565⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184116196480,184116196544⟩ : DyadicInterval 40),(⟨-221273154240,-221273154176⟩ : DyadicInterval 40),(⟨743752777195,743752796525⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184330122112,184330122176⟩ : DyadicInterval 40),(⟨-221582532864,-221582532800⟩ : DyadicInterval 40),(⟨743706116460,743706135790⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-37252410752,-37156957696⟩ : DyadicInterval 40),(⟨780701862464,780749608256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨184158592000,184351330752⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-221613212736,-221334454720⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e821_ok : ecellOkT e821 = true := by decide +kernel
theorem e821_pos {a z : ℝ} (ha1 : ((186711/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((747693/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e821 e821_ok ha1 ha2 hz1 hz2 hz

-- box ['747693/4096000', '374271/2048000', '1999/2000', '3999/4000']  interval_lower 82483711/549755813888
noncomputable def e822 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1300218939179,0,true,184351330688,184351330752⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨898804316373,0,false,-221613212736,-221613212672⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1300446840882,0,true,184544035648,184544035712⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨898576414670,0,false,-221892041344,-221892041280⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1300118585523,0,true,184266464768,184266464832⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨898904670029,0,false,-221490456448,-221490456384⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1300396607079,0,true,184501562752,184501562816⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨898626648473,0,false,-221830576192,-221830576128⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537337065,0,true,25708928,25708992⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485918487,0,false,-25709632,-25709568⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099563108749,0,true,51479744,51479808⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099460146803,0,false,-51482240,-51482176⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625365,0,false,-2432,-2368⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627175,0,false,-640,-576⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1300168757480,0,true,184308894464,184308894528⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨898854498072,0,false,-221551826944,-221551826880⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1300421732557,0,true,184522806656,184522806720⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨898601522995,0,false,-221861318848,-221861318784⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1062799992188,0,false,-37338512128,-37338512064⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1062892384574,0,false,-37242932416,-37242932352⟩
    { al := (747693/4096000), au := (374271/2048000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨200707311403,200935213106⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184351330688,184351330752⟩ : DyadicInterval 40),(⟨-221613212736,-221613212672⟩ : DyadicInterval 40),(⟨743701486762,743701506092⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184544035648,184544035712⟩ : DyadicInterval 40),(⟨-221892041344,-221892041280⟩ : DyadicInterval 40),(⟨743659389091,743659408421⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184266464768,184266464832⟩ : DyadicInterval 40),(⟨-221490456448,-221490456384⟩ : DyadicInterval 40),(⟨743720008433,743720027763⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184501562752,184501562816⟩ : DyadicInterval 40),(⟨-221830576192,-221830576128⟩ : DyadicInterval 40),(⟨743668672402,743668691732⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨25709289,51480973⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25708928,25708992⟩ : DyadicInterval 40),(⟨-25709632,-25709568⟩ : DyadicInterval 40),(⟨762123383302,762123402631⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨51479744,51479808⟩ : DyadicInterval 40),(⟨-51482240,-51482176⟩ : DyadicInterval 40),(⟨762123382389,762123401718⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2432,-576⟩ : DyadicInterval 40),(⟨762123383904,762123404096⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨200657129704,200910104781⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184308894464,184308894528⟩ : DyadicInterval 40),(⟨-221551826944,-221551826880⟩ : DyadicInterval 40),(⟨743710749669,743710768999⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184522806656,184522806720⟩ : DyadicInterval 40),(⟨-221861318848,-221861318784⟩ : DyadicInterval 40),(⟨743664029466,743664048795⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-37338512128,-37242932352⟩ : DyadicInterval 40),(⟨780744849792,780792658944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨184351330688,184544035712⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-221892041344,-221613212672⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e822_ok : ecellOkT e822 = true := by decide +kernel
theorem e822_pos {a z : ℝ} (ha1 : ((747693/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((374271/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e822 e822_ok ha1 ha2 hz1 hz2 hz

-- box ['186711/1024000', '747693/4096000', '3999/4000', '1']  interval_lower 161045169/1099511627776
noncomputable def e823 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1299991037476,0,true,184158592000,184158592064⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨899032218076,0,false,-221334454784,-221334454720⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1300218939180,0,true,184351330688,184351330752⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨898804316372,0,false,-221613212736,-221613212672⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1299940917623,0,true,184116200576,184116200640⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨899082337929,0,false,-221273160192,-221273160128⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537337900,0,true,25709760,25709824⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485917652,0,false,-25710464,-25710400⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627174,0,false,-640,-576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1299965972459,0,true,184137392192,184137392256⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨899057283093,0,false,-221303800832,-221303800768⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1300218947677,0,true,184351337920,184351337984⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨898804307875,0,false,-221613223104,-221613223040⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1062874063202,0,false,-37261885184,-37261885120⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1062966362327,0,false,-37166408640,-37166408576⟩
    { al := (186711/1024000), au := (747693/4096000), zl := (3999/4000), zu := 1,
      A := ⟨200479409700,200707311404⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184158592000,184158592064⟩ : DyadicInterval 40),(⟨-221334454784,-221334454720⟩ : DyadicInterval 40),(⟨743743535520,743743554850⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184351330688,184351330752⟩ : DyadicInterval 40),(⟨-221613212736,-221613212672⟩ : DyadicInterval 40),(⟨743701486762,743701506091⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184116200576,184116200640⟩ : DyadicInterval 40),(⟨-221273160192,-221273160128⟩ : DyadicInterval 40),(⟨743752776311,743752795641⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184351330688,184351330752⟩ : DyadicInterval 40),(⟨-221613212736,-221613212672⟩ : DyadicInterval 40),(⟨743701486762,743701506091⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,25710124⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25709760,25709824⟩ : DyadicInterval 40),(⟨-25710464,-25710400⟩ : DyadicInterval 40),(⟨762123383302,762123402631⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-640,0⟩ : DyadicInterval 40),(⟨762123383616,762123403200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨200454344683,200707319901⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184137392192,184137392256⟩ : DyadicInterval 40),(⟨-221303800832,-221303800768⟩ : DyadicInterval 40),(⟨743748157145,743748176475⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184351337920,184351337984⟩ : DyadicInterval 40),(⟨-221613223104,-221613223040⟩ : DyadicInterval 40),(⟨743701485155,743701504484⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-37261885184,-37166408576⟩ : DyadicInterval 40),(⟨780706587904,780754345472⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨184158592000,184351330752⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-221613212736,-221334454720⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e823_ok : ecellOkT e823 = true := by decide +kernel
theorem e823_pos {a z : ℝ} (ha1 : ((186711/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((747693/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e823 e823_ok ha1 ha2 hz1 hz2 hz

-- box ['747693/4096000', '374271/2048000', '3999/4000', '1']  interval_lower 164336835/1099511627776
noncomputable def e824 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1300218939179,0,true,184351330688,184351330752⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨898804316373,0,false,-221613212736,-221613212672⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1300446840882,0,true,184544035648,184544035712⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨898576414670,0,false,-221892041344,-221892041280⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1300168762351,0,true,184308898560,184308898624⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨898854493201,0,false,-221551832896,-221551832832⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537368551,0,true,25740416,25740480⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485887001,0,false,-25741120,-25741056⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627173,0,false,-640,-576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1300193845665,0,true,184330110528,184330110592⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨898829409887,0,false,-221582516160,-221582516096⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1300446849381,0,true,184544042816,184544042880⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨898576406171,0,false,-221892051712,-221892051648⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1062790812587,0,false,-37348008832,-37348008768⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1062883226985,0,false,-37252405568,-37252405504⟩
    { al := (747693/4096000), au := (374271/2048000), zl := (3999/4000), zu := 1,
      A := ⟨200707311403,200935213106⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184351330688,184351330752⟩ : DyadicInterval 40),(⟨-221613212736,-221613212672⟩ : DyadicInterval 40),(⟨743701486762,743701506092⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184544035648,184544035712⟩ : DyadicInterval 40),(⟨-221892041344,-221892041280⟩ : DyadicInterval 40),(⟨743659389091,743659408421⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184308898560,184308898624⟩ : DyadicInterval 40),(⟨-221551832896,-221551832832⟩ : DyadicInterval 40),(⟨743710748781,743710768111⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184544035648,184544035712⟩ : DyadicInterval 40),(⟨-221892041344,-221892041280⟩ : DyadicInterval 40),(⟨743659389091,743659408421⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,25740775⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25740416,25740480⟩ : DyadicInterval 40),(⟨-25741120,-25741056⟩ : DyadicInterval 40),(⟨762123383301,762123402630⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-640,0⟩ : DyadicInterval 40),(⟨762123383616,762123403200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨200682217889,200935221605⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184330110528,184330110592⟩ : DyadicInterval 40),(⟨-221582516160,-221582516096⟩ : DyadicInterval 40),(⟨743706119006,743706138336⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184544042816,184544042880⟩ : DyadicInterval 40),(⟨-221892051712,-221892051648⟩ : DyadicInterval 40),(⟨743659387518,743659406848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-37348008832,-37252405504⟩ : DyadicInterval 40),(⟨780749586368,780797407296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨184351330688,184544035712⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-221892041344,-221613212672⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e824_ok : ecellOkT e824 = true := by decide +kernel
theorem e824_pos {a z : ℝ} (ha1 : ((747693/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((374271/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e824 e824_ok ha1 ha2 hz1 hz2 hz

-- box ['374271/2048000', '749391/4096000', '1999/2000', '3999/4000']  interval_lower 168277073/1099511627776
noncomputable def e825 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1300446840881,0,true,184544035648,184544035712⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨898576414671,0,false,-221892041280,-221892041216⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1300674742584,0,true,184736706816,184736706880⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨898348512968,0,false,-222170940608,-222170940544⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1300346373274,0,true,184459088256,184459088320⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨898676882278,0,false,-221769114496,-221769114432⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1300624451806,0,true,184694193216,184694193280⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨898398803746,0,false,-222109390208,-222109390144⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537367715,0,true,25739584,25739648⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485887837,0,false,-25740288,-25740224⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099563170058,0,true,51541056,51541120⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099460085494,0,false,-51543552,-51543488⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625359,0,false,-2432,-2368⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627174,0,false,-640,-576⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1300396602208,0,true,184501558656,184501558720⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨898626653344,0,false,-221830570240,-221830570176⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1300649605775,0,true,184715457472,184715457536⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨898373649777,0,false,-222140175488,-222140175424⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1062716667930,0,false,-37424717952,-37424717888⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1062809175585,0,false,-37329011520,-37329011456⟩
    { al := (374271/2048000), au := (749391/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨200935213105,201163114808⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184544035648,184544035712⟩ : DyadicInterval 40),(⟨-221892041280,-221892041216⟩ : DyadicInterval 40),(⟨743659389066,743659408395⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184736706816,184736706880⟩ : DyadicInterval 40),(⟨-222170940608,-222170940544⟩ : DyadicInterval 40),(⟨743617242535,743617261865⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184459088256,184459088320⟩ : DyadicInterval 40),(⟨-221769114496,-221769114432⟩ : DyadicInterval 40),(⟨743677953323,743677972653⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184694193216,184694193280⟩ : DyadicInterval 40),(⟨-222109390208,-222109390144⟩ : DyadicInterval 40),(⟨743626547178,743626566507⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨25739939,51542282⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25739584,25739648⟩ : DyadicInterval 40),(⟨-25740288,-25740224⟩ : DyadicInterval 40),(⟨762123383301,762123402630⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨51541056,51541120⟩ : DyadicInterval 40),(⟨-51543552,-51543488⟩ : DyadicInterval 40),(⟨762123382383,762123401712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2432,-576⟩ : DyadicInterval 40),(⟨762123383904,762123404096⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨200884974432,201137977999⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184501558656,184501558720⟩ : DyadicInterval 40),(⟨-221830570240,-221830570176⟩ : DyadicInterval 40),(⟨743668673292,743668692621⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184715457472,184715457536⟩ : DyadicInterval 40),(⟨-222140175488,-222140175424⟩ : DyadicInterval 40),(⟨743621893572,743621912902⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-37424717952,-37329011456⟩ : DyadicInterval 40),(⟨780787889344,780835761856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨184544035648,184736706880⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-222170940608,-221892041216⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e825_ok : ecellOkT e825 = true := by decide +kernel
theorem e825_pos {a z : ℝ} (ha1 : ((374271/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((749391/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e825 e825_ok ha1 ha2 hz1 hz2 hz

-- box ['749391/4096000', '4689/25600', '1999/2000', '3999/4000']  interval_lower 85800939/549755813888
noncomputable def e826 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1300674742583,0,true,184736706816,184736706880⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨898348512969,0,false,-222170940608,-222170940544⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1300902644286,0,true,184929344256,184929344320⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨898120611266,0,false,-222449910720,-222449910656⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1300574161025,0,true,184651677952,184651678016⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨898449094527,0,false,-222047843200,-222047843136⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1300852296533,0,true,184886789952,184886790016⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨898170959019,0,false,-222388274944,-222388274880⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537398370,0,true,25770240,25770304⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485857182,0,false,-25770944,-25770880⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099563231380,0,true,51602368,51602432⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099460024172,0,false,-51604864,-51604800⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625354,0,false,-2432,-2368⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627172,0,false,-640,-576⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1300624446928,0,true,184694189120,184694189184⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨898398808624,0,false,-222109384256,-222109384192⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1300877478992,0,true,184908074560,184908074624⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨898145776560,0,false,-222419102912,-222419102848⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1062633249219,0,false,-37511028352,-37511028288⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1062725872169,0,false,-37415195072,-37415195008⟩
    { al := (749391/4096000), au := (4689/25600), zl := (1999/2000), zu := (3999/4000),
      A := ⟨201163114807,201391016510⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184736706816,184736706880⟩ : DyadicInterval 40),(⟨-222170940608,-222170940544⟩ : DyadicInterval 40),(⟨743617242536,743617261865⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184929344256,184929344320⟩ : DyadicInterval 40),(⟨-222449910720,-222449910656⟩ : DyadicInterval 40),(⟨743575047123,743575066453⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184651677952,184651678016⟩ : DyadicInterval 40),(⟨-222047843200,-222047843136⟩ : DyadicInterval 40),(⟨743635849430,743635868760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184886789952,184886790016⟩ : DyadicInterval 40),(⟨-222388274944,-222388274880⟩ : DyadicInterval 40),(⟨743584373096,743584392425⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨25770594,51603604⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25770240,25770304⟩ : DyadicInterval 40),(⟨-25770944,-25770880⟩ : DyadicInterval 40),(⟨762123383299,762123402628⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨51602368,51602432⟩ : DyadicInterval 40),(⟨-51604864,-51604800⟩ : DyadicInterval 40),(⟨762123382378,762123401707⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2432,-576⟩ : DyadicInterval 40),(⟨762123383904,762123404096⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨201112819152,201365851216⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184694189120,184694189184⟩ : DyadicInterval 40),(⟨-222109384256,-222109384192⟩ : DyadicInterval 40),(⟨743626548071,743626567400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184908074560,184908074624⟩ : DyadicInterval 40),(⟨-222419102912,-222419102848⟩ : DyadicInterval 40),(⟨743579708822,743579728152⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-37511028352,-37415195008⟩ : DyadicInterval 40),(⟨780830981120,780878917056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨184736706816,184929344320⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-222449910720,-222170940544⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e826_ok : ecellOkT e826 = true := by decide +kernel
theorem e826_pos {a z : ℝ} (ha1 : ((749391/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((4689/25600 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e826 e826_ok ha1 ha2 hz1 hz2 hz

-- box ['374271/2048000', '749391/4096000', '3999/4000', '1']  interval_lower 10477743/68719476736
noncomputable def e827 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1300446840881,0,true,184544035648,184544035712⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨898576414671,0,false,-221892041280,-221892041216⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1300674742584,0,true,184736706816,184736706880⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨898348512968,0,false,-222170940608,-222170940544⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1300396607077,0,true,184501562752,184501562816⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨898626648475,0,false,-221830576192,-221830576128⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537399207,0,true,25771072,25771136⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485856345,0,false,-25771776,-25771712⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627171,0,false,-640,-576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1300421718878,0,true,184522795072,184522795136⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨898601536674,0,false,-221861302080,-221861302016⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1300674751089,0,true,184736713984,184736714048⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨898348504463,0,false,-222170951040,-222170950976⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1062707467493,0,false,-37434236992,-37434236928⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1062799997188,0,false,-37338506944,-37338506880⟩
    { al := (374271/2048000), au := (749391/4096000), zl := (3999/4000), zu := 1,
      A := ⟨200935213105,201163114808⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184544035648,184544035712⟩ : DyadicInterval 40),(⟨-221892041280,-221892041216⟩ : DyadicInterval 40),(⟨743659389066,743659408395⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184736706816,184736706880⟩ : DyadicInterval 40),(⟨-222170940608,-222170940544⟩ : DyadicInterval 40),(⟨743617242535,743617261865⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184501562752,184501562816⟩ : DyadicInterval 40),(⟨-221830576192,-221830576128⟩ : DyadicInterval 40),(⟨743668672402,743668691732⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184736706816,184736706880⟩ : DyadicInterval 40),(⟨-222170940608,-222170940544⟩ : DyadicInterval 40),(⟨743617242535,743617261865⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,25771431⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25771072,25771136⟩ : DyadicInterval 40),(⟨-25771776,-25771712⟩ : DyadicInterval 40),(⟨762123383299,762123402628⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-640,0⟩ : DyadicInterval 40),(⟨762123383616,762123403200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨200910091102,201163123313⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184522795072,184522795136⟩ : DyadicInterval 40),(⟨-221861302080,-221861302016⟩ : DyadicInterval 40),(⟨743664031992,743664051321⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184736713984,184736714048⟩ : DyadicInterval 40),(⟨-222170951040,-222170950976⟩ : DyadicInterval 40),(⟨743617240984,743617260313⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-37434236992,-37338506880⟩ : DyadicInterval 40),(⟨780792637056,780840521376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨184544035648,184736706880⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-222170940608,-221892041216⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e827_ok : ecellOkT e827 = true := by decide +kernel
theorem e827_pos {a z : ℝ} (ha1 : ((374271/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((749391/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e827 e827_ok ha1 ha2 hz1 hz2 hz

-- box ['749391/4096000', '4689/25600', '3999/4000', '1']  interval_lower 170966235/1099511627776
noncomputable def e828 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1300674742583,0,true,184736706816,184736706880⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨898348512969,0,false,-222170940608,-222170940544⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1300902644286,0,true,184929344256,184929344320⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨898120611266,0,false,-222449910720,-222449910656⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1300624451804,0,true,184694193216,184694193280⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨898398803748,0,false,-222109390208,-222109390144⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537429869,0,true,25801728,25801792⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485825683,0,false,-25802432,-25802368⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627170,0,false,-640,-576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1300649592088,0,true,184715445888,184715445952⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨898373663464,0,false,-222140158720,-222140158656⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1300902652793,0,true,184929351424,184929351488⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨898120602759,0,false,-222449921152,-222449921088⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1062624027924,0,false,-37520569664,-37520569600⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1062716672939,0,false,-37424712768,-37424712704⟩
    { al := (749391/4096000), au := (4689/25600), zl := (3999/4000), zu := 1,
      A := ⟨201163114807,201391016510⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184736706816,184736706880⟩ : DyadicInterval 40),(⟨-222170940608,-222170940544⟩ : DyadicInterval 40),(⟨743617242536,743617261865⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184929344256,184929344320⟩ : DyadicInterval 40),(⟨-222449910720,-222449910656⟩ : DyadicInterval 40),(⟨743575047123,743575066453⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184694193216,184694193280⟩ : DyadicInterval 40),(⟨-222109390208,-222109390144⟩ : DyadicInterval 40),(⟨743626547178,743626566507⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184929344256,184929344320⟩ : DyadicInterval 40),(⟨-222449910720,-222449910656⟩ : DyadicInterval 40),(⟨743575047123,743575066453⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,25802093⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25801728,25801792⟩ : DyadicInterval 40),(⟨-25802432,-25802368⟩ : DyadicInterval 40),(⟨762123383298,762123402627⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-640,0⟩ : DyadicInterval 40),(⟨762123383616,762123403200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨201137964312,201391025017⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184715445888,184715445952⟩ : DyadicInterval 40),(⟨-222140158720,-222140158656⟩ : DyadicInterval 40),(⟨743621896106,743621915435⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184929351424,184929351488⟩ : DyadicInterval 40),(⟨-222449921152,-222449921088⟩ : DyadicInterval 40),(⟨743575045568,743575064897⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-37520569664,-37424712704⟩ : DyadicInterval 40),(⟨780835739968,780883687712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨184736706816,184929344320⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-222449910720,-222170940544⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e828_ok : ecellOkT e828 = true := by decide +kernel
theorem e828_pos {a z : ℝ} (ha1 : ((749391/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((4689/25600 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e828 e828_ok ha1 ha2 hz1 hz2 hz

-- box ['4689/25600', '751089/4096000', '999/1000', '3997/4000']  interval_lower 176217047/1099511627776
noncomputable def e829 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1300902644285,0,true,184929344256,184929344320⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨898120611267,0,false,-222449910720,-222449910656⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1301130545988,0,true,185121947904,185121947968⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨897892709564,0,false,-222728951616,-222728951552⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1300701253268,0,true,184759117120,184759117184⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨898322002284,0,false,-222203388224,-222203388160⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1300979331800,0,true,184994157952,184994158016⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨898043923752,0,false,-222543798336,-222543798272⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589031080,0,true,77400576,77400640⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434224472,0,false,-77406080,-77406016⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099614956087,0,true,103323456,103323520⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099408299465,0,false,-103333184,-103333120⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511618065,0,false,-9728,-9664⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622327,0,false,-5504,-5440⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1300801944822,0,true,184844230656,184844230720⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨898221310730,0,false,-222326637696,-222326637632⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1301054948092,0,true,185058062528,185058062592⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨897968307460,0,false,-222636382336,-222636382272⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1062568216776,0,false,-37578319744,-37578319680⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1062660910865,0,false,-37482407040,-37482406976⟩
    { al := (4689/25600), au := (751089/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨201391016509,201618918212⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184929344256,184929344320⟩ : DyadicInterval 40),(⟨-222449910720,-222449910656⟩ : DyadicInterval 40),(⟨743575047123,743575066453⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185121947904,185121947968⟩ : DyadicInterval 40),(⟨-222728951616,-222728951552⟩ : DyadicInterval 40),(⟨743532802855,743532822184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184759117120,184759117184⟩ : DyadicInterval 40),(⟨-222203388224,-222203388160⟩ : DyadicInterval 40),(⟨743612336674,743612356004⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184994157952,184994158016⟩ : DyadicInterval 40),(⟨-222543798336,-222543798272⟩ : DyadicInterval 40),(⟨743560837643,743560856972⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨77403304,103328311⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77400576,77400640⟩ : DyadicInterval 40),(⟨-77406080,-77406016⟩ : DyadicInterval 40),(⟨762123380854,762123400184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨103323456,103323520⟩ : DyadicInterval 40),(⟨-103333184,-103333120⟩ : DyadicInterval 40),(⟨762123378705,762123398035⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-9728,-5440⟩ : DyadicInterval 40),(⟨762123386336,762123407744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨201290317046,201543320316⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184844230656,184844230720⟩ : DyadicInterval 40),(⟨-222326637696,-222326637632⟩ : DyadicInterval 40),(⟨743593697382,743593716711⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185058062528,185058062592⟩ : DyadicInterval 40),(⟨-222636382336,-222636382272⟩ : DyadicInterval 40),(⟨743546821249,743546840578⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-37578319744,-37482406976⟩ : DyadicInterval 40),(⟨780864587104,780912562752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨184929344256,185121947968⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-222728951616,-222449910656⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e829_ok : ecellOkT e829 = true := by decide +kernel
theorem e829_pos {a z : ℝ} (ha1 : ((4689/25600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((751089/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e829 e829_ok ha1 ha2 hz1 hz2 hz

-- box ['751089/4096000', '375969/2048000', '999/1000', '3997/4000']  interval_lower 179577685/1099511627776
noncomputable def e830 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1301130545987,0,true,185121947904,185121947968⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨897892709565,0,false,-222728951616,-222728951552⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1301358447690,0,true,185314517824,185314517888⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨897664807862,0,false,-223008063296,-223008063232⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1300928927068,0,true,184951558016,184951558080⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨898094328484,0,false,-222482087552,-222482087488⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1301207062576,0,true,185186605824,185186605888⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨897816192976,0,false,-222822653760,-222822653696⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589123071,0,true,77492544,77492608⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434132481,0,false,-77498048,-77497984⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099615078764,0,true,103446080,103446144⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099408176788,0,false,-103455872,-103455808⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511618042,0,false,-9792,-9728⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622315,0,false,-5504,-5440⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1301029732570,0,true,185036752896,185036752960⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨897993522982,0,false,-222605507776,-222605507712⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1301282764332,0,true,185250571456,185250571520⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨897740491220,0,false,-222915365888,-222915365824⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1062484650963,0,false,-37664794368,-37664794304⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1062577460339,0,false,-37568754880,-37568754816⟩
    { al := (751089/4096000), au := (375969/2048000), zl := (999/1000), zu := (3997/4000),
      A := ⟨201618918211,201846819914⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185121947904,185121947968⟩ : DyadicInterval 40),(⟨-222728951616,-222728951552⟩ : DyadicInterval 40),(⟨743532802855,743532822185⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185314517824,185314517888⟩ : DyadicInterval 40),(⟨-223008063296,-223008063232⟩ : DyadicInterval 40),(⟨743490509681,743490529010⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184951558016,184951558080⟩ : DyadicInterval 40),(⟨-222482087552,-222482087488⟩ : DyadicInterval 40),(⟨743570177801,743570197131⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185186605824,185186605888⟩ : DyadicInterval 40),(⟨-222822653760,-222822653696⟩ : DyadicInterval 40),(⟨743518608644,743518627974⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨77495295,103450988⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77492544,77492608⟩ : DyadicInterval 40),(⟨-77498048,-77497984⟩ : DyadicInterval 40),(⟨762123380841,762123400171⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨103446080,103446144⟩ : DyadicInterval 40),(⟨-103455872,-103455808⟩ : DyadicInterval 40),(⟨762123378714,762123398043⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-9792,-5440⟩ : DyadicInterval 40),(⟨762123386336,762123407776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨201518104794,201771136556⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185036752896,185036752960⟩ : DyadicInterval 40),(⟨-222605507776,-222605507712⟩ : DyadicInterval 40),(⟨743551495842,743551515171⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185250571456,185250571520⟩ : DyadicInterval 40),(⟨-222915365888,-222915365824⟩ : DyadicInterval 40),(⟨743504560152,743504579482⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-37664794368,-37568754816⟩ : DyadicInterval 40),(⟨780907761024,780955800064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨185121947904,185314517888⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-223008063296,-222728951552⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e830_ok : ecellOkT e830 = true := by decide +kernel
theorem e830_pos {a z : ℝ} (ha1 : ((751089/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((375969/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e830 e830_ok ha1 ha2 hz1 hz2 hz

-- box ['4689/25600', '751089/4096000', '3997/4000', '1999/2000']  interval_lower 87789871/549755813888
noncomputable def e831 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1300902644285,0,true,184929344256,184929344320⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨898120611267,0,false,-222449910720,-222449910656⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1301130545988,0,true,185121947904,185121947968⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨897892709564,0,false,-222728951616,-222728951552⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1300751601022,0,true,184801676352,184801676416⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨898271654530,0,false,-222265013632,-222265013568⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1301029736530,0,true,185036756224,185036756288⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨897993519022,0,false,-222605512640,-222605512576⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099563230216,0,true,51601216,51601280⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099460025336,0,false,-51603712,-51603648⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589124560,0,true,77494016,77494080⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434130992,0,false,-77499520,-77499456⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622313,0,false,-5504,-5440⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625355,0,false,-2432,-2368⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1300827118161,0,true,184865508352,184865508416⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨898196137391,0,false,-222357452800,-222357452736⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1301080150068,0,true,185079360320,185079360384⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨897943105484,0,false,-222667241152,-222667241088⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1062558977023,0,false,-37587880768,-37587880704⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1062651693197,0,false,-37491944384,-37491944320⟩
    { al := (4689/25600), au := (751089/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨201391016509,201618918212⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184929344256,184929344320⟩ : DyadicInterval 40),(⟨-222449910720,-222449910656⟩ : DyadicInterval 40),(⟨743575047123,743575066453⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185121947904,185121947968⟩ : DyadicInterval 40),(⟨-222728951616,-222728951552⟩ : DyadicInterval 40),(⟨743532802855,743532822184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184801676352,184801676416⟩ : DyadicInterval 40),(⟨-222265013632,-222265013568⟩ : DyadicInterval 40),(⟨743603017864,743603037194⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185036756224,185036756288⟩ : DyadicInterval 40),(⟨-222605512640,-222605512576⟩ : DyadicInterval 40),(⟨743551495125,743551514454⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨51602440,77496784⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨51601216,51601280⟩ : DyadicInterval 40),(⟨-51603712,-51603648⟩ : DyadicInterval 40),(⟨762123382378,762123401707⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77494016,77494080⟩ : DyadicInterval 40),(⟨-77499520,-77499456⟩ : DyadicInterval 40),(⟨762123380841,762123400170⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5504,-2368⟩ : DyadicInterval 40),(⟨762123384800,762123405632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨201315490385,201568522292⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184865508352,184865508416⟩ : DyadicInterval 40),(⟨-222357452800,-222357452736⟩ : DyadicInterval 40),(⟨743589036018,743589055348⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185079360320,185079360384⟩ : DyadicInterval 40),(⟨-222667241152,-222667241088⟩ : DyadicInterval 40),(⟨743542148547,743542167877⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-37587880768,-37491944320⟩ : DyadicInterval 40),(⟨780869355776,780917343264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨184929344256,185121947968⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-222728951616,-222449910656⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e831_ok : ecellOkT e831 = true := by decide +kernel
theorem e831_pos {a z : ℝ} (ha1 : ((4689/25600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((751089/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e831 e831_ok ha1 ha2 hz1 hz2 hz

-- box ['751089/4096000', '375969/2048000', '3997/4000', '1999/2000']  interval_lower 178937993/1099511627776
noncomputable def e832 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1301130545987,0,true,185121947904,185121947968⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨897892709565,0,false,-222728951616,-222728951552⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1301358447690,0,true,185314517824,185314517888⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨897664807862,0,false,-223008063296,-223008063232⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1300979331798,0,true,184994157952,184994158016⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨898043923754,0,false,-222543798336,-222543798272⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1301257524281,0,true,185229244800,185229244864⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨897765731271,0,false,-222884453440,-222884453376⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099563291544,0,true,51662528,51662592⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099459964008,0,false,-51665024,-51664960⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589216571,0,true,77586048,77586112⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434038981,0,false,-77591552,-77591488⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622300,0,false,-5504,-5440⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625349,0,false,-2432,-2368⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1301054934395,0,true,185058051008,185058051072⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨897968321157,0,false,-222636365568,-222636365504⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1301307994799,0,true,185271889600,185271889664⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨897715260753,0,false,-222946267456,-222946267392⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1062475390309,0,false,-37674377792,-37674377728⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1062568221798,0,false,-37578314560,-37578314496⟩
    { al := (751089/4096000), au := (375969/2048000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨201618918211,201846819914⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185121947904,185121947968⟩ : DyadicInterval 40),(⟨-222728951616,-222728951552⟩ : DyadicInterval 40),(⟨743532802855,743532822185⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185314517824,185314517888⟩ : DyadicInterval 40),(⟨-223008063296,-223008063232⟩ : DyadicInterval 40),(⟨743490509681,743490529010⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184994157952,184994158016⟩ : DyadicInterval 40),(⟨-222543798336,-222543798272⟩ : DyadicInterval 40),(⟨743560837643,743560856973⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185229244800,185229244864⟩ : DyadicInterval 40),(⟨-222884453440,-222884453376⟩ : DyadicInterval 40),(⟨743509244716,743509264045⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨51663768,77588795⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨51662528,51662592⟩ : DyadicInterval 40),(⟨-51665024,-51664960⟩ : DyadicInterval 40),(⟨762123382372,762123401701⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77586048,77586112⟩ : DyadicInterval 40),(⟨-77591552,-77591488⟩ : DyadicInterval 40),(⟨762123380828,762123400158⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5504,-2368⟩ : DyadicInterval 40),(⟨762123384800,762123405632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨201543306619,201796367023⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185058051008,185058051072⟩ : DyadicInterval 40),(⟨-222636365568,-222636365504⟩ : DyadicInterval 40),(⟨743546823757,743546843086⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185271889600,185271889664⟩ : DyadicInterval 40),(⟨-222946267456,-222946267392⟩ : DyadicInterval 40),(⟨743499876764,743499896094⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-37674377792,-37578314496⟩ : DyadicInterval 40),(⟨780912540864,780960591776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨185121947904,185314517888⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-223008063296,-222728951552⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e832_ok : ecellOkT e832 = true := by decide +kernel
theorem e832_pos {a z : ℝ} (ha1 : ((751089/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((375969/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e832 e832_ok ha1 ha2 hz1 hz2 hz

-- box ['375969/2048000', '752787/4096000', '999/1000', '3997/4000']  interval_lower 182953719/1099511627776
noncomputable def e833 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1301358447689,0,true,185314517824,185314517888⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨897664807863,0,false,-223008063296,-223008063232⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1301586349392,0,true,185507054080,185507054144⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨897436906160,0,false,-223287245888,-223287245824⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1301156600869,0,true,185143965184,185143965248⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨897866654683,0,false,-222760857472,-222760857408⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1301434793351,0,true,185379020032,185379020096⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨897588462201,0,false,-223101579840,-223101579776⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589215077,0,true,77584512,77584576⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434040475,0,false,-77590080,-77590016⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099615201463,0,true,103568768,103568832⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099408054089,0,false,-103578624,-103578560⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511618019,0,false,-9792,-9728⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622302,0,false,-5504,-5440⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1301257520322,0,true,185229241472,185229241536⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨897765735230,0,false,-222884448640,-222884448576⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1301510580579,0,true,185443046720,185443046784⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨897512674973,0,false,-223194420224,-223194420160⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1062400990741,0,false,-37751373504,-37751373440⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1062493915430,0,false,-37655207104,-37655207040⟩
    { al := (375969/2048000), au := (752787/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨201846819913,202074721616⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185314517824,185314517888⟩ : DyadicInterval 40),(⟨-223008063296,-223008063232⟩ : DyadicInterval 40),(⟨743490509681,743490529010⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185507054080,185507054144⟩ : DyadicInterval 40),(⟨-223287245888,-223287245824⟩ : DyadicInterval 40),(⟨743448167604,743448186933⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185143965184,185143965248⟩ : DyadicInterval 40),(⟨-222760857472,-222760857408⟩ : DyadicInterval 40),(⟨743527970149,743527989479⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185379020032,185379020096⟩ : DyadicInterval 40),(⟨-223101579840,-223101579776⟩ : DyadicInterval 40),(⟨743476330793,743476350122⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨77587301,103573687⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77584512,77584576⟩ : DyadicInterval 40),(⟨-77590080,-77590016⟩ : DyadicInterval 40),(⟨762123380860,762123400190⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨103568768,103568832⟩ : DyadicInterval 40),(⟨-103578624,-103578560⟩ : DyadicInterval 40),(⟨762123378722,762123398052⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-9792,-5440⟩ : DyadicInterval 40),(⟨762123386336,762123407776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨201745892546,201998952803⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185229241472,185229241536⟩ : DyadicInterval 40),(⟨-222884448640,-222884448576⟩ : DyadicInterval 40),(⟨743509245460,743509264790⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185443046720,185443046784⟩ : DyadicInterval 40),(⟨-223194420224,-223194420160⟩ : DyadicInterval 40),(⟨743462250176,743462269506⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-37751373504,-37655207040⟩ : DyadicInterval 40),(⟨780950987136,780999089632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨185314517824,185507054144⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-223287245888,-223008063232⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e833_ok : ecellOkT e833 = true := by decide +kernel
theorem e833_pos {a z : ℝ} (ha1 : ((375969/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((752787/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e833 e833_ok ha1 ha2 hz1 hz2 hz

-- box ['752787/4096000', '188409/1024000', '999/1000', '3997/4000']  interval_lower 186345413/1099511627776
noncomputable def e834 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1301586349391,0,true,185507054080,185507054144⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨897436906161,0,false,-223287245888,-223287245824⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1301814251095,0,true,185699556544,185699556608⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨897209004457,0,false,-223566499392,-223566499328⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1301384274669,0,true,185336338688,185336338752⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨897638980883,0,false,-223039698176,-223039698112⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1301662524128,0,true,185571400576,185571400640⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨897360731424,0,false,-223380576768,-223380576704⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589307099,0,true,77676544,77676608⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433948453,0,false,-77682112,-77682048⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099615324182,0,true,103691456,103691520⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099407931370,0,false,-103701312,-103701248⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511617996,0,false,-9792,-9728⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622289,0,false,-5504,-5440⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1301485308071,0,true,185421696384,185421696448⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨897537947481,0,false,-223163460224,-223163460160⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1301738396817,0,true,185635488192,185635488256⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨897284858735,0,false,-223473545472,-223473545408⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1062317236117,0,false,-37838057216,-37838057152⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1062410276139,0,false,-37741763840,-37741763776⟩
    { al := (752787/4096000), au := (188409/1024000), zl := (999/1000), zu := (3997/4000),
      A := ⟨202074721615,202302623319⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185507054080,185507054144⟩ : DyadicInterval 40),(⟨-223287245888,-223287245824⟩ : DyadicInterval 40),(⟨743448167604,743448186933⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185699556544,185699556608⟩ : DyadicInterval 40),(⟨-223566499392,-223566499328⟩ : DyadicInterval 40),(⟨743405776688,743405796017⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185336338688,185336338752⟩ : DyadicInterval 40),(⟨-223039698176,-223039698112⟩ : DyadicInterval 40),(⟨743485713748,743485733078⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185571400576,185571400640⟩ : DyadicInterval 40),(⟨-223380576768,-223380576704⟩ : DyadicInterval 40),(⟨743434004155,743434023484⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨77679323,103696406⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77676544,77676608⟩ : DyadicInterval 40),(⟨-77682112,-77682048⟩ : DyadicInterval 40),(⟨762123380847,762123400177⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨103691456,103691520⟩ : DyadicInterval 40),(⟨-103701312,-103701248⟩ : DyadicInterval 40),(⟨762123378699,762123398029⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-9792,-5440⟩ : DyadicInterval 40),(⟨762123386336,762123407776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨201973680295,202226769041⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185421696384,185421696448⟩ : DyadicInterval 40),(⟨-223163460224,-223163460160⟩ : DyadicInterval 40),(⟨743466946201,743466965530⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185635488192,185635488256⟩ : DyadicInterval 40),(⟨-223473545472,-223473545408⟩ : DyadicInterval 40),(⟨743419891440,743419910770⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-37838057216,-37741763776⟩ : DyadicInterval 40),(⟨780994265504,781042431488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨185507054080,185699556608⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-223566499392,-223287245824⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e834_ok : ecellOkT e834 = true := by decide +kernel
theorem e834_pos {a z : ℝ} (ha1 : ((752787/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((188409/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e834 e834_ok ha1 ha2 hz1 hz2 hz

-- box ['375969/2048000', '752787/4096000', '3997/4000', '1999/2000']  interval_lower 182311461/1099511627776
noncomputable def e835 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1301358447689,0,true,185314517824,185314517888⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨897664807863,0,false,-223008063296,-223008063232⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1301586349392,0,true,185507054080,185507054144⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨897436906160,0,false,-223287245888,-223287245824⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1301207062574,0,true,185186605824,185186605888⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨897816192978,0,false,-222822653760,-222822653696⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1301485312032,0,true,185421699712,185421699776⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨897537943520,0,false,-223163465088,-223163465024⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099563352883,0,true,51723840,51723904⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099459902669,0,false,-51726336,-51726272⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589308596,0,true,77678016,77678080⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433946956,0,false,-77683584,-77683520⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622287,0,false,-5504,-5440⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625343,0,false,-2496,-2432⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1301282750630,0,true,185250559872,185250559936⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨897740504922,0,false,-222915349120,-222915349056⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1301535839529,0,true,185464385152,185464385216⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨897487416023,0,false,-223225364544,-223225364480⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1062391709165,0,false,-37760979392,-37760979328⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1062484655993,0,false,-37664789184,-37664789120⟩
    { al := (375969/2048000), au := (752787/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨201846819913,202074721616⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185314517824,185314517888⟩ : DyadicInterval 40),(⟨-223008063296,-223008063232⟩ : DyadicInterval 40),(⟨743490509681,743490529010⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185507054080,185507054144⟩ : DyadicInterval 40),(⟨-223287245888,-223287245824⟩ : DyadicInterval 40),(⟨743448167604,743448186933⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185186605824,185186605888⟩ : DyadicInterval 40),(⟨-222822653760,-222822653696⟩ : DyadicInterval 40),(⟨743518608645,743518627974⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185421699712,185421699776⟩ : DyadicInterval 40),(⟨-223163465088,-223163465024⟩ : DyadicInterval 40),(⟨743466945481,743466964810⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨51725107,77680820⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨51723840,51723904⟩ : DyadicInterval 40),(⟨-51726336,-51726272⟩ : DyadicInterval 40),(⟨762123382366,762123401695⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77678016,77678080⟩ : DyadicInterval 40),(⟨-77683584,-77683520⟩ : DyadicInterval 40),(⟨762123380847,762123400177⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5504,-2432⟩ : DyadicInterval 40),(⟨762123384832,762123405632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨201771122854,202024211753⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185250559872,185250559936⟩ : DyadicInterval 40),(⟨-222915349120,-222915349056⟩ : DyadicInterval 40),(⟨743504562705,743504582035⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185464385152,185464385216⟩ : DyadicInterval 40),(⟨-223225364544,-223225364480⟩ : DyadicInterval 40),(⟨743457556115,743457575445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-37760979392,-37664789120⟩ : DyadicInterval 40),(⟨780955778176,781003892576⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨185314517824,185507054144⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-223287245888,-223008063232⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e835_ok : ecellOkT e835 = true := by decide +kernel
theorem e835_pos {a z : ℝ} (ha1 : ((375969/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((752787/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e835 e835_ok ha1 ha2 hz1 hz2 hz

-- box ['752787/4096000', '188409/1024000', '3997/4000', '1999/2000']  interval_lower 92850375/549755813888
noncomputable def e836 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1301586349391,0,true,185507054080,185507054144⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨897436906161,0,false,-223287245888,-223287245824⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1301814251095,0,true,185699556544,185699556608⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨897209004457,0,false,-223566499392,-223566499328⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1301434793349,0,true,185379020032,185379020096⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨897588462203,0,false,-223101579840,-223101579776⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1301713099784,0,true,185614120896,185614120960⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨897310155768,0,false,-223442547520,-223442547456⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099563414232,0,true,51785216,51785280⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099459841320,0,false,-51787712,-51787648⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589400637,0,true,77770048,77770112⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099433854915,0,false,-77775616,-77775552⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622274,0,false,-5504,-5440⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625337,0,false,-2496,-2432⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1301510566872,0,true,185443035136,185443035200⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨897512688680,0,false,-223194403456,-223194403392⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1301763684253,0,true,185656847040,185656847104⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨897259571299,0,false,-223504532480,-223504532416⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1062307933594,0,false,-37847685440,-37847685376⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1062400995779,0,false,-37751368320,-37751368256⟩
    { al := (752787/4096000), au := (188409/1024000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨202074721615,202302623319⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185507054080,185507054144⟩ : DyadicInterval 40),(⟨-223287245888,-223287245824⟩ : DyadicInterval 40),(⟨743448167604,743448186933⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185699556544,185699556608⟩ : DyadicInterval 40),(⟨-223566499392,-223566499328⟩ : DyadicInterval 40),(⟨743405776688,743405796017⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185379020032,185379020096⟩ : DyadicInterval 40),(⟨-223101579840,-223101579776⟩ : DyadicInterval 40),(⟨743476330793,743476350122⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185614120896,185614120960⟩ : DyadicInterval 40),(⟨-223442547520,-223442547456⟩ : DyadicInterval 40),(⟨743424597419,743424616749⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨51786456,77772861⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨51785216,51785280⟩ : DyadicInterval 40),(⟨-51787712,-51787648⟩ : DyadicInterval 40),(⟨762123382360,762123401689⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77770048,77770112⟩ : DyadicInterval 40),(⟨-77775616,-77775552⟩ : DyadicInterval 40),(⟨762123380834,762123400164⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5504,-2432⟩ : DyadicInterval 40),(⟨762123384832,762123405632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨201998939096,202252056477⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185443035136,185443035200⟩ : DyadicInterval 40),(⟨-223194403456,-223194403392⟩ : DyadicInterval 40),(⟨743462252736,743462272065⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185656847040,185656847104⟩ : DyadicInterval 40),(⟨-223504532480,-223504532416⟩ : DyadicInterval 40),(⟨743415186578,743415205908⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-37847685440,-37751368256⟩ : DyadicInterval 40),(⟨780999067744,781047245600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨185507054080,185699556608⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-223566499392,-223287245824⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e836_ok : ecellOkT e836 = true := by decide +kernel
theorem e836_pos {a z : ℝ} (ha1 : ((752787/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((188409/1024000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e836 e836_ok ha1 ha2 hz1 hz2 hz

-- box ['4689/25600', '751089/4096000', '1999/2000', '3999/4000']  interval_lower 174942261/1099511627776
noncomputable def e837 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1300902644285,0,true,184929344256,184929344320⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨898120611267,0,false,-222449910720,-222449910656⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1301130545988,0,true,185121947904,185121947968⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨897892709564,0,false,-222728951616,-222728951552⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1300801948776,0,true,184844233984,184844234048⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨898221306776,0,false,-222326642560,-222326642496⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1301080141259,0,true,185079352896,185079352960⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨897943114293,0,false,-222667230400,-222667230336⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537429028,0,true,25800896,25800960⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485826524,0,false,-25801600,-25801536⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099563292710,0,true,51663680,51663744⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099459962842,0,false,-51666176,-51666112⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625348,0,false,-2432,-2368⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627171,0,false,-640,-576⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1300852291654,0,true,184886785792,184886785856⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨898170963898,0,false,-222388268928,-222388268864⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1301105352203,0,true,185100657856,185100657920⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨897917903349,0,false,-222698101056,-222698100992⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1062549736058,0,false,-37597443200,-37597443136⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1062642474321,0,false,-37501483136,-37501483072⟩
    { al := (4689/25600), au := (751089/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨201391016509,201618918212⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184929344256,184929344320⟩ : DyadicInterval 40),(⟨-222449910720,-222449910656⟩ : DyadicInterval 40),(⟨743575047123,743575066453⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185121947904,185121947968⟩ : DyadicInterval 40),(⟨-222728951616,-222728951552⟩ : DyadicInterval 40),(⟨743532802855,743532822184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184844233984,184844234048⟩ : DyadicInterval 40),(⟨-222326642560,-222326642496⟩ : DyadicInterval 40),(⟨743593696668,743593715997⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185079352896,185079352960⟩ : DyadicInterval 40),(⟨-222667230400,-222667230336⟩ : DyadicInterval 40),(⟨743542150183,743542169512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨25801252,51664934⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25800896,25800960⟩ : DyadicInterval 40),(⟨-25801600,-25801536⟩ : DyadicInterval 40),(⟨762123383298,762123402627⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨51663680,51663744⟩ : DyadicInterval 40),(⟨-51666176,-51666112⟩ : DyadicInterval 40),(⟨762123382372,762123401701⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2432,-576⟩ : DyadicInterval 40),(⟨762123383904,762123404096⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨201340663878,201593724427⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184886785792,184886785856⟩ : DyadicInterval 40),(⟨-222388268928,-222388268864⟩ : DyadicInterval 40),(⟨743584374003,743584393332⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185100657856,185100657920⟩ : DyadicInterval 40),(⟨-222698101056,-222698100992⟩ : DyadicInterval 40),(⟨743537475217,743537494546⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-37597443200,-37501483072⟩ : DyadicInterval 40),(⟨780874125152,780922124480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨184929344256,185121947968⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-222728951616,-222449910656⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e837_ok : ecellOkT e837 = true := by decide +kernel
theorem e837_pos {a z : ℝ} (ha1 : ((4689/25600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((751089/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e837 e837_ok ha1 ha2 hz1 hz2 hz

-- box ['751089/4096000', '375969/2048000', '1999/2000', '3999/4000']  interval_lower 22287209/137438953472
noncomputable def e838 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1301130545987,0,true,185121947904,185121947968⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨897892709565,0,false,-222728951616,-222728951552⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1301358447690,0,true,185314517824,185314517888⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨897664807862,0,false,-223008063296,-223008063232⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1301029736527,0,true,185036756224,185036756288⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨897993519025,0,false,-222605512640,-222605512576⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1301307985986,0,true,185271882176,185271882240⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨897715269566,0,false,-222946256640,-222946256576⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537459693,0,true,25831552,25831616⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485795859,0,false,-25832256,-25832192⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099563354050,0,true,51725056,51725120⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099459901502,0,false,-51727552,-51727488⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625342,0,false,-2496,-2432⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627170,0,false,-640,-576⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1301080136371,0,true,185079348800,185079348864⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨897943119181,0,false,-222667224384,-222667224320⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1301333225421,0,true,185293207488,185293207552⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨897690030131,0,false,-222977170048,-222977169984⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1062466128440,0,false,-37683962560,-37683962496⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1062558982047,0,false,-37587875584,-37587875520⟩
    { al := (751089/4096000), au := (375969/2048000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨201618918211,201846819914⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185121947904,185121947968⟩ : DyadicInterval 40),(⟨-222728951616,-222728951552⟩ : DyadicInterval 40),(⟨743532802855,743532822185⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185314517824,185314517888⟩ : DyadicInterval 40),(⟨-223008063296,-223008063232⟩ : DyadicInterval 40),(⟨743490509681,743490529010⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185036756224,185036756288⟩ : DyadicInterval 40),(⟨-222605512640,-222605512576⟩ : DyadicInterval 40),(⟨743551495125,743551514455⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185271882176,185271882240⟩ : DyadicInterval 40),(⟨-222946256640,-222946256576⟩ : DyadicInterval 40),(⟨743499878378,743499897707⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨25831917,51726274⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25831552,25831616⟩ : DyadicInterval 40),(⟨-25832256,-25832192⟩ : DyadicInterval 40),(⟨762123383297,762123402626⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨51725056,51725120⟩ : DyadicInterval 40),(⟨-51727552,-51727488⟩ : DyadicInterval 40),(⟨762123382366,762123401695⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2496,-576⟩ : DyadicInterval 40),(⟨762123383904,762123404128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨201568508595,201821597645⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185079348800,185079348864⟩ : DyadicInterval 40),(⟨-222667224384,-222667224320⟩ : DyadicInterval 40),(⟨743542151056,743542170386⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185293207488,185293207552⟩ : DyadicInterval 40),(⟨-222977170048,-222977169984⟩ : DyadicInterval 40),(⟨743495192719,743495212048⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-37683962560,-37587875520⟩ : DyadicInterval 40),(⟨780917321376,780965384160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨185121947904,185314517888⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-223008063296,-222728951552⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e838_ok : ecellOkT e838 = true := by decide +kernel
theorem e838_pos {a z : ℝ} (ha1 : ((751089/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((375969/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e838 e838_ok ha1 ha2 hz1 hz2 hz

-- box ['4689/25600', '751089/4096000', '3999/4000', '1']  interval_lower 87151923/549755813888
noncomputable def e839 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1300902644285,0,true,184929344256,184929344320⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨898120611267,0,false,-222449910720,-222449910656⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1301130545988,0,true,185121947904,185121947968⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨897892709564,0,false,-222728951616,-222728951552⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1300852296530,0,true,184886789952,184886790016⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨898170959022,0,false,-222388274880,-222388274816⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537460533,0,true,25832448,25832512⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099485795019,0,false,-25833088,-25833024⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627169,0,false,-640,-576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1300877465302,0,true,184908062976,184908063040⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨898145790250,0,false,-222419086144,-222419086080⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1301130554490,0,true,185121955072,185121955136⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨897892701062,0,false,-222728962048,-222728961984⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1062540493881,0,false,-37607006912,-37607006848⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1062633254235,0,false,-37511023104,-37511023040⟩
    { al := (4689/25600), au := (751089/4096000), zl := (3999/4000), zu := 1,
      A := ⟨201391016509,201618918212⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184929344256,184929344320⟩ : DyadicInterval 40),(⟨-222449910720,-222449910656⟩ : DyadicInterval 40),(⟨743575047123,743575066453⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185121947904,185121947968⟩ : DyadicInterval 40),(⟨-222728951616,-222728951552⟩ : DyadicInterval 40),(⟨743532802855,743532822184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184886789952,184886790016⟩ : DyadicInterval 40),(⟨-222388274880,-222388274816⟩ : DyadicInterval 40),(⟨743584373070,743584392399⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185121947904,185121947968⟩ : DyadicInterval 40),(⟨-222728951616,-222728951552⟩ : DyadicInterval 40),(⟨743532802855,743532822184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,25832757⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25832448,25832512⟩ : DyadicInterval 40),(⟨-25833088,-25833024⟩ : DyadicInterval 40),(⟨762123383265,762123402594⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-640,0⟩ : DyadicInterval 40),(⟨762123383616,762123403200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨201365837526,201618926714⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨184908062976,184908063040⟩ : DyadicInterval 40),(⟨-222419086144,-222419086080⟩ : DyadicInterval 40),(⟨743579711362,743579730692⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨185121955072,185121955136⟩ : DyadicInterval 40),(⟨-222728962048,-222728961984⟩ : DyadicInterval 40),(⟨743532801296,743532820625⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-37607006912,-37511023040⟩ : DyadicInterval 40),(⟨780878895136,780926906336⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨184929344256,185121947968⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-222728951616,-222449910656⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e839_ok : ecellOkT e839 = true := by decide +kernel
theorem e839_pos {a z : ℝ} (ha1 : ((4689/25600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((751089/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e839 e839_ok ha1 ha2 hz1 hz2 hz

end CKLaneC2R.EpCells.B013

end


