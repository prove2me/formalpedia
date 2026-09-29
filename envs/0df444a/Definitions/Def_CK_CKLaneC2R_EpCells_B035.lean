-- Prove2me | Definitions.Def_CK_CKLaneC2R_EpCells_B035
-- name    : CK_CKLaneC2R_EpCells_B035
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T14:55:34.151386+00:00
-- url     : https://prove2.me/theorems/89a39244-a005-431f-9cea-79d7e35c1cbb
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EpCells.B035` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EpCells.B035` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EpCells.B035` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EpCells.B035 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EpCells/B035.lean)

import Definitions.Def_CK_CKLaneC2R_EndpointCheckT

-- ===== source module CKLaneC2R.EpCells.B035 =====
section

namespace CKLaneC2R.EpCells.B035

open GeneralCK GeneralCK.Certificates CKLaneC2R CKLaneC2R.Endpoint

-- box ['128823/819200', '1289079/8192000', '3999/4000', '7999/8000']  interval_lower 185070357/1099511627776
noncomputable def e2100 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272414931517,0,true,160584233152,160584233216⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926608324035,0,false,-188115916224,-188115916160⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272528882369,0,true,160682695296,160682695360⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926494373183,0,false,-188251138368,-188251138304⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272371705691,0,true,160546880512,160546880576⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926651549861,0,false,-188064625728,-188064625664⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272507255213,0,true,160664008448,160664008512⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926516000339,0,false,-188225472768,-188225472704⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522631025,0,true,11003136,11003200⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500624527,0,false,-11003328,-11003264⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533650133,0,true,22022080,22022144⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489605419,0,false,-22022592,-22022528⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627334,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627666,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272393314102,0,true,160565553088,160565553152⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926629941450,0,false,-188090265344,-188090265280⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272518073169,0,true,160673355712,160673355776⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926505182383,0,false,-188238310720,-188238310656⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072289332539,0,false,-27564955008,-27564954944⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072328579674,0,false,-27524712192,-27524712128⟩
    { al := (128823/819200), au := (1289079/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨172903303741,173017254593⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160584233152,160584233216⟩ : DyadicInterval 40),(⟨-188115916224,-188115916160⟩ : DyadicInterval 40),(⟨748471867090,748471886419⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160682695296,160682695360⟩ : DyadicInterval 40),(⟨-188251138368,-188251138304⟩ : DyadicInterval 40),(⟨748453791772,748453811101⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160546880512,160546880576⟩ : DyadicInterval 40),(⟨-188064625728,-188064625664⟩ : DyadicInterval 40),(⟨748478720531,748478739860⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160664008448,160664008512⟩ : DyadicInterval 40),(⟨-188225472768,-188225472704⟩ : DyadicInterval 40),(⟨748457223298,748457242628⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11003249,22022357⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11003136,11003200⟩ : DyadicInterval 40),(⟨-11003328,-11003264⟩ : DyadicInterval 40),(⟨762123383537,762123402866⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22022080,22022144⟩ : DyadicInterval 40),(⟨-22022592,-22022528⟩ : DyadicInterval 40),(⟨762123383366,762123402695⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172881686326,173006445393⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160565553088,160565553152⟩ : DyadicInterval 40),(⟨-188090265344,-188090265280⟩ : DyadicInterval 40),(⟨748475294753,748475314083⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160673355712,160673355776⟩ : DyadicInterval 40),(⟨-188238310720,-188238310656⟩ : DyadicInterval 40),(⟨748455506898,748455526227⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27564955008,-27524712128⟩ : DyadicInterval 40),(⟨775885739680,775905880384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160584233152,160682695360⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188251138368,-188115916160⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2100_ok : ecellOkT e2100 = true := by decide +kernel
theorem e2100_pos {a z : ℝ} (ha1 : ((128823/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1289079/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2100 e2100_ok ha1 ha2 hz1 hz2 hz

-- box ['1289079/8192000', '161241/1024000', '3999/4000', '7999/8000']  interval_lower 186187111/1099511627776
noncomputable def e2101 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272528882368,0,true,160682695296,160682695360⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926494373184,0,false,-188251138368,-188251138304⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272642833220,0,true,160781148608,160781148672⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926380422332,0,false,-188386377216,-188386377152⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272485628054,0,true,160645321344,160645321408⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926537627498,0,false,-188199807808,-188199807744⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272621191820,0,true,160762451136,160762451200⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926402063732,0,false,-188360691520,-188360691456⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522638543,0,true,11010688,11010752⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500617009,0,false,-11010880,-11010816⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533665169,0,true,22037120,22037184⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489590383,0,false,-22037632,-22037568⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627334,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627666,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272507250706,0,true,160664004608,160664004672⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926516004846,0,false,-188225467456,-188225467392⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272632016898,0,true,160771803712,160771803776⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926391238654,0,false,-188373539456,-188373539392⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072253462993,0,false,-27601735744,-27601735680⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072292738229,0,false,-27561462848,-27561462784⟩
    { al := (1289079/8192000), au := (161241/1024000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨173017254592,173131205444⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160682695296,160682695360⟩ : DyadicInterval 40),(⟨-188251138368,-188251138304⟩ : DyadicInterval 40),(⟨748453791772,748453811101⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160781148608,160781148672⟩ : DyadicInterval 40),(⟨-188386377216,-188386377152⟩ : DyadicInterval 40),(⟨748435704383,748435723712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160645321344,160645321408⟩ : DyadicInterval 40),(⟨-188199807808,-188199807744⟩ : DyadicInterval 40),(⟨748460654371,748460673700⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160762451136,160762451200⟩ : DyadicInterval 40),(⟨-188360691520,-188360691456⟩ : DyadicInterval 40),(⟨748439140450,748439159779⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11010767,22037393⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11010688,11010752⟩ : DyadicInterval 40),(⟨-11010880,-11010816⟩ : DyadicInterval 40),(⟨762123383537,762123402866⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22037120,22037184⟩ : DyadicInterval 40),(⟨-22037632,-22037568⟩ : DyadicInterval 40),(⟨762123383366,762123402695⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨172995622930,173120389122⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160664004608,160664004672⟩ : DyadicInterval 40),(⟨-188225467456,-188225467392⟩ : DyadicInterval 40),(⟨748457223997,748457243327⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160771803712,160771803776⟩ : DyadicInterval 40),(⟨-188373539456,-188373539392⟩ : DyadicInterval 40),(⟨748437421752,748437441081⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27601735744,-27561462784⟩ : DyadicInterval 40),(⟨775904115008,775924270752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160682695296,160781148672⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188386377216,-188251138304⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2101_ok : ecellOkT e2101 = true := by decide +kernel
theorem e2101_pos {a z : ℝ} (ha1 : ((1289079/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((161241/1024000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2101 e2101_ok ha1 ha2 hz1 hz2 hz

-- box ['128823/819200', '1289079/8192000', '7999/8000', '1']  interval_lower 184909815/1099511627776
noncomputable def e2102 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272414931517,0,true,160584233152,160584233216⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926608324035,0,false,-188115916224,-188115916160⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272528882369,0,true,160682695296,160682695360⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926494373183,0,false,-188251138368,-188251138304⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272393318603,0,true,160565556992,160565557056⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926629936949,0,false,-188090270656,-188090270592⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522639109,0,true,11011264,11011328⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500616443,0,false,-11011392,-11011328⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627665,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1272404120521,0,true,160574891200,160574891264⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨926619135031,0,false,-188103088000,-188103087936⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1272528886737,0,true,160682699072,160682699136⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨926494368815,0,false,-188251143552,-188251143488⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1072285929436,0,false,-27568444480,-27568444416⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1072325181274,0,false,-27528196736,-27528196672⟩
    { al := (128823/819200), au := (1289079/8192000), zl := (7999/8000), zu := 1,
      A := ⟨172903303741,173017254593⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160584233152,160584233216⟩ : DyadicInterval 40),(⟨-188115916224,-188115916160⟩ : DyadicInterval 40),(⟨748471867090,748471886419⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160682695296,160682695360⟩ : DyadicInterval 40),(⟨-188251138368,-188251138304⟩ : DyadicInterval 40),(⟨748453791772,748453811101⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160565556992,160565557056⟩ : DyadicInterval 40),(⟨-188090270656,-188090270592⟩ : DyadicInterval 40),(⟨748475294019,748475313348⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160682695296,160682695360⟩ : DyadicInterval 40),(⟨-188251138368,-188251138304⟩ : DyadicInterval 40),(⟨748453791772,748453811101⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11011333⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11011264,11011328⟩ : DyadicInterval 40),(⟨-11011392,-11011328⟩ : DyadicInterval 40),(⟨762123383505,762123402834⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨172892492745,173017258961⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160574891200,160574891264⟩ : DyadicInterval 40),(⟨-188103088000,-188103087936⟩ : DyadicInterval 40),(⟨748473581331,748473600661⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160682699072,160682699136⟩ : DyadicInterval 40),(⟨-188251143552,-188251143488⟩ : DyadicInterval 40),(⟨748453791077,748453810407⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27568444480,-27528196672⟩ : DyadicInterval 40),(⟨775887481952,775907625120⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨160584233152,160682695360⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188251138368,-188115916160⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2102_ok : ecellOkT e2102 = true := by decide +kernel
theorem e2102_pos {a z : ℝ} (ha1 : ((128823/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1289079/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2102 e2102_ok ha1 ha2 hz1 hz2 hz

-- box ['1289079/8192000', '161241/1024000', '7999/8000', '1']  interval_lower 186026303/1099511627776
noncomputable def e2103 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272528882368,0,true,160682695296,160682695360⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926494373184,0,false,-188251138368,-188251138304⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272642833220,0,true,160781148608,160781148672⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926380422332,0,false,-188386377216,-188386377152⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272507255211,0,true,160664008448,160664008512⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926516000341,0,false,-188225472768,-188225472704⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522646627,0,true,11018752,11018816⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500608925,0,false,-11018944,-11018880⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627665,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1272518064248,0,true,160673347968,160673348032⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨926505191304,0,false,-188238300096,-188238300032⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1272642837585,0,true,160781152384,160781152448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨926380417967,0,false,-188386382400,-188386382336⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1072250055408,0,false,-27605229952,-27605229888⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1072289335347,0,false,-27564952128,-27564952064⟩
    { al := (1289079/8192000), au := (161241/1024000), zl := (7999/8000), zu := 1,
      A := ⟨173017254592,173131205444⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160682695296,160682695360⟩ : DyadicInterval 40),(⟨-188251138368,-188251138304⟩ : DyadicInterval 40),(⟨748453791772,748453811101⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160781148608,160781148672⟩ : DyadicInterval 40),(⟨-188386377216,-188386377152⟩ : DyadicInterval 40),(⟨748435704383,748435723712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160664008448,160664008512⟩ : DyadicInterval 40),(⟨-188225472768,-188225472704⟩ : DyadicInterval 40),(⟨748457223298,748457242628⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160781148608,160781148672⟩ : DyadicInterval 40),(⟨-188386377216,-188386377152⟩ : DyadicInterval 40),(⟨748435704383,748435723712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11018851⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11018752,11018816⟩ : DyadicInterval 40),(⟨-11018944,-11018880⟩ : DyadicInterval 40),(⟨762123383537,762123402866⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨173006436472,173131209809⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160673347968,160673348032⟩ : DyadicInterval 40),(⟨-188238300096,-188238300032⟩ : DyadicInterval 40),(⟨748455508318,748455527648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160781152384,160781152448⟩ : DyadicInterval 40),(⟨-188386382400,-188386382336⟩ : DyadicInterval 40),(⟨748435703689,748435723018⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27605229952,-27564952064⟩ : DyadicInterval 40),(⟨775905859648,775926017856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨160682695296,160781148672⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188386377216,-188251138304⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2103_ok : ecellOkT e2103 = true := by decide +kernel
theorem e2103_pos {a z : ℝ} (ha1 : ((1289079/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((161241/1024000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2103 e2103_ok ha1 ha2 hz1 hz2 hz

-- box ['161241/1024000', '1290777/8192000', '999/1000', '7993/8000']  interval_lower 94136323/549755813888
noncomputable def e2104 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272642833219,0,true,160781148608,160781148672⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926380422333,0,false,-188386377216,-188386377152⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272756784071,0,true,160879593088,160879593152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926266471481,0,false,-188521632640,-188521632576⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272469702013,0,true,160631560128,160631560192⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926553553539,0,false,-188180908672,-188180908608⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272605194560,0,true,160748629824,160748629888⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926418060992,0,false,-188341705152,-188341705088⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588756255,0,true,77125760,77125824⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434499297,0,false,-77131200,-77131136⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099599835513,0,true,88204160,88204224⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099423420039,0,false,-88211328,-88211264⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620699,0,false,-7104,-7040⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622366,0,false,-5440,-5376⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272556263843,0,true,160706353600,160706353664⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926466991709,0,false,-188283633664,-188283633600⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272680994279,0,true,160814117696,160814117760⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926342261273,0,false,-188431671104,-188431671040⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072238037631,0,false,-27617553344,-27617553280⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072277312727,0,false,-27577280000,-27577279936⟩
    { al := (161241/1024000), au := (1290777/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨173131205443,173245156295⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160781148608,160781148672⟩ : DyadicInterval 40),(⟨-188386377216,-188386377152⟩ : DyadicInterval 40),(⟨748435704383,748435723713⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160879593088,160879593152⟩ : DyadicInterval 40),(⟨-188521632640,-188521632576⟩ : DyadicInterval 40),(⟨748417604869,748417624198⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160631560128,160631560192⟩ : DyadicInterval 40),(⟨-188180908672,-188180908608⟩ : DyadicInterval 40),(⟨748463180670,748463199999⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160748629824,160748629888⟩ : DyadicInterval 40),(⟨-188341705152,-188341705088⟩ : DyadicInterval 40),(⟨748441680110,748441699440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨77128479,88207737⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77125760,77125824⟩ : DyadicInterval 40),(⟨-77131200,-77131136⟩ : DyadicInterval 40),(⟨762123380861,762123400190⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨88204160,88204224⟩ : DyadicInterval 40),(⟨-88211328,-88211264⟩ : DyadicInterval 40),(⟨762123380059,762123399388⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7104,-5376⟩ : DyadicInterval 40),(⟨762123386304,762123406432⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173044636067,173169366503⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160706353600,160706353664⟩ : DyadicInterval 40),(⟨-188283633664,-188283633600⟩ : DyadicInterval 40),(⟨748449446648,748449465978⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160814117696,160814117760⟩ : DyadicInterval 40),(⟨-188431671104,-188431671040⟩ : DyadicInterval 40),(⟨748429644378,748429663707⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27617553344,-27577279936⟩ : DyadicInterval 40),(⟨775912023584,775932179552⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160781148608,160879593152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188521632640,-188386377152⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2104_ok : ecellOkT e2104 = true := by decide +kernel
theorem e2104_pos {a z : ℝ} (ha1 : ((161241/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1290777/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2104 e2104_ok ha1 ha2 hz1 hz2 hz

-- box ['1290777/8192000', '645813/4096000', '999/1000', '7993/8000']  interval_lower 189397125/1099511627776
noncomputable def e2105 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272756784070,0,true,160879593088,160879593152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926266471482,0,false,-188521632640,-188521632576⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272870734922,0,true,160978028736,160978028800⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926152520630,0,false,-188656904704,-188656904640⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272583538913,0,true,160729919552,160729919616⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926439716639,0,false,-188316003648,-188316003584⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272719045704,0,true,160846991104,160846991168⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926304209848,0,false,-188476836736,-188476836672⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588808883,0,true,77178368,77178432⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434446669,0,false,-77183872,-77183808⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099599895665,0,true,88264320,88264384⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099423359887,0,false,-88271488,-88271424⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620689,0,false,-7104,-7040⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622359,0,false,-5440,-5376⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272670157714,0,true,160804755584,160804755648⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926353097838,0,false,-188418808832,-188418808768⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272794895277,0,true,160912516160,160912516224⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926228360275,0,false,-188566872960,-188566872896⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072202147787,0,false,-27654356736,-27654356672⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072241450970,0,false,-27614053248,-27614053184⟩
    { al := (1290777/8192000), au := (645813/4096000), zl := (999/1000), zu := (7993/8000),
      A := ⟨173245156294,173359107146⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160879593088,160879593152⟩ : DyadicInterval 40),(⟨-188521632640,-188521632576⟩ : DyadicInterval 40),(⟨748417604869,748417624198⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160978028736,160978028800⟩ : DyadicInterval 40),(⟨-188656904704,-188656904640⟩ : DyadicInterval 40),(⟨748399493255,748399512585⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160729919552,160729919616⟩ : DyadicInterval 40),(⟨-188316003648,-188316003584⟩ : DyadicInterval 40),(⟨748445117667,748445136997⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160846991104,160846991168⟩ : DyadicInterval 40),(⟨-188476836736,-188476836672⟩ : DyadicInterval 40),(⟨748423600423,748423619753⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨77181107,88267889⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77178368,77178432⟩ : DyadicInterval 40),(⟨-77183872,-77183808⟩ : DyadicInterval 40),(⟨762123380886,762123400215⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨88264320,88264384⟩ : DyadicInterval 40),(⟨-88271488,-88271424⟩ : DyadicInterval 40),(⟨762123380049,762123399379⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7104,-5376⟩ : DyadicInterval 40),(⟨762123386304,762123406432⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173158529938,173283267501⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160804755584,160804755648⟩ : DyadicInterval 40),(⟨-188418808832,-188418808768⟩ : DyadicInterval 40),(⟨748431365369,748431384699⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160912516160,160912516224⟩ : DyadicInterval 40),(⟨-188566872960,-188566872896⟩ : DyadicInterval 40),(⟨748411548747,748411568077⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27654356736,-27614053184⟩ : DyadicInterval 40),(⟨775930410208,775950581248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160879593088,160978028800⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188656904704,-188521632576⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2105_ok : ecellOkT e2105 = true := by decide +kernel
theorem e2105_pos {a z : ℝ} (ha1 : ((1290777/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((645813/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2105 e2105_ok ha1 ha2 hz1 hz2 hz

-- box ['161241/1024000', '1290777/8192000', '7993/8000', '3997/4000']  interval_lower 188111651/1099511627776
noncomputable def e2106 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272642833219,0,true,160781148608,160781148672⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926380422333,0,false,-188386377216,-188386377152⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272756784071,0,true,160879593088,160879593152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926266471481,0,false,-188521632640,-188521632576⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272491343414,0,true,160650259776,160650259840⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926531912138,0,false,-188206590144,-188206590080⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272626850204,0,true,160767339840,160767339904⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926396405348,0,false,-188367407296,-188367407232⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577738016,0,true,66108224,66108288⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445517536,0,false,-66112256,-66112192⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588809755,0,true,77179264,77179328⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434445797,0,false,-77184704,-77184640⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622358,0,false,-5440,-5376⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623801,0,false,-4032,-3968⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272567084358,0,true,160715702720,160715702784⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926456171194,0,false,-188296475328,-188296475264⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272691821943,0,true,160823472064,160823472128⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926331433609,0,false,-188444522944,-188444522880⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072234626883,0,false,-27621050880,-27621050816⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072273906686,0,false,-27580772544,-27580772480⟩
    { al := (161241/1024000), au := (1290777/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨173131205443,173245156295⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160781148608,160781148672⟩ : DyadicInterval 40),(⟨-188386377216,-188386377152⟩ : DyadicInterval 40),(⟨748435704383,748435723713⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160879593088,160879593152⟩ : DyadicInterval 40),(⟨-188521632640,-188521632576⟩ : DyadicInterval 40),(⟨748417604869,748417624198⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160650259776,160650259840⟩ : DyadicInterval 40),(⟨-188206590144,-188206590080⟩ : DyadicInterval 40),(⟨748459747679,748459767008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160767339840,160767339904⟩ : DyadicInterval 40),(⟨-188367407296,-188367407232⟩ : DyadicInterval 40),(⟨748438242098,748438261427⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨66110240,77181979⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66108224,66108288⟩ : DyadicInterval 40),(⟨-66112256,-66112192⟩ : DyadicInterval 40),(⟨762123381592,762123400922⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77179264,77179328⟩ : DyadicInterval 40),(⟨-77184704,-77184640⟩ : DyadicInterval 40),(⟨762123380853,762123400183⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5440,-3968⟩ : DyadicInterval 40),(⟨762123385600,762123405600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173055456582,173180194167⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160715702720,160715702784⟩ : DyadicInterval 40),(⟨-188296475328,-188296475264⟩ : DyadicInterval 40),(⟨748447729343,748447748672⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160823472064,160823472128⟩ : DyadicInterval 40),(⟨-188444522944,-188444522880⟩ : DyadicInterval 40),(⟨748427924669,748427943998⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27621050880,-27580772480⟩ : DyadicInterval 40),(⟨775913769856,775933928320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160781148608,160879593152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188521632640,-188386377152⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2106_ok : ecellOkT e2106 = true := by decide +kernel
theorem e2106_pos {a z : ℝ} (ha1 : ((161241/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1290777/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2106 e2106_ok ha1 ha2 hz1 hz2 hz

-- box ['1290777/8192000', '645813/4096000', '7993/8000', '3997/4000']  interval_lower 94617895/549755813888
noncomputable def e2107 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272756784070,0,true,160879593088,160879593152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926266471482,0,false,-188521632640,-188521632576⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272870734922,0,true,160978028736,160978028800⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926152520630,0,false,-188656904704,-188656904640⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272605194558,0,true,160748629824,160748629888⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926418060994,0,false,-188341705152,-188341705088⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272740715592,0,true,160865711744,160865711808⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926282539960,0,false,-188502558912,-188502558848⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577783126,0,true,66153344,66153408⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445472426,0,false,-66157376,-66157312⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588862389,0,true,77231872,77231936⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434393163,0,false,-77237376,-77237312⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622350,0,false,-5440,-5376⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623796,0,false,-4032,-3968⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272680985353,0,true,160814110016,160814110080⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926342270199,0,false,-188431660544,-188431660480⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272805730064,0,true,160921875840,160921875904⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926217525488,0,false,-188579734848,-188579734784⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072198732551,0,false,-27657858944,-27657858880⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072238040444,0,false,-27617550464,-27617550400⟩
    { al := (1290777/8192000), au := (645813/4096000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨173245156294,173359107146⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160879593088,160879593152⟩ : DyadicInterval 40),(⟨-188521632640,-188521632576⟩ : DyadicInterval 40),(⟨748417604869,748417624198⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160978028736,160978028800⟩ : DyadicInterval 40),(⟨-188656904704,-188656904640⟩ : DyadicInterval 40),(⟨748399493255,748399512585⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160748629824,160748629888⟩ : DyadicInterval 40),(⟨-188341705152,-188341705088⟩ : DyadicInterval 40),(⟨748441680111,748441699440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160865711744,160865711808⟩ : DyadicInterval 40),(⟨-188502558912,-188502558848⟩ : DyadicInterval 40),(⟨748420157837,748420177167⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨66155350,77234613⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66153344,66153408⟩ : DyadicInterval 40),(⟨-66157376,-66157312⟩ : DyadicInterval 40),(⟨762123381587,762123400916⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77231872,77231936⟩ : DyadicInterval 40),(⟨-77237376,-77237312⟩ : DyadicInterval 40),(⟨762123380878,762123400207⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5440,-3968⟩ : DyadicInterval 40),(⟨762123385600,762123405600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173169357577,173294102288⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160814110016,160814110080⟩ : DyadicInterval 40),(⟨-188431660544,-188431660480⟩ : DyadicInterval 40),(⟨748429645792,748429665121⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160921875840,160921875904⟩ : DyadicInterval 40),(⟨-188579734848,-188579734784⟩ : DyadicInterval 40),(⟨748409826763,748409846092⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27657858944,-27617550400⟩ : DyadicInterval 40),(⟨775932158816,775952332352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160879593088,160978028800⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188656904704,-188521632576⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2107_ok : ecellOkT e2107 = true := by decide +kernel
theorem e2107_pos {a z : ℝ} (ha1 : ((1290777/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((645813/4096000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2107 e2107_ok ha1 ha2 hz1 hz2 hz

-- box ['645813/4096000', '51699/327680', '999/1000', '7993/8000']  interval_lower 47631031/274877906944
noncomputable def e2108 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272870734921,0,true,160978028736,160978028800⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926152520631,0,false,-188656904704,-188656904640⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272984685773,0,true,161076455616,161076455680⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926038569779,0,false,-188792193472,-188792193408⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272697375813,0,true,160828270144,160828270208⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926325879739,0,false,-188451115136,-188451115072⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272832896848,0,true,160945343552,160945343616⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926190358704,0,false,-188611984960,-188611984896⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588861517,0,true,77230976,77231040⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434394035,0,false,-77236480,-77236416⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099599955822,0,true,88324480,88324544⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099423299730,0,false,-88331648,-88331584⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620680,0,false,-7104,-7040⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622351,0,false,-5440,-5376⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272784051588,0,true,160903148736,160903148800⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926239203964,0,false,-188554000640,-188554000576⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272908796273,0,true,161010905856,161010905920⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926114459279,0,false,-188702091392,-188702091328⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072166234345,0,false,-27691185536,-27691185472⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072205565617,0,false,-27650851840,-27650851776⟩
    { al := (645813/4096000), au := (51699/327680), zl := (999/1000), zu := (7993/8000),
      A := ⟨173359107145,173473057997⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160978028736,160978028800⟩ : DyadicInterval 40),(⟨-188656904704,-188656904640⟩ : DyadicInterval 40),(⟨748399493255,748399512585⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161076455616,161076455680⟩ : DyadicInterval 40),(⟨-188792193472,-188792193408⟩ : DyadicInterval 40),(⟨748381369531,748381388860⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160828270144,160828270208⟩ : DyadicInterval 40),(⟨-188451115136,-188451115072⟩ : DyadicInterval 40),(⟨748427042561,748427061891⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160945343552,160945343616⟩ : DyadicInterval 40),(⟨-188611984960,-188611984896⟩ : DyadicInterval 40),(⟨748405508679,748405528008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨77233741,88328046⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77230976,77231040⟩ : DyadicInterval 40),(⟨-77236480,-77236416⟩ : DyadicInterval 40),(⟨762123380878,762123400208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨88324480,88324544⟩ : DyadicInterval 40),(⟨-88331648,-88331584⟩ : DyadicInterval 40),(⟨762123380039,762123399369⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7104,-5376⟩ : DyadicInterval 40),(⟨762123386304,762123406432⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173272423812,173397168497⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160903148736,160903148800⟩ : DyadicInterval 40),(⟨-188554000640,-188554000576⟩ : DyadicInterval 40),(⟨748413272015,748413291345⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161010905856,161010905920⟩ : DyadicInterval 40),(⟨-188702091392,-188702091328⟩ : DyadicInterval 40),(⟨748393440973,748393460303⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27691185536,-27650851776⟩ : DyadicInterval 40),(⟨775948809504,775968995648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160978028736,161076455680⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188792193472,-188656904640⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2108_ok : ecellOkT e2108 = true := by decide +kernel
theorem e2108_pos {a z : ℝ} (ha1 : ((645813/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((51699/327680 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2108 e2108_ok ha1 ha2 hz1 hz2 hz

-- box ['51699/327680', '323331/2048000', '999/1000', '7993/8000']  interval_lower 191653961/1099511627776
noncomputable def e2109 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272984685772,0,true,161076455616,161076455680⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926038569780,0,false,-188792193472,-188792193408⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273098636624,0,true,161174873664,161174873728⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925924618928,0,false,-188927498816,-188927498752⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272811212713,0,true,160926612032,160926612096⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926212042839,0,false,-188586243264,-188586243200⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272946747992,0,true,161043687232,161043687296⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926076507560,0,false,-188747149760,-188747149696⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588914153,0,true,77283648,77283712⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434341399,0,false,-77289152,-77289088⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099600015982,0,true,88384640,88384704⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099423239570,0,false,-88391808,-88391744⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620670,0,false,-7168,-7104⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622344,0,false,-5440,-5376⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272897945463,0,true,161001533120,161001533184⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926125310089,0,false,-188689209088,-188689209024⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273022697273,0,true,161109286720,161109286784⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926000558279,0,false,-188837326464,-188837326400⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072130297303,0,false,-27728039744,-27728039680⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072169656667,0,false,-27687675904,-27687675840⟩
    { al := (51699/327680), au := (323331/2048000), zl := (999/1000), zu := (7993/8000),
      A := ⟨173473057996,173587008848⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161076455616,161076455680⟩ : DyadicInterval 40),(⟨-188792193472,-188792193408⟩ : DyadicInterval 40),(⟨748381369531,748381388860⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161174873664,161174873728⟩ : DyadicInterval 40),(⟨-188927498816,-188927498752⟩ : DyadicInterval 40),(⟨748363233677,748363253007⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160926612032,160926612096⟩ : DyadicInterval 40),(⟨-188586243264,-188586243200⟩ : DyadicInterval 40),(⟨748408955331,748408974661⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161043687232,161043687296⟩ : DyadicInterval 40),(⟨-188747149760,-188747149696⟩ : DyadicInterval 40),(⟨748387404812,748387424142⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨77286377,88388206⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77283648,77283712⟩ : DyadicInterval 40),(⟨-77289152,-77289088⟩ : DyadicInterval 40),(⟨762123380871,762123400200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨88384640,88384704⟩ : DyadicInterval 40),(⟨-88391808,-88391744⟩ : DyadicInterval 40),(⟨762123380030,762123399359⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7168,-5376⟩ : DyadicInterval 40),(⟨762123386304,762123406464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173386317687,173511069497⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161001533120,161001533184⟩ : DyadicInterval 40),(⟨-188689209088,-188689209024⟩ : DyadicInterval 40),(⟨748395166548,748395185877⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161109286720,161109286784⟩ : DyadicInterval 40),(⟨-188837326464,-188837326400⟩ : DyadicInterval 40),(⟨748375321119,748375340449⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27728039744,-27687675840⟩ : DyadicInterval 40),(⟨775967221536,775987422752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161076455616,161174873728⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188927498816,-188792193408⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2109_ok : ecellOkT e2109 = true := by decide +kernel
theorem e2109_pos {a z : ℝ} (ha1 : ((51699/327680 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((323331/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2109 e2109_ok ha1 ha2 hz1 hz2 hz

-- box ['645813/4096000', '51699/327680', '7993/8000', '3997/4000']  interval_lower 190362691/1099511627776
noncomputable def e2110 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272870734921,0,true,160978028736,160978028800⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926152520631,0,false,-188656904704,-188656904640⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272984685773,0,true,161076455616,161076455680⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926038569779,0,false,-188792193472,-188792193408⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272719045702,0,true,160846991104,160846991168⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926304209850,0,false,-188476836736,-188476836672⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272854580980,0,true,160964074816,160964074880⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926168674572,0,false,-188637727232,-188637727168⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577828241,0,true,66198464,66198528⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445427311,0,false,-66202496,-66202432⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588915026,0,true,77284480,77284544⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434340526,0,false,-77289984,-77289920⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622343,0,false,-5440,-5376⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623791,0,false,-4032,-3968⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272794886349,0,true,160912508480,160912508544⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926228369203,0,false,-188566862336,-188566862272⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272919638180,0,true,161020270784,161020270848⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926103617372,0,false,-188714963328,-188714963264⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072162814618,0,false,-27694692480,-27694692416⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072202150602,0,false,-27654353856,-27654353792⟩
    { al := (645813/4096000), au := (51699/327680), zl := (7993/8000), zu := (3997/4000),
      A := ⟨173359107145,173473057997⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160978028736,160978028800⟩ : DyadicInterval 40),(⟨-188656904704,-188656904640⟩ : DyadicInterval 40),(⟨748399493255,748399512585⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161076455616,161076455680⟩ : DyadicInterval 40),(⟨-188792193472,-188792193408⟩ : DyadicInterval 40),(⟨748381369531,748381388860⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160846991104,160846991168⟩ : DyadicInterval 40),(⟨-188476836736,-188476836672⟩ : DyadicInterval 40),(⟨748423600423,748423619753⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160964074816,160964074880⟩ : DyadicInterval 40),(⟨-188637727232,-188637727168⟩ : DyadicInterval 40),(⟨748402061541,748402080870⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨66200465,77287250⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66198464,66198528⟩ : DyadicInterval 40),(⟨-66202496,-66202432⟩ : DyadicInterval 40),(⟨762123381582,762123400911⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77284480,77284544⟩ : DyadicInterval 40),(⟨-77289984,-77289920⟩ : DyadicInterval 40),(⟨762123380871,762123400200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5440,-3968⟩ : DyadicInterval 40),(⟨762123385600,762123405600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173283258573,173408010404⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160912508480,160912508544⟩ : DyadicInterval 40),(⟨-188566862336,-188566862272⟩ : DyadicInterval 40),(⟨748411550136,748411569466⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161020270784,161020270848⟩ : DyadicInterval 40),(⟨-188714963328,-188714963264⟩ : DyadicInterval 40),(⟨748391716749,748391736078⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27694692480,-27654353792⟩ : DyadicInterval 40),(⟨775950560512,775970749120⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160978028736,161076455680⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188792193472,-188656904640⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2110_ok : ecellOkT e2110 = true := by decide +kernel
theorem e2110_pos {a z : ℝ} (ha1 : ((645813/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((51699/327680 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2110 e2110_ok ha1 ha2 hz1 hz2 hz

-- box ['51699/327680', '323331/2048000', '7993/8000', '3997/4000']  interval_lower 191492057/1099511627776
noncomputable def e2111 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272984685772,0,true,161076455616,161076455680⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926038569780,0,false,-188792193472,-188792193408⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273098636624,0,true,161174873664,161174873728⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925924618928,0,false,-188927498816,-188927498752⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272832896846,0,true,160945343552,160945343616⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926190358706,0,false,-188611984960,-188611984896⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272968446368,0,true,161062429120,161062429184⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926054809184,0,false,-188772912128,-188772912064⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577873357,0,true,66243584,66243648⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445382195,0,false,-66247616,-66247552⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588967667,0,true,77337152,77337216⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434287885,0,false,-77342656,-77342592⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622335,0,false,-5504,-5440⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623785,0,false,-4032,-3968⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272908787342,0,true,161010898112,161010898176⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926114468210,0,false,-188702080768,-188702080704⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273033546301,0,true,161118656960,161118657024⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925989709251,0,false,-188850208448,-188850208384⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072126873083,0,false,-27731551424,-27731551360⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072166237163,0,false,-27691182656,-27691182592⟩
    { al := (51699/327680), au := (323331/2048000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨173473057996,173587008848⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161076455616,161076455680⟩ : DyadicInterval 40),(⟨-188792193472,-188792193408⟩ : DyadicInterval 40),(⟨748381369531,748381388860⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161174873664,161174873728⟩ : DyadicInterval 40),(⟨-188927498816,-188927498752⟩ : DyadicInterval 40),(⟨748363233677,748363253007⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160945343552,160945343616⟩ : DyadicInterval 40),(⟨-188611984960,-188611984896⟩ : DyadicInterval 40),(⟨748405508679,748405528009⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161062429120,161062429184⟩ : DyadicInterval 40),(⟨-188772912128,-188772912064⟩ : DyadicInterval 40),(⟨748383953116,748383972445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨66245581,77339891⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66243584,66243648⟩ : DyadicInterval 40),(⟨-66247616,-66247552⟩ : DyadicInterval 40),(⟨762123381576,762123400905⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77337152,77337216⟩ : DyadicInterval 40),(⟨-77342656,-77342592⟩ : DyadicInterval 40),(⟨762123380863,762123400193⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5504,-3968⟩ : DyadicInterval 40),(⟨762123385600,762123405632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173397159566,173521918525⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161010898112,161010898176⟩ : DyadicInterval 40),(⟨-188702080768,-188702080704⟩ : DyadicInterval 40),(⟨748393442402,748393461732⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161118656960,161118657024⟩ : DyadicInterval 40),(⟨-188850208448,-188850208384⟩ : DyadicInterval 40),(⟨748373594614,748373613944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27731551424,-27691182592⟩ : DyadicInterval 40),(⟨775968974912,775989178592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161076455616,161174873728⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188927498816,-188792193408⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2111_ok : ecellOkT e2111 = true := by decide +kernel
theorem e2111_pos {a z : ℝ} (ha1 : ((51699/327680 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((323331/2048000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2111 e2111_ok ha1 ha2 hz1 hz2 hz

-- box ['161241/1024000', '1290777/8192000', '3997/4000', '1599/1600']  interval_lower 187950693/1099511627776
noncomputable def e2112 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272642833219,0,true,160781148608,160781148672⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926380422333,0,false,-188386377216,-188386377152⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272756784071,0,true,160879593088,160879593152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926266471481,0,false,-188521632640,-188521632576⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272512984814,0,true,160668959104,160668959168⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926510270738,0,false,-188232272256,-188232272192⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272648505849,0,true,160786049472,160786049536⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926374749703,0,false,-188393110016,-188393109952⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566719726,0,true,55090560,55090624⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456535826,0,false,-55093376,-55093312⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577783947,0,true,66154176,66154240⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445471605,0,false,-66158208,-66158144⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623795,0,false,-4032,-3968⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625016,0,false,-2816,-2752⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272577904895,0,true,160725051712,160725051776⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926445350657,0,false,-188309317120,-188309317056⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272702649628,0,true,160832826304,160832826368⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926320605924,0,false,-188457374976,-188457374912⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072231215916,0,false,-27624548608,-27624548544⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072270500426,0,false,-27584265344,-27584265280⟩
    { al := (161241/1024000), au := (1290777/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨173131205443,173245156295⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160781148608,160781148672⟩ : DyadicInterval 40),(⟨-188386377216,-188386377152⟩ : DyadicInterval 40),(⟨748435704383,748435723713⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160879593088,160879593152⟩ : DyadicInterval 40),(⟨-188521632640,-188521632576⟩ : DyadicInterval 40),(⟨748417604869,748417624198⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160668959104,160668959168⟩ : DyadicInterval 40),(⟨-188232272256,-188232272192⟩ : DyadicInterval 40),(⟨748456314269,748456333598⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160786049472,160786049536⟩ : DyadicInterval 40),(⟨-188393110016,-188393109952⟩ : DyadicInterval 40),(⟨748434803674,748434823003⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨55091950,66156171⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55090560,55090624⟩ : DyadicInterval 40),(⟨-55093376,-55093312⟩ : DyadicInterval 40),(⟨762123382199,762123401528⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66154176,66154240⟩ : DyadicInterval 40),(⟨-66158208,-66158144⟩ : DyadicInterval 40),(⟨762123381587,762123400916⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4032,-2752⟩ : DyadicInterval 40),(⟨762123384992,762123404896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173066277119,173191021852⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160725051712,160725051776⟩ : DyadicInterval 40),(⟨-188309317120,-188309317056⟩ : DyadicInterval 40),(⟨748446011944,748446031273⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160832826304,160832826368⟩ : DyadicInterval 40),(⟨-188457374976,-188457374912⟩ : DyadicInterval 40),(⟨748426204892,748426224222⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27624548608,-27584265280⟩ : DyadicInterval 40),(⟨775915516256,775935677184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160781148608,160879593152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188521632640,-188386377152⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2112_ok : ecellOkT e2112 = true := by decide +kernel
theorem e2112_pos {a z : ℝ} (ha1 : ((161241/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1290777/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2112 e2112_ok ha1 ha2 hz1 hz2 hz

-- box ['1290777/8192000', '645813/4096000', '3997/4000', '1599/1600']  interval_lower 47268623/274877906944
noncomputable def e2113 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272756784070,0,true,160879593088,160879593152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926266471482,0,false,-188521632640,-188521632576⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272870734922,0,true,160978028736,160978028800⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926152520630,0,false,-188656904704,-188656904640⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272626850202,0,true,160767339840,160767339904⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926396405350,0,false,-188367407296,-188367407232⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272762385481,0,true,160884432000,160884432064⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926260870071,0,false,-188528281728,-188528281664⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566757319,0,true,55128128,55128192⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456498233,0,false,-55130944,-55130880⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577829062,0,true,66199232,66199296⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445426490,0,false,-66203328,-66203264⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623790,0,false,-4032,-3968⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625012,0,false,-2816,-2752⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272691813017,0,true,160823464320,160823464384⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926331442535,0,false,-188444512384,-188444512320⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272816564870,0,true,160931235456,160931235520⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926206690682,0,false,-188592596864,-188592596800⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072195317095,0,false,-27661361408,-27661361344⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072234629696,0,false,-27621048000,-27621047936⟩
    { al := (1290777/8192000), au := (645813/4096000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨173245156294,173359107146⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160879593088,160879593152⟩ : DyadicInterval 40),(⟨-188521632640,-188521632576⟩ : DyadicInterval 40),(⟨748417604869,748417624198⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160978028736,160978028800⟩ : DyadicInterval 40),(⟨-188656904704,-188656904640⟩ : DyadicInterval 40),(⟨748399493255,748399512585⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160767339840,160767339904⟩ : DyadicInterval 40),(⟨-188367407296,-188367407232⟩ : DyadicInterval 40),(⟨748438242098,748438261427⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160884432000,160884432064⟩ : DyadicInterval 40),(⟨-188528281728,-188528281664⟩ : DyadicInterval 40),(⟨748416714867,748416734197⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨55129543,66201286⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55128128,55128192⟩ : DyadicInterval 40),(⟨-55130944,-55130880⟩ : DyadicInterval 40),(⟨762123382195,762123401524⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66199232,66199296⟩ : DyadicInterval 40),(⟨-66203328,-66203264⟩ : DyadicInterval 40),(⟨762123381613,762123400943⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4032,-2752⟩ : DyadicInterval 40),(⟨762123384992,762123404896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173180185241,173304937094⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160823464320,160823464384⟩ : DyadicInterval 40),(⟨-188444512384,-188444512320⟩ : DyadicInterval 40),(⟨748427926120,748427945449⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160931235456,160931235520⟩ : DyadicInterval 40),(⟨-188592596864,-188592596800⟩ : DyadicInterval 40),(⟨748408104648,748408123977⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27661361408,-27621047936⟩ : DyadicInterval 40),(⟨775933907584,775954083584⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160879593088,160978028800⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188656904704,-188521632576⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2113_ok : ecellOkT e2113 = true := by decide +kernel
theorem e2113_pos {a z : ℝ} (ha1 : ((1290777/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((645813/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2113 e2113_ok ha1 ha2 hz1 hz2 hz

-- box ['161241/1024000', '1290777/8192000', '1599/1600', '1999/2000']  interval_lower 187789805/1099511627776
noncomputable def e2114 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272642833219,0,true,160781148608,160781148672⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926380422333,0,false,-188386377216,-188386377152⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272756784071,0,true,160879593088,160879593152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926266471481,0,false,-188521632640,-188521632576⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272534626215,0,true,160687658176,160687658240⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926488629337,0,false,-188257954880,-188257954816⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272670161493,0,true,160804758848,160804758912⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926353094059,0,false,-188418813312,-188418813248⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555701386,0,true,44072704,44072768⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467554166,0,false,-44074496,-44074432⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566758088,0,true,55128896,55128960⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456497464,0,false,-55131712,-55131648⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625011,0,false,-2816,-2752⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626010,0,false,-1792,-1728⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272588725466,0,true,160734400704,160734400768⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926434530086,0,false,-188322159104,-188322159040⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272713477343,0,true,160842180544,160842180608⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926309778209,0,false,-188470227200,-188470227136⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072227804726,0,false,-27628046592,-27628046528⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072267093942,0,false,-27587758400,-27587758336⟩
    { al := (161241/1024000), au := (1290777/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨173131205443,173245156295⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160781148608,160781148672⟩ : DyadicInterval 40),(⟨-188386377216,-188386377152⟩ : DyadicInterval 40),(⟨748435704383,748435723713⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160879593088,160879593152⟩ : DyadicInterval 40),(⟨-188521632640,-188521632576⟩ : DyadicInterval 40),(⟨748417604869,748417624198⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160687658176,160687658240⟩ : DyadicInterval 40),(⟨-188257954880,-188257954816⟩ : DyadicInterval 40),(⟨748452880349,748452899679⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160804758848,160804758912⟩ : DyadicInterval 40),(⟨-188418813312,-188418813248⟩ : DyadicInterval 40),(⟨748431364767,748431384097⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨44073610,55130312⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44072704,44072768⟩ : DyadicInterval 40),(⟨-44074496,-44074432⟩ : DyadicInterval 40),(⟨762123382681,762123402010⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55128896,55128960⟩ : DyadicInterval 40),(⟨-55131712,-55131648⟩ : DyadicInterval 40),(⟨762123382195,762123401524⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2816,-1728⟩ : DyadicInterval 40),(⟨762123384480,762123404288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173077097690,173201849567⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160734400704,160734400768⟩ : DyadicInterval 40),(⟨-188322159104,-188322159040⟩ : DyadicInterval 40),(⟨748444294401,748444313731⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160842180544,160842180608⟩ : DyadicInterval 40),(⟨-188470227200,-188470227136⟩ : DyadicInterval 40),(⟨748424484974,748424504304⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27628046592,-27587758336⟩ : DyadicInterval 40),(⟨775917262784,775937426176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160781148608,160879593152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188521632640,-188386377152⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2114_ok : ecellOkT e2114 = true := by decide +kernel
theorem e2114_pos {a z : ℝ} (ha1 : ((161241/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1290777/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2114 e2114_ok ha1 ha2 hz1 hz2 hz

-- box ['1290777/8192000', '645813/4096000', '1599/1600', '1999/2000']  interval_lower 94456525/549755813888
noncomputable def e2115 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272756784070,0,true,160879593088,160879593152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926266471482,0,false,-188521632640,-188521632576⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272870734922,0,true,160978028736,160978028800⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926152520630,0,false,-188656904704,-188656904640⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272648505847,0,true,160786049472,160786049536⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926374749705,0,false,-188393110016,-188393109952⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272784055369,0,true,160903152000,160903152064⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926239200183,0,false,-188554005120,-188554005056⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555731460,0,true,44102784,44102848⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467524092,0,false,-44104576,-44104512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566795684,0,true,55166464,55166528⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456459868,0,false,-55169344,-55169280⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625007,0,false,-2816,-2752⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626007,0,false,-1792,-1728⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272702640702,0,true,160832818624,160832818688⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926320614850,0,false,-188457364416,-188457364352⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272827399705,0,true,160940594944,160940595008⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926195855847,0,false,-188605459136,-188605459072⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072191901417,0,false,-27664864128,-27664864064⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072231218729,0,false,-27624545728,-27624545664⟩
    { al := (1290777/8192000), au := (645813/4096000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨173245156294,173359107146⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160879593088,160879593152⟩ : DyadicInterval 40),(⟨-188521632640,-188521632576⟩ : DyadicInterval 40),(⟨748417604869,748417624198⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160978028736,160978028800⟩ : DyadicInterval 40),(⟨-188656904704,-188656904640⟩ : DyadicInterval 40),(⟨748399493255,748399512585⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160786049472,160786049536⟩ : DyadicInterval 40),(⟨-188393110016,-188393109952⟩ : DyadicInterval 40),(⟨748434803675,748434823004⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160903152000,160903152064⟩ : DyadicInterval 40),(⟨-188554005120,-188554005056⟩ : DyadicInterval 40),(⟨748413271412,748413290742⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨44103684,55167908⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44102784,44102848⟩ : DyadicInterval 40),(⟨-44104576,-44104512⟩ : DyadicInterval 40),(⟨762123382678,762123402007⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55166464,55166528⟩ : DyadicInterval 40),(⟨-55169344,-55169280⟩ : DyadicInterval 40),(⟨762123382223,762123401553⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2816,-1728⟩ : DyadicInterval 40),(⟨762123384480,762123404288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173191012926,173315771929⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160832818624,160832818688⟩ : DyadicInterval 40),(⟨-188457364416,-188457364352⟩ : DyadicInterval 40),(⟨748426206307,748426225637⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160940594944,160940595008⟩ : DyadicInterval 40),(⟨-188605459136,-188605459072⟩ : DyadicInterval 40),(⟨748406382491,748406401820⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27664864128,-27624545664⟩ : DyadicInterval 40),(⟨775935656448,775955834944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160879593088,160978028800⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188656904704,-188521632576⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2115_ok : ecellOkT e2115 = true := by decide +kernel
theorem e2115_pos {a z : ℝ} (ha1 : ((1290777/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((645813/4096000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2115 e2115_ok ha1 ha2 hz1 hz2 hz

-- box ['645813/4096000', '51699/327680', '3997/4000', '1599/1600']  interval_lower 185743/1073741824
noncomputable def e2116 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272870734921,0,true,160978028736,160978028800⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926152520631,0,false,-188656904704,-188656904640⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272984685773,0,true,161076455616,161076455680⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926038569779,0,false,-188792193472,-188792193408⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272740715590,0,true,160865711744,160865711808⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926282539962,0,false,-188502558912,-188502558848⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272876265112,0,true,160982805760,160982805824⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926146990440,0,false,-188663470080,-188663470016⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566794914,0,true,55165696,55165760⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456460638,0,false,-55168576,-55168512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577874179,0,true,66244352,66244416⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445381373,0,false,-66248448,-66248384⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623784,0,false,-4032,-3968⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625009,0,false,-2816,-2752⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272805721135,0,true,160921868096,160921868160⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926217534417,0,false,-188579724224,-188579724160⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272930480113,0,true,161029635712,161029635776⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926092775439,0,false,-188727835392,-188727835328⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072159394669,0,false,-27698199680,-27698199616⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072198735366,0,false,-27657856064,-27657856000⟩
    { al := (645813/4096000), au := (51699/327680), zl := (3997/4000), zu := (1599/1600),
      A := ⟨173359107145,173473057997⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160978028736,160978028800⟩ : DyadicInterval 40),(⟨-188656904704,-188656904640⟩ : DyadicInterval 40),(⟨748399493255,748399512585⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161076455616,161076455680⟩ : DyadicInterval 40),(⟨-188792193472,-188792193408⟩ : DyadicInterval 40),(⟨748381369531,748381388860⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160865711744,160865711808⟩ : DyadicInterval 40),(⟨-188502558912,-188502558848⟩ : DyadicInterval 40),(⟨748420157838,748420177167⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160982805760,160982805824⟩ : DyadicInterval 40),(⟨-188663470080,-188663470016⟩ : DyadicInterval 40),(⟨748398613954,748398633283⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨55167138,66246403⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55165696,55165760⟩ : DyadicInterval 40),(⟨-55168576,-55168512⟩ : DyadicInterval 40),(⟨762123382223,762123401553⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66244352,66244416⟩ : DyadicInterval 40),(⟨-66248448,-66248384⟩ : DyadicInterval 40),(⟨762123381608,762123400937⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4032,-2752⟩ : DyadicInterval 40),(⟨762123384992,762123404896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173294093359,173418852337⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160921868096,160921868160⟩ : DyadicInterval 40),(⟨-188579724224,-188579724160⟩ : DyadicInterval 40),(⟨748409828189,748409847519⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161029635712,161029635776⟩ : DyadicInterval 40),(⟨-188727835392,-188727835328⟩ : DyadicInterval 40),(⟨748389992355,748390011684⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27698199680,-27657856000⟩ : DyadicInterval 40),(⟨775952311616,775972502720⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160978028736,161076455680⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188792193472,-188656904640⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2116_ok : ecellOkT e2116 = true := by decide +kernel
theorem e2116_pos {a z : ℝ} (ha1 : ((645813/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((51699/327680 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2116 e2116_ok ha1 ha2 hz1 hz2 hz

-- box ['51699/327680', '323331/2048000', '3997/4000', '1599/1600']  interval_lower 191330125/1099511627776
noncomputable def e2117 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272984685772,0,true,161076455616,161076455680⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926038569780,0,false,-188792193472,-188792193408⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273098636624,0,true,161174873664,161174873728⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925924618928,0,false,-188927498816,-188927498752⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272854580978,0,true,160964074816,160964074880⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926168674574,0,false,-188637727232,-188637727168⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272990144744,0,true,161081170688,161081170752⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926033110808,0,false,-188798675072,-188798675008⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566832512,0,true,55203328,55203392⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456423040,0,false,-55206144,-55206080⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577919301,0,true,66289472,66289536⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445336251,0,false,-66293568,-66293504⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623779,0,false,-4032,-3968⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625005,0,false,-2816,-2752⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272919629248,0,true,161020263104,161020263168⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926103626304,0,false,-188714952704,-188714952640⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273044395355,0,true,161128027200,161128027264⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925978860197,0,false,-188863090624,-188863090560⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072123448640,0,false,-27735063360,-27735063296⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072162817437,0,false,-27694689600,-27694689536⟩
    { al := (51699/327680), au := (323331/2048000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨173473057996,173587008848⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161076455616,161076455680⟩ : DyadicInterval 40),(⟨-188792193472,-188792193408⟩ : DyadicInterval 40),(⟨748381369531,748381388860⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161174873664,161174873728⟩ : DyadicInterval 40),(⟨-188927498816,-188927498752⟩ : DyadicInterval 40),(⟨748363233677,748363253007⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160964074816,160964074880⟩ : DyadicInterval 40),(⟨-188637727232,-188637727168⟩ : DyadicInterval 40),(⟨748402061541,748402080871⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161081170688,161081170752⟩ : DyadicInterval 40),(⟨-188798675072,-188798675008⟩ : DyadicInterval 40),(⟨748380500969,748380520299⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨55204736,66291525⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55203328,55203392⟩ : DyadicInterval 40),(⟨-55206144,-55206080⟩ : DyadicInterval 40),(⟨762123382188,762123401517⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66289472,66289536⟩ : DyadicInterval 40),(⟨-66293568,-66293504⟩ : DyadicInterval 40),(⟨762123381603,762123400932⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4032,-2752⟩ : DyadicInterval 40),(⟨762123384992,762123404896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173408001472,173532767579⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161020263104,161020263168⟩ : DyadicInterval 40),(⟨-188714952704,-188714952640⟩ : DyadicInterval 40),(⟨748391718141,748391737470⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161128027200,161128027264⟩ : DyadicInterval 40),(⟨-188863090624,-188863090560⟩ : DyadicInterval 40),(⟨748371867965,748371887295⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27735063360,-27694689536⟩ : DyadicInterval 40),(⟨775970728384,775990934560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161076455616,161174873728⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188927498816,-188792193408⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2117_ok : ecellOkT e2117 = true := by decide +kernel
theorem e2117_pos {a z : ℝ} (ha1 : ((51699/327680 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((323331/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2117 e2117_ok ha1 ha2 hz1 hz2 hz

-- box ['645813/4096000', '51699/327680', '1599/1600', '1999/2000']  interval_lower 1484679/8589934592
noncomputable def e2118 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272870734921,0,true,160978028736,160978028800⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926152520631,0,false,-188656904704,-188656904640⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272984685773,0,true,161076455616,161076455680⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926038569779,0,false,-188792193472,-188792193408⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272762385478,0,true,160884432000,160884432064⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926260870074,0,false,-188528281728,-188528281664⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272897949245,0,true,161001536384,161001536448⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926125306307,0,false,-188689213568,-188689213504⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555761536,0,true,44132864,44132928⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467494016,0,false,-44134656,-44134592⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566833282,0,true,55204096,55204160⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456422270,0,false,-55206912,-55206848⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625004,0,false,-2816,-2752⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626005,0,false,-1792,-1728⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272816555940,0,true,160931227712,160931227776⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926206699612,0,false,-188592586304,-188592586240⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272941322068,0,true,161039000576,161039000640⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926081933484,0,false,-188740707712,-188740707648⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072155974500,0,false,-27701707072,-27701707008⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072195319911,0,false,-27661358528,-27661358464⟩
    { al := (645813/4096000), au := (51699/327680), zl := (1599/1600), zu := (1999/2000),
      A := ⟨173359107145,173473057997⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160978028736,160978028800⟩ : DyadicInterval 40),(⟨-188656904704,-188656904640⟩ : DyadicInterval 40),(⟨748399493255,748399512585⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161076455616,161076455680⟩ : DyadicInterval 40),(⟨-188792193472,-188792193408⟩ : DyadicInterval 40),(⟨748381369531,748381388860⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160884432000,160884432064⟩ : DyadicInterval 40),(⟨-188528281728,-188528281664⟩ : DyadicInterval 40),(⟨748416714867,748416734197⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161001536384,161001536448⟩ : DyadicInterval 40),(⟨-188689213568,-188689213504⟩ : DyadicInterval 40),(⟨748395165944,748395185274⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨44133760,55205506⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44132864,44132928⟩ : DyadicInterval 40),(⟨-44134656,-44134592⟩ : DyadicInterval 40),(⟨762123382676,762123402005⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55204096,55204160⟩ : DyadicInterval 40),(⟨-55206912,-55206848⟩ : DyadicInterval 40),(⟨762123382188,762123401517⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2816,-1728⟩ : DyadicInterval 40),(⟨762123384480,762123404288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173304928164,173429694292⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160931227712,160931227776⟩ : DyadicInterval 40),(⟨-188592586304,-188592586240⟩ : DyadicInterval 40),(⟨748408106102,748408125431⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161039000576,161039000640⟩ : DyadicInterval 40),(⟨-188740707712,-188740707648⟩ : DyadicInterval 40),(⟨748388267883,748388287212⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27701707072,-27661358464⟩ : DyadicInterval 40),(⟨775954062848,775974256416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160978028736,161076455680⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188792193472,-188656904640⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2118_ok : ecellOkT e2118 = true := by decide +kernel
theorem e2118_pos {a z : ℝ} (ha1 : ((645813/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((51699/327680 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2118 e2118_ok ha1 ha2 hz1 hz2 hz

-- box ['51699/327680', '323331/2048000', '1599/1600', '1999/2000']  interval_lower 95583993/549755813888
noncomputable def e2119 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272984685772,0,true,161076455616,161076455680⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926038569780,0,false,-188792193472,-188792193408⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273098636624,0,true,161174873664,161174873728⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925924618928,0,false,-188927498816,-188927498752⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272876265110,0,true,160982805760,160982805824⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926146990442,0,false,-188663470080,-188663470016⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273011843120,0,true,161099911936,161099912000⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926011412432,0,false,-188824438592,-188824438528⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555791615,0,true,44162944,44163008⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467463937,0,false,-44164736,-44164672⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566870884,0,true,55241664,55241728⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456384668,0,false,-55244544,-55244480⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625000,0,false,-2816,-2752⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626003,0,false,-1792,-1728⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272930471181,0,true,161029628032,161029628096⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926092784371,0,false,-188727824832,-188727824768⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273055244434,0,true,161137397376,161137397440⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925968011118,0,false,-188875972928,-188875972864⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072120023974,0,false,-27738575488,-27738575424⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072159397488,0,false,-27698196800,-27698196736⟩
    { al := (51699/327680), au := (323331/2048000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨173473057996,173587008848⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161076455616,161076455680⟩ : DyadicInterval 40),(⟨-188792193472,-188792193408⟩ : DyadicInterval 40),(⟨748381369531,748381388860⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161174873664,161174873728⟩ : DyadicInterval 40),(⟨-188927498816,-188927498752⟩ : DyadicInterval 40),(⟨748363233677,748363253007⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160982805760,160982805824⟩ : DyadicInterval 40),(⟨-188663470080,-188663470016⟩ : DyadicInterval 40),(⟨748398613954,748398633283⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161099911936,161099912000⟩ : DyadicInterval 40),(⟨-188824438592,-188824438528⟩ : DyadicInterval 40),(⟨748377048372,748377067702⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨44163839,55243108⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44162944,44163008⟩ : DyadicInterval 40),(⟨-44164736,-44164672⟩ : DyadicInterval 40),(⟨762123382674,762123402003⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55241664,55241728⟩ : DyadicInterval 40),(⟨-55244544,-55244480⟩ : DyadicInterval 40),(⟨762123382216,762123401545⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2816,-1728⟩ : DyadicInterval 40),(⟨762123384480,762123404288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173418843405,173543616658⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161029628032,161029628096⟩ : DyadicInterval 40),(⟨-188727824832,-188727824768⟩ : DyadicInterval 40),(⟨748389993774,748390013103⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161137397376,161137397440⟩ : DyadicInterval 40),(⟨-188875972928,-188875972864⟩ : DyadicInterval 40),(⟨748370141185,748370160514⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27738575488,-27698196736⟩ : DyadicInterval 40),(⟨775972481984,775992690624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161076455616,161174873728⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188927498816,-188792193408⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2119_ok : ecellOkT e2119 = true := by decide +kernel
theorem e2119_pos {a z : ℝ} (ha1 : ((51699/327680 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((323331/2048000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2119 e2119_ok ha1 ha2 hz1 hz2 hz

-- box ['323331/2048000', '1294173/8192000', '999/1000', '7993/8000']  interval_lower 6024585/34359738368
noncomputable def e2120 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273098636623,0,true,161174873664,161174873728⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925924618929,0,false,-188927498816,-188927498752⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273212587475,0,true,161273282944,161273283008⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925810668077,0,false,-189062820864,-189062820800⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272925049614,0,true,161024945024,161024945088⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926098205938,0,false,-188721388032,-188721387968⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273060599136,0,true,161142022144,161142022208⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925962656416,0,false,-188882331200,-188882331136⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099588966793,0,true,77336256,77336320⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434288759,0,false,-77341760,-77341696⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099600076146,0,true,88444800,88444864⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099423179406,0,false,-88451968,-88451904⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620660,0,false,-7168,-7104⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622337,0,false,-5440,-5376⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273011839335,0,true,161099908672,161099908736⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926011416217,0,false,-188824434112,-188824434048⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273136598276,0,true,161207658752,161207658816⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925886657276,0,false,-188972578240,-188972578176⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072094336662,0,false,-27764919424,-27764919360⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072133724123,0,false,-27724525440,-27724525376⟩
    { al := (323331/2048000), au := (1294173/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨173587008847,173700959699⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161174873664,161174873728⟩ : DyadicInterval 40),(⟨-188927498816,-188927498752⟩ : DyadicInterval 40),(⟨748363233677,748363253007⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161273282944,161273283008⟩ : DyadicInterval 40),(⟨-189062820864,-189062820800⟩ : DyadicInterval 40),(⟨748345085710,748345105039⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161024945024,161024945088⟩ : DyadicInterval 40),(⟨-188721388032,-188721387968⟩ : DyadicInterval 40),(⟨748390856085,748390875415⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161142022144,161142022208⟩ : DyadicInterval 40),(⟨-188882331200,-188882331136⟩ : DyadicInterval 40),(⟨748369288849,748369308179⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨77339017,88448370⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77336256,77336320⟩ : DyadicInterval 40),(⟨-77341760,-77341696⟩ : DyadicInterval 40),(⟨762123380863,762123400193⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨88444800,88444864⟩ : DyadicInterval 40),(⟨-88451968,-88451904⟩ : DyadicInterval 40),(⟨762123380020,762123399350⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7168,-5376⟩ : DyadicInterval 40),(⟨762123386304,762123406464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173500211559,173624970500⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161099908672,161099908736⟩ : DyadicInterval 40),(⟨-188824434112,-188824434048⟩ : DyadicInterval 40),(⟨748377048977,748377068307⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161207658752,161207658816⟩ : DyadicInterval 40),(⟨-188972578240,-188972578176⟩ : DyadicInterval 40),(⟨748357189210,748357208540⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27764919424,-27724525376⟩ : DyadicInterval 40),(⟨775985646304,776005862592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161174873664,161273283008⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189062820864,-188927498752⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2120_ok : ecellOkT e2120 = true := by decide +kernel
theorem e2120_pos {a z : ℝ} (ha1 : ((323331/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1294173/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2120 e2120_ok ha1 ha2 hz1 hz2 hz

-- box ['1294173/8192000', '647511/4096000', '999/1000', '7993/8000']  interval_lower 193922165/1099511627776
noncomputable def e2121 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273212587474,0,true,161273282944,161273283008⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925810668078,0,false,-189062820864,-189062820800⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273326538327,0,true,161371683392,161371683456⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925696717225,0,false,-189198159552,-189198159488⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273038886514,0,true,161123269312,161123269376⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925984369038,0,false,-188856549376,-188856549312⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273174450281,0,true,161240348224,161240348288⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925848805271,0,false,-189017529280,-189017529216⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589019437,0,true,77388928,77388992⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434236115,0,false,-77394432,-77394368⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099600136316,0,true,88504960,88505024⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099423119236,0,false,-88512128,-88512064⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620651,0,false,-7168,-7104⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622329,0,false,-5504,-5440⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273125733214,0,true,161198275392,161198275456⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925897522338,0,false,-188959675776,-188959675712⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273250499275,0,true,161306022016,161306022080⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925772756277,0,false,-189107846592,-189107846528⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072058352424,0,false,-27801824512,-27801824448⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072097767981,0,false,-27761400320,-27761400256⟩
    { al := (1294173/8192000), au := (647511/4096000), zl := (999/1000), zu := (7993/8000),
      A := ⟨173700959698,173814910551⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161273282944,161273283008⟩ : DyadicInterval 40),(⟨-189062820864,-189062820800⟩ : DyadicInterval 40),(⟨748345085710,748345105039⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161371683392,161371683456⟩ : DyadicInterval 40),(⟨-189198159552,-189198159488⟩ : DyadicInterval 40),(⟨748326925638,748326944968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161123269312,161123269376⟩ : DyadicInterval 40),(⟨-188856549376,-188856549312⟩ : DyadicInterval 40),(⟨748372744686,748372764015⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161240348224,161240348288⟩ : DyadicInterval 40),(⟨-189017529280,-189017529216⟩ : DyadicInterval 40),(⟨748351160826,748351180155⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨77391661,88508540⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77388928,77388992⟩ : DyadicInterval 40),(⟨-77394432,-77394368⟩ : DyadicInterval 40),(⟨762123380856,762123400185⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨88504960,88505024⟩ : DyadicInterval 40),(⟨-88512128,-88512064⟩ : DyadicInterval 40),(⟨762123380010,762123399340⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7168,-5440⟩ : DyadicInterval 40),(⟨762123386336,762123406464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173614105438,173738871499⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161198275392,161198275456⟩ : DyadicInterval 40),(⟨-188959675776,-188959675712⟩ : DyadicInterval 40),(⟨748358919327,748358938657⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161306022016,161306022080⟩ : DyadicInterval 40),(⟨-189107846592,-189107846528⟩ : DyadicInterval 40),(⟨748339045156,748339064485⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27801824512,-27761400256⟩ : DyadicInterval 40),(⟨776004083744,776024315136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161273282944,161371683456⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189198159552,-189062820800⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2121_ok : ecellOkT e2121 = true := by decide +kernel
theorem e2121_pos {a z : ℝ} (ha1 : ((1294173/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((647511/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2121 e2121_ok ha1 ha2 hz1 hz2 hz

-- box ['323331/2048000', '1294173/8192000', '7993/8000', '3997/4000']  interval_lower 12039015/68719476736
noncomputable def e2122 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273098636623,0,true,161174873664,161174873728⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925924618929,0,false,-188927498816,-188927498752⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273212587475,0,true,161273282944,161273283008⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925810668077,0,false,-189062820864,-189062820800⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272946747990,0,true,161043687232,161043687296⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926076507562,0,false,-188747149760,-188747149696⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273082311756,0,true,161160774592,161160774656⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925940943796,0,false,-188908113600,-188908113536⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577918478,0,true,66288640,66288704⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445337074,0,false,-66292736,-66292672⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589020311,0,true,77389760,77389824⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434235241,0,false,-77395264,-77395200⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622328,0,false,-5504,-5440⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623780,0,false,-4032,-3968⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273022688340,0,true,161109278976,161109279040⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926000567212,0,false,-188837315904,-188837315840⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273147454424,0,true,161217034368,161217034432⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925875801128,0,false,-188985470208,-188985470144⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072090907945,0,false,-27768435840,-27768435776⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072130300124,0,false,-27728036864,-27728036800⟩
    { al := (323331/2048000), au := (1294173/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨173587008847,173700959699⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161174873664,161174873728⟩ : DyadicInterval 40),(⟨-188927498816,-188927498752⟩ : DyadicInterval 40),(⟨748363233677,748363253007⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161273282944,161273283008⟩ : DyadicInterval 40),(⟨-189062820864,-189062820800⟩ : DyadicInterval 40),(⟨748345085710,748345105039⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161043687232,161043687296⟩ : DyadicInterval 40),(⟨-188747149760,-188747149696⟩ : DyadicInterval 40),(⟨748387404813,748387424142⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161160774592,161160774656⟩ : DyadicInterval 40),(⟨-188908113600,-188908113536⟩ : DyadicInterval 40),(⟨748365832599,748365851928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨66290702,77392535⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66288640,66288704⟩ : DyadicInterval 40),(⟨-66292736,-66292672⟩ : DyadicInterval 40),(⟨762123381603,762123400932⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77389760,77389824⟩ : DyadicInterval 40),(⟨-77395264,-77395200⟩ : DyadicInterval 40),(⟨762123380856,762123400185⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5504,-3968⟩ : DyadicInterval 40),(⟨762123385600,762123405632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173511060564,173635826648⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161109278976,161109279040⟩ : DyadicInterval 40),(⟨-188837315904,-188837315840⟩ : DyadicInterval 40),(⟨748375322577,748375341907⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161217034368,161217034432⟩ : DyadicInterval 40),(⟨-188985470208,-188985470144⟩ : DyadicInterval 40),(⟨748355460357,748355479686⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27768435840,-27728036800⟩ : DyadicInterval 40),(⟨775987402016,776007620800⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161174873664,161273283008⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189062820864,-188927498752⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2122_ok : ecellOkT e2122 = true := by decide +kernel
theorem e2122_pos {a z : ℝ} (ha1 : ((323331/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1294173/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2122 e2122_ok ha1 ha2 hz1 hz2 hz

-- box ['1294173/8192000', '647511/4096000', '7993/8000', '3997/4000']  interval_lower 193759527/1099511627776
noncomputable def e2123 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273212587474,0,true,161273282944,161273283008⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925810668078,0,false,-189062820864,-189062820800⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273326538327,0,true,161371683392,161371683456⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925696717225,0,false,-189198159552,-189198159488⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273060599134,0,true,161142022144,161142022208⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925962656418,0,false,-188882331200,-188882331136⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273196177145,0,true,161259111360,161259111424⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925827078407,0,false,-189043331776,-189043331712⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577963602,0,true,66333824,66333888⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445291950,0,false,-66337856,-66337792⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589072960,0,true,77442432,77442496⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434182592,0,false,-77447936,-77447872⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622321,0,false,-5504,-5440⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623774,0,false,-4032,-3968⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273136589340,0,true,161207651072,161207651136⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925886666212,0,false,-188972567616,-188972567552⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273261362548,0,true,161315402944,161315403008⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925761893004,0,false,-189120748672,-189120748608⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072054919205,0,false,-27805345664,-27805345600⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072094339485,0,false,-27764916544,-27764916480⟩
    { al := (1294173/8192000), au := (647511/4096000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨173700959698,173814910551⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161273282944,161273283008⟩ : DyadicInterval 40),(⟨-189062820864,-189062820800⟩ : DyadicInterval 40),(⟨748345085710,748345105039⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161371683392,161371683456⟩ : DyadicInterval 40),(⟨-189198159552,-189198159488⟩ : DyadicInterval 40),(⟨748326925638,748326944968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161142022144,161142022208⟩ : DyadicInterval 40),(⟨-188882331200,-188882331136⟩ : DyadicInterval 40),(⟨748369288850,748369308179⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161259111360,161259111424⟩ : DyadicInterval 40),(⟨-189043331776,-189043331712⟩ : DyadicInterval 40),(⟨748347699967,748347719296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨66335826,77445184⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66333824,66333888⟩ : DyadicInterval 40),(⟨-66337856,-66337792⟩ : DyadicInterval 40),(⟨762123381565,762123400894⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77442432,77442496⟩ : DyadicInterval 40),(⟨-77447936,-77447872⟩ : DyadicInterval 40),(⟨762123380848,762123400178⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5504,-3968⟩ : DyadicInterval 40),(⟨762123385600,762123405632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173624961564,173749734772⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161207651072,161207651136⟩ : DyadicInterval 40),(⟨-188972567616,-188972567552⟩ : DyadicInterval 40),(⟨748357190607,748357209936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161315402944,161315403008⟩ : DyadicInterval 40),(⟨-189120748672,-189120748608⟩ : DyadicInterval 40),(⟨748337314041,748337333371⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27805345664,-27764916480⟩ : DyadicInterval 40),(⟨776005841856,776026075712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161273282944,161371683456⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189198159552,-189062820800⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2123_ok : ecellOkT e2123 = true := by decide +kernel
theorem e2123_pos {a z : ℝ} (ha1 : ((1294173/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((647511/4096000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2123 e2123_ok ha1 ha2 hz1 hz2 hz

-- box ['647511/4096000', '1295871/8192000', '999/1000', '7993/8000']  interval_lower 195060611/1099511627776
noncomputable def e2124 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273326538326,0,true,161371683392,161371683456⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925696717226,0,false,-189198159552,-189198159488⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273440489178,0,true,161470075008,161470075072⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925582766374,0,false,-189333514880,-189333514816⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273152723415,0,true,161221584768,161221584832⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925870532137,0,false,-188991727360,-188991727296⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273288301425,0,true,161338665472,161338665536⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925734954127,0,false,-189152743936,-189152743872⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589072085,0,true,77441536,77441600⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434183467,0,false,-77447040,-77446976⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099600196490,0,true,88565120,88565184⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099423059062,0,false,-88572288,-88572224⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620641,0,false,-7168,-7104⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622322,0,false,-5504,-5440⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273239627089,0,true,161296633344,161296633408⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925783628463,0,false,-189094934080,-189094934016⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273364400272,0,true,161404376512,161404376576⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925658855280,0,false,-189243131584,-189243131520⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072022344587,0,false,-27838755072,-27838755008⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072061788245,0,false,-27798300736,-27798300672⟩
    { al := (647511/4096000), au := (1295871/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨173814910550,173928861402⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161371683392,161371683456⟩ : DyadicInterval 40),(⟨-189198159552,-189198159488⟩ : DyadicInterval 40),(⟨748326925638,748326944968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161470075008,161470075072⟩ : DyadicInterval 40),(⟨-189333514880,-189333514816⟩ : DyadicInterval 40),(⟨748308753461,748308772790⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161221584768,161221584832⟩ : DyadicInterval 40),(⟨-188991727360,-188991727296⟩ : DyadicInterval 40),(⟨748354621232,748354640561⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161338665472,161338665536⟩ : DyadicInterval 40),(⟨-189152743936,-189152743872⟩ : DyadicInterval 40),(⟨748333020713,748333040043⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨77444309,88568714⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77441536,77441600⟩ : DyadicInterval 40),(⟨-77447040,-77446976⟩ : DyadicInterval 40),(⟨762123380849,762123400178⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨88565120,88565184⟩ : DyadicInterval 40),(⟨-88572288,-88572224⟩ : DyadicInterval 40),(⟨762123380001,762123399330⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7168,-5440⟩ : DyadicInterval 40),(⟨762123386336,762123406464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173727999313,173852772496⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161296633344,161296633408⟩ : DyadicInterval 40),(⟨-189094934080,-189094934016⟩ : DyadicInterval 40),(⟨748340777561,748340796891⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161404376512,161404376576⟩ : DyadicInterval 40),(⟨-189243131584,-189243131520⟩ : DyadicInterval 40),(⟨748320888980,748320908310⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27838755072,-27798300672⟩ : DyadicInterval 40),(⟨776022533952,776042780416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161371683392,161470075072⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189333514880,-189198159488⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2124_ok : ecellOkT e2124 = true := by decide +kernel
theorem e2124_pos {a z : ℝ} (ha1 : ((647511/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1295871/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2124 e2124_ok ha1 ha2 hz1 hz2 hz

-- box ['1295871/8192000', '16209/102400', '999/1000', '7993/8000']  interval_lower 196201699/1099511627776
noncomputable def e2125 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273440489177,0,true,161470075008,161470075072⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925582766375,0,false,-189333514880,-189333514816⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273554440029,0,true,161568457856,161568457920⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925468815523,0,false,-189468886912,-189468886848⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273266560315,0,true,161319891392,161319891456⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925756695237,0,false,-189126921984,-189126921920⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273402152569,0,true,161436974016,161436974080⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925621102983,0,false,-189287975296,-189287975232⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589124736,0,true,77494208,77494272⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434130816,0,false,-77499712,-77499648⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099600256668,0,true,88625280,88625344⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099422998884,0,false,-88632512,-88632448⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620631,0,false,-7168,-7104⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622314,0,false,-5504,-5440⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273353520959,0,true,161394982528,161394982592⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925669734593,0,false,-189230209088,-189230209024⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273478301272,0,true,161502722176,161502722240⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925544954280,0,false,-189378433280,-189378433216⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071986313152,0,false,-27875711040,-27875710976⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072025784915,0,false,-27835226496,-27835226432⟩
    { al := (1295871/8192000), au := (16209/102400), zl := (999/1000), zu := (7993/8000),
      A := ⟨173928861401,174042812253⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161470075008,161470075072⟩ : DyadicInterval 40),(⟨-189333514880,-189333514816⟩ : DyadicInterval 40),(⟨748308753461,748308772790⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161568457856,161568457920⟩ : DyadicInterval 40),(⟨-189468886912,-189468886848⟩ : DyadicInterval 40),(⟨748290569166,748290588496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161319891392,161319891456⟩ : DyadicInterval 40),(⟨-189126921984,-189126921920⟩ : DyadicInterval 40),(⟨748336485723,748336505052⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161436974016,161436974080⟩ : DyadicInterval 40),(⟨-189287975296,-189287975232⟩ : DyadicInterval 40),(⟨748314868491,748314887821⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨77496960,88628892⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77494208,77494272⟩ : DyadicInterval 40),(⟨-77499712,-77499648⟩ : DyadicInterval 40),(⟨762123380841,762123400170⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨88625280,88625344⟩ : DyadicInterval 40),(⟨-88632512,-88632448⟩ : DyadicInterval 40),(⟨762123380023,762123399353⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7168,-5440⟩ : DyadicInterval 40),(⟨762123386336,762123406464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173841893183,173966673496⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161394982528,161394982592⟩ : DyadicInterval 40),(⟨-189230209088,-189230209024⟩ : DyadicInterval 40),(⟨748322623706,748322643036⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161502722176,161502722240⟩ : DyadicInterval 40),(⟨-189378433280,-189378433216⟩ : DyadicInterval 40),(⟨748302720746,748302740076⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27875711040,-27835226432⟩ : DyadicInterval 40),(⟨776040996832,776061258400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161470075008,161568457920⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189468886912,-189333514816⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2125_ok : ecellOkT e2125 = true := by decide +kernel
theorem e2125_pos {a z : ℝ} (ha1 : ((1295871/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((16209/102400 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2125 e2125_ok ha1 ha2 hz1 hz2 hz

-- box ['647511/4096000', '1295871/8192000', '7993/8000', '3997/4000']  interval_lower 194897447/1099511627776
noncomputable def e2126 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273326538326,0,true,161371683392,161371683456⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925696717226,0,false,-189198159552,-189198159488⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273440489178,0,true,161470075008,161470075072⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925582766374,0,false,-189333514880,-189333514816⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273174450279,0,true,161240348224,161240348288⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925848805273,0,false,-189017529280,-189017529216⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273310042533,0,true,161357439232,161357439296⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925713213019,0,false,-189178566528,-189178566464⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578008729,0,true,66378944,66379008⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445246823,0,false,-66382976,-66382912⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589125612,0,true,77495104,77495168⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434129940,0,false,-77500608,-77500544⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622313,0,false,-5504,-5440⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623769,0,false,-4032,-3968⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273250490336,0,true,161306014336,161306014400⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925772765216,0,false,-189107835968,-189107835904⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273375270667,0,true,161413762752,161413762816⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925647984885,0,false,-189256043712,-189256043648⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072018906866,0,false,-27842280960,-27842280896⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072058355250,0,false,-27801821632,-27801821568⟩
    { al := (647511/4096000), au := (1295871/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨173814910550,173928861402⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161371683392,161371683456⟩ : DyadicInterval 40),(⟨-189198159552,-189198159488⟩ : DyadicInterval 40),(⟨748326925638,748326944968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161470075008,161470075072⟩ : DyadicInterval 40),(⟨-189333514880,-189333514816⟩ : DyadicInterval 40),(⟨748308753461,748308772790⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161240348224,161240348288⟩ : DyadicInterval 40),(⟨-189017529280,-189017529216⟩ : DyadicInterval 40),(⟨748351160826,748351180155⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161357439232,161357439296⟩ : DyadicInterval 40),(⟨-189178566528,-189178566464⟩ : DyadicInterval 40),(⟨748329555278,748329574607⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨66380953,77497836⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66378944,66379008⟩ : DyadicInterval 40),(⟨-66382976,-66382912⟩ : DyadicInterval 40),(⟨762123381560,762123400889⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77495104,77495168⟩ : DyadicInterval 40),(⟨-77500608,-77500544⟩ : DyadicInterval 40),(⟨762123380841,762123400170⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5504,-3968⟩ : DyadicInterval 40),(⟨762123385600,762123405632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173738862560,173863642891⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161306014336,161306014400⟩ : DyadicInterval 40),(⟨-189107835968,-189107835904⟩ : DyadicInterval 40),(⟨748339046554,748339065884⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161413762752,161413762816⟩ : DyadicInterval 40),(⟨-189256043712,-189256043648⟩ : DyadicInterval 40),(⟨748319155575,748319174905⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27842280960,-27801821568⟩ : DyadicInterval 40),(⟨776024294400,776044543360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161371683392,161470075072⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189333514880,-189198159488⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2126_ok : ecellOkT e2126 = true := by decide +kernel
theorem e2126_pos {a z : ℝ} (ha1 : ((647511/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1295871/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2126 e2126_ok ha1 ha2 hz1 hz2 hz

-- box ['1295871/8192000', '16209/102400', '7993/8000', '3997/4000']  interval_lower 196038319/1099511627776
noncomputable def e2127 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273440489177,0,true,161470075008,161470075072⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925582766375,0,false,-189333514880,-189333514816⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273554440029,0,true,161568457856,161568457920⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925468815523,0,false,-189468886912,-189468886848⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273288301423,0,true,161338665472,161338665536⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925734954129,0,false,-189152743936,-189152743872⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273423907920,0,true,161455758336,161455758400⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925599347632,0,false,-189313817984,-189313817920⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578053859,0,true,66424064,66424128⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445201693,0,false,-66428096,-66428032⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099589178269,0,true,77547712,77547776⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099434077283,0,false,-77553280,-77553216⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622306,0,false,-5504,-5440⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623763,0,false,-4032,-3968⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273364391331,0,true,161404368768,161404368832⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925658864221,0,false,-189243120960,-189243120896⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273489178784,0,true,161512113664,161512113728⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925534076768,0,false,-189391355392,-189391355328⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071982870926,0,false,-27879241664,-27879241600⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072022347416,0,false,-27838752192,-27838752128⟩
    { al := (1295871/8192000), au := (16209/102400), zl := (7993/8000), zu := (3997/4000),
      A := ⟨173928861401,174042812253⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161470075008,161470075072⟩ : DyadicInterval 40),(⟨-189333514880,-189333514816⟩ : DyadicInterval 40),(⟨748308753461,748308772790⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161568457856,161568457920⟩ : DyadicInterval 40),(⟨-189468886912,-189468886848⟩ : DyadicInterval 40),(⟨748290569166,748290588496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161338665472,161338665536⟩ : DyadicInterval 40),(⟨-189152743936,-189152743872⟩ : DyadicInterval 40),(⟨748333020714,748333040044⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161455758336,161455758400⟩ : DyadicInterval 40),(⟨-189313817984,-189313817920⟩ : DyadicInterval 40),(⟨748311398509,748311417839⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨66426083,77550493⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66424064,66424128⟩ : DyadicInterval 40),(⟨-66428096,-66428032⟩ : DyadicInterval 40),(⟨762123381554,762123400884⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨77547712,77547776⟩ : DyadicInterval 40),(⟨-77553280,-77553216⟩ : DyadicInterval 40),(⟨762123380866,762123400195⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5504,-3968⟩ : DyadicInterval 40),(⟨762123385600,762123405632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173852763555,173977551008⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161404368768,161404368832⟩ : DyadicInterval 40),(⟨-189243120960,-189243120896⟩ : DyadicInterval 40),(⟨748320890418,748320909747⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161512113664,161512113728⟩ : DyadicInterval 40),(⟨-189391355392,-189391355328⟩ : DyadicInterval 40),(⟨748300985059,748301004388⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27879241664,-27838752128⟩ : DyadicInterval 40),(⟨776042759680,776063023712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161470075008,161568457920⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189468886912,-189333514816⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2127_ok : ecellOkT e2127 = true := by decide +kernel
theorem e2127_pos {a z : ℝ} (ha1 : ((1295871/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((16209/102400 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2127 e2127_ok ha1 ha2 hz1 hz2 hz

-- box ['323331/2048000', '1294173/8192000', '3997/4000', '1599/1600']  interval_lower 48115521/274877906944
noncomputable def e2128 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273098636623,0,true,161174873664,161174873728⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925924618929,0,false,-188927498816,-188927498752⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273212587475,0,true,161273282944,161273283008⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925810668077,0,false,-189062820864,-189062820800⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272968446366,0,true,161062429120,161062429184⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926054809186,0,false,-188772912128,-188772912064⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273104024376,0,true,161179526784,161179526848⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925919231176,0,false,-188933896640,-188933896576⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566870112,0,true,55240896,55240960⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456385440,0,false,-55243776,-55243712⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099577964424,0,true,66334592,66334656⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445291128,0,false,-66338688,-66338624⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623773,0,false,-4032,-3968⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625001,0,false,-2816,-2752⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273033537367,0,true,161118649280,161118649344⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925989718185,0,false,-188850197824,-188850197760⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273158310598,0,true,161226409920,161226409984⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925864944954,0,false,-188998362432,-188998362368⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072087479005,0,false,-27771952448,-27771952384⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072126875904,0,false,-27731548544,-27731548480⟩
    { al := (323331/2048000), au := (1294173/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨173587008847,173700959699⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161174873664,161174873728⟩ : DyadicInterval 40),(⟨-188927498816,-188927498752⟩ : DyadicInterval 40),(⟨748363233677,748363253007⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161273282944,161273283008⟩ : DyadicInterval 40),(⟨-189062820864,-189062820800⟩ : DyadicInterval 40),(⟨748345085710,748345105039⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161062429120,161062429184⟩ : DyadicInterval 40),(⟨-188772912128,-188772912064⟩ : DyadicInterval 40),(⟨748383953116,748383972446⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161179526784,161179526848⟩ : DyadicInterval 40),(⟨-188933896640,-188933896576⟩ : DyadicInterval 40),(⟨748362375886,748362395216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨55242336,66336648⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55240896,55240960⟩ : DyadicInterval 40),(⟨-55243776,-55243712⟩ : DyadicInterval 40),(⟨762123382216,762123401545⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66334592,66334656⟩ : DyadicInterval 40),(⟨-66338688,-66338624⟩ : DyadicInterval 40),(⟨762123381597,762123400926⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4032,-2752⟩ : DyadicInterval 40),(⟨762123384992,762123404896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173521909591,173646682822⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161118649280,161118649344⟩ : DyadicInterval 40),(⟨-188850197824,-188850197760⟩ : DyadicInterval 40),(⟨748373596008,748373615338⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161226409920,161226409984⟩ : DyadicInterval 40),(⟨-188998362432,-188998362368⟩ : DyadicInterval 40),(⟨748353731424,748353750754⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27771952448,-27731548480⟩ : DyadicInterval 40),(⟨775989157856,776009379104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161174873664,161273283008⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189062820864,-188927498752⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2128_ok : ecellOkT e2128 = true := by decide +kernel
theorem e2128_pos {a z : ℝ} (ha1 : ((323331/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1294173/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2128 e2128_ok ha1 ha2 hz1 hz2 hz

-- box ['1294173/8192000', '647511/4096000', '3997/4000', '1599/1600']  interval_lower 193596665/1099511627776
noncomputable def e2129 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273212587474,0,true,161273282944,161273283008⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925810668078,0,false,-189062820864,-189062820800⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273326538327,0,true,161371683392,161371683456⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925696717225,0,false,-189198159552,-189198159488⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273082311754,0,true,161160774592,161160774656⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925940943798,0,false,-188908113600,-188908113536⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273217904008,0,true,161277874112,161277874176⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925805351544,0,false,-189069134912,-189069134848⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566907716,0,true,55278528,55278592⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456347836,0,false,-55281344,-55281280⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578009553,0,true,66379712,66379776⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445245999,0,false,-66383808,-66383744⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623768,0,false,-4032,-3968⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624997,0,false,-2816,-2752⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273147445487,0,true,161217026624,161217026688⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925875810065,0,false,-188985459584,-188985459520⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273272225839,0,true,161324783808,161324783872⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925751029713,0,false,-189133650880,-189133650816⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072051485767,0,false,-27808867072,-27808867008⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072090910769,0,false,-27768432896,-27768432832⟩
    { al := (1294173/8192000), au := (647511/4096000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨173700959698,173814910551⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161273282944,161273283008⟩ : DyadicInterval 40),(⟨-189062820864,-189062820800⟩ : DyadicInterval 40),(⟨748345085710,748345105039⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161371683392,161371683456⟩ : DyadicInterval 40),(⟨-189198159552,-189198159488⟩ : DyadicInterval 40),(⟨748326925638,748326944968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161160774592,161160774656⟩ : DyadicInterval 40),(⟨-188908113600,-188908113536⟩ : DyadicInterval 40),(⟨748365832599,748365851928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161277874112,161277874176⟩ : DyadicInterval 40),(⟨-189069134912,-189069134848⟩ : DyadicInterval 40),(⟨748344238720,748344258049⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨55279940,66381777⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55278528,55278592⟩ : DyadicInterval 40),(⟨-55281344,-55281280⟩ : DyadicInterval 40),(⟨762123382180,762123401509⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66379712,66379776⟩ : DyadicInterval 40),(⟨-66383808,-66383744⟩ : DyadicInterval 40),(⟨762123381592,762123400921⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4032,-2752⟩ : DyadicInterval 40),(⟨762123384992,762123404896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173635817711,173760598063⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161217026624,161217026688⟩ : DyadicInterval 40),(⟨-188985459584,-188985459520⟩ : DyadicInterval 40),(⟨748355461790,748355481120⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161324783808,161324783872⟩ : DyadicInterval 40),(⟨-189133650880,-189133650816⟩ : DyadicInterval 40),(⟨748335582795,748335602124⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27808867072,-27768432832⟩ : DyadicInterval 40),(⟨776007600032,776027836416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161273282944,161371683456⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189198159552,-189062820800⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2129_ok : ecellOkT e2129 = true := by decide +kernel
theorem e2129_pos {a z : ℝ} (ha1 : ((1294173/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((647511/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2129 e2129_ok ha1 ha2 hz1 hz2 hz

-- box ['323331/2048000', '1294173/8192000', '1599/1600', '1999/2000']  interval_lower 12018711/68719476736
noncomputable def e2130 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273098636623,0,true,161174873664,161174873728⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925924618929,0,false,-188927498816,-188927498752⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273212587475,0,true,161273282944,161273283008⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925810668077,0,false,-189062820864,-189062820800⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272990144742,0,true,161081170688,161081170752⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926033110810,0,false,-188798675072,-188798675008⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273125736996,0,true,161198278656,161198278720⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925897518556,0,false,-188959680256,-188959680192⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555821696,0,true,44193024,44193088⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467433856,0,false,-44194816,-44194752⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566908487,0,true,55279296,55279360⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456347065,0,false,-55282112,-55282048⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624996,0,false,-2816,-2752⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626000,0,false,-1792,-1728⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273044386420,0,true,161128019520,161128019584⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925978869132,0,false,-188863080000,-188863079936⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273169166799,0,true,161235785408,161235785472⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925854088753,0,false,-189011254784,-189011254720⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072084049842,0,false,-27775469376,-27775469312⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072123451461,0,false,-27735060480,-27735060416⟩
    { al := (323331/2048000), au := (1294173/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨173587008847,173700959699⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161174873664,161174873728⟩ : DyadicInterval 40),(⟨-188927498816,-188927498752⟩ : DyadicInterval 40),(⟨748363233677,748363253007⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161273282944,161273283008⟩ : DyadicInterval 40),(⟨-189062820864,-189062820800⟩ : DyadicInterval 40),(⟨748345085710,748345105039⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161081170688,161081170752⟩ : DyadicInterval 40),(⟨-188798675072,-188798675008⟩ : DyadicInterval 40),(⟨748380500969,748380520299⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161198278656,161198278720⟩ : DyadicInterval 40),(⟨-188959680256,-188959680192⟩ : DyadicInterval 40),(⟨748358918722,748358938051⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨44193920,55280711⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44193024,44193088⟩ : DyadicInterval 40),(⟨-44194816,-44194752⟩ : DyadicInterval 40),(⟨762123382671,762123402000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55279296,55279360⟩ : DyadicInterval 40),(⟨-55282112,-55282048⟩ : DyadicInterval 40),(⟨762123382180,762123401509⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2816,-1728⟩ : DyadicInterval 40),(⟨762123384480,762123404288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173532758644,173657539023⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161128019520,161128019584⟩ : DyadicInterval 40),(⟨-188863080000,-188863079936⟩ : DyadicInterval 40),(⟨748371869360,748371888690⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161235785408,161235785472⟩ : DyadicInterval 40),(⟨-189011254784,-189011254720⟩ : DyadicInterval 40),(⟨748352002359,748352021688⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27775469376,-27735060416⟩ : DyadicInterval 40),(⟨775990913824,776011137568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161174873664,161273283008⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189062820864,-188927498752⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2130_ok : ecellOkT e2130 = true := by decide +kernel
theorem e2130_pos {a z : ℝ} (ha1 : ((323331/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1294173/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2130 e2130_ok ha1 ha2 hz1 hz2 hz

-- box ['1294173/8192000', '647511/4096000', '1599/1600', '1999/2000']  interval_lower 96716873/549755813888
noncomputable def e2131 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273212587474,0,true,161273282944,161273283008⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925810668078,0,false,-189062820864,-189062820800⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273326538327,0,true,161371683392,161371683456⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925696717225,0,false,-189198159552,-189198159488⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273104024374,0,true,161179526784,161179526848⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925919231178,0,false,-188933896640,-188933896576⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273239630872,0,true,161296636608,161296636672⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925783624680,0,false,-189094938624,-189094938560⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555851778,0,true,44223104,44223168⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467403774,0,false,-44224896,-44224832⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566946094,0,true,55316864,55316928⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456309458,0,false,-55319744,-55319680⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624992,0,false,-2816,-2752⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625998,0,false,-1792,-1728⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273158301661,0,true,161226402176,161226402240⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925864953891,0,false,-188998351808,-188998351744⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273283089161,0,true,161334164608,161334164672⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925740166391,0,false,-189146553280,-189146553216⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072048052103,0,false,-27812388672,-27812388608⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072087481829,0,false,-27771949568,-27771949504⟩
    { al := (1294173/8192000), au := (647511/4096000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨173700959698,173814910551⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161273282944,161273283008⟩ : DyadicInterval 40),(⟨-189062820864,-189062820800⟩ : DyadicInterval 40),(⟨748345085710,748345105039⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161371683392,161371683456⟩ : DyadicInterval 40),(⟨-189198159552,-189198159488⟩ : DyadicInterval 40),(⟨748326925638,748326944968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161179526784,161179526848⟩ : DyadicInterval 40),(⟨-188933896640,-188933896576⟩ : DyadicInterval 40),(⟨748362375886,748362395216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161296636608,161296636672⟩ : DyadicInterval 40),(⟨-189094938624,-189094938560⟩ : DyadicInterval 40),(⟨748340776982,748340796312⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨44224002,55318318⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44223104,44223168⟩ : DyadicInterval 40),(⟨-44224896,-44224832⟩ : DyadicInterval 40),(⟨762123382669,762123401998⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55316864,55316928⟩ : DyadicInterval 40),(⟨-55319744,-55319680⟩ : DyadicInterval 40),(⟨762123382208,762123401537⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2816,-1728⟩ : DyadicInterval 40),(⟨762123384480,762123404288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173646673885,173771461385⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161226402176,161226402240⟩ : DyadicInterval 40),(⟨-188998351808,-188998351744⟩ : DyadicInterval 40),(⟨748353732858,748353752188⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161334164608,161334164672⟩ : DyadicInterval 40),(⟨-189146553280,-189146553216⟩ : DyadicInterval 40),(⟨748333851441,748333870770⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27812388672,-27771949504⟩ : DyadicInterval 40),(⟨776009358368,776029597216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161273282944,161371683456⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189198159552,-189062820800⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2131_ok : ecellOkT e2131 = true := by decide +kernel
theorem e2131_pos {a z : ℝ} (ha1 : ((1294173/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((647511/4096000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2131 e2131_ok ha1 ha2 hz1 hz2 hz

-- box ['647511/4096000', '1295871/8192000', '3997/4000', '1599/1600']  interval_lower 97367051/549755813888
noncomputable def e2132 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273326538326,0,true,161371683392,161371683456⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925696717226,0,false,-189198159552,-189198159488⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273440489178,0,true,161470075008,161470075072⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925582766374,0,false,-189333514880,-189333514816⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273196177143,0,true,161259111296,161259111360⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925827078409,0,false,-189043331776,-189043331712⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273331783640,0,true,161376212672,161376212736⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925691471912,0,false,-189204389760,-189204389696⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566945322,0,true,55316096,55316160⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456310230,0,false,-55318976,-55318912⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578054684,0,true,66424896,66424960⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445200868,0,false,-66428928,-66428864⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623762,0,false,-4032,-3968⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624993,0,false,-2816,-2752⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273261353604,0,true,161315395200,161315395264⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925761901948,0,false,-189120738048,-189120737984⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273386141083,0,true,161423148864,161423148928⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925637114469,0,false,-189268955968,-189268955904⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072015468923,0,false,-27845807040,-27845806976⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072054922033,0,false,-27805342784,-27805342720⟩
    { al := (647511/4096000), au := (1295871/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨173814910550,173928861402⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161371683392,161371683456⟩ : DyadicInterval 40),(⟨-189198159552,-189198159488⟩ : DyadicInterval 40),(⟨748326925638,748326944968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161470075008,161470075072⟩ : DyadicInterval 40),(⟨-189333514880,-189333514816⟩ : DyadicInterval 40),(⟨748308753461,748308772790⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161259111296,161259111360⟩ : DyadicInterval 40),(⟨-189043331776,-189043331712⟩ : DyadicInterval 40),(⟨748347700004,748347719334⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161376212672,161376212736⟩ : DyadicInterval 40),(⟨-189204389760,-189204389696⟩ : DyadicInterval 40),(⟨748326089415,748326108744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨55317546,66426908⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55316096,55316160⟩ : DyadicInterval 40),(⟨-55318976,-55318912⟩ : DyadicInterval 40),(⟨762123382208,762123401537⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66424896,66424960⟩ : DyadicInterval 40),(⟨-66428928,-66428864⟩ : DyadicInterval 40),(⟨762123381554,762123400883⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4032,-2752⟩ : DyadicInterval 40),(⟨762123384992,762123404896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173749725828,173874513307⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161315395200,161315395264⟩ : DyadicInterval 40),(⟨-189120738048,-189120737984⟩ : DyadicInterval 40),(⟨748337315478,748337334807⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161423148864,161423148928⟩ : DyadicInterval 40),(⟨-189268955968,-189268955904⟩ : DyadicInterval 40),(⟨748317422074,748317441404⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27845807040,-27805342720⟩ : DyadicInterval 40),(⟨776026054976,776046306400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161371683392,161470075072⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189333514880,-189198159488⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2132_ok : ecellOkT e2132 = true := by decide +kernel
theorem e2132_pos {a z : ℝ} (ha1 : ((647511/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1295871/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2132 e2132_ok ha1 ha2 hz1 hz2 hz

-- box ['1295871/8192000', '16209/102400', '3997/4000', '1599/1600']  interval_lower 97937279/549755813888
noncomputable def e2133 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273440489177,0,true,161470075008,161470075072⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925582766375,0,false,-189333514880,-189333514816⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273554440029,0,true,161568457856,161568457920⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925468815523,0,false,-189468886912,-189468886848⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273310042530,0,true,161357439232,161357439296⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925713213022,0,false,-189178566528,-189178566464⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273445663272,0,true,161474542400,161474542464⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925577592280,0,false,-189339661248,-189339661184⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566982931,0,true,55353728,55353792⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456272621,0,false,-55356608,-55356544⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099578099818,0,true,66470016,66470080⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099445155734,0,false,-66474112,-66474048⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623757,0,false,-4032,-3968⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624990,0,false,-2816,-2752⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273375261724,0,true,161413755008,161413755072⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925647993828,0,false,-189256033088,-189256033024⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273500056327,0,true,161521505152,161521505216⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925523199225,0,false,-189404277760,-189404277696⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071979428475,0,false,-27882772544,-27882772480⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072018909695,0,false,-27842278016,-27842277952⟩
    { al := (1295871/8192000), au := (16209/102400), zl := (3997/4000), zu := (1599/1600),
      A := ⟨173928861401,174042812253⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161470075008,161470075072⟩ : DyadicInterval 40),(⟨-189333514880,-189333514816⟩ : DyadicInterval 40),(⟨748308753461,748308772790⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161568457856,161568457920⟩ : DyadicInterval 40),(⟨-189468886912,-189468886848⟩ : DyadicInterval 40),(⟨748290569166,748290588496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161357439232,161357439296⟩ : DyadicInterval 40),(⟨-189178566528,-189178566464⟩ : DyadicInterval 40),(⟨748329555278,748329574608⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161474542400,161474542464⟩ : DyadicInterval 40),(⟨-189339661248,-189339661184⟩ : DyadicInterval 40),(⟨748307928035,748307947364⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨55355155,66472042⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55353728,55353792⟩ : DyadicInterval 40),(⟨-55356608,-55356544⟩ : DyadicInterval 40),(⟨762123382205,762123401534⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨66470016,66470080⟩ : DyadicInterval 40),(⟨-66474112,-66474048⟩ : DyadicInterval 40),(⟨762123381581,762123400910⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4032,-2752⟩ : DyadicInterval 40),(⟨762123384992,762123404896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173863633948,173988428551⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161413755008,161413755072⟩ : DyadicInterval 40),(⟨-189256033088,-189256033024⟩ : DyadicInterval 40),(⟨748319157013,748319176343⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161521505152,161521505216⟩ : DyadicInterval 40),(⟨-189404277760,-189404277696⟩ : DyadicInterval 40),(⟨748299249253,748299268582⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27882772544,-27842277952⟩ : DyadicInterval 40),(⟨776044522592,776064789152⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161470075008,161568457920⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189468886912,-189333514816⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2133_ok : ecellOkT e2133 = true := by decide +kernel
theorem e2133_pos {a z : ℝ} (ha1 : ((1295871/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((16209/102400 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2133 e2133_ok ha1 ha2 hz1 hz2 hz

-- box ['647511/4096000', '1295871/8192000', '1599/1600', '1999/2000']  interval_lower 97285439/549755813888
noncomputable def e2134 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273326538326,0,true,161371683392,161371683456⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925696717226,0,false,-189198159552,-189198159488⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273440489178,0,true,161470075008,161470075072⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925582766374,0,false,-189333514880,-189333514816⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273217904006,0,true,161277874112,161277874176⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925805351546,0,false,-189069134912,-189069134848⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273353524748,0,true,161394985792,161394985856⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925669730804,0,false,-189230213568,-189230213504⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555881864,0,true,44253184,44253248⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467373688,0,false,-44255040,-44254976⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566983704,0,true,55354496,55354560⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456271848,0,false,-55357376,-55357312⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624989,0,false,-2816,-2752⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625995,0,false,-1792,-1728⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273272216899,0,true,161324776064,161324776128⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925751038653,0,false,-189133640256,-189133640192⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273397011527,0,true,161432534976,161432535040⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925626244025,0,false,-189281868416,-189281868352⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072012030756,0,false,-27849333440,-27849333376⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072051488593,0,false,-27808864128,-27808864064⟩
    { al := (647511/4096000), au := (1295871/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨173814910550,173928861402⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161371683392,161371683456⟩ : DyadicInterval 40),(⟨-189198159552,-189198159488⟩ : DyadicInterval 40),(⟨748326925638,748326944968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161470075008,161470075072⟩ : DyadicInterval 40),(⟨-189333514880,-189333514816⟩ : DyadicInterval 40),(⟨748308753461,748308772790⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161277874112,161277874176⟩ : DyadicInterval 40),(⟨-189069134912,-189069134848⟩ : DyadicInterval 40),(⟨748344238720,748344258049⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161394985792,161394985856⟩ : DyadicInterval 40),(⟨-189230213568,-189230213504⟩ : DyadicInterval 40),(⟨748322623098,748322642427⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨44254088,55355928⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44253184,44253248⟩ : DyadicInterval 40),(⟨-44255040,-44254976⟩ : DyadicInterval 40),(⟨762123382698,762123402027⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55354496,55354560⟩ : DyadicInterval 40),(⟨-55357376,-55357312⟩ : DyadicInterval 40),(⟨762123382204,762123401534⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2816,-1728⟩ : DyadicInterval 40),(⟨762123384480,762123404288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173760589123,173885383751⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161324776064,161324776128⟩ : DyadicInterval 40),(⟨-189133640256,-189133640192⟩ : DyadicInterval 40),(⟨748335584231,748335603560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161432534976,161432535040⟩ : DyadicInterval 40),(⟨-189281868416,-189281868352⟩ : DyadicInterval 40),(⟨748315688430,748315707759⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27849333440,-27808864064⟩ : DyadicInterval 40),(⟨776027815648,776048069600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161371683392,161470075072⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189333514880,-189198159488⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2134_ok : ecellOkT e2134 = true := by decide +kernel
theorem e2134_pos {a z : ℝ} (ha1 : ((647511/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1295871/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2134 e2134_ok ha1 ha2 hz1 hz2 hz

-- box ['1295871/8192000', '16209/102400', '1599/1600', '1999/2000']  interval_lower 12231929/68719476736
noncomputable def e2135 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273440489177,0,true,161470075008,161470075072⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925582766375,0,false,-189333514880,-189333514816⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273554440029,0,true,161568457856,161568457920⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925468815523,0,false,-189468886912,-189468886848⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273331783638,0,true,161376212672,161376212736⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925691471914,0,false,-189204389760,-189204389696⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273467418624,0,true,161493326144,161493326208⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925555836928,0,false,-189365505152,-189365505088⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555911951,0,true,44283264,44283328⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467343601,0,false,-44285120,-44285056⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099567021315,0,true,55392128,55392192⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099456234237,0,false,-55394944,-55394880⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624985,0,false,-2816,-2752⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625993,0,false,-1792,-1728⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273386132141,0,true,161423141184,161423141248⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925637123411,0,false,-189268945344,-189268945280⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273510933893,0,true,161530896576,161530896640⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925512321659,0,false,-189417200256,-189417200192⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071975985801,0,false,-27886303616,-27886303552⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072015471752,0,false,-27845804160,-27845804096⟩
    { al := (1295871/8192000), au := (16209/102400), zl := (1599/1600), zu := (1999/2000),
      A := ⟨173928861401,174042812253⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161470075008,161470075072⟩ : DyadicInterval 40),(⟨-189333514880,-189333514816⟩ : DyadicInterval 40),(⟨748308753461,748308772790⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161568457856,161568457920⟩ : DyadicInterval 40),(⟨-189468886912,-189468886848⟩ : DyadicInterval 40),(⟨748290569166,748290588496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161376212672,161376212736⟩ : DyadicInterval 40),(⟨-189204389760,-189204389696⟩ : DyadicInterval 40),(⟨748326089415,748326108745⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161493326144,161493326208⟩ : DyadicInterval 40),(⟨-189365505152,-189365505088⟩ : DyadicInterval 40),(⟨748304457132,748304476461⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨44284175,55393539⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44283264,44283328⟩ : DyadicInterval 40),(⟨-44285120,-44285056⟩ : DyadicInterval 40),(⟨762123382696,762123402025⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨55392128,55392192⟩ : DyadicInterval 40),(⟨-55394944,-55394880⟩ : DyadicInterval 40),(⟨762123382169,762123401498⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2816,-1728⟩ : DyadicInterval 40),(⟨762123384480,762123404288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173874504365,173999306117⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161423141184,161423141248⟩ : DyadicInterval 40),(⟨-189268945344,-189268945280⟩ : DyadicInterval 40),(⟨748317423476,748317442805⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161530896576,161530896640⟩ : DyadicInterval 40),(⟨-189417200256,-189417200192⟩ : DyadicInterval 40),(⟨748297513314,748297532643⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27886303616,-27845804096⟩ : DyadicInterval 40),(⟨776046285664,776066554688⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161470075008,161568457920⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189468886912,-189333514816⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2135_ok : ecellOkT e2135 = true := by decide +kernel
theorem e2135_pos {a z : ℝ} (ha1 : ((1295871/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((16209/102400 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2135 e2135_ok ha1 ha2 hz1 hz2 hz

-- box ['161241/1024000', '1290777/8192000', '1999/2000', '7997/8000']  interval_lower 46907205/274877906944
noncomputable def e2136 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272642833219,0,true,160781148608,160781148672⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926380422333,0,false,-188386377216,-188386377152⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272756784071,0,true,160879593088,160879593152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926266471481,0,false,-188521632640,-188521632576⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272556267616,0,true,160706356864,160706356928⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926466987936,0,false,-188283638144,-188283638080⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272691817138,0,true,160823467904,160823467968⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926331438414,0,false,-188444517248,-188444517184⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544682994,0,true,33054720,33054784⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478572558,0,false,-33055744,-33055680⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555732179,0,true,44103488,44103552⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467523373,0,false,-44105344,-44105280⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626006,0,false,-1792,-1728⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626783,0,false,-1024,-960⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272599546054,0,true,160743749632,160743749696⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926423709498,0,false,-188335001280,-188335001216⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272724305081,0,true,160851534720,160851534784⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926298950471,0,false,-188483079552,-188483079488⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072224393315,0,false,-27631544832,-27631544768⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072263687239,0,false,-27591251648,-27591251584⟩
    { al := (161241/1024000), au := (1290777/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨173131205443,173245156295⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160781148608,160781148672⟩ : DyadicInterval 40),(⟨-188386377216,-188386377152⟩ : DyadicInterval 40),(⟨748435704383,748435723713⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160879593088,160879593152⟩ : DyadicInterval 40),(⟨-188521632640,-188521632576⟩ : DyadicInterval 40),(⟨748417604869,748417624198⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160706356864,160706356928⟩ : DyadicInterval 40),(⟨-188283638144,-188283638080⟩ : DyadicInterval 40),(⟨748449446048,748449465378⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160823467904,160823467968⟩ : DyadicInterval 40),(⟨-188444517248,-188444517184⟩ : DyadicInterval 40),(⟨748427925440,748427944770⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨33055218,44104403⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33054720,33054784⟩ : DyadicInterval 40),(⟨-33055744,-33055680⟩ : DyadicInterval 40),(⟨762123383070,762123402399⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44103488,44103552⟩ : DyadicInterval 40),(⟨-44105344,-44105280⟩ : DyadicInterval 40),(⟨762123382710,762123402039⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1792,-960⟩ : DyadicInterval 40),(⟨762123384096,762123403776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173087918278,173212677305⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160743749632,160743749696⟩ : DyadicInterval 40),(⟨-188335001280,-188335001216⟩ : DyadicInterval 40),(⟨748442576755,748442596085⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160851534720,160851534784⟩ : DyadicInterval 40),(⟨-188483079552,-188483079488⟩ : DyadicInterval 40),(⟨748422764924,748422784253⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27631544832,-27591251584⟩ : DyadicInterval 40),(⟨775919009408,775939175296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160781148608,160879593152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188521632640,-188386377152⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2136_ok : ecellOkT e2136 = true := by decide +kernel
theorem e2136_pos {a z : ℝ} (ha1 : ((161241/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1290777/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2136 e2136_ok ha1 ha2 hz1 hz2 hz

-- box ['1290777/8192000', '645813/4096000', '1999/2000', '7997/8000']  interval_lower 94375855/549755813888
noncomputable def e2137 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272756784070,0,true,160879593088,160879593152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926266471482,0,false,-188521632640,-188521632576⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272870734922,0,true,160978028736,160978028800⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926152520630,0,false,-188656904704,-188656904640⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272670161491,0,true,160804758848,160804758912⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926353094061,0,false,-188418813312,-188418813248⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272805725257,0,true,160921871680,160921871744⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926217530295,0,false,-188579729152,-188579729088⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544705550,0,true,33077248,33077312⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478550002,0,false,-33078272,-33078208⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555762255,0,true,44133568,44133632⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467493297,0,false,-44135424,-44135360⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626004,0,false,-1792,-1728⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626781,0,false,-1024,-960⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272713468417,0,true,160842172864,160842172928⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926309787135,0,false,-188470216576,-188470216512⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272838234563,0,true,160949954432,160949954496⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926185020989,0,false,-188618321536,-188618321472⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072188485517,0,false,-27668367104,-27668367040⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072227807539,0,false,-27628043712,-27628043648⟩
    { al := (1290777/8192000), au := (645813/4096000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨173245156294,173359107146⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160879593088,160879593152⟩ : DyadicInterval 40),(⟨-188521632640,-188521632576⟩ : DyadicInterval 40),(⟨748417604869,748417624198⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160978028736,160978028800⟩ : DyadicInterval 40),(⟨-188656904704,-188656904640⟩ : DyadicInterval 40),(⟨748399493255,748399512585⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160804758848,160804758912⟩ : DyadicInterval 40),(⟨-188418813312,-188418813248⟩ : DyadicInterval 40),(⟨748431364768,748431384097⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160921871680,160921871744⟩ : DyadicInterval 40),(⟨-188579729152,-188579729088⟩ : DyadicInterval 40),(⟨748409827536,748409846865⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨33077774,44134479⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33077248,33077312⟩ : DyadicInterval 40),(⟨-33078272,-33078208⟩ : DyadicInterval 40),(⟨762123383068,762123402397⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44133568,44133632⟩ : DyadicInterval 40),(⟨-44135424,-44135360⟩ : DyadicInterval 40),(⟨762123382708,762123402037⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1792,-960⟩ : DyadicInterval 40),(⟨762123384096,762123403776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173201840641,173326606787⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160842172864,160842172928⟩ : DyadicInterval 40),(⟨-188470216576,-188470216512⟩ : DyadicInterval 40),(⟨748424486361,748424505691⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160949954432,160949954496⟩ : DyadicInterval 40),(⟨-188618321536,-188618321472⟩ : DyadicInterval 40),(⟨748404660166,748404679495⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27668367104,-27628043648⟩ : DyadicInterval 40),(⟨775937405440,775957586432⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160879593088,160978028800⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188656904704,-188521632576⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2137_ok : ecellOkT e2137 = true := by decide +kernel
theorem e2137_pos {a z : ℝ} (ha1 : ((1290777/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((645813/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2137 e2137_ok ha1 ha2 hz1 hz2 hz

-- box ['161241/1024000', '1290777/8192000', '7997/8000', '3999/4000']  interval_lower 187467489/1099511627776
noncomputable def e2138 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272642833219,0,true,160781148608,160781148672⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926380422333,0,false,-188386377216,-188386377152⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272756784071,0,true,160879593088,160879593152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926266471481,0,false,-188521632640,-188521632576⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272577909016,0,true,160725055296,160725055360⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926445346536,0,false,-188309321984,-188309321920⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272713472783,0,true,160842176576,160842176640⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926309782769,0,false,-188470221760,-188470221696⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533664553,0,true,22036544,22036608⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489590999,0,false,-22037056,-22036992⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544706218,0,true,33077888,33077952⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478549334,0,false,-33078976,-33078912⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626780,0,false,-1024,-960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627335,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272610366671,0,true,160753098432,160753098496⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926412888881,0,false,-188347843648,-188347843584⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272735132841,0,true,160860888832,160860888896⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926288122711,0,false,-188495932160,-188495932096⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072220981684,0,false,-27635043328,-27635043264⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072260280314,0,false,-27594745152,-27594745088⟩
    { al := (161241/1024000), au := (1290777/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨173131205443,173245156295⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160781148608,160781148672⟩ : DyadicInterval 40),(⟨-188386377216,-188386377152⟩ : DyadicInterval 40),(⟨748435704383,748435723713⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160879593088,160879593152⟩ : DyadicInterval 40),(⟨-188521632640,-188521632576⟩ : DyadicInterval 40),(⟨748417604869,748417624198⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160725055296,160725055360⟩ : DyadicInterval 40),(⟨-188309321984,-188309321920⟩ : DyadicInterval 40),(⟨748446011264,748446030594⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160842176576,160842176640⟩ : DyadicInterval 40),(⟨-188470221760,-188470221696⟩ : DyadicInterval 40),(⟨748424485703,748424505033⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22036777,33078442⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22036544,22036608⟩ : DyadicInterval 40),(⟨-22037056,-22036992⟩ : DyadicInterval 40),(⟨762123383366,762123402695⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33077888,33077952⟩ : DyadicInterval 40),(⟨-33078976,-33078912⟩ : DyadicInterval 40),(⟨762123383100,762123402429⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1024,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173098738895,173223505065⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160753098432,160753098496⟩ : DyadicInterval 40),(⟨-188347843648,-188347843584⟩ : DyadicInterval 40),(⟨748440859042,748440878371⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160860888832,160860888896⟩ : DyadicInterval 40),(⟨-188495932160,-188495932096⟩ : DyadicInterval 40),(⟨748421044796,748421064126⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27635043328,-27594745088⟩ : DyadicInterval 40),(⟨775920756160,775940924544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160781148608,160879593152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188521632640,-188386377152⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2138_ok : ecellOkT e2138 = true := by decide +kernel
theorem e2138_pos {a z : ℝ} (ha1 : ((161241/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1290777/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2138 e2138_ok ha1 ha2 hz1 hz2 hz

-- box ['1290777/8192000', '645813/4096000', '7997/8000', '3999/4000']  interval_lower 94294923/549755813888
noncomputable def e2139 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272756784070,0,true,160879593088,160879593152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926266471482,0,false,-188521632640,-188521632576⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272870734922,0,true,160978028736,160978028800⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926152520630,0,false,-188656904704,-188656904640⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272691817136,0,true,160823467904,160823467968⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926331438416,0,false,-188444517248,-188444517184⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272827395146,0,true,160940591040,160940591104⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926195860406,0,false,-188605453696,-188605453632⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533679591,0,true,22051584,22051648⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489575961,0,false,-22052096,-22052032⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544728776,0,true,33100480,33100544⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478526776,0,false,-33101504,-33101440⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626779,0,false,-1024,-960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627334,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272724296155,0,true,160851526976,160851527040⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926298959397,0,false,-188483068992,-188483068928⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272849069449,0,true,160959313856,160959313920⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926174186103,0,false,-188631184128,-188631184064⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072185069396,0,false,-27671870272,-27671870208⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072224396128,0,false,-27631541952,-27631541888⟩
    { al := (1290777/8192000), au := (645813/4096000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨173245156294,173359107146⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160879593088,160879593152⟩ : DyadicInterval 40),(⟨-188521632640,-188521632576⟩ : DyadicInterval 40),(⟨748417604869,748417624198⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160978028736,160978028800⟩ : DyadicInterval 40),(⟨-188656904704,-188656904640⟩ : DyadicInterval 40),(⟨748399493255,748399512585⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160823467904,160823467968⟩ : DyadicInterval 40),(⟨-188444517248,-188444517184⟩ : DyadicInterval 40),(⟨748427925440,748427944770⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160940591040,160940591104⟩ : DyadicInterval 40),(⟨-188605453696,-188605453632⟩ : DyadicInterval 40),(⟨748406383184,748406402514⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22051815,33101000⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22051584,22051648⟩ : DyadicInterval 40),(⟨-22052096,-22052032⟩ : DyadicInterval 40),(⟨762123383365,762123402694⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33100480,33100544⟩ : DyadicInterval 40),(⟨-33101504,-33101440⟩ : DyadicInterval 40),(⟨762123383067,762123402396⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1024,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173212668379,173337441673⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160851526976,160851527040⟩ : DyadicInterval 40),(⟨-188483068992,-188483068928⟩ : DyadicInterval 40),(⟨748422766376,748422785705⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160959313856,160959313920⟩ : DyadicInterval 40),(⟨-188631184128,-188631184064⟩ : DyadicInterval 40),(⟨748402937735,748402957064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27671870272,-27631541888⟩ : DyadicInterval 40),(⟨775939154560,775959338016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160879593088,160978028800⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188656904704,-188521632576⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2139_ok : ecellOkT e2139 = true := by decide +kernel
theorem e2139_pos {a z : ℝ} (ha1 : ((1290777/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((645813/4096000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2139 e2139_ok ha1 ha2 hz1 hz2 hz

-- box ['645813/4096000', '51699/327680', '1999/2000', '7997/8000']  interval_lower 47469325/274877906944
noncomputable def e2140 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272870734921,0,true,160978028736,160978028800⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926152520631,0,false,-188656904704,-188656904640⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272984685773,0,true,161076455616,161076455680⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926038569779,0,false,-188792193472,-188792193408⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272784055367,0,true,160903152000,160903152064⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926239200185,0,false,-188554005120,-188554005056⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272919633377,0,true,161020266688,161020266752⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926103622175,0,false,-188714957632,-188714957568⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544728108,0,true,33099776,33099840⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478527444,0,false,-33100864,-33100800⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555792334,0,true,44163648,44163712⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467463218,0,false,-44165504,-44165440⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626002,0,false,-1792,-1728⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626780,0,false,-1024,-960⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272827390776,0,true,160940587264,160940587328⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926195864776,0,false,-188605448512,-188605448448⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272952164049,0,true,161048365376,161048365440⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926071091503,0,false,-188753580160,-188753580096⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072152554108,0,false,-27705214784,-27705214720⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072191904232,0,false,-27664861248,-27664861184⟩
    { al := (645813/4096000), au := (51699/327680), zl := (1999/2000), zu := (7997/8000),
      A := ⟨173359107145,173473057997⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160978028736,160978028800⟩ : DyadicInterval 40),(⟨-188656904704,-188656904640⟩ : DyadicInterval 40),(⟨748399493255,748399512585⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161076455616,161076455680⟩ : DyadicInterval 40),(⟨-188792193472,-188792193408⟩ : DyadicInterval 40),(⟨748381369531,748381388860⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160903152000,160903152064⟩ : DyadicInterval 40),(⟨-188554005120,-188554005056⟩ : DyadicInterval 40),(⟨748413271412,748413290742⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161020266688,161020266752⟩ : DyadicInterval 40),(⟨-188714957632,-188714957568⟩ : DyadicInterval 40),(⟨748391717485,748391736814⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨33100332,44164558⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33099776,33099840⟩ : DyadicInterval 40),(⟨-33100864,-33100800⟩ : DyadicInterval 40),(⟨762123383099,762123402428⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44163648,44163712⟩ : DyadicInterval 40),(⟨-44165504,-44165440⟩ : DyadicInterval 40),(⟨762123382705,762123402035⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1792,-960⟩ : DyadicInterval 40),(⟨762123384096,762123403776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173315763000,173440536273⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160940587264,160940587328⟩ : DyadicInterval 40),(⟨-188605448512,-188605448448⟩ : DyadicInterval 40),(⟨748406383881,748406403211⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161048365376,161048365440⟩ : DyadicInterval 40),(⟨-188753580160,-188753580096⟩ : DyadicInterval 40),(⟨748386543278,748386562608⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27705214784,-27664861184⟩ : DyadicInterval 40),(⟨775955814208,775976010272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160978028736,161076455680⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188792193472,-188656904640⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2140_ok : ecellOkT e2140 = true := by decide +kernel
theorem e2140_pos {a z : ℝ} (ha1 : ((645813/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((51699/327680 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2140 e2140_ok ha1 ha2 hz1 hz2 hz

-- box ['51699/327680', '323331/2048000', '1999/2000', '7997/8000']  interval_lower 47751397/274877906944
noncomputable def e2141 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272984685772,0,true,161076455616,161076455680⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926038569780,0,false,-188792193472,-188792193408⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273098636624,0,true,161174873664,161174873728⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925924618928,0,false,-188927498816,-188927498752⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272897949242,0,true,161001536384,161001536448⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926125306310,0,false,-188689213568,-188689213504⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273033541496,0,true,161118652864,161118652928⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925989714056,0,false,-188850202752,-188850202688⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544750667,0,true,33122368,33122432⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478504885,0,false,-33123392,-33123328⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555822416,0,true,44193728,44193792⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467433136,0,false,-44195584,-44195520⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625999,0,false,-1792,-1728⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626779,0,false,-1024,-960⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272941313137,0,true,161038992832,161038992896⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926081942415,0,false,-188740697088,-188740697024⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273066093536,0,true,161146767488,161146767552⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925957162016,0,false,-188888855424,-188888855360⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072116599088,0,false,-27742087872,-27742087808⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072155977318,0,false,-27701704192,-27701704128⟩
    { al := (51699/327680), au := (323331/2048000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨173473057996,173587008848⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161076455616,161076455680⟩ : DyadicInterval 40),(⟨-188792193472,-188792193408⟩ : DyadicInterval 40),(⟨748381369531,748381388860⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161174873664,161174873728⟩ : DyadicInterval 40),(⟨-188927498816,-188927498752⟩ : DyadicInterval 40),(⟨748363233677,748363253007⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161001536384,161001536448⟩ : DyadicInterval 40),(⟨-188689213568,-188689213504⟩ : DyadicInterval 40),(⟨748395165944,748395185274⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161118652864,161118652928⟩ : DyadicInterval 40),(⟨-188850202752,-188850202688⟩ : DyadicInterval 40),(⟨748373595351,748373614681⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨33122891,44194640⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33122368,33122432⟩ : DyadicInterval 40),(⟨-33123392,-33123328⟩ : DyadicInterval 40),(⟨762123383066,762123402395⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44193728,44193792⟩ : DyadicInterval 40),(⟨-44195584,-44195520⟩ : DyadicInterval 40),(⟨762123382703,762123402032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1792,-960⟩ : DyadicInterval 40),(⟨762123384096,762123403776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173429685361,173554465760⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161038992832,161038992896⟩ : DyadicInterval 40),(⟨-188740697088,-188740697024⟩ : DyadicInterval 40),(⟨748388269312,748388288642⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161146767488,161146767552⟩ : DyadicInterval 40),(⟨-188888855424,-188888855360⟩ : DyadicInterval 40),(⟨748368414298,748368433628⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27742087872,-27701704128⟩ : DyadicInterval 40),(⟨775974235680,775994446816⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161076455616,161174873728⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188927498816,-188792193408⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2141_ok : ecellOkT e2141 = true := by decide +kernel
theorem e2141_pos {a z : ℝ} (ha1 : ((51699/327680 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((323331/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2141 e2141_ok ha1 ha2 hz1 hz2 hz

-- box ['645813/4096000', '51699/327680', '7997/8000', '3999/4000']  interval_lower 2964301/17179869184
noncomputable def e2142 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272870734921,0,true,160978028736,160978028800⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926152520631,0,false,-188656904704,-188656904640⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272984685773,0,true,161076455616,161076455680⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926038569779,0,false,-188792193472,-188792193408⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272805725255,0,true,160921871680,160921871744⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926217530297,0,false,-188579729088,-188579729024⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272941317509,0,true,161038996608,161038996672⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926081938043,0,false,-188740702272,-188740702208⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533694629,0,true,22066624,22066688⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489560923,0,false,-22067136,-22067072⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544751335,0,true,33123008,33123072⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478504217,0,false,-33124096,-33124032⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626778,0,false,-1024,-960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627334,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272838225636,0,true,160949946752,160949946816⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926185029916,0,false,-188618310976,-188618310912⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272963006053,0,true,161057730112,161057730176⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926060249499,0,false,-188766452800,-188766452736⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072149133495,0,false,-27708722688,-27708722624⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072188488333,0,false,-27668364160,-27668364096⟩
    { al := (645813/4096000), au := (51699/327680), zl := (7997/8000), zu := (3999/4000),
      A := ⟨173359107145,173473057997⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160978028736,160978028800⟩ : DyadicInterval 40),(⟨-188656904704,-188656904640⟩ : DyadicInterval 40),(⟨748399493255,748399512585⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161076455616,161076455680⟩ : DyadicInterval 40),(⟨-188792193472,-188792193408⟩ : DyadicInterval 40),(⟨748381369531,748381388860⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160921871680,160921871744⟩ : DyadicInterval 40),(⟨-188579729088,-188579729024⟩ : DyadicInterval 40),(⟨748409827509,748409846839⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161038996608,161038996672⟩ : DyadicInterval 40),(⟨-188740702272,-188740702208⟩ : DyadicInterval 40),(⟨748388268614,748388287943⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22066853,33123559⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22066624,22066688⟩ : DyadicInterval 40),(⟨-22067136,-22067072⟩ : DyadicInterval 40),(⟨762123383365,762123402694⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33123008,33123072⟩ : DyadicInterval 40),(⟨-33124096,-33124032⟩ : DyadicInterval 40),(⟨762123383098,762123402427⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1024,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173326597860,173451378277⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160949946752,160949946816⟩ : DyadicInterval 40),(⟨-188618310976,-188618310912⟩ : DyadicInterval 40),(⟨748404661582,748404680912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161057730112,161057730176⟩ : DyadicInterval 40),(⟨-188766452800,-188766452736⟩ : DyadicInterval 40),(⟨748384818569,748384837898⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27708722688,-27668364096⟩ : DyadicInterval 40),(⟨775957565664,775977764224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160978028736,161076455680⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188792193472,-188656904640⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2142_ok : ecellOkT e2142 = true := by decide +kernel
theorem e2142_pos {a z : ℝ} (ha1 : ((645813/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((51699/327680 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2142 e2142_ok ha1 ha2 hz1 hz2 hz

-- box ['51699/327680', '323331/2048000', '7997/8000', '3999/4000']  interval_lower 190843105/1099511627776
noncomputable def e2143 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272984685772,0,true,161076455616,161076455680⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926038569780,0,false,-188792193472,-188792193408⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273098636624,0,true,161174873664,161174873728⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925924618928,0,false,-188927498816,-188927498752⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272919633375,0,true,161020266688,161020266752⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926103622177,0,false,-188714957632,-188714957568⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273055239872,0,true,161137393472,161137393536⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925968015680,0,false,-188875967488,-188875967424⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533709669,0,true,22081664,22081728⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489545883,0,false,-22082176,-22082112⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544773897,0,true,33145600,33145664⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478481655,0,false,-33146624,-33146560⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626776,0,false,-1024,-960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627333,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272952155117,0,true,161048357632,161048357696⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926071100435,0,false,-188753569536,-188753569472⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273076942664,0,true,161156137536,161156137600⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925946312888,0,false,-188901738112,-188901738048⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072113173979,0,false,-27745600512,-27745600448⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072152556927,0,false,-27705211840,-27705211776⟩
    { al := (51699/327680), au := (323331/2048000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨173473057996,173587008848⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161076455616,161076455680⟩ : DyadicInterval 40),(⟨-188792193472,-188792193408⟩ : DyadicInterval 40),(⟨748381369531,748381388860⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161174873664,161174873728⟩ : DyadicInterval 40),(⟨-188927498816,-188927498752⟩ : DyadicInterval 40),(⟨748363233677,748363253007⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161020266688,161020266752⟩ : DyadicInterval 40),(⟨-188714957632,-188714957568⟩ : DyadicInterval 40),(⟨748391717486,748391736815⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161137393472,161137393536⟩ : DyadicInterval 40),(⟨-188875967488,-188875967424⟩ : DyadicInterval 40),(⟨748370141880,748370161209⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22081893,33146121⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22081664,22081728⟩ : DyadicInterval 40),(⟨-22082176,-22082112⟩ : DyadicInterval 40),(⟨762123383364,762123402693⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33145600,33145664⟩ : DyadicInterval 40),(⟨-33146624,-33146560⟩ : DyadicInterval 40),(⟨762123383064,762123402393⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1024,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173440527341,173565314888⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161048357632,161048357696⟩ : DyadicInterval 40),(⟨-188753569536,-188753569472⟩ : DyadicInterval 40),(⟨748386544708,748386564037⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161156137536,161156137600⟩ : DyadicInterval 40),(⟨-188901738112,-188901738048⟩ : DyadicInterval 40),(⟨748366687306,748366706635⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27745600512,-27705211776⟩ : DyadicInterval 40),(⟨775975989504,775996203136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161076455616,161174873728⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188927498816,-188792193408⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2143_ok : ecellOkT e2143 = true := by decide +kernel
theorem e2143_pos {a z : ℝ} (ha1 : ((51699/327680 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((323331/2048000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2143 e2143_ok ha1 ha2 hz1 hz2 hz

-- box ['161241/1024000', '1290777/8192000', '3999/4000', '7999/8000']  interval_lower 187306287/1099511627776
noncomputable def e2144 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272642833219,0,true,160781148608,160781148672⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926380422333,0,false,-188386377216,-188386377152⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272756784071,0,true,160879593088,160879593152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926266471481,0,false,-188521632640,-188521632576⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272599550417,0,true,160743753408,160743753472⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926423705135,0,false,-188335006464,-188335006400⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272735128427,0,true,160860884992,160860885056⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926288127125,0,false,-188495926912,-188495926848⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522646062,0,true,11018176,11018240⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500609490,0,false,-11018368,-11018304⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533680207,0,true,22052160,22052224⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489575345,0,false,-22052672,-22052608⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627333,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627666,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272621187312,0,true,160762447232,160762447296⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926402068240,0,false,-188360686208,-188360686144⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272745960625,0,true,160870242880,160870242944⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926277294927,0,false,-188508784896,-188508784832⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072217569832,0,false,-27638542016,-27638541952⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072256873169,0,false,-27598238912,-27598238848⟩
    { al := (161241/1024000), au := (1290777/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨173131205443,173245156295⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160781148608,160781148672⟩ : DyadicInterval 40),(⟨-188386377216,-188386377152⟩ : DyadicInterval 40),(⟨748435704383,748435723713⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160879593088,160879593152⟩ : DyadicInterval 40),(⟨-188521632640,-188521632576⟩ : DyadicInterval 40),(⟨748417604869,748417624198⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160743753408,160743753472⟩ : DyadicInterval 40),(⟨-188335006464,-188335006400⟩ : DyadicInterval 40),(⟨748442576062,748442595391⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160860884992,160860885056⟩ : DyadicInterval 40),(⟨-188495926912,-188495926848⟩ : DyadicInterval 40),(⟨748421045510,748421064839⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11018286,22052431⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11018176,11018240⟩ : DyadicInterval 40),(⟨-11018368,-11018304⟩ : DyadicInterval 40),(⟨762123383537,762123402866⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22052160,22052224⟩ : DyadicInterval 40),(⟨-22052672,-22052608⟩ : DyadicInterval 40),(⟨762123383365,762123402694⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173109559536,173234332849⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160762447232,160762447296⟩ : DyadicInterval 40),(⟨-188360686208,-188360686144⟩ : DyadicInterval 40),(⟨748439141187,748439160516⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160870242880,160870242944⟩ : DyadicInterval 40),(⟨-188508784896,-188508784832⟩ : DyadicInterval 40),(⟨748419324538,748419343867⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27638542016,-27598238848⟩ : DyadicInterval 40),(⟨775922503040,775942673888⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160781148608,160879593152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188521632640,-188386377152⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2144_ok : ecellOkT e2144 = true := by decide +kernel
theorem e2144_pos {a z : ℝ} (ha1 : ((161241/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1290777/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2144 e2144_ok ha1 ha2 hz1 hz2 hz

-- box ['1290777/8192000', '645813/4096000', '3999/4000', '7999/8000']  interval_lower 188428355/1099511627776
noncomputable def e2145 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272756784070,0,true,160879593088,160879593152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926266471482,0,false,-188521632640,-188521632576⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272870734922,0,true,160978028736,160978028800⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926152520630,0,false,-188656904704,-188656904640⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272713472780,0,true,160842176576,160842176640⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926309782772,0,false,-188470221760,-188470221696⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272849065034,0,true,160959310080,160959310144⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926174190518,0,false,-188631178944,-188631178880⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522653580,0,true,11025728,11025792⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500601972,0,false,-11025920,-11025856⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533695246,0,true,22067200,22067264⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489560306,0,false,-22067712,-22067648⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627333,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627666,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272735123913,0,true,160860881088,160860881152⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926288131639,0,false,-188495921536,-188495921472⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272859904355,0,true,160968673216,160968673280⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926163351197,0,false,-188644046912,-188644046848⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072181653054,0,false,-27675373696,-27675373632⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072220984498,0,false,-27635040384,-27635040320⟩
    { al := (1290777/8192000), au := (645813/4096000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨173245156294,173359107146⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160879593088,160879593152⟩ : DyadicInterval 40),(⟨-188521632640,-188521632576⟩ : DyadicInterval 40),(⟨748417604869,748417624198⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160978028736,160978028800⟩ : DyadicInterval 40),(⟨-188656904704,-188656904640⟩ : DyadicInterval 40),(⟨748399493255,748399512585⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160842176576,160842176640⟩ : DyadicInterval 40),(⟨-188470221760,-188470221696⟩ : DyadicInterval 40),(⟨748424485704,748424505033⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160959310080,160959310144⟩ : DyadicInterval 40),(⟨-188631178944,-188631178880⟩ : DyadicInterval 40),(⟨748402938439,748402957768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11025804,22067470⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11025728,11025792⟩ : DyadicInterval 40),(⟨-11025920,-11025856⟩ : DyadicInterval 40),(⟨762123383537,762123402866⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22067200,22067264⟩ : DyadicInterval 40),(⟨-22067712,-22067648⟩ : DyadicInterval 40),(⟨762123383365,762123402694⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173223496137,173348276579⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160860881088,160860881152⟩ : DyadicInterval 40),(⟨-188495921536,-188495921472⟩ : DyadicInterval 40),(⟨748421046222,748421065551⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160968673216,160968673280⟩ : DyadicInterval 40),(⟨-188644046912,-188644046848⟩ : DyadicInterval 40),(⟨748401215199,748401234529⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27675373696,-27635040320⟩ : DyadicInterval 40),(⟨775940903776,775961089728⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160879593088,160978028800⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188656904704,-188521632576⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2145_ok : ecellOkT e2145 = true := by decide +kernel
theorem e2145_pos {a z : ℝ} (ha1 : ((1290777/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((645813/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2145 e2145_ok ha1 ha2 hz1 hz2 hz

-- box ['161241/1024000', '1290777/8192000', '7999/8000', '1']  interval_lower 93572469/549755813888
noncomputable def e2146 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272642833219,0,true,160781148608,160781148672⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926380422333,0,false,-188386377216,-188386377152⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272756784071,0,true,160879593088,160879593152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926266471481,0,false,-188521632640,-188521632576⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272621191818,0,true,160762451136,160762451200⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926402063734,0,false,-188360691520,-188360691456⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522654146,0,true,11026304,11026368⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500601406,0,false,-11026432,-11026368⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627665,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1272632007973,0,true,160771795968,160771796032⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨926391247579,0,false,-188373528896,-188373528832⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1272756788436,0,true,160879596864,160879596928⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨926266467116,0,false,-188521637824,-188521637760⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1072214157759,0,false,-27642040960,-27642040896⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1072253465805,0,false,-27601732864,-27601732800⟩
    { al := (161241/1024000), au := (1290777/8192000), zl := (7999/8000), zu := 1,
      A := ⟨173131205443,173245156295⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160781148608,160781148672⟩ : DyadicInterval 40),(⟨-188386377216,-188386377152⟩ : DyadicInterval 40),(⟨748435704383,748435723713⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160879593088,160879593152⟩ : DyadicInterval 40),(⟨-188521632640,-188521632576⟩ : DyadicInterval 40),(⟨748417604869,748417624198⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160762451136,160762451200⟩ : DyadicInterval 40),(⟨-188360691520,-188360691456⟩ : DyadicInterval 40),(⟨748439140450,748439159780⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160879593088,160879593152⟩ : DyadicInterval 40),(⟨-188521632640,-188521632576⟩ : DyadicInterval 40),(⟨748417604869,748417624198⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11026370⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11026304,11026368⟩ : DyadicInterval 40),(⟨-11026432,-11026368⟩ : DyadicInterval 40),(⟨762123383505,762123402834⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨173120380197,173245160660⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160771795968,160771796032⟩ : DyadicInterval 40),(⟨-188373528896,-188373528832⟩ : DyadicInterval 40),(⟨748437423201,748437442531⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160879596864,160879596928⟩ : DyadicInterval 40),(⟨-188521637824,-188521637760⟩ : DyadicInterval 40),(⟨748417604173,748417623503⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27642040960,-27601732800⟩ : DyadicInterval 40),(⟨775924250016,775944423360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨160781148608,160879593152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188521632640,-188386377152⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2146_ok : ecellOkT e2146 = true := by decide +kernel
theorem e2146_pos {a z : ℝ} (ha1 : ((161241/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1290777/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2146 e2146_ok ha1 ha2 hz1 hz2 hz

-- box ['1290777/8192000', '645813/4096000', '7999/8000', '1']  interval_lower 11766687/68719476736
noncomputable def e2147 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272756784070,0,true,160879593088,160879593152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926266471482,0,false,-188521632640,-188521632576⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272870734922,0,true,160978028736,160978028800⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926152520630,0,false,-188656904704,-188656904640⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272735128425,0,true,160860884992,160860885056⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926288127127,0,false,-188495926912,-188495926848⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522661665,0,true,11033792,11033856⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500593887,0,false,-11033984,-11033920⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627665,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1272745951698,0,true,160870235136,160870235200⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨926277303854,0,false,-188508774272,-188508774208⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1272870739285,0,true,160978032512,160978032576⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨926152516267,0,false,-188656909888,-188656909824⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1072178236492,0,false,-27678877312,-27678877248⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1072217572646,0,false,-27638539136,-27638539072⟩
    { al := (1290777/8192000), au := (645813/4096000), zl := (7999/8000), zu := 1,
      A := ⟨173245156294,173359107146⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160879593088,160879593152⟩ : DyadicInterval 40),(⟨-188521632640,-188521632576⟩ : DyadicInterval 40),(⟨748417604869,748417624198⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160978028736,160978028800⟩ : DyadicInterval 40),(⟨-188656904704,-188656904640⟩ : DyadicInterval 40),(⟨748399493255,748399512585⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160860884992,160860885056⟩ : DyadicInterval 40),(⟨-188495926912,-188495926848⟩ : DyadicInterval 40),(⟨748421045510,748421064839⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160978028736,160978028800⟩ : DyadicInterval 40),(⟨-188656904704,-188656904640⟩ : DyadicInterval 40),(⟨748399493255,748399512585⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11033889⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11033792,11033856⟩ : DyadicInterval 40),(⟨-11033984,-11033920⟩ : DyadicInterval 40),(⟨762123383537,762123402866⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨173234323922,173359111509⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160870235136,160870235200⟩ : DyadicInterval 40),(⟨-188508774272,-188508774208⟩ : DyadicInterval 40),(⟨748419325963,748419345292⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160978032512,160978032576⟩ : DyadicInterval 40),(⟨-188656909888,-188656909824⟩ : DyadicInterval 40),(⟨748399492559,748399511889⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27678877312,-27638539072⟩ : DyadicInterval 40),(⟨775942653152,775962841536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨160879593088,160978028800⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188656904704,-188521632576⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2147_ok : ecellOkT e2147 = true := by decide +kernel
theorem e2147_pos {a z : ℝ} (ha1 : ((1290777/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((645813/4096000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2147 e2147_ok ha1 ha2 hz1 hz2 hz

-- box ['645813/4096000', '51699/327680', '3999/4000', '7999/8000']  interval_lower 189553445/1099511627776
noncomputable def e2148 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272870734921,0,true,160978028736,160978028800⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926152520631,0,false,-188656904704,-188656904640⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272984685773,0,true,161076455616,161076455680⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926038569779,0,false,-188792193472,-188792193408⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272827395144,0,true,160940591040,160940591104⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926195860408,0,false,-188605453696,-188605453632⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1272963001641,0,true,161057726272,161057726336⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨926060253911,0,false,-188766447552,-188766447488⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522661099,0,true,11033216,11033280⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500594453,0,false,-11033408,-11033344⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533710286,0,true,22082240,22082304⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489545266,0,false,-22082752,-22082688⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627332,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627666,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272849060520,0,true,160959306176,160959306240⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926174195032,0,false,-188631173568,-188631173504⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1272973848082,0,true,161067094784,161067094848⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨926049407470,0,false,-188779325632,-188779325568⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072145712661,0,false,-27712230784,-27712230720⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072185072212,0,false,-27671867392,-27671867328⟩
    { al := (645813/4096000), au := (51699/327680), zl := (3999/4000), zu := (7999/8000),
      A := ⟨173359107145,173473057997⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160978028736,160978028800⟩ : DyadicInterval 40),(⟨-188656904704,-188656904640⟩ : DyadicInterval 40),(⟨748399493255,748399512585⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161076455616,161076455680⟩ : DyadicInterval 40),(⟨-188792193472,-188792193408⟩ : DyadicInterval 40),(⟨748381369531,748381388860⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160940591040,160940591104⟩ : DyadicInterval 40),(⟨-188605453696,-188605453632⟩ : DyadicInterval 40),(⟨748406383184,748406402514⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161057726272,161057726336⟩ : DyadicInterval 40),(⟨-188766447552,-188766447488⟩ : DyadicInterval 40),(⟨748384819283,748384838613⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11033323,22082510⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11033216,11033280⟩ : DyadicInterval 40),(⟨-11033408,-11033344⟩ : DyadicInterval 40),(⟨762123383537,762123402866⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22082240,22082304⟩ : DyadicInterval 40),(⟨-22082752,-22082688⟩ : DyadicInterval 40),(⟨762123383364,762123402693⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173337432744,173462220306⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160959306176,160959306240⟩ : DyadicInterval 40),(⟨-188631173568,-188631173504⟩ : DyadicInterval 40),(⟨748402939152,748402958481⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161067094784,161067094848⟩ : DyadicInterval 40),(⟨-188779325632,-188779325568⟩ : DyadicInterval 40),(⟨748383093754,748383113084⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27712230784,-27671867328⟩ : DyadicInterval 40),(⟨775959317280,775979518272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨160978028736,161076455680⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188792193472,-188656904640⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2148_ok : ecellOkT e2148 = true := by decide +kernel
theorem e2148_pos {a z : ℝ} (ha1 : ((645813/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((51699/327680 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2148 e2148_ok ha1 ha2 hz1 hz2 hz

-- box ['51699/327680', '323331/2048000', '3999/4000', '7999/8000']  interval_lower 95340439/549755813888
noncomputable def e2149 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272984685772,0,true,161076455616,161076455680⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926038569780,0,false,-188792193472,-188792193408⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273098636624,0,true,161174873664,161174873728⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925924618928,0,false,-188927498816,-188927498752⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272941317507,0,true,161038996608,161038996672⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926081938045,0,false,-188740702272,-188740702208⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273076938248,0,true,161156133696,161156133760⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925946317304,0,false,-188901732864,-188901732800⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522668619,0,true,11040768,11040832⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500586933,0,false,-11040960,-11040896⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533725327,0,true,22097280,22097344⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489530225,0,false,-22097792,-22097728⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627331,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627666,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1272962997120,0,true,161057722368,161057722432⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨926060258432,0,false,-188766442176,-188766442112⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273087791810,0,true,161165507520,161165507584⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925935463742,0,false,-188914620928,-188914620864⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072109748651,0,false,-27749113408,-27749113344⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072149136315,0,false,-27708719744,-27708719680⟩
    { al := (51699/327680), au := (323331/2048000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨173473057996,173587008848⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161076455616,161076455680⟩ : DyadicInterval 40),(⟨-188792193472,-188792193408⟩ : DyadicInterval 40),(⟨748381369531,748381388860⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161174873664,161174873728⟩ : DyadicInterval 40),(⟨-188927498816,-188927498752⟩ : DyadicInterval 40),(⟨748363233677,748363253007⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161038996608,161038996672⟩ : DyadicInterval 40),(⟨-188740702272,-188740702208⟩ : DyadicInterval 40),(⟨748388268614,748388287944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161156133696,161156133760⟩ : DyadicInterval 40),(⟨-188901732864,-188901732800⟩ : DyadicInterval 40),(⟨748366688022,748366707352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11040843,22097551⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11040768,11040832⟩ : DyadicInterval 40),(⟨-11040960,-11040896⟩ : DyadicInterval 40),(⟨762123383537,762123402866⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22097280,22097344⟩ : DyadicInterval 40),(⟨-22097792,-22097728⟩ : DyadicInterval 40),(⟨762123383363,762123402692⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173451369344,173576164034⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161057722368,161057722432⟩ : DyadicInterval 40),(⟨-188766442176,-188766442112⟩ : DyadicInterval 40),(⟨748384819999,748384839328⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161165507520,161165507584⟩ : DyadicInterval 40),(⟨-188914620928,-188914620864⟩ : DyadicInterval 40),(⟨748364960182,748364979512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27749113408,-27708719680⟩ : DyadicInterval 40),(⟨775977743456,775997959584⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161076455616,161174873728⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188927498816,-188792193408⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2149_ok : ecellOkT e2149 = true := by decide +kernel
theorem e2149_pos {a z : ℝ} (ha1 : ((51699/327680 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((323331/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2149 e2149_ok ha1 ha2 hz1 hz2 hz

-- box ['645813/4096000', '51699/327680', '7999/8000', '1']  interval_lower 94695677/549755813888
noncomputable def e2150 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272870734921,0,true,160978028736,160978028800⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926152520631,0,false,-188656904704,-188656904640⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1272984685773,0,true,161076455616,161076455680⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨926038569779,0,false,-188792193472,-188792193408⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272849065032,0,true,160959310080,160959310144⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926174190520,0,false,-188631178944,-188631178880⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522669185,0,true,11041344,11041408⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500586367,0,false,-11041472,-11041408⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627665,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1272859895425,0,true,160968665536,160968665600⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨926163360127,0,false,-188644036352,-188644036288⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1272984690134,0,true,161076459392,161076459456⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨926038565418,0,false,-188792198592,-188792198528⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1072142291605,0,false,-27715739200,-27715739136⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1072181655871,0,false,-27675370816,-27675370752⟩
    { al := (645813/4096000), au := (51699/327680), zl := (7999/8000), zu := 1,
      A := ⟨173359107145,173473057997⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160978028736,160978028800⟩ : DyadicInterval 40),(⟨-188656904704,-188656904640⟩ : DyadicInterval 40),(⟨748399493255,748399512585⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161076455616,161076455680⟩ : DyadicInterval 40),(⟨-188792193472,-188792193408⟩ : DyadicInterval 40),(⟨748381369531,748381388860⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160959310080,160959310144⟩ : DyadicInterval 40),(⟨-188631178944,-188631178880⟩ : DyadicInterval 40),(⟨748402938439,748402957769⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161076455616,161076455680⟩ : DyadicInterval 40),(⟨-188792193472,-188792193408⟩ : DyadicInterval 40),(⟨748381369531,748381388860⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11041409⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11041344,11041408⟩ : DyadicInterval 40),(⟨-11041472,-11041408⟩ : DyadicInterval 40),(⟨762123383505,762123402834⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨173348267649,173473062358⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨160968665536,160968665600⟩ : DyadicInterval 40),(⟨-188644036352,-188644036288⟩ : DyadicInterval 40),(⟨748401216617,748401235946⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161076459392,161076459456⟩ : DyadicInterval 40),(⟨-188792198592,-188792198528⟩ : DyadicInterval 40),(⟨748381368807,748381388136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27715739200,-27675370752⟩ : DyadicInterval 40),(⟨775961068992,775981272480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨160978028736,161076455680⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188792193472,-188656904640⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2150_ok : ecellOkT e2150 = true := by decide +kernel
theorem e2150_pos {a z : ℝ} (ha1 : ((645813/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((51699/327680 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2150 e2150_ok ha1 ha2 hz1 hz2 hz

-- box ['51699/327680', '323331/2048000', '7999/8000', '1']  interval_lower 47629647/274877906944
noncomputable def e2151 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1272984685772,0,true,161076455616,161076455680⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨926038569780,0,false,-188792193472,-188792193408⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273098636624,0,true,161174873664,161174873728⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925924618928,0,false,-188927498816,-188927498752⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1272963001639,0,true,161057726272,161057726336⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926060253913,0,false,-188766447552,-188766447488⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522676706,0,true,11048832,11048896⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099500578846,0,false,-11049024,-11048960⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627664,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1272973839149,0,true,161067087040,161067087104⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨926049416403,0,false,-188779315008,-188779314944⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1273098640987,0,true,161174877440,161174877504⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨925924614565,0,false,-188927504000,-188927503936⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1072106323098,0,false,-27752626496,-27752626432⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1072145715480,0,false,-27712227904,-27712227840⟩
    { al := (51699/327680), au := (323331/2048000), zl := (7999/8000), zu := 1,
      A := ⟨173473057996,173587008848⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161076455616,161076455680⟩ : DyadicInterval 40),(⟨-188792193472,-188792193408⟩ : DyadicInterval 40),(⟨748381369531,748381388860⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161174873664,161174873728⟩ : DyadicInterval 40),(⟨-188927498816,-188927498752⟩ : DyadicInterval 40),(⟨748363233677,748363253007⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161057726272,161057726336⟩ : DyadicInterval 40),(⟨-188766447552,-188766447488⟩ : DyadicInterval 40),(⟨748384819284,748384838613⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161174873664,161174873728⟩ : DyadicInterval 40),(⟨-188927498816,-188927498752⟩ : DyadicInterval 40),(⟨748363233677,748363253007⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11048930⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11048832,11048896⟩ : DyadicInterval 40),(⟨-11049024,-11048960⟩ : DyadicInterval 40),(⟨762123383536,762123402865⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨173462211373,173587013211⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161067087040,161067087104⟩ : DyadicInterval 40),(⟨-188779315008,-188779314944⟩ : DyadicInterval 40),(⟨748383095184,748383114513⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161174877440,161174877504⟩ : DyadicInterval 40),(⟨-188927504000,-188927503936⟩ : DyadicInterval 40),(⟨748363232979,748363252309⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27752626496,-27712227840⟩ : DyadicInterval 40),(⟨775979497536,775999716128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨161076455616,161174873728⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-188927498816,-188792193408⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e2151_ok : ecellOkT e2151 = true := by decide +kernel
theorem e2151_pos {a z : ℝ} (ha1 : ((51699/327680 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((323331/2048000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2151 e2151_ok ha1 ha2 hz1 hz2 hz

-- box ['323331/2048000', '1294173/8192000', '1999/2000', '7997/8000']  interval_lower 192136935/1099511627776
noncomputable def e2152 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273098636623,0,true,161174873664,161174873728⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925924618929,0,false,-188927498816,-188927498752⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273212587475,0,true,161273282944,161273283008⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925810668077,0,false,-189062820864,-189062820800⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273011843118,0,true,161099911936,161099912000⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨926011412434,0,false,-188824438592,-188824438528⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273147449616,0,true,161217030208,161217030272⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925875805936,0,false,-188985464512,-188985464448⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544773228,0,true,33144896,33144960⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478482324,0,false,-33145984,-33145920⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555852499,0,true,44223808,44223872⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467403053,0,false,-44225664,-44225600⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625997,0,false,-1792,-1728⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626777,0,false,-1024,-960⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273055235499,0,true,161137389696,161137389760⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925968020053,0,false,-188875962304,-188875962240⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273180023022,0,true,161245160832,161245160896⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925843232530,0,false,-189024147328,-189024147264⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072080620458,0,false,-27778986496,-27778986432⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072120026796,0,false,-27738572608,-27738572544⟩
    { al := (323331/2048000), au := (1294173/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨173587008847,173700959699⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161174873664,161174873728⟩ : DyadicInterval 40),(⟨-188927498816,-188927498752⟩ : DyadicInterval 40),(⟨748363233677,748363253007⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161273282944,161273283008⟩ : DyadicInterval 40),(⟨-189062820864,-189062820800⟩ : DyadicInterval 40),(⟨748345085710,748345105039⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161099911936,161099912000⟩ : DyadicInterval 40),(⟨-188824438592,-188824438528⟩ : DyadicInterval 40),(⟨748377048372,748377067702⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161217030208,161217030272⟩ : DyadicInterval 40),(⟨-188985464512,-188985464448⟩ : DyadicInterval 40),(⟨748355461133,748355480462⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨33145452,44224723⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33144896,33144960⟩ : DyadicInterval 40),(⟨-33145984,-33145920⟩ : DyadicInterval 40),(⟨762123383096,762123402425⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44223808,44223872⟩ : DyadicInterval 40),(⟨-44225664,-44225600⟩ : DyadicInterval 40),(⟨762123382701,762123402030⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1792,-960⟩ : DyadicInterval 40),(⟨762123384096,762123403776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173543607723,173668395246⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161137389696,161137389760⟩ : DyadicInterval 40),(⟨-188875962304,-188875962240⟩ : DyadicInterval 40),(⟨748370142579,748370161908⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161245160832,161245160896⟩ : DyadicInterval 40),(⟨-189024147328,-189024147264⟩ : DyadicInterval 40),(⟨748350273187,748350292517⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27778986496,-27738572544⟩ : DyadicInterval 40),(⟨775992669888,776012896128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161174873664,161273283008⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189062820864,-188927498752⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2152_ok : ecellOkT e2152 = true := by decide +kernel
theorem e2152_pos {a z : ℝ} (ha1 : ((323331/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1294173/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2152 e2152_ok ha1 ha2 hz1 hz2 hz

-- box ['1294173/8192000', '647511/4096000', '1999/2000', '7997/8000']  interval_lower 6039711/34359738368
noncomputable def e2153 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273212587474,0,true,161273282944,161273283008⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925810668078,0,false,-189062820864,-189062820800⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273326538327,0,true,161371683392,161371683456⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925696717225,0,false,-189198159552,-189198159488⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273125736994,0,true,161198278656,161198278720⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925897518558,0,false,-188959680256,-188959680192⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273261357736,0,true,161315398784,161315398848⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925761897816,0,false,-189120742912,-189120742848⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544795790,0,true,33167488,33167552⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478459762,0,false,-33168576,-33168512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555882584,0,true,44253888,44253952⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467372968,0,false,-44255744,-44255680⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625994,0,false,-1792,-1728⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626776,0,false,-1024,-960⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273169157861,0,true,161235777664,161235777728⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925854097691,0,false,-189011244160,-189011244096⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273293952509,0,true,161343545280,161343545344⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925729303043,0,false,-189159455872,-189159455808⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072044618217,0,false,-27815910528,-27815910464⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072084052666,0,false,-27775466432,-27775466368⟩
    { al := (1294173/8192000), au := (647511/4096000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨173700959698,173814910551⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161273282944,161273283008⟩ : DyadicInterval 40),(⟨-189062820864,-189062820800⟩ : DyadicInterval 40),(⟨748345085710,748345105039⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161371683392,161371683456⟩ : DyadicInterval 40),(⟨-189198159552,-189198159488⟩ : DyadicInterval 40),(⟨748326925638,748326944968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161198278656,161198278720⟩ : DyadicInterval 40),(⟨-188959680256,-188959680192⟩ : DyadicInterval 40),(⟨748358918722,748358938052⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161315398784,161315398848⟩ : DyadicInterval 40),(⟨-189120742912,-189120742848⟩ : DyadicInterval 40),(⟨748337314792,748337334121⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨33168014,44254808⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33167488,33167552⟩ : DyadicInterval 40),(⟨-33168576,-33168512⟩ : DyadicInterval 40),(⟨762123383095,762123402424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44253888,44253952⟩ : DyadicInterval 40),(⟨-44255744,-44255680⟩ : DyadicInterval 40),(⟨762123382698,762123402027⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1792,-960⟩ : DyadicInterval 40),(⟨762123384096,762123403776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173657530085,173782324733⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161235777664,161235777728⟩ : DyadicInterval 40),(⟨-189011244160,-189011244096⟩ : DyadicInterval 40),(⟨748352003793,748352023122⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161343545280,161343545344⟩ : DyadicInterval 40),(⟨-189159455872,-189159455808⟩ : DyadicInterval 40),(⟨748332120018,748332139348⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27815910528,-27775466368⟩ : DyadicInterval 40),(⟨776011116800,776031358144⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161273282944,161371683456⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189198159552,-189062820800⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2153_ok : ecellOkT e2153 = true := by decide +kernel
theorem e2153_pos {a z : ℝ} (ha1 : ((1294173/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((647511/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2153 e2153_ok ha1 ha2 hz1 hz2 hz

-- box ['323331/2048000', '1294173/8192000', '7997/8000', '3999/4000']  interval_lower 191974041/1099511627776
noncomputable def e2154 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273098636623,0,true,161174873664,161174873728⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925924618929,0,false,-188927498816,-188927498752⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273212587475,0,true,161273282944,161273283008⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925810668077,0,false,-189062820864,-189062820800⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273033541494,0,true,161118652864,161118652928⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925989714058,0,false,-188850202752,-188850202688⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273169162236,0,true,161235781440,161235781504⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925854093316,0,false,-189011249344,-189011249280⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533724709,0,true,22096704,22096768⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489530843,0,false,-22097216,-22097152⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544796459,0,true,33168128,33168192⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478459093,0,false,-33169216,-33169152⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626775,0,false,-1024,-960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627332,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273066084601,0,true,161146759744,161146759808⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925957170951,0,false,-188888844800,-188888844736⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273190879271,0,true,161254536192,161254536256⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925832376281,0,false,-189037040064,-189037040000⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072077190851,0,false,-27782503872,-27782503808⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072116601910,0,false,-27742084992,-27742084928⟩
    { al := (323331/2048000), au := (1294173/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨173587008847,173700959699⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161174873664,161174873728⟩ : DyadicInterval 40),(⟨-188927498816,-188927498752⟩ : DyadicInterval 40),(⟨748363233677,748363253007⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161273282944,161273283008⟩ : DyadicInterval 40),(⟨-189062820864,-189062820800⟩ : DyadicInterval 40),(⟨748345085710,748345105039⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161118652864,161118652928⟩ : DyadicInterval 40),(⟨-188850202752,-188850202688⟩ : DyadicInterval 40),(⟨748373595351,748373614681⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161235781440,161235781504⟩ : DyadicInterval 40),(⟨-189011249344,-189011249280⟩ : DyadicInterval 40),(⟨748352003092,748352022422⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22096933,33168683⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22096704,22096768⟩ : DyadicInterval 40),(⟨-22097216,-22097152⟩ : DyadicInterval 40),(⟨762123383363,762123402692⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33168128,33168192⟩ : DyadicInterval 40),(⟨-33169216,-33169152⟩ : DyadicInterval 40),(⟨762123383095,762123402424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1024,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173554456825,173679251495⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161146759744,161146759808⟩ : DyadicInterval 40),(⟨-188888844800,-188888844736⟩ : DyadicInterval 40),(⟨748368415730,748368435060⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161254536192,161254536256⟩ : DyadicInterval 40),(⟨-189037040064,-189037040000⟩ : DyadicInterval 40),(⟨748348543910,748348563239⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27782503872,-27742084928⟩ : DyadicInterval 40),(⟨775994426080,776014654816⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161174873664,161273283008⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189062820864,-188927498752⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2154_ok : ecellOkT e2154 = true := by decide +kernel
theorem e2154_pos {a z : ℝ} (ha1 : ((323331/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1294173/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2154 e2154_ok ha1 ha2 hz1 hz2 hz

-- box ['1294173/8192000', '647511/4096000', '7997/8000', '3999/4000']  interval_lower 12069237/68719476736
noncomputable def e2155 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273212587474,0,true,161273282944,161273283008⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925810668078,0,false,-189062820864,-189062820800⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273326538327,0,true,161371683392,161371683456⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925696717225,0,false,-189198159552,-189198159488⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273147449614,0,true,161217030208,161217030272⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925875805938,0,false,-188985464512,-188985464448⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273283084600,0,true,161334160640,161334160704⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925740170952,0,false,-189146547840,-189146547776⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533739750,0,true,22111744,22111808⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489515802,0,false,-22112256,-22112192⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544819023,0,true,33190720,33190784⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478436529,0,false,-33191808,-33191744⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626774,0,false,-1024,-960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627332,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273180014084,0,true,161245153088,161245153152⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925843241468,0,false,-189024136704,-189024136640⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273304815880,0,true,161352925952,161352926016⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925718439672,0,false,-189172358656,-189172358592⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072041184109,0,false,-27819432640,-27819432576⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072080623282,0,false,-27778983616,-27778983552⟩
    { al := (1294173/8192000), au := (647511/4096000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨173700959698,173814910551⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161273282944,161273283008⟩ : DyadicInterval 40),(⟨-189062820864,-189062820800⟩ : DyadicInterval 40),(⟨748345085710,748345105039⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161371683392,161371683456⟩ : DyadicInterval 40),(⟨-189198159552,-189198159488⟩ : DyadicInterval 40),(⟨748326925638,748326944968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161217030208,161217030272⟩ : DyadicInterval 40),(⟨-188985464512,-188985464448⟩ : DyadicInterval 40),(⟨748355461133,748355480462⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161334160640,161334160704⟩ : DyadicInterval 40),(⟨-189146547840,-189146547776⟩ : DyadicInterval 40),(⟨748333852175,748333871505⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22111974,33191247⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22111744,22111808⟩ : DyadicInterval 40),(⟨-22112256,-22112192⟩ : DyadicInterval 40),(⟨762123383363,762123402692⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33190720,33190784⟩ : DyadicInterval 40),(⟨-33191808,-33191744⟩ : DyadicInterval 40),(⟨762123383094,762123402423⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1024,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173668386308,173793188104⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161245153088,161245153152⟩ : DyadicInterval 40),(⟨-189024136704,-189024136640⟩ : DyadicInterval 40),(⟨748350274622,748350293951⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161352925952,161352926016⟩ : DyadicInterval 40),(⟨-189172358656,-189172358592⟩ : DyadicInterval 40),(⟨748330388452,748330407781⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27819432640,-27778983552⟩ : DyadicInterval 40),(⟨776012875392,776033119200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161273282944,161371683456⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189198159552,-189062820800⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2155_ok : ecellOkT e2155 = true := by decide +kernel
theorem e2155_pos {a z : ℝ} (ha1 : ((1294173/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((647511/4096000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2155 e2155_ok ha1 ha2 hz1 hz2 hz

-- box ['647511/4096000', '1295871/8192000', '1999/2000', '7997/8000']  interval_lower 194407639/1099511627776
noncomputable def e2156 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273326538326,0,true,161371683392,161371683456⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925696717226,0,false,-189198159552,-189198159488⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273440489178,0,true,161470075008,161470075072⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925582766374,0,false,-189333514880,-189333514816⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273239630870,0,true,161296636608,161296636672⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925783624682,0,false,-189094938624,-189094938560⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273375265856,0,true,161413758592,161413758656⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925647989696,0,false,-189256037952,-189256037888⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544818354,0,true,33190016,33190080⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478437198,0,false,-33191104,-33191040⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555912672,0,true,44283968,44284032⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467342880,0,false,-44285824,-44285760⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625992,0,false,-1792,-1728⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626775,0,false,-1024,-960⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273283080221,0,true,161334156864,161334156928⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925740175331,0,false,-189146542656,-189146542592⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273407881997,0,true,161441921024,161441921088⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925615373555,0,false,-189294781056,-189294780992⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072008592366,0,false,-27852860032,-27852859968⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072048054930,0,false,-27812385792,-27812385728⟩
    { al := (647511/4096000), au := (1295871/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨173814910550,173928861402⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161371683392,161371683456⟩ : DyadicInterval 40),(⟨-189198159552,-189198159488⟩ : DyadicInterval 40),(⟨748326925638,748326944968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161470075008,161470075072⟩ : DyadicInterval 40),(⟨-189333514880,-189333514816⟩ : DyadicInterval 40),(⟨748308753461,748308772790⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161296636608,161296636672⟩ : DyadicInterval 40),(⟨-189094938624,-189094938560⟩ : DyadicInterval 40),(⟨748340776982,748340796312⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161413758592,161413758656⟩ : DyadicInterval 40),(⟨-189256037952,-189256037888⟩ : DyadicInterval 40),(⟨748319156327,748319175656⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨33190578,44284896⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33190016,33190080⟩ : DyadicInterval 40),(⟨-33191104,-33191040⟩ : DyadicInterval 40),(⟨762123383094,762123402423⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44283968,44284032⟩ : DyadicInterval 40),(⟨-44285824,-44285760⟩ : DyadicInterval 40),(⟨762123382696,762123402025⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1792,-960⟩ : DyadicInterval 40),(⟨762123384096,762123403776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173771452445,173896254221⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161334156864,161334156928⟩ : DyadicInterval 40),(⟨-189146542656,-189146542592⟩ : DyadicInterval 40),(⟨748333852877,748333872207⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161441921024,161441921088⟩ : DyadicInterval 40),(⟨-189294781056,-189294780992⟩ : DyadicInterval 40),(⟨748313954679,748313974008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27852860032,-27812385728⟩ : DyadicInterval 40),(⟨776029576480,776049832896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161371683392,161470075072⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189333514880,-189198159488⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2156_ok : ecellOkT e2156 = true := by decide +kernel
theorem e2156_pos {a z : ℝ} (ha1 : ((647511/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1295871/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2156 e2156_ok ha1 ha2 hz1 hz2 hz

-- box ['1295871/8192000', '16209/102400', '1999/2000', '7997/8000']  interval_lower 24443387/137438953472
noncomputable def e2157 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273440489177,0,true,161470075008,161470075072⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925582766375,0,false,-189333514880,-189333514816⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273554440029,0,true,161568457856,161568457920⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925468815523,0,false,-189468886912,-189468886848⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273353524746,0,true,161394985792,161394985856⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925669730806,0,false,-189230213568,-189230213504⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273489173975,0,true,161512109568,161512109632⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925534081577,0,false,-189391349696,-189391349632⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544840920,0,true,33212608,33212672⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478414632,0,false,-33213696,-33213632⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099555942762,0,true,44314048,44314112⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099467312790,0,false,-44315904,-44315840⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625989,0,false,-1792,-1728⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626773,0,false,-1024,-960⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273397002584,0,true,161432527232,161432527296⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925626252968,0,false,-189281857792,-189281857728⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273521811481,0,true,161540287936,161540288000⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925501444071,0,false,-189430122944,-189430122880⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071972542905,0,false,-27889834944,-27889834880⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072012033586,0,false,-27849330496,-27849330432⟩
    { al := (1295871/8192000), au := (16209/102400), zl := (1999/2000), zu := (7997/8000),
      A := ⟨173928861401,174042812253⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161470075008,161470075072⟩ : DyadicInterval 40),(⟨-189333514880,-189333514816⟩ : DyadicInterval 40),(⟨748308753461,748308772790⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161568457856,161568457920⟩ : DyadicInterval 40),(⟨-189468886912,-189468886848⟩ : DyadicInterval 40),(⟨748290569166,748290588496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161394985792,161394985856⟩ : DyadicInterval 40),(⟨-189230213568,-189230213504⟩ : DyadicInterval 40),(⟨748322623098,748322642428⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161512109568,161512109632⟩ : DyadicInterval 40),(⟨-189391349696,-189391349632⟩ : DyadicInterval 40),(⟨748300985800,748301005130⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨33213144,44314986⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33212608,33212672⟩ : DyadicInterval 40),(⟨-33213696,-33213632⟩ : DyadicInterval 40),(⟨762123383092,762123402421⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨44314048,44314112⟩ : DyadicInterval 40),(⟨-44315904,-44315840⟩ : DyadicInterval 40),(⟨762123382693,762123402022⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1792,-960⟩ : DyadicInterval 40),(⟨762123384096,762123403776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173885374808,174010183705⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161432527232,161432527296⟩ : DyadicInterval 40),(⟨-189281857792,-189281857728⟩ : DyadicInterval 40),(⟨748315689869,748315709198⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161540287936,161540288000⟩ : DyadicInterval 40),(⟨-189430122944,-189430122880⟩ : DyadicInterval 40),(⟨748295777269,748295796598⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27889834944,-27849330432⟩ : DyadicInterval 40),(⟨776048048832,776068320352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161470075008,161568457920⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189468886912,-189333514816⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2157_ok : ecellOkT e2157 = true := by decide +kernel
theorem e2157_pos {a z : ℝ} (ha1 : ((1295871/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((16209/102400 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2157 e2157_ok ha1 ha2 hz1 hz2 hz

-- box ['647511/4096000', '1295871/8192000', '7997/8000', '3999/4000']  interval_lower 194244207/1099511627776
noncomputable def e2158 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273326538326,0,true,161371683392,161371683456⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925696717226,0,false,-189198159552,-189198159488⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273440489178,0,true,161470075008,161470075072⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925582766374,0,false,-189333514880,-189333514816⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273261357734,0,true,161315398784,161315398848⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925761897818,0,false,-189120742912,-189120742848⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273397006963,0,true,161432531008,161432531072⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925626248589,0,false,-189281862976,-189281862912⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533754793,0,true,22126784,22126848⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489500759,0,false,-22127296,-22127232⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544841589,0,true,33213248,33213312⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478413963,0,false,-33214336,-33214272⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626772,0,false,-1024,-960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627331,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273293943569,0,true,161343537600,161343537664⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925729311983,0,false,-189159445248,-189159445184⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273418752486,0,true,161451307008,161451307072⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925604503066,0,false,-189307693888,-189307693824⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1072005153755,0,false,-27856386880,-27856386816⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072044621044,0,false,-27815907648,-27815907584⟩
    { al := (647511/4096000), au := (1295871/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨173814910550,173928861402⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161371683392,161371683456⟩ : DyadicInterval 40),(⟨-189198159552,-189198159488⟩ : DyadicInterval 40),(⟨748326925638,748326944968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161470075008,161470075072⟩ : DyadicInterval 40),(⟨-189333514880,-189333514816⟩ : DyadicInterval 40),(⟨748308753461,748308772790⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161315398784,161315398848⟩ : DyadicInterval 40),(⟨-189120742912,-189120742848⟩ : DyadicInterval 40),(⟨748337314792,748337334122⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161432531008,161432531072⟩ : DyadicInterval 40),(⟨-189281862976,-189281862912⟩ : DyadicInterval 40),(⟨748315689166,748315708495⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22127017,33213813⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22126784,22126848⟩ : DyadicInterval 40),(⟨-22127296,-22127232⟩ : DyadicInterval 40),(⟨762123383362,762123402691⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33213248,33213312⟩ : DyadicInterval 40),(⟨-33214336,-33214272⟩ : DyadicInterval 40),(⟨762123383092,762123402421⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1024,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173782315793,173907124710⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161343537600,161343537664⟩ : DyadicInterval 40),(⟨-189159445248,-189159445184⟩ : DyadicInterval 40),(⟨748332121417,748332140747⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161451307008,161451307072⟩ : DyadicInterval 40),(⟨-189307693888,-189307693824⟩ : DyadicInterval 40),(⟨748312220821,748312240151⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27856386880,-27815907584⟩ : DyadicInterval 40),(⟨776031337408,776051596320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161371683392,161470075072⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189333514880,-189198159488⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2158_ok : ecellOkT e2158 = true := by decide +kernel
theorem e2158_pos {a z : ℝ} (ha1 : ((647511/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1295871/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2158 e2158_ok ha1 ha2 hz1 hz2 hz

-- box ['1295871/8192000', '16209/102400', '7997/8000', '3999/4000']  interval_lower 195383283/1099511627776
noncomputable def e2159 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1273440489177,0,true,161470075008,161470075072⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨925582766375,0,false,-189333514880,-189333514816⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1273554440029,0,true,161568457856,161568457920⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨925468815523,0,false,-189468886912,-189468886848⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1273375265853,0,true,161413758592,161413758656⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨925647989699,0,false,-189256037952,-189256037888⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1273510929327,0,true,161530892608,161530892672⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨925512326225,0,false,-189417194816,-189417194752⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099533769837,0,true,22141824,22141888⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099489485715,0,false,-22142336,-22142272⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099544864157,0,true,33235840,33235904⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099478391395,0,false,-33236928,-33236864⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626771,0,false,-1024,-960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627331,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1273407873054,0,true,161441913280,161441913344⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨925615382498,0,false,-189294770432,-189294770368⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1273532689092,0,true,161549679232,161549679296⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨925490566460,0,false,-189443045760,-189443045696⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1071969099787,0,false,-27893366528,-27893366464⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1072008595196,0,false,-27852857088,-27852857024⟩
    { al := (1295871/8192000), au := (16209/102400), zl := (7997/8000), zu := (3999/4000),
      A := ⟨173928861401,174042812253⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161470075008,161470075072⟩ : DyadicInterval 40),(⟨-189333514880,-189333514816⟩ : DyadicInterval 40),(⟨748308753461,748308772790⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161568457856,161568457920⟩ : DyadicInterval 40),(⟨-189468886912,-189468886848⟩ : DyadicInterval 40),(⟨748290569166,748290588496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161413758592,161413758656⟩ : DyadicInterval 40),(⟨-189256037952,-189256037888⟩ : DyadicInterval 40),(⟨748319156327,748319175656⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161530892608,161530892672⟩ : DyadicInterval 40),(⟨-189417194816,-189417194752⟩ : DyadicInterval 40),(⟨748297514051,748297533381⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨22142061,33236381⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22141824,22141888⟩ : DyadicInterval 40),(⟨-22142336,-22142272⟩ : DyadicInterval 40),(⟨762123383362,762123402691⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33235840,33235904⟩ : DyadicInterval 40),(⟨-33236928,-33236864⟩ : DyadicInterval 40),(⟨762123383091,762123402420⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1024,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨173896245278,174021061316⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161441913280,161441913344⟩ : DyadicInterval 40),(⟨-189294770432,-189294770368⟩ : DyadicInterval 40),(⟨748313956117,748313975447⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨161549679232,161549679296⟩ : DyadicInterval 40),(⟨-189443045760,-189443045696⟩ : DyadicInterval 40),(⟨748294041090,748294060419⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-27893366528,-27852857024⟩ : DyadicInterval 40),(⟨776049812128,776070086144⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨161470075008,161568457920⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-189468886912,-189333514816⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e2159_ok : ecellOkT e2159 = true := by decide +kernel
theorem e2159_pos {a z : ℝ} (ha1 : ((1295871/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((16209/102400 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e2159 e2159_ok ha1 ha2 hz1 hz2 hz

end CKLaneC2R.EpCells.B035

end


