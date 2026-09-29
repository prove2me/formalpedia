-- Prove2me | Definitions.Def_CK_CKLaneC2R_EpCells_B022
-- name    : CK_CKLaneC2R_EpCells_B022
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T14:15:13.691982+00:00
-- url     : https://prove2.me/theorems/b5e89e37-ab38-4dbf-acca-133571b3f760
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EpCells.B022` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EpCells.B022` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EpCells.B022` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EpCells.B022 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EpCells/B022.lean)

import Definitions.Def_CK_CKLaneC2R_EndpointCheckT

-- ===== source module CKLaneC2R.EpCells.B022 =====
section

namespace CKLaneC2R.EpCells.B022

open GeneralCK GeneralCK.Certificates CKLaneC2R CKLaneC2R.Endpoint

-- box ['852969/4096000', '426909/2048000', '3999/4000', '1']  interval_lower 704471091/1099511627776
noncomputable def e1320 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1328478750244,0,true,207992838144,207992838208⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨870544505308,0,false,-256738715456,-256738715392⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1328706651948,0,true,208181444160,208181444224⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨870316603604,0,false,-257026596608,-257026596544⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1328421508463,0,true,207945461120,207945461184⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨870601747089,0,false,-256666420544,-256666420480⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541211513,0,true,29583296,29583360⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482044039,0,false,-29584192,-29584128⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626980,0,false,-832,-768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1328450123676,0,true,207969145152,207969145216⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨870573131876,0,false,-256702560256,-256702560192⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1328706660494,0,true,208181451200,208181451264⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨870316595058,0,false,-257026607424,-257026607360⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1051735540924,0,false,-48845156160,-48845156096⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1051842432126,0,false,-48733414976,-48733414912⟩
    { al := (852969/4096000), au := (426909/2048000), zl := (3999/4000), zu := 1,
      A := ⟨228967122468,229195024172⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207992838144,207992838208⟩ : DyadicInterval 40),(⟨-256738715456,-256738715392⟩ : DyadicInterval 40),(⟨738107453977,738107473307⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208181444160,208181444224⟩ : DyadicInterval 40),(⟨-257026596608,-257026596544⟩ : DyadicInterval 40),(⟨738059265567,738059284896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207945461120,207945461184⟩ : DyadicInterval 40),(⟨-256666420544,-256666420480⟩ : DyadicInterval 40),(⟨738119549639,738119568969⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208181444160,208181444224⟩ : DyadicInterval 40),(⟨-257026596608,-257026596544⟩ : DyadicInterval 40),(⟨738059265567,738059284896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,29583737⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29583296,29583360⟩ : DyadicInterval 40),(⟨-29584192,-29584128⟩ : DyadicInterval 40),(⟨762123383204,762123402533⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-832,0⟩ : DyadicInterval 40),(⟨762123383616,762123403296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨228938495900,229195032718⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨207969145152,207969145216⟩ : DyadicInterval 40),(⟨-256702560256,-256702560192⟩ : DyadicInterval 40),(⟨738113503428,738113522757⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208181451200,208181451264⟩ : DyadicInterval 40),(⟨-257026607424,-257026607360⟩ : DyadicInterval 40),(⟨738059263786,738059283116⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-48845156160,-48733414912⟩ : DyadicInterval 40),(⟨786490091072,786545980960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨207992838144,208181444224⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-257026596608,-256738715392⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1320_ok : ecellOkT e1320 = true := by decide +kernel
theorem e1320_pos {a z : ℝ} (ha1 : ((852969/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((426909/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1320 e1320_ok ha1 ha2 hz1 hz2 hz

-- box ['426909/2048000', '854667/4096000', '1999/2000', '3999/4000']  interval_lower 177758383/274877906944
noncomputable def e1321 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1328706651947,0,true,208181444160,208181444224⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨870316603605,0,false,-257026596608,-257026596544⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1328934553650,0,true,208370017792,208370017856⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨870088701902,0,false,-257314553216,-257314553152⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1328592054434,0,true,208086610048,208086610112⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨870431201118,0,false,-256881829760,-256881829696⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1328877197919,0,true,208322562752,208322562816⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨870146057633,0,false,-257242076416,-257242076352⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541210511,0,true,29582336,29582400⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482045041,0,false,-29583168,-29583104⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570857209,0,true,59227776,59227840⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452398343,0,false,-59231040,-59230976⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624585,0,false,-3200,-3136⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626981,0,false,-832,-768⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1328649347854,0,true,208134023680,208134023744⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨870373907698,0,false,-256954204096,-256954204032⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1328905884439,0,true,208346297728,208346297792⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨870117371113,0,false,-257278325120,-257278325056⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1051652447699,0,false,-48932027392,-48932027328⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1051759431769,0,false,-48820180352,-48820180288⟩
    { al := (426909/2048000), au := (854667/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨229195024171,229422925874⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208181444160,208181444224⟩ : DyadicInterval 40),(⟨-257026596608,-257026596544⟩ : DyadicInterval 40),(⟨738059265567,738059284897⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208370017792,208370017856⟩ : DyadicInterval 40),(⟨-257314553216,-257314553152⟩ : DyadicInterval 40),(⟨738011027820,738011047149⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208086610048,208086610112⟩ : DyadicInterval 40),(⟨-256881829760,-256881829696⟩ : DyadicInterval 40),(⟨738083502669,738083521999⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208322562752,208322562816⟩ : DyadicInterval 40),(⟨-257242076416,-257242076352⟩ : DyadicInterval 40),(⟨738023172392,738023191722⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨29582735,59229433⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29582336,29582400⟩ : DyadicInterval 40),(⟨-29583168,-29583104⟩ : DyadicInterval 40),(⟨762123383172,762123402501⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59227776,59227840⟩ : DyadicInterval 40),(⟨-59231040,-59230976⟩ : DyadicInterval 40),(⟨762123381993,762123401322⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3200,-768⟩ : DyadicInterval 40),(⟨762123384000,762123404480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨229137720078,229394256663⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208134023680,208134023744⟩ : DyadicInterval 40),(⟨-256954204096,-256954204032⟩ : DyadicInterval 40),(⟨738071386840,738071406169⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208346297728,208346297792⟩ : DyadicInterval 40),(⟨-257278325120,-257278325056⟩ : DyadicInterval 40),(⟨738017098627,738017117956⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-48932027392,-48820180288⟩ : DyadicInterval 40),(⟨786533473760,786589416576⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨208181444160,208370017856⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-257314553216,-257026596544⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1321_ok : ecellOkT e1321 = true := by decide +kernel
theorem e1321_pos {a z : ℝ} (ha1 : ((426909/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((854667/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1321 e1321_ok ha1 ha2 hz1 hz2 hz

-- box ['854667/4096000', '213879/1024000', '1999/2000', '3999/4000']  interval_lower 716599427/1099511627776
noncomputable def e1322 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1328934553649,0,true,208370017792,208370017856⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨870088701903,0,false,-257314553216,-257314553152⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1329162455352,0,true,208558559168,208558559232⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨869860800200,0,false,-257602585216,-257602585152⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1328819842186,0,true,208275105664,208275105728⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨870203413366,0,false,-257169604416,-257169604352⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1329105042646,0,true,208511065088,208511065152⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨869918212906,0,false,-257530017408,-257530017344⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541241862,0,true,29613632,29613696⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482013690,0,false,-29614528,-29614464⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570919923,0,true,59290496,59290560⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452335629,0,false,-59293760,-59293696⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624578,0,false,-3200,-3136⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626979,0,false,-832,-768⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1328877192572,0,true,208322558336,208322558400⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨870146062980,0,false,-257242069696,-257242069632⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1329133757659,0,true,208534819520,208534819584⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨869889497893,0,false,-257566311680,-257566311616⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1051557316789,0,false,-49031492096,-49031492032⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1051664419084,0,false,-48919511296,-48919511232⟩
    { al := (854667/4096000), au := (213879/1024000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨229422925873,229650827576⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208370017792,208370017856⟩ : DyadicInterval 40),(⟨-257314553216,-257314553152⟩ : DyadicInterval 40),(⟨738011027820,738011047149⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208558559168,208558559232⟩ : DyadicInterval 40),(⟨-257602585216,-257602585152⟩ : DyadicInterval 40),(⟨737962740618,737962759948⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208275105664,208275105728⟩ : DyadicInterval 40),(⟨-257169604416,-257169604352⟩ : DyadicInterval 40),(⟨738035313846,738035333176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208511065088,208511065152⟩ : DyadicInterval 40),(⟨-257530017408,-257530017344⟩ : DyadicInterval 40),(⟨737974909719,737974929049⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨29614086,59292147⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29613632,29613696⟩ : DyadicInterval 40),(⟨-29614528,-29614464⟩ : DyadicInterval 40),(⟨762123383202,762123402531⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59290496,59290560⟩ : DyadicInterval 40),(⟨-59293760,-59293696⟩ : DyadicInterval 40),(⟨762123381986,762123401315⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3200,-768⟩ : DyadicInterval 40),(⟨762123384000,762123404480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨229365564796,229622129883⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208322558336,208322558400⟩ : DyadicInterval 40),(⟨-257242069696,-257242069632⟩ : DyadicInterval 40),(⟨738023173534,738023192863⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208534819520,208534819584⟩ : DyadicInterval 40),(⟨-257566311680,-257566311616⟩ : DyadicInterval 40),(⟨737968823750,737968843080⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-49031492096,-48919511232⟩ : DyadicInterval 40),(⟨786583139232,786639148928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨208370017792,208558559232⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-257602585216,-257314553152⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1322_ok : ecellOkT e1322 = true := by decide +kernel
theorem e1322_pos {a z : ℝ} (ha1 : ((854667/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((213879/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1322 e1322_ok ha1 ha2 hz1 hz2 hz

-- box ['426909/2048000', '854667/4096000', '3999/4000', '1']  interval_lower 177503131/274877906944
noncomputable def e1323 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1328706651947,0,true,208181444160,208181444224⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨870316603605,0,false,-257026596608,-257026596544⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1328934553650,0,true,208370017792,208370017856⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨870088701902,0,false,-257314553216,-257314553152⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1328649353190,0,true,208134028096,208134028160⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨870373902362,0,false,-256954210816,-256954210752⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541242864,0,true,29614656,29614720⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099482012688,0,false,-29615488,-29615424⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626978,0,false,-832,-768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1328677996887,0,true,208157731712,208157731776⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨870345258665,0,false,-256990395968,-256990395904⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1328934562187,0,true,208370024896,208370024960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨870088693365,0,false,-257314563968,-257314563904⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1051640480710,0,false,-48944539072,-48944539008⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1051747490131,0,false,-48832664256,-48832664192⟩
    { al := (426909/2048000), au := (854667/4096000), zl := (3999/4000), zu := 1,
      A := ⟨229195024171,229422925874⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208181444160,208181444224⟩ : DyadicInterval 40),(⟨-257026596608,-257026596544⟩ : DyadicInterval 40),(⟨738059265567,738059284897⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208370017792,208370017856⟩ : DyadicInterval 40),(⟨-257314553216,-257314553152⟩ : DyadicInterval 40),(⟨738011027820,738011047149⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208134028096,208134028160⟩ : DyadicInterval 40),(⟨-256954210816,-256954210752⟩ : DyadicInterval 40),(⟨738071385703,738071405033⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208370017792,208370017856⟩ : DyadicInterval 40),(⟨-257314553216,-257314553152⟩ : DyadicInterval 40),(⟨738011027820,738011047149⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,29615088⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29614656,29614720⟩ : DyadicInterval 40),(⟨-29615488,-29615424⟩ : DyadicInterval 40),(⟨762123383170,762123402499⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-832,0⟩ : DyadicInterval 40),(⟨762123383616,762123403296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨229166369111,229422934411⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208157731712,208157731776⟩ : DyadicInterval 40),(⟨-256990395968,-256990395904⟩ : DyadicInterval 40),(⟨738065327220,738065346550⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208370024896,208370024960⟩ : DyadicInterval 40),(⟨-257314563968,-257314563904⟩ : DyadicInterval 40),(⟨738011025973,738011045302⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-48944539072,-48832664192⟩ : DyadicInterval 40),(⟨786539715712,786595672416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨208181444160,208370017856⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-257314553216,-257026596544⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1323_ok : ecellOkT e1323 = true := by decide +kernel
theorem e1323_pos {a z : ℝ} (ha1 : ((426909/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((854667/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1323 e1323_ok ha1 ha2 hz1 hz2 hz

-- box ['854667/4096000', '213879/1024000', '3999/4000', '1']  interval_lower 715574419/1099511627776
noncomputable def e1324 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1328934553649,0,true,208370017792,208370017856⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨870088701903,0,false,-257314553216,-257314553152⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1329162455352,0,true,208558559168,208558559232⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨869860800200,0,false,-257602585216,-257602585152⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1328877197917,0,true,208322562752,208322562816⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨870146057635,0,false,-257242076416,-257242076352⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541274223,0,true,29646016,29646080⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099481981329,0,false,-29646848,-29646784⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626976,0,false,-832,-768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1328905870094,0,true,208346285824,208346285888⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨870117385458,0,false,-257278307008,-257278306944⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1329162463898,0,true,208558566208,208558566272⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨869860791654,0,false,-257602596032,-257602595968⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1051545326011,0,false,-49044029760,-49044029696⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1051652453686,0,false,-48932021120,-48932021056⟩
    { al := (854667/4096000), au := (213879/1024000), zl := (3999/4000), zu := 1,
      A := ⟨229422925873,229650827576⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208370017792,208370017856⟩ : DyadicInterval 40),(⟨-257314553216,-257314553152⟩ : DyadicInterval 40),(⟨738011027820,738011047149⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208558559168,208558559232⟩ : DyadicInterval 40),(⟨-257602585216,-257602585152⟩ : DyadicInterval 40),(⟨737962740618,737962759948⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208322562752,208322562816⟩ : DyadicInterval 40),(⟨-257242076416,-257242076352⟩ : DyadicInterval 40),(⟨738023172393,738023191722⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208558559168,208558559232⟩ : DyadicInterval 40),(⟨-257602585216,-257602585152⟩ : DyadicInterval 40),(⟨737962740618,737962759948⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,29646447⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29646016,29646080⟩ : DyadicInterval 40),(⟨-29646848,-29646784⟩ : DyadicInterval 40),(⟨762123383168,762123402497⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-832,0⟩ : DyadicInterval 40),(⟨762123383616,762123403296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨229394242318,229650836122⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208346285824,208346285888⟩ : DyadicInterval 40),(⟨-257278307008,-257278306944⟩ : DyadicInterval 40),(⟨738017101691,738017121021⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208558566208,208558566272⟩ : DyadicInterval 40),(⟨-257602596032,-257602595968⟩ : DyadicInterval 40),(⟨737962738830,737962758159⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-49044029760,-48932021056⟩ : DyadicInterval 40),(⟨786589394144,786645417760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨208370017792,208558559232⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-257602585216,-257314553152⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1324_ok : ecellOkT e1324 = true := by decide +kernel
theorem e1324_pos {a z : ℝ} (ha1 : ((854667/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((213879/1024000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1324 e1324_ok ha1 ha2 hz1 hz2 hz

-- box ['213879/1024000', '171273/819200', '999/1000', '3997/4000']  interval_lower 724241155/1099511627776
noncomputable def e1325 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1329162455351,0,true,208558559168,208558559232⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨869860800201,0,false,-257602585216,-257602585152⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1329390357054,0,true,208747068160,208747068224⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨869632898498,0,false,-257890692672,-257890692608⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1328932804523,0,true,208368570624,208368570688⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨870090451029,0,false,-257312342848,-257312342784⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1329217948008,0,true,208604462912,208604462976⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨869805307544,0,false,-257672730624,-257672730560⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099600563152,0,true,88931776,88931840⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099422692400,0,false,-88939008,-88938944⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099630335306,0,true,118701120,118701184⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099392920246,0,false,-118713984,-118713920⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511614959,0,false,-12864,-12800⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620583,0,false,-7232,-7168⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1329047625964,0,true,208463565696,208463565760⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨869975629588,0,false,-257457449408,-257457449344⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1329304162111,0,true,208675775744,208675775808⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨869719093441,0,false,-257781718400,-257781718336⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1051486115810,0,false,-49105942592,-49105942528⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1051593285548,0,false,-48993883712,-48993883648⟩
    { al := (213879/1024000), au := (171273/819200), zl := (999/1000), zu := (3997/4000),
      A := ⟨229650827575,229878729278⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208558559168,208558559232⟩ : DyadicInterval 40),(⟨-257602585216,-257602585152⟩ : DyadicInterval 40),(⟨737962740618,737962759948⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208747068160,208747068224⟩ : DyadicInterval 40),(⟨-257890692672,-257890692608⟩ : DyadicInterval 40),(⟨737914404052,737914423382⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208368570624,208368570688⟩ : DyadicInterval 40),(⟨-257312342848,-257312342784⟩ : DyadicInterval 40),(⟨738011398216,738011417546⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208604462912,208604462976⟩ : DyadicInterval 40),(⟨-257672730624,-257672730560⟩ : DyadicInterval 40),(⟨737950975507,737950994837⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨88935376,118707530⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨88931776,88931840⟩ : DyadicInterval 40),(⟨-88939008,-88938944⟩ : DyadicInterval 40),(⟨762123379974,762123399303⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨118701120,118701184⟩ : DyadicInterval 40),(⟨-118713984,-118713920⟩ : DyadicInterval 40),(⟨762123377167,762123396497⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-12864,-7168⟩ : DyadicInterval 40),(⟨762123387200,762123409312⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨229535998188,229792534335⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208463565696,208463565760⟩ : DyadicInterval 40),(⟨-257457449408,-257457449344⟩ : DyadicInterval 40),(⟨737987076528,737987095857⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208675775744,208675775808⟩ : DyadicInterval 40),(⟨-257781718400,-257781718336⟩ : DyadicInterval 40),(⟨737932691315,737932710645⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-49105942592,-48993883648⟩ : DyadicInterval 40),(⟨786620325440,786676374176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨208558559168,208747068224⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-257890692672,-257602585152⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1325_ok : ecellOkT e1325 = true := by decide +kernel
theorem e1325_pos {a z : ℝ} (ha1 : ((213879/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((171273/819200 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1325 e1325_ok ha1 ha2 hz1 hz2 hz

-- box ['171273/819200', '428607/2048000', '999/1000', '3997/4000']  interval_lower 182464287/274877906944
noncomputable def e1326 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1329390357053,0,true,208747068160,208747068224⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨869632898499,0,false,-257890692672,-257890692608⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1329618258756,0,true,208935544832,208935544896⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨869404996796,0,false,-258178875648,-258178875584⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1329160478323,0,true,208556923712,208556923776⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨869862777229,0,false,-257600086208,-257600086144⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1329445678783,0,true,208792822656,208792822720⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨869577576769,0,false,-257960640384,-257960640320⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099600657236,0,true,89025792,89025856⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099422598316,0,false,-89033088,-89033024⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099630460778,0,true,118826560,118826624⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099392794774,0,false,-118839488,-118839424⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511614932,0,false,-12864,-12800⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620568,0,false,-7232,-7168⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1329275413719,0,true,208651996736,208651996800⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨869747841833,0,false,-257745374848,-257745374784⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1329531978349,0,true,208864193984,208864194048⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨869491277203,0,false,-258069764736,-258069764672⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1051390843655,0,false,-49205570688,-49205570624⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1051498131605,0,false,-49093378048,-49093377984⟩
    { al := (171273/819200), au := (428607/2048000), zl := (999/1000), zu := (3997/4000),
      A := ⟨229878729277,230106630980⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208747068160,208747068224⟩ : DyadicInterval 40),(⟨-257890692672,-257890692608⟩ : DyadicInterval 40),(⟨737914404052,737914423382⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208935544832,208935544896⟩ : DyadicInterval 40),(⟨-258178875648,-258178875584⟩ : DyadicInterval 40),(⟨737866018095,737866037425⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208556923712,208556923776⟩ : DyadicInterval 40),(⟨-257600086208,-257600086144⟩ : DyadicInterval 40),(⟨737963159715,737963179045⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208792822656,208792822720⟩ : DyadicInterval 40),(⟨-257960640384,-257960640320⟩ : DyadicInterval 40),(⟨737902663220,737902682550⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨89029460,118833002⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨89025792,89025856⟩ : DyadicInterval 40),(⟨-89033088,-89033024⟩ : DyadicInterval 40),(⟨762123379990,762123399320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨118826560,118826624⟩ : DyadicInterval 40),(⟨-118839488,-118839424⟩ : DyadicInterval 40),(⟨762123377172,762123396502⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-12864,-7168⟩ : DyadicInterval 40),(⟨762123387200,762123409312⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨229763785943,230020350573⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208651996736,208651996800⟩ : DyadicInterval 40),(⟨-257745374848,-257745374784⟩ : DyadicInterval 40),(⟨737938789035,737938808364⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208864193984,208864194048⟩ : DyadicInterval 40),(⟨-258069764736,-258069764672⟩ : DyadicInterval 40),(⟨737884342172,737884361501⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-49205570688,-49093377984⟩ : DyadicInterval 40),(⟨786670072608,786726188224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨208747068160,208935544896⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-258178875648,-257890692608⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1326_ok : ecellOkT e1326 = true := by decide +kernel
theorem e1326_pos {a z : ℝ} (ha1 : ((171273/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((428607/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1326 e1326_ok ha1 ha2 hz1 hz2 hz

-- box ['213879/1024000', '171273/819200', '3997/4000', '1999/2000']  interval_lower 361607101/549755813888
noncomputable def e1327 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1329162455351,0,true,208558559168,208558559232⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨869860800201,0,false,-257602585216,-257602585152⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1329390357054,0,true,208747068160,208747068224⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨869632898498,0,false,-257890692672,-257890692608⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1328990217230,0,true,208416070848,208416070912⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨870033038322,0,false,-257384896256,-257384896192⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1329275417690,0,true,208652000064,208652000128⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨869747837862,0,false,-257745379840,-257745379776⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570918429,0,true,59289024,59289088⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452337123,0,false,-59292288,-59292224⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099600659223,0,true,89027840,89027904⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099422596329,0,false,-89035072,-89035008⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620566,0,false,-7232,-7168⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624579,0,false,-3200,-3136⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1329076331517,0,true,208487313344,208487313408⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨869946924035,0,false,-257493729344,-257493729280⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1329332896380,0,true,208699542592,208699542656⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨869690359172,0,false,-257818045248,-257818045184⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1051474104417,0,false,-49118502656,-49118502592⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1051581299554,0,false,-49006415936,-49006415872⟩
    { al := (213879/1024000), au := (171273/819200), zl := (3997/4000), zu := (1999/2000),
      A := ⟨229650827575,229878729278⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208558559168,208558559232⟩ : DyadicInterval 40),(⟨-257602585216,-257602585152⟩ : DyadicInterval 40),(⟨737962740618,737962759948⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208747068160,208747068224⟩ : DyadicInterval 40),(⟨-257890692672,-257890692608⟩ : DyadicInterval 40),(⟨737914404052,737914423382⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208416070848,208416070912⟩ : DyadicInterval 40),(⟨-257384896256,-257384896192⟩ : DyadicInterval 40),(⟨737999238511,737999257841⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208652000064,208652000128⟩ : DyadicInterval 40),(⟨-257745379840,-257745379776⟩ : DyadicInterval 40),(⟨737938788155,737938807485⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨59290653,89031447⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59289024,59289088⟩ : DyadicInterval 40),(⟨-59292288,-59292224⟩ : DyadicInterval 40),(⟨762123381986,762123401315⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨89027840,89027904⟩ : DyadicInterval 40),(⟨-89035072,-89035008⟩ : DyadicInterval 40),(⟨762123379958,762123399288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7232,-3136⟩ : DyadicInterval 40),(⟨762123385184,762123406496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨229564703741,229821268604⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208487313344,208487313408⟩ : DyadicInterval 40),(⟨-257493729344,-257493729280⟩ : DyadicInterval 40),(⟨737980994128,737981013458⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208699542592,208699542656⟩ : DyadicInterval 40),(⟨-257818045248,-257818045184⟩ : DyadicInterval 40),(⟨737926595764,737926615093⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-49118502656,-49006415872⟩ : DyadicInterval 40),(⟨786626591552,786682654208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨208558559168,208747068224⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-257890692672,-257602585152⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1327_ok : ecellOkT e1327 = true := by decide +kernel
theorem e1327_pos {a z : ℝ} (ha1 : ((213879/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((171273/819200 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1327 e1327_ok ha1 ha2 hz1 hz2 hz

-- box ['171273/819200', '428607/2048000', '3997/4000', '1999/2000']  interval_lower 91103337/137438953472
noncomputable def e1328 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1329390357053,0,true,208747068160,208747068224⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨869632898499,0,false,-257890692672,-257890692608⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1329618258756,0,true,208935544832,208935544896⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨869404996796,0,false,-258178875648,-258178875584⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1329217948006,0,true,208604462912,208604462976⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨869805307546,0,false,-257672730624,-257672730560⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1329503205441,0,true,208840398784,208840398848⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨869520050111,0,false,-258033380672,-258033380608⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570981154,0,true,59351744,59351808⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452274398,0,false,-59355008,-59354944⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099600753330,0,true,89121920,89121984⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099422502222,0,false,-89129216,-89129152⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620551,0,false,-7232,-7168⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624573,0,false,-3264,-3200⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1329304147757,0,true,208675763904,208675763968⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨869719107795,0,false,-257781700224,-257781700160⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1329560741104,0,true,208887980288,208887980352⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨869462514448,0,false,-258106137152,-258106137088⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1051378808435,0,false,-49218156800,-49218156736⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1051486121811,0,false,-49105936320,-49105936256⟩
    { al := (171273/819200), au := (428607/2048000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨229878729277,230106630980⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208747068160,208747068224⟩ : DyadicInterval 40),(⟨-257890692672,-257890692608⟩ : DyadicInterval 40),(⟨737914404052,737914423382⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208935544832,208935544896⟩ : DyadicInterval 40),(⟨-258178875648,-258178875584⟩ : DyadicInterval 40),(⟨737866018095,737866037425⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208604462912,208604462976⟩ : DyadicInterval 40),(⟨-257672730624,-257672730560⟩ : DyadicInterval 40),(⟨737950975508,737950994837⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208840398784,208840398848⟩ : DyadicInterval 40),(⟨-258033380672,-258033380608⟩ : DyadicInterval 40),(⟨737890451325,737890470654⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨59353378,89125554⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59351744,59351808⟩ : DyadicInterval 40),(⟨-59355008,-59354944⟩ : DyadicInterval 40),(⟨762123381979,762123401309⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨89121920,89121984⟩ : DyadicInterval 40),(⟨-89129216,-89129152⟩ : DyadicInterval 40),(⟨762123379975,762123399304⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7232,-3200⟩ : DyadicInterval 40),(⟨762123385216,762123406496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨229792519981,230049113328⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208675763904,208675763968⟩ : DyadicInterval 40),(⟨-257781700224,-257781700160⟩ : DyadicInterval 40),(⟨737932694328,737932713658⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208887980288,208887980352⟩ : DyadicInterval 40),(⟨-258106137152,-258106137088⟩ : DyadicInterval 40),(⟨737878234373,737878253703⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-49218156800,-49105936256⟩ : DyadicInterval 40),(⟨786676351744,786732481280⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨208747068160,208935544896⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-258178875648,-257890692608⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1328_ok : ecellOkT e1328 = true := by decide +kernel
theorem e1328_pos {a z : ℝ} (ha1 : ((171273/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((428607/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1328 e1328_ok ha1 ha2 hz1 hz2 hz

-- box ['428607/2048000', '858063/4096000', '999/1000', '3997/4000']  interval_lower 183873549/274877906944
noncomputable def e1329 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1329618258755,0,true,208935544832,208935544896⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨869404996797,0,false,-258178875648,-258178875584⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1329846160458,0,true,209123989248,209123989312⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨869177095094,0,false,-258467134208,-258467134144⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1329388152123,0,true,208745244480,208745244544⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨869635103429,0,false,-257887904896,-257887904832⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1329673409559,0,true,208981150208,208981150272⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨869349845993,0,false,-258248625536,-258248625472⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099600751338,0,true,89119936,89120000⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099422504214,0,false,-89127232,-89127168⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099630586275,0,true,118952064,118952128⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099392669277,0,false,-118964992,-118964928⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511614905,0,false,-12928,-12864⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620552,0,false,-7232,-7168⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1329503201467,0,true,208840395520,208840395584⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨869520054085,0,false,-258033375616,-258033375552⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1329759794597,0,true,209052579968,209052580032⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨869263460955,0,false,-258357886592,-258357886528⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1051295477091,0,false,-49305306560,-49305306496⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1051402883282,0,false,-49192980096,-49192980032⟩
    { al := (428607/2048000), au := (858063/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨230106630979,230334532682⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208935544832,208935544896⟩ : DyadicInterval 40),(⟨-258178875648,-258178875584⟩ : DyadicInterval 40),(⟨737866018096,737866037425⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209123989248,209123989312⟩ : DyadicInterval 40),(⟨-258467134208,-258467134144⟩ : DyadicInterval 40),(⟨737817582720,737817602049⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208745244480,208745244544⟩ : DyadicInterval 40),(⟨-257887904896,-257887904832⟩ : DyadicInterval 40),(⟨737914871958,737914891287⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208981150208,208981150272⟩ : DyadicInterval 40),(⟨-258248625536,-258248625472⟩ : DyadicInterval 40),(⟨737854301558,737854320888⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨89123562,118958499⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨89119936,89120000⟩ : DyadicInterval 40),(⟨-89127232,-89127168⟩ : DyadicInterval 40),(⟨762123379975,762123399305⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨118952064,118952128⟩ : DyadicInterval 40),(⟨-118964992,-118964928⟩ : DyadicInterval 40),(⟨762123377145,762123396474⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-12928,-7168⟩ : DyadicInterval 40),(⟨762123387200,762123409344⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨229991573691,230248166821⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208840395520,208840395584⟩ : DyadicInterval 40),(⟨-258033375616,-258033375552⟩ : DyadicInterval 40),(⟨737890452142,737890471472⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209052579968,209052580032⟩ : DyadicInterval 40),(⟨-258357886592,-258357886528⟩ : DyadicInterval 40),(⟨737835943662,737835962992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-49305306560,-49192980032⟩ : DyadicInterval 40),(⟨786719873632,786776056160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨208935544832,209123989312⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-258467134208,-258178875584⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1329_ok : ecellOkT e1329 = true := by decide +kernel
theorem e1329_pos {a z : ℝ} (ha1 : ((428607/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((858063/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1329 e1329_ok ha1 ha2 hz1 hz2 hz

-- box ['858063/4096000', '26841/128000', '999/1000', '3997/4000']  interval_lower 741152619/1099511627776
noncomputable def e1330 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1329846160457,0,true,209123989248,209123989312⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨869177095095,0,false,-258467134208,-258467134144⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1330074062160,0,true,209312401344,209312401408⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨868949193392,0,false,-258755468352,-258755468288⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1329615825924,0,true,208933533056,208933533120⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨869407429628,0,false,-258175798976,-258175798912⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1329901140335,0,true,209169445440,209169445504⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨869122115217,0,false,-258536686144,-258536686080⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099600845458,0,true,89214016,89214080⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099422410094,0,false,-89221312,-89221248⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099630711796,0,true,119077568,119077632⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099392543756,0,false,-119090496,-119090432⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511614878,0,false,-12928,-12864⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620537,0,false,-7296,-7232⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1329730989221,0,true,209028761984,209028762048⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨869292266331,0,false,-258321451904,-258321451840⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1329987610836,0,true,209240933632,209240933696⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨869035644716,0,false,-258646083904,-258646083840⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1051200016124,0,false,-49405150272,-49405150208⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1051307540575,0,false,-49292689920,-49292689856⟩
    { al := (858063/4096000), au := (26841/128000), zl := (999/1000), zu := (3997/4000),
      A := ⟨230334532681,230562434384⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209123989248,209123989312⟩ : DyadicInterval 40),(⟨-258467134208,-258467134144⟩ : DyadicInterval 40),(⟨737817582720,737817602050⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209312401344,209312401408⟩ : DyadicInterval 40),(⟨-258755468352,-258755468288⟩ : DyadicInterval 40),(⟨737769097952,737769117281⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208933533056,208933533120⟩ : DyadicInterval 40),(⟨-258175798976,-258175798912⟩ : DyadicInterval 40),(⟨737866534879,737866554208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209169445440,209169445504⟩ : DyadicInterval 40),(⟨-258536686144,-258536686080⟩ : DyadicInterval 40),(⟨737805890611,737805909941⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨89217682,119084020⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨89214016,89214080⟩ : DyadicInterval 40),(⟨-89221312,-89221248⟩ : DyadicInterval 40),(⟨762123379960,762123399289⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨119077568,119077632⟩ : DyadicInterval 40),(⟨-119090496,-119090432⟩ : DyadicInterval 40),(⟨762123377118,762123396447⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-12928,-7232⟩ : DyadicInterval 40),(⟨762123387232,762123409344⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨230219361445,230475983060⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209028761984,209028762048⟩ : DyadicInterval 40),(⟨-258321451904,-258321451840⟩ : DyadicInterval 40),(⟨737842065950,737842085279⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209240933632,209240933696⟩ : DyadicInterval 40),(⟨-258646083904,-258646083840⟩ : DyadicInterval 40),(⟨737787495790,737787515119⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-49405150272,-49292689856⟩ : DyadicInterval 40),(⟨786769728544,786825978016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨209123989248,209312401408⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-258755468352,-258467134144⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1330_ok : ecellOkT e1330 = true := by decide +kernel
theorem e1330_pos {a z : ℝ} (ha1 : ((858063/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((26841/128000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1330 e1330_ok ha1 ha2 hz1 hz2 hz

-- box ['428607/2048000', '858063/4096000', '3997/4000', '1999/2000']  interval_lower 367229951/549755813888
noncomputable def e1331 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1329618258755,0,true,208935544832,208935544896⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨869404996797,0,false,-258178875648,-258178875584⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1329846160458,0,true,209123989248,209123989312⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨869177095094,0,false,-258467134208,-258467134144⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1329445678781,0,true,208792822656,208792822720⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨869577576771,0,false,-257960640384,-257960640320⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1329730993192,0,true,209028765248,209028765312⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨869292262360,0,false,-258321456960,-258321456896⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099571043890,0,true,59414464,59414528⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452211662,0,false,-59417728,-59417664⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099600847454,0,true,89216000,89216064⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099422408098,0,false,-89223360,-89223296⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620536,0,false,-7296,-7232⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624566,0,false,-3264,-3200⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1329531963990,0,true,208864182144,208864182208⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨869491291562,0,false,-258069746560,-258069746496⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1329788585832,0,true,209076385728,209076385792⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨869234669720,0,false,-258394304576,-258394304512⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1051283418021,0,false,-49317918784,-49317918720⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1051390849664,0,false,-49205564416,-49205564352⟩
    { al := (428607/2048000), au := (858063/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨230106630979,230334532682⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208935544832,208935544896⟩ : DyadicInterval 40),(⟨-258178875648,-258178875584⟩ : DyadicInterval 40),(⟨737866018096,737866037425⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209123989248,209123989312⟩ : DyadicInterval 40),(⟨-258467134208,-258467134144⟩ : DyadicInterval 40),(⟨737817582720,737817602049⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208792822656,208792822720⟩ : DyadicInterval 40),(⟨-257960640384,-257960640320⟩ : DyadicInterval 40),(⟨737902663221,737902682550⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209028765248,209028765312⟩ : DyadicInterval 40),(⟨-258321456960,-258321456896⟩ : DyadicInterval 40),(⟨737842065131,737842084460⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨59416114,89219678⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59414464,59414528⟩ : DyadicInterval 40),(⟨-59417728,-59417664⟩ : DyadicInterval 40),(⟨762123381973,762123401302⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨89216000,89216064⟩ : DyadicInterval 40),(⟨-89223360,-89223296⟩ : DyadicInterval 40),(⟨762123379991,762123399321⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7296,-3200⟩ : DyadicInterval 40),(⟨762123385216,762123406528⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨230020336214,230276958056⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208864182144,208864182208⟩ : DyadicInterval 40),(⟨-258069746560,-258069746496⟩ : DyadicInterval 40),(⟨737884345192,737884364522⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209076385728,209076385792⟩ : DyadicInterval 40),(⟨-258394304576,-258394304512⟩ : DyadicInterval 40),(⟨737829823591,737829842921⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-49317918784,-49205564352⟩ : DyadicInterval 40),(⟨786726165792,786782362272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨208935544832,209123989312⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-258467134208,-258178875584⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1331_ok : ecellOkT e1331 = true := by decide +kernel
theorem e1331_pos {a z : ℝ} (ha1 : ((428607/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((858063/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1331 e1331_ok ha1 ha2 hz1 hz2 hz

-- box ['858063/4096000', '26841/128000', '3997/4000', '1999/2000']  interval_lower 740114267/1099511627776
noncomputable def e1332 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1329846160457,0,true,209123989248,209123989312⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨869177095095,0,false,-258467134208,-258467134144⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1330074062160,0,true,209312401344,209312401408⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨868949193392,0,false,-258755468352,-258755468288⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1329673409557,0,true,208981150208,208981150272⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨869349845995,0,false,-258248625536,-258248625472⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1329958780943,0,true,209217099456,209217099520⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨869064474609,0,false,-258609608704,-258609608640⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099571106638,0,true,59477248,59477312⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452148914,0,false,-59480512,-59480448⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099600941598,0,true,89310144,89310208⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099422313954,0,false,-89317504,-89317440⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620520,0,false,-7296,-7232⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624559,0,false,-3264,-3200⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1329759780232,0,true,209052568064,209052568128⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨869263475320,0,false,-258357868416,-258357868352⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1330016430561,0,true,209264758848,209264758912⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨869006824991,0,false,-258682547520,-258682547456⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1051187933178,0,false,-49417788608,-49417788544⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1051295483108,0,false,-49305300288,-49305300224⟩
    { al := (858063/4096000), au := (26841/128000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨230334532681,230562434384⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209123989248,209123989312⟩ : DyadicInterval 40),(⟨-258467134208,-258467134144⟩ : DyadicInterval 40),(⟨737817582720,737817602050⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209312401344,209312401408⟩ : DyadicInterval 40),(⟨-258755468352,-258755468288⟩ : DyadicInterval 40),(⟨737769097952,737769117281⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208981150208,208981150272⟩ : DyadicInterval 40),(⟨-258248625536,-258248625472⟩ : DyadicInterval 40),(⟨737854301559,737854320888⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209217099456,209217099520⟩ : DyadicInterval 40),(⟨-258609608704,-258609608640⟩ : DyadicInterval 40),(⟨737793629561,737793648890⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨59478862,89313822⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59477248,59477312⟩ : DyadicInterval 40),(⟨-59480512,-59480448⟩ : DyadicInterval 40),(⟨762123381966,762123401295⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨89310144,89310208⟩ : DyadicInterval 40),(⟨-89317504,-89317440⟩ : DyadicInterval 40),(⟨762123379976,762123399306⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7296,-3200⟩ : DyadicInterval 40),(⟨762123385216,762123406528⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨230248152456,230504802785⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209052568064,209052568128⟩ : DyadicInterval 40),(⟨-258357868416,-258357868352⟩ : DyadicInterval 40),(⟨737835946729,737835966059⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209264758848,209264758912⟩ : DyadicInterval 40),(⟨-258682547520,-258682547456⟩ : DyadicInterval 40),(⟨737781363443,737781382773⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-49417788608,-49305300224⟩ : DyadicInterval 40),(⟨786776033728,786832297184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨209123989248,209312401408⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-258755468352,-258467134144⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1332_ok : ecellOkT e1332 = true := by decide +kernel
theorem e1332_pos {a z : ℝ} (ha1 : ((858063/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((26841/128000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1332 e1332_ok ha1 ha2 hz1 hz2 hz

-- box ['213879/1024000', '171273/819200', '1999/2000', '3999/4000']  interval_lower 722186453/1099511627776
noncomputable def e1333 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1329162455351,0,true,208558559168,208558559232⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨869860800201,0,false,-257602585216,-257602585152⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1329390357054,0,true,208747068160,208747068224⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨869632898498,0,false,-257890692672,-257890692608⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1329047629937,0,true,208463569024,208463569088⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨869975625615,0,false,-257457454464,-257457454400⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1329332887372,0,true,208699535104,208699535168⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨869690368180,0,false,-257818033856,-257818033792⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541273219,0,true,29644992,29645056⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099481982333,0,false,-29645888,-29645824⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570982650,0,true,59353216,59353280⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452272902,0,false,-59356480,-59356416⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624571,0,false,-3264,-3200⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626977,0,false,-832,-768⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1329105037300,0,true,208511060672,208511060736⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨869918218252,0,false,-257530010688,-257530010624⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1329361630872,0,true,208723309056,208723309120⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨869661624680,0,false,-257854373632,-257854373568⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1051462091428,0,false,-49131064512,-49131064448⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1051569311965,0,false,-49018949952,-49018949888⟩
    { al := (213879/1024000), au := (171273/819200), zl := (1999/2000), zu := (3999/4000),
      A := ⟨229650827575,229878729278⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208558559168,208558559232⟩ : DyadicInterval 40),(⟨-257602585216,-257602585152⟩ : DyadicInterval 40),(⟨737962740618,737962759948⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208747068160,208747068224⟩ : DyadicInterval 40),(⟨-257890692672,-257890692608⟩ : DyadicInterval 40),(⟨737914404052,737914423382⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208463569024,208463569088⟩ : DyadicInterval 40),(⟨-257457454464,-257457454400⟩ : DyadicInterval 40),(⟨737987075675,737987095005⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208699535104,208699535168⟩ : DyadicInterval 40),(⟨-257818033856,-257818033792⟩ : DyadicInterval 40),(⟨737926597696,737926617026⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨29645443,59354874⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29644992,29645056⟩ : DyadicInterval 40),(⟨-29645888,-29645824⟩ : DyadicInterval 40),(⟨762123383200,762123402529⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59353216,59353280⟩ : DyadicInterval 40),(⟨-59356480,-59356416⟩ : DyadicInterval 40),(⟨762123381979,762123401308⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3264,-768⟩ : DyadicInterval 40),(⟨762123384000,762123404512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨229593409524,229850003096⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208511060672,208511060736⟩ : DyadicInterval 40),(⟨-257530010688,-257530010624⟩ : DyadicInterval 40),(⟨737974910863,737974930193⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208723309056,208723309120⟩ : DyadicInterval 40),(⟨-257854373632,-257854373568⟩ : DyadicInterval 40),(⟨737920499435,737920518764⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-49131064512,-49018949888⟩ : DyadicInterval 40),(⟨786632858560,786688935136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨208558559168,208747068224⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-257890692672,-257602585152⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1333_ok : ecellOkT e1333 = true := by decide +kernel
theorem e1333_pos {a z : ℝ} (ha1 : ((213879/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((171273/819200 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1333 e1333_ok ha1 ha2 hz1 hz2 hz

-- box ['171273/819200', '428607/2048000', '1999/2000', '3999/4000']  interval_lower 727794677/1099511627776
noncomputable def e1334 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1329390357053,0,true,208747068160,208747068224⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨869632898499,0,false,-257890692672,-257890692608⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1329618258756,0,true,208935544832,208935544896⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨869404996796,0,false,-258178875648,-258178875584⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1329275417688,0,true,208652000064,208652000128⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨869747837864,0,false,-257745379840,-257745379776⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1329560732099,0,true,208887972864,208887972928⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨869462523453,0,false,-258106125760,-258106125696⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541304581,0,true,29676352,29676416⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099481950971,0,false,-29677248,-29677184⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099571045389,0,true,59416000,59416064⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452210163,0,false,-59419264,-59419200⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624565,0,false,-3264,-3200⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626975,0,false,-832,-768⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1329332882025,0,true,208699530688,208699530752⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨869690373527,0,false,-257818027136,-257818027072⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1329589504091,0,true,208911766272,208911766336⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨869433751461,0,false,-258142511104,-258142511040⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1051366771612,0,false,-49230744768,-49230744704⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1051474110419,0,false,-49118496384,-49118496320⟩
    { al := (171273/819200), au := (428607/2048000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨229878729277,230106630980⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208747068160,208747068224⟩ : DyadicInterval 40),(⟨-257890692672,-257890692608⟩ : DyadicInterval 40),(⟨737914404052,737914423382⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208935544832,208935544896⟩ : DyadicInterval 40),(⟨-258178875648,-258178875584⟩ : DyadicInterval 40),(⟨737866018095,737866037425⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208652000064,208652000128⟩ : DyadicInterval 40),(⟨-257745379840,-257745379776⟩ : DyadicInterval 40),(⟨737938788156,737938807485⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208887972864,208887972928⟩ : DyadicInterval 40),(⟨-258106125760,-258106125696⟩ : DyadicInterval 40),(⟨737878236270,737878255600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨29676805,59417613⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29676352,29676416⟩ : DyadicInterval 40),(⟨-29677248,-29677184⟩ : DyadicInterval 40),(⟨762123383198,762123402528⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59416000,59416064⟩ : DyadicInterval 40),(⟨-59419264,-59419200⟩ : DyadicInterval 40),(⟨762123381972,762123401302⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3264,-768⟩ : DyadicInterval 40),(⟨762123384000,762123404512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨229821254249,230077876315⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208699530688,208699530752⟩ : DyadicInterval 40),(⟨-257818027136,-257818027072⟩ : DyadicInterval 40),(⟨737926598842,737926618172⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208911766272,208911766336⟩ : DyadicInterval 40),(⟨-258142511104,-258142511040⟩ : DyadicInterval 40),(⟨737872125753,737872145082⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-49230744768,-49118496320⟩ : DyadicInterval 40),(⟨786682631776,786738775264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨208747068160,208935544896⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-258178875648,-257890692608⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1334_ok : ecellOkT e1334 = true := by decide +kernel
theorem e1334_pos {a z : ℝ} (ha1 : ((171273/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((428607/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1334 e1334_ok ha1 ha2 hz1 hz2 hz

-- box ['213879/1024000', '171273/819200', '3999/4000', '1']  interval_lower 180289509/274877906944
noncomputable def e1335 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1329162455351,0,true,208558559168,208558559232⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨869860800201,0,false,-257602585216,-257602585152⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1329390357054,0,true,208747068160,208747068224⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨869632898498,0,false,-257890692672,-257890692608⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1329105042644,0,true,208511065088,208511065152⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨869918212908,0,false,-257530017408,-257530017344⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541305587,0,true,29677376,29677440⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099481949965,0,false,-29678272,-29678208⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626974,0,false,-832,-768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1329133743308,0,true,208534807680,208534807744⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨869889512244,0,false,-257566293504,-257566293440⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1329390365601,0,true,208747075200,208747075264⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨869632889951,0,false,-257890703488,-257890703424⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1051450076839,0,false,-49143628224,-49143628160⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1051557322784,0,false,-49031485824,-49031485760⟩
    { al := (213879/1024000), au := (171273/819200), zl := (3999/4000), zu := 1,
      A := ⟨229650827575,229878729278⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208558559168,208558559232⟩ : DyadicInterval 40),(⟨-257602585216,-257602585152⟩ : DyadicInterval 40),(⟨737962740618,737962759948⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208747068160,208747068224⟩ : DyadicInterval 40),(⟨-257890692672,-257890692608⟩ : DyadicInterval 40),(⟨737914404052,737914423382⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208511065088,208511065152⟩ : DyadicInterval 40),(⟨-257530017408,-257530017344⟩ : DyadicInterval 40),(⟨737974909720,737974929049⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208747068160,208747068224⟩ : DyadicInterval 40),(⟨-257890692672,-257890692608⟩ : DyadicInterval 40),(⟨737914404052,737914423382⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,29677811⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29677376,29677440⟩ : DyadicInterval 40),(⟨-29678272,-29678208⟩ : DyadicInterval 40),(⟨762123383198,762123402527⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-832,0⟩ : DyadicInterval 40),(⟨762123383616,762123403296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨229622115532,229878737825⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208534807680,208534807744⟩ : DyadicInterval 40),(⟨-257566293504,-257566293440⟩ : DyadicInterval 40),(⟨737968826758,737968846088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208747075200,208747075264⟩ : DyadicInterval 40),(⟨-257890703488,-257890703424⟩ : DyadicInterval 40),(⟨737914402260,737914421590⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-49143628224,-49031485760⟩ : DyadicInterval 40),(⟨786639126496,786695216992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨208558559168,208747068224⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-257890692672,-257602585152⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1335_ok : ecellOkT e1335 = true := by decide +kernel
theorem e1335_pos {a z : ℝ} (ha1 : ((213879/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((171273/819200 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1335 e1335_ok ha1 ha2 hz1 hz2 hz

-- box ['171273/819200', '428607/2048000', '3999/4000', '1']  interval_lower 363381139/549755813888
noncomputable def e1336 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1329390357053,0,true,208747068160,208747068224⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨869632898499,0,false,-257890692672,-257890692608⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1329618258756,0,true,208935544832,208935544896⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨869404996796,0,false,-258178875648,-258178875584⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1329332887370,0,true,208699535104,208699535168⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨869690368182,0,false,-257818033856,-257818033792⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541336957,0,true,29708736,29708800⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099481918595,0,false,-29709632,-29709568⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626973,0,false,-832,-768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1329361616517,0,true,208723297152,208723297216⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨869661639035,0,false,-257854355456,-257854355392⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1329618267302,0,true,208935551936,208935552000⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨869404988250,0,false,-258178886464,-258178886400⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1051354733190,0,false,-49243334528,-49243334464⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1051462097431,0,false,-49131058240,-49131058176⟩
    { al := (171273/819200), au := (428607/2048000), zl := (3999/4000), zu := 1,
      A := ⟨229878729277,230106630980⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208747068160,208747068224⟩ : DyadicInterval 40),(⟨-257890692672,-257890692608⟩ : DyadicInterval 40),(⟨737914404052,737914423382⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208935544832,208935544896⟩ : DyadicInterval 40),(⟨-258178875648,-258178875584⟩ : DyadicInterval 40),(⟨737866018095,737866037425⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208699535104,208699535168⟩ : DyadicInterval 40),(⟨-257818033856,-257818033792⟩ : DyadicInterval 40),(⟨737926597696,737926617026⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208935544832,208935544896⟩ : DyadicInterval 40),(⟨-258178875648,-258178875584⟩ : DyadicInterval 40),(⟨737866018095,737866037425⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,29709181⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29708736,29708800⟩ : DyadicInterval 40),(⟨-29709632,-29709568⟩ : DyadicInterval 40),(⟨762123383197,762123402526⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-832,0⟩ : DyadicInterval 40),(⟨762123383616,762123403296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨229849988741,230106639526⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208723297152,208723297216⟩ : DyadicInterval 40),(⟨-257854355456,-257854355392⟩ : DyadicInterval 40),(⟨737920502488,737920521818⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208935551936,208935552000⟩ : DyadicInterval 40),(⟨-258178886464,-258178886400⟩ : DyadicInterval 40),(⟨737866016261,737866035590⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-49243334528,-49131058176⟩ : DyadicInterval 40),(⟨786688912704,786745070144⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨208747068160,208935544896⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-258178875648,-257890692608⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1336_ok : ecellOkT e1336 = true := by decide +kernel
theorem e1336_pos {a z : ℝ} (ha1 : ((171273/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((428607/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1336 e1336_ok ha1 ha2 hz1 hz2 hz

-- box ['428607/2048000', '858063/4096000', '1999/2000', '3999/4000']  interval_lower 733423993/1099511627776
noncomputable def e1337 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1329618258755,0,true,208935544832,208935544896⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨869404996797,0,false,-258178875648,-258178875584⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1329846160458,0,true,209123989248,209123989312⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨869177095094,0,false,-258467134208,-258467134144⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1329503205439,0,true,208840398784,208840398848⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨869520050113,0,false,-258033380672,-258033380608⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1329788576826,0,true,209076378304,209076378368⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨869234678726,0,false,-258394293184,-258394293120⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541335950,0,true,29707712,29707776⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099481919602,0,false,-29708608,-29708544⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099571108141,0,true,59478720,59478784⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452147411,0,false,-59481984,-59481920⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624558,0,false,-3264,-3200⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626974,0,false,-832,-768⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1329560726744,0,true,208887968384,208887968448⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨869462528808,0,false,-258106118976,-258106118912⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1329817377306,0,true,209100191168,209100191232⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨869205878246,0,false,-258430724032,-258430723968⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1051271357344,0,false,-49330532864,-49330532800⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1051378814445,0,false,-49218150528,-49218150464⟩
    { al := (428607/2048000), au := (858063/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨230106630979,230334532682⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208935544832,208935544896⟩ : DyadicInterval 40),(⟨-258178875648,-258178875584⟩ : DyadicInterval 40),(⟨737866018096,737866037425⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209123989248,209123989312⟩ : DyadicInterval 40),(⟨-258467134208,-258467134144⟩ : DyadicInterval 40),(⟨737817582720,737817602049⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208840398784,208840398848⟩ : DyadicInterval 40),(⟨-258033380672,-258033380608⟩ : DyadicInterval 40),(⟨737890451325,737890470654⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209076378304,209076378368⟩ : DyadicInterval 40),(⟨-258394293184,-258394293120⟩ : DyadicInterval 40),(⟨737829825492,737829844821⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨29708174,59480365⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29707712,29707776⟩ : DyadicInterval 40),(⟨-29708608,-29708544⟩ : DyadicInterval 40),(⟨762123383197,762123402526⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59478720,59478784⟩ : DyadicInterval 40),(⟨-59481984,-59481920⟩ : DyadicInterval 40),(⟨762123381966,762123401295⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3264,-768⟩ : DyadicInterval 40),(⟨762123384000,762123404512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨230049098968,230305749530⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208887968384,208887968448⟩ : DyadicInterval 40),(⟨-258106118976,-258106118912⟩ : DyadicInterval 40),(⟨737878237433,737878256763⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209100191168,209100191232⟩ : DyadicInterval 40),(⟨-258430724032,-258430723968⟩ : DyadicInterval 40),(⟨737823702668,737823721997⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-49330532864,-49218150464⟩ : DyadicInterval 40),(⟨786732458848,786788669312⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨208935544832,209123989312⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-258467134208,-258178875584⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1337_ok : ecellOkT e1337 = true := by decide +kernel
theorem e1337_pos {a z : ℝ} (ha1 : ((428607/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((858063/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1337 e1337_ok ha1 ha2 hz1 hz2 hz

-- box ['858063/4096000', '26841/128000', '1999/2000', '3999/4000']  interval_lower 369537357/549755813888
noncomputable def e1338 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1329846160457,0,true,209123989248,209123989312⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨869177095095,0,false,-258467134208,-258467134144⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1330074062160,0,true,209312401344,209312401408⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨868949193392,0,false,-258755468352,-258755468288⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1329730993190,0,true,209028765248,209028765312⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨869292262362,0,false,-258321456960,-258321456896⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1330016421552,0,true,209264751424,209264751488⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨869006834000,0,false,-258682536128,-258682536064⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541367325,0,true,29739136,29739200⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099481888227,0,false,-29739968,-29739904⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099571170904,0,true,59541504,59541568⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452084648,0,false,-59544768,-59544704⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624551,0,false,-3264,-3200⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626972,0,false,-832,-768⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1329788571466,0,true,209076373824,209076373888⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨869234684086,0,false,-258394286400,-258394286336⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1330045250518,0,true,209288583808,209288583872⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨868978005034,0,false,-258719012608,-258719012544⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1051175848624,0,false,-49430428736,-49430428672⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1051283424040,0,false,-49317912512,-49317912448⟩
    { al := (858063/4096000), au := (26841/128000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨230334532681,230562434384⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209123989248,209123989312⟩ : DyadicInterval 40),(⟨-258467134208,-258467134144⟩ : DyadicInterval 40),(⟨737817582720,737817602050⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209312401344,209312401408⟩ : DyadicInterval 40),(⟨-258755468352,-258755468288⟩ : DyadicInterval 40),(⟨737769097952,737769117281⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209028765248,209028765312⟩ : DyadicInterval 40),(⟨-258321456960,-258321456896⟩ : DyadicInterval 40),(⟨737842065131,737842084461⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209264751424,209264751488⟩ : DyadicInterval 40),(⟨-258682536128,-258682536064⟩ : DyadicInterval 40),(⟨737781365349,737781384678⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨29739549,59543128⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29739136,29739200⟩ : DyadicInterval 40),(⟨-29739968,-29739904⟩ : DyadicInterval 40),(⟨762123383163,762123402492⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59541504,59541568⟩ : DyadicInterval 40),(⟨-59544768,-59544704⟩ : DyadicInterval 40),(⟨762123381959,762123401288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3264,-768⟩ : DyadicInterval 40),(⟨762123384000,762123404512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨230276943690,230533622742⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209076373824,209076373888⟩ : DyadicInterval 40),(⟨-258394286400,-258394286336⟩ : DyadicInterval 40),(⟨737829826659,737829845989⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209288583808,209288583872⟩ : DyadicInterval 40),(⟨-258719012608,-258719012544⟩ : DyadicInterval 40),(⟨737775230204,737775249533⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-49430428736,-49317912448⟩ : DyadicInterval 40),(⟨786782339840,786838617248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨209123989248,209312401408⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-258755468352,-258467134144⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1338_ok : ecellOkT e1338 = true := by decide +kernel
theorem e1338_pos {a z : ℝ} (ha1 : ((858063/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((26841/128000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1338 e1338_ok ha1 ha2 hz1 hz2 hz

-- box ['428607/2048000', '858063/4096000', '3999/4000', '1']  interval_lower 732387807/1099511627776
noncomputable def e1339 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1329618258755,0,true,208935544832,208935544896⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨869404996797,0,false,-258178875648,-258178875584⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1329846160458,0,true,209123989248,209123989312⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨869177095094,0,false,-258467134208,-258467134144⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1329560732097,0,true,208887972864,208887972928⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨869462523455,0,false,-258106125760,-258106125696⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541368334,0,true,29740096,29740160⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099481887218,0,false,-29740992,-29740928⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626971,0,false,-832,-768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1329589489730,0,true,208911754368,208911754432⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨869433765822,0,false,-258142492928,-258142492864⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1329846169008,0,true,209123996288,209123996352⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨869177086544,0,false,-258467145024,-258467144960⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1051259295063,0,false,-49343148736,-49343148672⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1051366777623,0,false,-49230738496,-49230738432⟩
    { al := (428607/2048000), au := (858063/4096000), zl := (3999/4000), zu := 1,
      A := ⟨230106630979,230334532682⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208935544832,208935544896⟩ : DyadicInterval 40),(⟨-258178875648,-258178875584⟩ : DyadicInterval 40),(⟨737866018096,737866037425⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209123989248,209123989312⟩ : DyadicInterval 40),(⟨-258467134208,-258467134144⟩ : DyadicInterval 40),(⟨737817582720,737817602049⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208887972864,208887972928⟩ : DyadicInterval 40),(⟨-258106125760,-258106125696⟩ : DyadicInterval 40),(⟨737878236270,737878255600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209123989248,209123989312⟩ : DyadicInterval 40),(⟨-258467134208,-258467134144⟩ : DyadicInterval 40),(⟨737817582720,737817602049⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,29740558⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29740096,29740160⟩ : DyadicInterval 40),(⟨-29740992,-29740928⟩ : DyadicInterval 40),(⟨762123383195,762123402524⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-832,0⟩ : DyadicInterval 40),(⟨762123383616,762123403296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨230077861954,230334541232⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨208911754368,208911754432⟩ : DyadicInterval 40),(⟨-258142492928,-258142492864⟩ : DyadicInterval 40),(⟨737872128814,737872148143⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209123996288,209123996352⟩ : DyadicInterval 40),(⟨-258467145024,-258467144960⟩ : DyadicInterval 40),(⟨737817580920,737817600249⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-49343148736,-49230738432⟩ : DyadicInterval 40),(⟨786738752832,786794977248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨208935544832,209123989312⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-258467134208,-258178875584⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1339_ok : ecellOkT e1339 = true := by decide +kernel
theorem e1339_pos {a z : ℝ} (ha1 : ((428607/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((858063/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1339 e1339_ok ha1 ha2 hz1 hz2 hz

-- box ['858063/4096000', '26841/128000', '3999/4000', '1']  interval_lower 738034429/1099511627776
noncomputable def e1340 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1329846160457,0,true,209123989248,209123989312⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨869177095095,0,false,-258467134208,-258467134144⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1330074062160,0,true,209312401344,209312401408⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨868949193392,0,false,-258755468352,-258755468288⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1329788576823,0,true,209076378304,209076378368⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨869234678729,0,false,-258394293184,-258394293120⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541399717,0,true,29771520,29771584⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099481855835,0,false,-29772352,-29772288⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626969,0,false,-832,-768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1329817362940,0,true,209100179264,209100179328⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨869205892612,0,false,-258430705856,-258430705792⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1330074070710,0,true,209312408384,209312408448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨868949184842,0,false,-258755479168,-258755479104⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1051163762461,0,false,-49443070784,-49443070720⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1051271363363,0,false,-49330526528,-49330526464⟩
    { al := (858063/4096000), au := (26841/128000), zl := (3999/4000), zu := 1,
      A := ⟨230334532681,230562434384⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209123989248,209123989312⟩ : DyadicInterval 40),(⟨-258467134208,-258467134144⟩ : DyadicInterval 40),(⟨737817582720,737817602050⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209312401344,209312401408⟩ : DyadicInterval 40),(⟨-258755468352,-258755468288⟩ : DyadicInterval 40),(⟨737769097952,737769117281⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209076378304,209076378368⟩ : DyadicInterval 40),(⟨-258394293184,-258394293120⟩ : DyadicInterval 40),(⟨737829825493,737829844822⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209312401344,209312401408⟩ : DyadicInterval 40),(⟨-258755468352,-258755468288⟩ : DyadicInterval 40),(⟨737769097952,737769117281⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,29771941⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29771520,29771584⟩ : DyadicInterval 40),(⟨-29772352,-29772288⟩ : DyadicInterval 40),(⟨762123383161,762123402490⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-832,0⟩ : DyadicInterval 40),(⟨762123383616,762123403296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨230305735164,230562442934⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209100179264,209100179328⟩ : DyadicInterval 40),(⟨-258430705856,-258430705792⟩ : DyadicInterval 40),(⟨737823705736,737823725066⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209312408384,209312408448⟩ : DyadicInterval 40),(⟨-258755479168,-258755479104⟩ : DyadicInterval 40),(⟨737769096148,737769115477⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-49443070784,-49330526464⟩ : DyadicInterval 40),(⟨786788646848,786844938272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨209123989248,209312401408⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-258755468352,-258467134144⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1340_ok : ecellOkT e1340 = true := by decide +kernel
theorem e1340_pos {a z : ℝ} (ha1 : ((858063/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((26841/128000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1340 e1340_ok ha1 ha2 hz1 hz2 hz

-- box ['26841/128000', '859761/4096000', '999/1000', '3997/4000']  interval_lower 746832433/1099511627776
noncomputable def e1341 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1330074062159,0,true,209312401344,209312401408⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨868949193393,0,false,-258755468352,-258755468288⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1330301963863,0,true,209500781120,209500781184⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨868721291689,0,false,-259043878144,-259043878080⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1329843499724,0,true,209121789312,209121789376⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨869179755828,0,false,-258463768384,-258463768320⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1330128871112,0,true,209357708480,209357708544⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨868894384440,0,false,-258824822208,-258824822144⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099600939596,0,true,89308160,89308224⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099422315956,0,false,-89315456,-89315392⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099630837342,0,true,119203072,119203136⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099392418210,0,false,-119216064,-119216000⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511614851,0,false,-12928,-12864⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620522,0,false,-7296,-7232⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1329958776970,0,true,209217096192,209217096256⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨869064478582,0,false,-258609603648,-258609603584⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1330215427078,0,true,209429255040,209429255104⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨868807828474,0,false,-258934356864,-258934356800⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1051104460750,0,false,-49505101760,-49505101696⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1051212103488,0,false,-49392507456,-49392507392⟩
    { al := (26841/128000), au := (859761/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨230562434383,230790336087⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209312401344,209312401408⟩ : DyadicInterval 40),(⟨-258755468352,-258755468288⟩ : DyadicInterval 40),(⟨737769097952,737769117282⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209500781120,209500781184⟩ : DyadicInterval 40),(⟨-259043878144,-259043878080⟩ : DyadicInterval 40),(⟨737720563802,737720583132⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209121789312,209121789376⟩ : DyadicInterval 40),(⟨-258463768384,-258463768320⟩ : DyadicInterval 40),(⟨737818148517,737818167846⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209357708480,209357708544⟩ : DyadicInterval 40),(⟨-258824822208,-258824822144⟩ : DyadicInterval 40),(⟨737757430288,737757449618⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨89311820,119209566⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨89308160,89308224⟩ : DyadicInterval 40),(⟨-89315456,-89315392⟩ : DyadicInterval 40),(⟨762123379945,762123399274⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨119203072,119203136⟩ : DyadicInterval 40),(⟨-119216064,-119216000⟩ : DyadicInterval 40),(⟨762123377122,762123396452⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-12928,-7232⟩ : DyadicInterval 40),(⟨762123387232,762123409344⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨230447149194,230703799302⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209217096192,209217096256⟩ : DyadicInterval 40),(⟨-258609603648,-258609603584⟩ : DyadicInterval 40),(⟨737793630382,737793649711⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209429255040,209429255104⟩ : DyadicInterval 40),(⟨-258934356864,-258934356800⟩ : DyadicInterval 40),(⟨737738998577,737739017906⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-49505101760,-49392507392⟩ : DyadicInterval 40),(⟨786819637312,786875953760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨209312401344,209500781184⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-259043878144,-258755468288⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1341_ok : ecellOkT e1341 = true := by decide +kernel
theorem e1341_pos {a z : ℝ} (ha1 : ((26841/128000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((859761/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1341 e1341_ok ha1 ha2 hz1 hz2 hz

-- box ['859761/4096000', '86061/409600', '999/1000', '3997/4000']  interval_lower 752533301/1099511627776
noncomputable def e1342 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1330301963862,0,true,209500781120,209500781184⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨868721291690,0,false,-259043878144,-259043878080⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1330529865565,0,true,209689128704,209689128768⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨868493389987,0,false,-259332363584,-259332363520⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1330071173525,0,true,209310013440,209310013504⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨868952082027,0,false,-258751813248,-258751813184⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1330356601887,0,true,209545939264,209545939328⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨868666653665,0,false,-259113033856,-259113033792⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099601033753,0,true,89402304,89402368⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099422221799,0,false,-89409664,-89409600⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099630962911,0,true,119328640,119328704⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099392292641,0,false,-119341632,-119341568⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511614824,0,false,-12992,-12928⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620507,0,false,-7296,-7232⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1330186564724,0,true,209405398144,209405398208⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨868836690828,0,false,-258897830976,-258897830912⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1330443243321,0,true,209617544192,209617544256⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨868580012231,0,false,-259222705408,-259222705344⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1051008810969,0,false,-49605161152,-49605161088⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1051116572016,0,false,-49492432832,-49492432768⟩
    { al := (859761/4096000), au := (86061/409600), zl := (999/1000), zu := (3997/4000),
      A := ⟨230790336086,231018237789⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209500781120,209500781184⟩ : DyadicInterval 40),(⟨-259043878144,-259043878080⟩ : DyadicInterval 40),(⟨737720563802,737720583132⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209689128704,209689128768⟩ : DyadicInterval 40),(⟨-259332363584,-259332363520⟩ : DyadicInterval 40),(⟨737671980181,737671999510⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209310013440,209310013504⟩ : DyadicInterval 40),(⟨-258751813248,-258751813184⟩ : DyadicInterval 40),(⟨737769712792,737769732122⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209545939264,209545939328⟩ : DyadicInterval 40),(⟨-259113033856,-259113033792⟩ : DyadicInterval 40),(⟨737708920665,737708939995⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨89405977,119335135⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨89402304,89402368⟩ : DyadicInterval 40),(⟨-89409664,-89409600⟩ : DyadicInterval 40),(⟨762123379961,762123399291⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨119328640,119328704⟩ : DyadicInterval 40),(⟨-119341632,-119341568⟩ : DyadicInterval 40),(⟨762123377095,762123396425⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-12992,-7232⟩ : DyadicInterval 40),(⟨762123387232,762123409376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨230674936948,230931615545⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209405398144,209405398208⟩ : DyadicInterval 40),(⟨-258897830976,-258897830912⟩ : DyadicInterval 40),(⟨737745145473,737745164802⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209617544192,209617544256⟩ : DyadicInterval 40),(⟨-259222705408,-259222705344⟩ : DyadicInterval 40),(⟨737690451984,737690471313⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-49605161152,-49492432768⟩ : DyadicInterval 40),(⟨786869600000,786925983456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨209500781120,209689128768⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-259332363584,-259043878080⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1342_ok : ecellOkT e1342 = true := by decide +kernel
theorem e1342_pos {a z : ℝ} (ha1 : ((859761/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((86061/409600 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1342 e1342_ok ha1 ha2 hz1 hz2 hz

-- box ['26841/128000', '859761/4096000', '3997/4000', '1999/2000']  interval_lower 745790219/1099511627776
noncomputable def e1343 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1330074062159,0,true,209312401344,209312401408⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨868949193393,0,false,-258755468352,-258755468288⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1330301963863,0,true,209500781120,209500781184⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨868721291689,0,false,-259043878144,-259043878080⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1329901140333,0,true,209169445440,209169445504⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨869122115219,0,false,-258536686144,-258536686080⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1330186568696,0,true,209405401408,209405401472⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨868836686856,0,false,-258897836032,-258897835968⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099571169399,0,true,59539968,59540032⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452086153,0,false,-59543296,-59543232⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099601035760,0,true,89404288,89404352⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099422219792,0,false,-89411648,-89411584⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620505,0,false,-7296,-7232⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624552,0,false,-3264,-3200⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1329987596466,0,true,209240921728,209240921792⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨869035659086,0,false,-258646065728,-258646065664⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1330244275285,0,true,209453099776,209453099840⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨868778980267,0,false,-258970866048,-258970865984⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1051092353907,0,false,-49517766272,-49517766208⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1051200022149,0,false,-49405144000,-49405143936⟩
    { al := (26841/128000), au := (859761/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨230562434383,230790336087⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209312401344,209312401408⟩ : DyadicInterval 40),(⟨-258755468352,-258755468288⟩ : DyadicInterval 40),(⟨737769097952,737769117282⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209500781120,209500781184⟩ : DyadicInterval 40),(⟨-259043878144,-259043878080⟩ : DyadicInterval 40),(⟨737720563802,737720583132⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209169445440,209169445504⟩ : DyadicInterval 40),(⟨-258536686144,-258536686080⟩ : DyadicInterval 40),(⟨737805890612,737805909941⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209405401408,209405401472⟩ : DyadicInterval 40),(⟨-258897836032,-258897835968⟩ : DyadicInterval 40),(⟨737745144650,737745163980⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨59541623,89407984⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59539968,59540032⟩ : DyadicInterval 40),(⟨-59543296,-59543232⟩ : DyadicInterval 40),(⟨762123381991,762123401320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨89404288,89404352⟩ : DyadicInterval 40),(⟨-89411648,-89411584⟩ : DyadicInterval 40),(⟨762123379961,762123399290⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7296,-3200⟩ : DyadicInterval 40),(⟨762123385216,762123406528⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨230475968690,230732647509⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209240921728,209240921792⟩ : DyadicInterval 40),(⟨-258646065728,-258646065664⟩ : DyadicInterval 40),(⟨737787498864,737787518194⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209453099776,209453099840⟩ : DyadicInterval 40),(⟨-258970866048,-258970865984⟩ : DyadicInterval 40),(⟨737732853865,737732873195⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-49517766272,-49405143936⟩ : DyadicInterval 40),(⟨786825955584,786882286016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨209312401344,209500781184⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-259043878144,-258755468288⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1343_ok : ecellOkT e1343 = true := by decide +kernel
theorem e1343_pos {a z : ℝ} (ha1 : ((26841/128000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((859761/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1343 e1343_ok ha1 ha2 hz1 hz2 hz

-- box ['859761/4096000', '86061/409600', '3997/4000', '1999/2000']  interval_lower 187871853/274877906944
noncomputable def e1344 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1330301963862,0,true,209500781120,209500781184⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨868721291690,0,false,-259043878144,-259043878080⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1330529865565,0,true,209689128704,209689128768⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨868493389987,0,false,-259332363584,-259332363520⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1330128871109,0,true,209357708480,209357708544⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨868894384443,0,false,-258824822208,-258824822144⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1330414356447,0,true,209593671104,209593671168⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨868608899105,0,false,-259186138880,-259186138816⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099571232171,0,true,59602752,59602816⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452023381,0,false,-59606016,-59605952⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099601129940,0,true,89498496,89498560⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099422125612,0,false,-89505856,-89505792⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620490,0,false,-7296,-7232⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624545,0,false,-3264,-3200⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1330215412702,0,true,209429243200,209429243264⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨868807842850,0,false,-258934338688,-258934338624⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1330472120017,0,true,209641408384,209641408448⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨868551135535,0,false,-259259260224,-259259260160⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1050996680204,0,false,-49617851776,-49617851712⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1051104466784,0,false,-49505095488,-49505095424⟩
    { al := (859761/4096000), au := (86061/409600), zl := (3997/4000), zu := (1999/2000),
      A := ⟨230790336086,231018237789⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209500781120,209500781184⟩ : DyadicInterval 40),(⟨-259043878144,-259043878080⟩ : DyadicInterval 40),(⟨737720563802,737720583132⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209689128704,209689128768⟩ : DyadicInterval 40),(⟨-259332363584,-259332363520⟩ : DyadicInterval 40),(⟨737671980181,737671999510⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209357708480,209357708544⟩ : DyadicInterval 40),(⟨-258824822208,-258824822144⟩ : DyadicInterval 40),(⟨737757430289,737757449618⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209593671104,209593671168⟩ : DyadicInterval 40),(⟨-259186138880,-259186138816⟩ : DyadicInterval 40),(⟨737696610362,737696629692⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨59604395,89502164⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59602752,59602816⟩ : DyadicInterval 40),(⟨-59606016,-59605952⟩ : DyadicInterval 40),(⟨762123381952,762123401281⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨89498496,89498560⟩ : DyadicInterval 40),(⟨-89505856,-89505792⟩ : DyadicInterval 40),(⟨762123379946,762123399275⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7296,-3200⟩ : DyadicInterval 40),(⟨762123385216,762123406528⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨230703784926,230960492241⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209429243200,209429243264⟩ : DyadicInterval 40),(⟨-258934338688,-258934338624⟩ : DyadicInterval 40),(⟨737739001620,737739020949⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209641408384,209641408448⟩ : DyadicInterval 40),(⟨-259259260224,-259259260160⟩ : DyadicInterval 40),(⟨737684294945,737684314274⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-49617851776,-49505095424⟩ : DyadicInterval 40),(⟨786875931328,786932328768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨209500781120,209689128768⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-259332363584,-259043878080⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1344_ok : ecellOkT e1344 = true := by decide +kernel
theorem e1344_pos {a z : ℝ} (ha1 : ((859761/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((86061/409600 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1344 e1344_ok ha1 ha2 hz1 hz2 hz

-- box ['86061/409600', '861459/4096000', '999/1000', '3997/4000']  interval_lower 94781975/137438953472
noncomputable def e1345 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1330529865564,0,true,209689128704,209689128768⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨868493389988,0,false,-259332363584,-259332363520⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1330757767267,0,true,209877443968,209877444032⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨868265488285,0,false,-259620924736,-259620924672⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1330298847326,0,true,209498205248,209498205312⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨868724408226,0,false,-259039933632,-259039933568⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1330584332663,0,true,209734137792,209734137856⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨868438922889,0,false,-259401321024,-259401320960⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099601127929,0,true,89496448,89496512⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099422127623,0,false,-89503808,-89503744⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099631088506,0,true,119454208,119454272⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099392167046,0,false,-119467264,-119467200⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511614796,0,false,-12992,-12928⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620491,0,false,-7296,-7232⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1330414352474,0,true,209593667840,209593667904⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨868608903078,0,false,-259186133888,-259186133824⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1330671059560,0,true,209805801152,209805801216⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨868352195992,0,false,-259511129536,-259511129472⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1050913066785,0,false,-49705328384,-49705328320⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1051020946163,0,false,-49592465984,-49592465920⟩
    { al := (86061/409600), au := (861459/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨231018237788,231246139491⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209689128704,209689128768⟩ : DyadicInterval 40),(⟨-259332363584,-259332363520⟩ : DyadicInterval 40),(⟨737671980181,737671999511⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209877443968,209877444032⟩ : DyadicInterval 40),(⟨-259620924736,-259620924672⟩ : DyadicInterval 40),(⟨737623347177,737623366506⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209498205248,209498205312⟩ : DyadicInterval 40),(⟨-259039933632,-259039933568⟩ : DyadicInterval 40),(⟨737721227834,737721247164⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209734137792,209734137856⟩ : DyadicInterval 40),(⟨-259401321024,-259401320960⟩ : DyadicInterval 40),(⟨737660361703,737660381033⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨89500153,119460730⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨89496448,89496512⟩ : DyadicInterval 40),(⟨-89503808,-89503744⟩ : DyadicInterval 40),(⟨762123379946,762123399275⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨119454208,119454272⟩ : DyadicInterval 40),(⟨-119467264,-119467200⟩ : DyadicInterval 40),(⟨762123377100,762123396430⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-12992,-7232⟩ : DyadicInterval 40),(⟨762123387232,762123409376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨230902724698,231159431784⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209593667840,209593667904⟩ : DyadicInterval 40),(⟨-259186133888,-259186133824⟩ : DyadicInterval 40),(⟨737696611212,737696630541⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209805801152,209805801216⟩ : DyadicInterval 40),(⟨-259511129536,-259511129472⟩ : DyadicInterval 40),(⟨737641855960,737641875290⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-49705328384,-49592465920⟩ : DyadicInterval 40),(⟨786919616576,786976067072⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨209689128704,209877444032⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-259620924736,-259332363520⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1345_ok : ecellOkT e1345 = true := by decide +kernel
theorem e1345_pos {a z : ℝ} (ha1 : ((86061/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((861459/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1345 e1345_ok ha1 ha2 hz1 hz2 hz

-- box ['861459/4096000', '215577/1024000', '999/1000', '3997/4000']  interval_lower 190999927/274877906944
noncomputable def e1346 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1330757767266,0,true,209877443968,209877444032⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨868265488286,0,false,-259620924736,-259620924672⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1330985668969,0,true,210065727040,210065727104⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨868037586583,0,false,-259909561600,-259909561536⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1330526521126,0,true,209686364928,209686364992⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨868496734426,0,false,-259328129536,-259328129472⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1330812063439,0,true,209922304192,209922304256⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨868211192113,0,false,-259689683840,-259689683776⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099601222122,0,true,89590656,89590720⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099422033430,0,false,-89598016,-89597952⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099631214125,0,true,119579840,119579904⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099392041427,0,false,-119592896,-119592832⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511614769,0,false,-13056,-12992⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620476,0,false,-7360,-7296⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1330642140225,0,true,209781905344,209781905408⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨868381115327,0,false,-259474512320,-259474512256⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1330898875809,0,true,209994025856,209994025920⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨868124379743,0,false,-259799629376,-259799629312⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1050817228190,0,false,-49805603520,-49805603456⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1050925225927,0,false,-49692606976,-49692606912⟩
    { al := (861459/4096000), au := (215577/1024000), zl := (999/1000), zu := (3997/4000),
      A := ⟨231246139490,231474041193⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209877443968,209877444032⟩ : DyadicInterval 40),(⟨-259620924736,-259620924672⟩ : DyadicInterval 40),(⟨737623347177,737623366506⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210065727040,210065727104⟩ : DyadicInterval 40),(⟨-259909561600,-259909561536⟩ : DyadicInterval 40),(⟨737574664699,737574684028⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209686364928,209686364992⟩ : DyadicInterval 40),(⟨-259328129536,-259328129472⟩ : DyadicInterval 40),(⟨737672693513,737672712843⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209922304192,209922304256⟩ : DyadicInterval 40),(⟨-259689683840,-259689683776⟩ : DyadicInterval 40),(⟨737611753362,737611772692⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨89594346,119586349⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨89590656,89590720⟩ : DyadicInterval 40),(⟨-89598016,-89597952⟩ : DyadicInterval 40),(⟨762123379931,762123399260⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨119579840,119579904⟩ : DyadicInterval 40),(⟨-119592896,-119592832⟩ : DyadicInterval 40),(⟨762123377073,762123396402⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-13056,-7296⟩ : DyadicInterval 40),(⟨762123387264,762123409408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨231130512449,231387248033⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209781905344,209781905408⟩ : DyadicInterval 40),(⟨-259474512320,-259474512256⟩ : DyadicInterval 40),(⟨737648027520,737648046850⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209994025856,209994025920⟩ : DyadicInterval 40),(⟨-259799629376,-259799629312⟩ : DyadicInterval 40),(⟨737593210579,737593229908⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-49805603520,-49692606912⟩ : DyadicInterval 40),(⟨786969687072,787026204640⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨209877443968,210065727104⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-259909561600,-259620924672⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1346_ok : ecellOkT e1346 = true := by decide +kernel
theorem e1346_pos {a z : ℝ} (ha1 : ((861459/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((215577/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1346 e1346_ok ha1 ha2 hz1 hz2 hz

-- box ['86061/409600', '861459/4096000', '3997/4000', '1999/2000']  interval_lower 757205803/1099511627776
noncomputable def e1347 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1330529865564,0,true,209689128704,209689128768⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨868493389988,0,false,-259332363584,-259332363520⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1330757767267,0,true,209877443968,209877444032⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨868265488285,0,false,-259620924736,-259620924672⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1330356601885,0,true,209545939264,209545939328⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨868666653667,0,false,-259113033856,-259113033792⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1330642144198,0,true,209781908608,209781908672⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨868381111354,0,false,-259474517376,-259474517312⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099571294957,0,true,59665536,59665600⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099451960595,0,false,-59668864,-59668800⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099601224138,0,true,89592704,89592768⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099422031414,0,false,-89600064,-89600000⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620475,0,false,-7360,-7296⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624539,0,false,-3264,-3200⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1330443228941,0,true,209617532352,209617532416⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨868580026611,0,false,-259222687168,-259222687104⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1330699964746,0,true,209829684800,209829684864⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨868323290806,0,false,-259547730048,-259547729984⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1050900912072,0,false,-49718045248,-49718045184⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1051008817011,0,false,-49605154816,-49605154752⟩
    { al := (86061/409600), au := (861459/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨231018237788,231246139491⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209689128704,209689128768⟩ : DyadicInterval 40),(⟨-259332363584,-259332363520⟩ : DyadicInterval 40),(⟨737671980181,737671999511⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209877443968,209877444032⟩ : DyadicInterval 40),(⟨-259620924736,-259620924672⟩ : DyadicInterval 40),(⟨737623347177,737623366506⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209545939264,209545939328⟩ : DyadicInterval 40),(⟨-259113033856,-259113033792⟩ : DyadicInterval 40),(⟨737708920666,737708939995⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209781908608,209781908672⟩ : DyadicInterval 40),(⟨-259474517376,-259474517312⟩ : DyadicInterval 40),(⟨737648026694,737648046023⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨59667181,89596362⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59665536,59665600⟩ : DyadicInterval 40),(⟨-59668864,-59668800⟩ : DyadicInterval 40),(⟨762123381977,762123401307⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨89592704,89592768⟩ : DyadicInterval 40),(⟨-89600064,-89600000⟩ : DyadicInterval 40),(⟨762123379930,762123399260⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7360,-3200⟩ : DyadicInterval 40),(⟨762123385216,762123406560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨230931601165,231188336970⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209617532352,209617532416⟩ : DyadicInterval 40),(⟨-259222687168,-259222687104⟩ : DyadicInterval 40),(⟨737690455009,737690474338⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209829684800,209829684864⟩ : DyadicInterval 40),(⟨-259547730048,-259547729984⟩ : DyadicInterval 40),(⟨737635686592,737635705921⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-49718045248,-49605154752⟩ : DyadicInterval 40),(⟨786925960992,786982425504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨209689128704,209877444032⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-259620924736,-259332363520⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1347_ok : ecellOkT e1347 = true := by decide +kernel
theorem e1347_pos {a z : ℝ} (ha1 : ((86061/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((861459/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1347 e1347_ok ha1 ha2 hz1 hz2 hz

-- box ['861459/4096000', '215577/1024000', '3997/4000', '1999/2000']  interval_lower 762945733/1099511627776
noncomputable def e1348 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1330757767266,0,true,209877443968,209877444032⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨868265488286,0,false,-259620924736,-259620924672⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1330985668969,0,true,210065727040,210065727104⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨868037586583,0,false,-259909561600,-259909561536⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1330584332661,0,true,209734137792,209734137856⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨868438922891,0,false,-259401321024,-259401320960⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1330869931949,0,true,209970113856,209970113920⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨868153323603,0,false,-259762971520,-259762971456⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099571357753,0,true,59728320,59728384⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099451897799,0,false,-59731648,-59731584⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099601318354,0,true,89686912,89686976⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099421937198,0,false,-89694272,-89694208⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620459,0,false,-7360,-7296⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624532,0,false,-3264,-3200⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1330671045174,0,true,209805789248,209805789312⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨868352210378,0,false,-259511111296,-259511111232⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1330927809479,0,true,210017928896,210017928960⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨868095446073,0,false,-259836275584,-259836275520⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1050805049508,0,false,-49818346624,-49818346560⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1050913072835,0,false,-49705322048,-49705321984⟩
    { al := (861459/4096000), au := (215577/1024000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨231246139490,231474041193⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209877443968,209877444032⟩ : DyadicInterval 40),(⟨-259620924736,-259620924672⟩ : DyadicInterval 40),(⟨737623347177,737623366506⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210065727040,210065727104⟩ : DyadicInterval 40),(⟨-259909561600,-259909561536⟩ : DyadicInterval 40),(⟨737574664699,737574684028⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209734137792,209734137856⟩ : DyadicInterval 40),(⟨-259401321024,-259401320960⟩ : DyadicInterval 40),(⟨737660361704,737660381033⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209970113856,209970113920⟩ : DyadicInterval 40),(⟨-259762971520,-259762971456⟩ : DyadicInterval 40),(⟨737599393671,737599413001⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨59729977,89690578⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59728320,59728384⟩ : DyadicInterval 40),(⟨-59731648,-59731584⟩ : DyadicInterval 40),(⟨762123381971,762123401300⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨89686912,89686976⟩ : DyadicInterval 40),(⟨-89694272,-89694208⟩ : DyadicInterval 40),(⟨762123379915,762123399244⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7360,-3200⟩ : DyadicInterval 40),(⟨762123385216,762123406560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨231159417398,231416181703⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209805789248,209805789312⟩ : DyadicInterval 40),(⟨-259511111296,-259511111232⟩ : DyadicInterval 40),(⟨737641859031,737641878361⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210017928896,210017928960⟩ : DyadicInterval 40),(⟨-259836275584,-259836275520⟩ : DyadicInterval 40),(⟨737587028894,737587048223⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-49818346624,-49705321984⟩ : DyadicInterval 40),(⟨786976044608,787032576192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨209877443968,210065727104⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-259909561600,-259620924672⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1348_ok : ecellOkT e1348 = true := by decide +kernel
theorem e1348_pos {a z : ℝ} (ha1 : ((861459/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((215577/1024000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1348 e1348_ok ha1 ha2 hz1 hz2 hz

-- box ['26841/128000', '859761/4096000', '1999/2000', '3999/4000']  interval_lower 46546669/68719476736
noncomputable def e1349 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1330074062159,0,true,209312401344,209312401408⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨868949193393,0,false,-258755468352,-258755468288⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1330301963863,0,true,209500781120,209500781184⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨868721291689,0,false,-259043878144,-259043878080⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1329958780941,0,true,209217099456,209217099520⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨869064474611,0,false,-258609608704,-258609608640⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1330244266280,0,true,209453092288,209453092352⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨868778989272,0,false,-258970854656,-258970854592⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541398707,0,true,29770496,29770560⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099481856845,0,false,-29771392,-29771328⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099571233681,0,true,59604288,59604352⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452021871,0,false,-59607552,-59607488⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624544,0,false,-3264,-3200⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626970,0,false,-832,-768⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1330016416190,0,true,209264747008,209264747072⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨869006839362,0,false,-258682529344,-258682529280⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1330273123728,0,true,209476944128,209476944192⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨868750131824,0,false,-259007376768,-259007376704⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1051080245452,0,false,-49530432576,-49530432512⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1051187939205,0,false,-49417782272,-49417782208⟩
    { al := (26841/128000), au := (859761/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨230562434383,230790336087⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209312401344,209312401408⟩ : DyadicInterval 40),(⟨-258755468352,-258755468288⟩ : DyadicInterval 40),(⟨737769097952,737769117282⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209500781120,209500781184⟩ : DyadicInterval 40),(⟨-259043878144,-259043878080⟩ : DyadicInterval 40),(⟨737720563802,737720583132⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209217099456,209217099520⟩ : DyadicInterval 40),(⟨-258609608704,-258609608640⟩ : DyadicInterval 40),(⟨737793629561,737793648891⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209453092288,209453092352⟩ : DyadicInterval 40),(⟨-258970854656,-258970854592⟩ : DyadicInterval 40),(⟨737732855813,737732875143⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨29770931,59605905⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29770496,29770560⟩ : DyadicInterval 40),(⟨-29771392,-29771328⟩ : DyadicInterval 40),(⟨762123383193,762123402522⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59604288,59604352⟩ : DyadicInterval 40),(⟨-59607552,-59607488⟩ : DyadicInterval 40),(⟨762123381952,762123401281⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3264,-768⟩ : DyadicInterval 40),(⟨762123384000,762123404512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨230504788414,230761495952⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209264747008,209264747072⟩ : DyadicInterval 40),(⟨-258682529344,-258682529280⟩ : DyadicInterval 40),(⟨737781366480,737781385809⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209476944128,209476944192⟩ : DyadicInterval 40),(⟨-259007376768,-259007376704⟩ : DyadicInterval 40),(⟨737726708360,737726727689⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-49530432576,-49417782208⟩ : DyadicInterval 40),(⟨786832274720,786888619168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨209312401344,209500781184⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-259043878144,-258755468288⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1349_ok : ecellOkT e1349 = true := by decide +kernel
theorem e1349_pos {a z : ℝ} (ha1 : ((26841/128000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((859761/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1349 e1349_ok ha1 ha2 hz1 hz2 hz

-- box ['859761/4096000', '86061/409600', '1999/2000', '3999/4000']  interval_lower 93804985/137438953472
noncomputable def e1350 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1330301963862,0,true,209500781120,209500781184⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨868721291690,0,false,-259043878144,-259043878080⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1330529865565,0,true,209689128704,209689128768⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨868493389987,0,false,-259332363584,-259332363520⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1330186568693,0,true,209405401408,209405401472⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨868836686859,0,false,-258897836032,-258897835968⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1330472111006,0,true,209641400960,209641401024⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨868551144546,0,false,-259259248768,-259259248704⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541430093,0,true,29801856,29801920⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099481825459,0,false,-29802752,-29802688⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099571296469,0,true,59667072,59667136⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099451959083,0,false,-59670336,-59670272⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624537,0,false,-3264,-3200⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626969,0,false,-832,-768⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1330244260908,0,true,209453087872,209453087936⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨868778994644,0,false,-258970847872,-258970847808⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1330500996952,0,true,209665272256,209665272320⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨868522258600,0,false,-259295816576,-259295816512⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1050984547821,0,false,-49630544256,-49630544192⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1051092359942,0,false,-49517759936,-49517759872⟩
    { al := (859761/4096000), au := (86061/409600), zl := (1999/2000), zu := (3999/4000),
      A := ⟨230790336086,231018237789⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209500781120,209500781184⟩ : DyadicInterval 40),(⟨-259043878144,-259043878080⟩ : DyadicInterval 40),(⟨737720563802,737720583132⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209689128704,209689128768⟩ : DyadicInterval 40),(⟨-259332363584,-259332363520⟩ : DyadicInterval 40),(⟨737671980181,737671999510⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209405401408,209405401472⟩ : DyadicInterval 40),(⟨-258897836032,-258897835968⟩ : DyadicInterval 40),(⟨737745144651,737745163980⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209641400960,209641401024⟩ : DyadicInterval 40),(⟨-259259248768,-259259248704⟩ : DyadicInterval 40),(⟨737684296833,737684316162⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨29802317,59668693⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29801856,29801920⟩ : DyadicInterval 40),(⟨-29802752,-29802688⟩ : DyadicInterval 40),(⟨762123383192,762123402521⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59667072,59667136⟩ : DyadicInterval 40),(⟨-59670336,-59670272⟩ : DyadicInterval 40),(⟨762123381945,762123401274⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3264,-768⟩ : DyadicInterval 40),(⟨762123384000,762123404512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨230732633132,230989369176⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209453087872,209453087936⟩ : DyadicInterval 40),(⟨-258970847872,-258970847808⟩ : DyadicInterval 40),(⟨737732856948,737732876278⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209665272256,209665272320⟩ : DyadicInterval 40),(⟨-259295816576,-259295816512⟩ : DyadicInterval 40),(⟨737678137068,737678156397⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-49630544256,-49517759872⟩ : DyadicInterval 40),(⟨786882263552,786938675008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨209500781120,209689128768⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-259332363584,-259043878080⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1350_ok : ecellOkT e1350 = true := by decide +kernel
theorem e1350_pos {a z : ℝ} (ha1 : ((859761/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((86061/409600 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1350 e1350_ok ha1 ha2 hz1 hz2 hz

-- box ['26841/128000', '859761/4096000', '3999/4000', '1']  interval_lower 743702727/1099511627776
noncomputable def e1351 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1330074062159,0,true,209312401344,209312401408⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨868949193393,0,false,-258755468352,-258755468288⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1330301963863,0,true,209500781120,209500781184⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨868721291689,0,false,-259043878144,-259043878080⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1330016421550,0,true,209264751424,209264751488⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨869006834002,0,false,-258682536128,-258682536064⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541431106,0,true,29802880,29802944⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099481824446,0,false,-29803776,-29803712⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626968,0,false,-832,-768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1330045236147,0,true,209288571904,209288571968⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨868978019405,0,false,-258718994432,-258718994368⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1330301972404,0,true,209500788224,209500788288⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨868721283148,0,false,-259043888960,-259043888896⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1051068135385,0,false,-49543100736,-49543100672⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1051175854651,0,false,-49430422464,-49430422400⟩
    { al := (26841/128000), au := (859761/4096000), zl := (3999/4000), zu := 1,
      A := ⟨230562434383,230790336087⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209312401344,209312401408⟩ : DyadicInterval 40),(⟨-258755468352,-258755468288⟩ : DyadicInterval 40),(⟨737769097952,737769117282⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209500781120,209500781184⟩ : DyadicInterval 40),(⟨-259043878144,-259043878080⟩ : DyadicInterval 40),(⟨737720563802,737720583132⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209264751424,209264751488⟩ : DyadicInterval 40),(⟨-258682536128,-258682536064⟩ : DyadicInterval 40),(⟨737781365349,737781384679⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209500781120,209500781184⟩ : DyadicInterval 40),(⟨-259043878144,-259043878080⟩ : DyadicInterval 40),(⟨737720563802,737720583132⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,29803330⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29802880,29802944⟩ : DyadicInterval 40),(⟨-29803776,-29803712⟩ : DyadicInterval 40),(⟨762123383192,762123402521⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-832,0⟩ : DyadicInterval 40),(⟨762123383616,762123403296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨230533608371,230790344628⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209288571904,209288571968⟩ : DyadicInterval 40),(⟨-258718994432,-258718994368⟩ : DyadicInterval 40),(⟨737775233280,737775252609⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209500788224,209500788288⟩ : DyadicInterval 40),(⟨-259043888960,-259043888896⟩ : DyadicInterval 40),(⟨737720561957,737720581287⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-49543100736,-49430422400⟩ : DyadicInterval 40),(⟨786838594816,786894953248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨209312401344,209500781184⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-259043878144,-258755468288⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1351_ok : ecellOkT e1351 = true := by decide +kernel
theorem e1351_pos {a z : ℝ} (ha1 : ((26841/128000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((859761/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1351 e1351_ok ha1 ha2 hz1 hz2 hz

-- box ['859761/4096000', '86061/409600', '3999/4000', '1']  interval_lower 749392045/1099511627776
noncomputable def e1352 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1330301963862,0,true,209500781120,209500781184⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨868721291690,0,false,-259043878144,-259043878080⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1330529865565,0,true,209689128704,209689128768⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨868493389987,0,false,-259332363584,-259332363520⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1330244266277,0,true,209453092288,209453092352⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨868778989275,0,false,-258970854656,-258970854592⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541462500,0,true,29834304,29834368⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099481793052,0,false,-29835136,-29835072⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626966,0,false,-832,-768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1330273109351,0,true,209476932288,209476932352⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨868750146201,0,false,-259007358528,-259007358464⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1330529874113,0,true,209689135744,209689135808⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨868493381439,0,false,-259332374400,-259332374336⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1050972413826,0,false,-49643238592,-49643238528⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1051080251488,0,false,-49530426240,-49530426176⟩
    { al := (859761/4096000), au := (86061/409600), zl := (3999/4000), zu := 1,
      A := ⟨230790336086,231018237789⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209500781120,209500781184⟩ : DyadicInterval 40),(⟨-259043878144,-259043878080⟩ : DyadicInterval 40),(⟨737720563802,737720583132⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209689128704,209689128768⟩ : DyadicInterval 40),(⟨-259332363584,-259332363520⟩ : DyadicInterval 40),(⟨737671980181,737671999510⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209453092288,209453092352⟩ : DyadicInterval 40),(⟨-258970854656,-258970854592⟩ : DyadicInterval 40),(⟨737732855814,737732875143⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209689128704,209689128768⟩ : DyadicInterval 40),(⟨-259332363584,-259332363520⟩ : DyadicInterval 40),(⟨737671980181,737671999510⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,29834724⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29834304,29834368⟩ : DyadicInterval 40),(⟨-29835136,-29835072⟩ : DyadicInterval 40),(⟨762123383158,762123402487⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-832,0⟩ : DyadicInterval 40),(⟨762123383616,762123403296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨230761481575,231018246337⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209476932288,209476932352⟩ : DyadicInterval 40),(⟨-259007358528,-259007358464⟩ : DyadicInterval 40),(⟨737726711380,737726730709⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209689135744,209689135808⟩ : DyadicInterval 40),(⟨-259332374400,-259332374336⟩ : DyadicInterval 40),(⟨737671978370,737671997699⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-49643238592,-49530426176⟩ : DyadicInterval 40),(⟨786888596704,786945022176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨209500781120,209689128768⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-259332363584,-259043878080⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1352_ok : ecellOkT e1352 = true := by decide +kernel
theorem e1352_pos {a z : ℝ} (ha1 : ((859761/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((86061/409600 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1352 e1352_ok ha1 ha2 hz1 hz2 hz

-- box ['86061/409600', '861459/4096000', '1999/2000', '3999/4000']  interval_lower 189038651/274877906944
noncomputable def e1353 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1330529865564,0,true,209689128704,209689128768⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨868493389988,0,false,-259332363584,-259332363520⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1330757767267,0,true,209877443968,209877444032⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨868265488285,0,false,-259620924736,-259620924672⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1330414356445,0,true,209593671104,209593671168⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨868608899107,0,false,-259186138880,-259186138816⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1330699955733,0,true,209829677312,209829677376⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨868323299819,0,false,-259547718592,-259547718528⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541461486,0,true,29833280,29833344⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099481794066,0,false,-29834176,-29834112⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099571359268,0,true,59729856,59729920⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099451896284,0,false,-59733120,-59733056⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624531,0,false,-3264,-3200⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626967,0,false,-832,-768⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1330472105636,0,true,209641396480,209641396544⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨868551149916,0,false,-259259241984,-259259241920⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1330728870162,0,true,209853568064,209853568128⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨868294385390,0,false,-259584332032,-259584331968⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1050888755742,0,false,-49730763904,-49730763840⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1050996686246,0,false,-49617845440,-49617845376⟩
    { al := (86061/409600), au := (861459/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨231018237788,231246139491⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209689128704,209689128768⟩ : DyadicInterval 40),(⟨-259332363584,-259332363520⟩ : DyadicInterval 40),(⟨737671980181,737671999511⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209877443968,209877444032⟩ : DyadicInterval 40),(⟨-259620924736,-259620924672⟩ : DyadicInterval 40),(⟨737623347177,737623366506⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209593671104,209593671168⟩ : DyadicInterval 40),(⟨-259186138880,-259186138816⟩ : DyadicInterval 40),(⟨737696610363,737696629692⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209829677312,209829677376⟩ : DyadicInterval 40),(⟨-259547718592,-259547718528⟩ : DyadicInterval 40),(⟨737635688523,737635707852⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨29833710,59731492⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29833280,29833344⟩ : DyadicInterval 40),(⟨-29834176,-29834112⟩ : DyadicInterval 40),(⟨762123383190,762123402519⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59729856,59729920⟩ : DyadicInterval 40),(⟨-59733120,-59733056⟩ : DyadicInterval 40),(⟨762123381938,762123401268⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3264,-768⟩ : DyadicInterval 40),(⟨762123384000,762123404512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨230960477860,231217242386⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209641396480,209641396544⟩ : DyadicInterval 40),(⟨-259259241984,-259259241920⟩ : DyadicInterval 40),(⟨737684298009,737684317339⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209853568064,209853568128⟩ : DyadicInterval 40),(⟨-259584332032,-259584331968⟩ : DyadicInterval 40),(⟨737629516397,737629535726⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-49730763904,-49617845376⟩ : DyadicInterval 40),(⟨786932306304,786988784832⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨209689128704,209877444032⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-259620924736,-259332363520⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1353_ok : ecellOkT e1353 = true := by decide +kernel
theorem e1353_pos {a z : ℝ} (ha1 : ((86061/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((861459/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1353 e1353_ok ha1 ha2 hz1 hz2 hz

-- box ['861459/4096000', '215577/1024000', '1999/2000', '3999/4000']  interval_lower 380945477/549755813888
noncomputable def e1354 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1330757767266,0,true,209877443968,209877444032⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨868265488286,0,false,-259620924736,-259620924672⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1330985668969,0,true,210065727040,210065727104⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨868037586583,0,false,-259909561600,-259909561536⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1330642144196,0,true,209781908608,209781908672⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨868381111356,0,false,-259474517376,-259474517312⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1330927800459,0,true,210017921472,210017921536⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨868095455093,0,false,-259836264128,-259836264064⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541492886,0,true,29864704,29864768⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099481762666,0,false,-29865536,-29865472⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099571422082,0,true,59792640,59792704⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099451833470,0,false,-59795968,-59795904⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624524,0,false,-3264,-3200⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626965,0,false,-832,-768⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1330699950360,0,true,209829672896,209829672960⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨868323305192,0,false,-259547711808,-259547711744⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1330956743382,0,true,210041831680,210041831744⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨868066512170,0,false,-259872923264,-259872923200⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1050792869206,0,false,-49831091584,-49831091520⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1050900918122,0,false,-49718038912,-49718038848⟩
    { al := (861459/4096000), au := (215577/1024000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨231246139490,231474041193⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209877443968,209877444032⟩ : DyadicInterval 40),(⟨-259620924736,-259620924672⟩ : DyadicInterval 40),(⟨737623347177,737623366506⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210065727040,210065727104⟩ : DyadicInterval 40),(⟨-259909561600,-259909561536⟩ : DyadicInterval 40),(⟨737574664699,737574684028⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209781908608,209781908672⟩ : DyadicInterval 40),(⟨-259474517376,-259474517312⟩ : DyadicInterval 40),(⟨737648026694,737648046024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210017921472,210017921536⟩ : DyadicInterval 40),(⟨-259836264128,-259836264064⟩ : DyadicInterval 40),(⟨737587030792,737587050122⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨29865110,59794306⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29864704,29864768⟩ : DyadicInterval 40),(⟨-29865536,-29865472⟩ : DyadicInterval 40),(⟨762123383156,762123402485⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59792640,59792704⟩ : DyadicInterval 40),(⟨-59795968,-59795904⟩ : DyadicInterval 40),(⟨762123381964,762123401293⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3264,-768⟩ : DyadicInterval 40),(⟨762123384000,762123404512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨231188322584,231445115606⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209829672896,209829672960⟩ : DyadicInterval 40),(⟨-259547711808,-259547711744⟩ : DyadicInterval 40),(⟨737635689663,737635708993⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210041831680,210041831744⟩ : DyadicInterval 40),(⟨-259872923264,-259872923200⟩ : DyadicInterval 40),(⟨737580846302,737580865631⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-49831091584,-49718038848⟩ : DyadicInterval 40),(⟨786982403040,787038948672⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨209877443968,210065727104⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-259909561600,-259620924672⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1354_ok : ecellOkT e1354 = true := by decide +kernel
theorem e1354_pos {a z : ℝ} (ha1 : ((861459/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((215577/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1354 e1354_ok ha1 ha2 hz1 hz2 hz

-- box ['86061/409600', '861459/4096000', '3999/4000', '1']  interval_lower 377551523/549755813888
noncomputable def e1355 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1330529865564,0,true,209689128704,209689128768⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨868493389988,0,false,-259332363584,-259332363520⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1330757767267,0,true,209877443968,209877444032⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨868265488285,0,false,-259620924736,-259620924672⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1330472111004,0,true,209641400960,209641401024⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨868551144548,0,false,-259259248768,-259259248704⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541493901,0,true,29865664,29865728⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099481761651,0,false,-29866560,-29866496⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626964,0,false,-832,-768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1330500982571,0,true,209665260352,209665260416⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨868522272981,0,false,-259295798336,-259295798272⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1330757775811,0,true,209877451008,209877451072⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨868265479741,0,false,-259620935552,-259620935488⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1050876597795,0,false,-49743484480,-49743484416⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1050984553864,0,false,-49630537984,-49630537920⟩
    { al := (86061/409600), au := (861459/4096000), zl := (3999/4000), zu := 1,
      A := ⟨231018237788,231246139491⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209689128704,209689128768⟩ : DyadicInterval 40),(⟨-259332363584,-259332363520⟩ : DyadicInterval 40),(⟨737671980181,737671999511⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209877443968,209877444032⟩ : DyadicInterval 40),(⟨-259620924736,-259620924672⟩ : DyadicInterval 40),(⟨737623347177,737623366506⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209641400960,209641401024⟩ : DyadicInterval 40),(⟨-259259248768,-259259248704⟩ : DyadicInterval 40),(⟨737684296833,737684316163⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209877443968,209877444032⟩ : DyadicInterval 40),(⟨-259620924736,-259620924672⟩ : DyadicInterval 40),(⟨737623347177,737623366506⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,29866125⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29865664,29865728⟩ : DyadicInterval 40),(⟨-29866560,-29866496⟩ : DyadicInterval 40),(⟨762123383188,762123402517⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-832,0⟩ : DyadicInterval 40),(⟨762123383616,762123403296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨230989354795,231246148035⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209665260352,209665260416⟩ : DyadicInterval 40),(⟨-259295798336,-259295798272⟩ : DyadicInterval 40),(⟨737678140133,737678159463⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209877451008,209877451072⟩ : DyadicInterval 40),(⟨-259620935552,-259620935488⟩ : DyadicInterval 40),(⟨737623345363,737623364692⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-49743484480,-49630537920⟩ : DyadicInterval 40),(⟨786938652576,786995145120⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨209689128704,209877444032⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-259620924736,-259332363520⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1355_ok : ecellOkT e1355 = true := by decide +kernel
theorem e1355_pos {a z : ℝ} (ha1 : ((86061/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((861459/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1355 e1355_ok ha1 ha2 hz1 hz2 hz

-- box ['861459/4096000', '215577/1024000', '3999/4000', '1']  interval_lower 760835127/1099511627776
noncomputable def e1356 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1330757767266,0,true,209877443968,209877444032⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨868265488286,0,false,-259620924736,-259620924672⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1330985668969,0,true,210065727040,210065727104⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨868037586583,0,false,-259909561600,-259909561536⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1330699955731,0,true,209829677312,209829677376⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨868323299821,0,false,-259547718592,-259547718528⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541525309,0,true,29897088,29897152⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099481730243,0,false,-29897984,-29897920⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626963,0,false,-832,-768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1330728855775,0,true,209853556160,209853556224⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨868294399777,0,false,-259584313792,-259584313728⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1330985677524,0,true,210065734080,210065734144⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨868037578028,0,false,-259909572480,-259909572416⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1050780687280,0,false,-49843838336,-49843838272⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1050888761794,0,false,-49730757632,-49730757568⟩
    { al := (861459/4096000), au := (215577/1024000), zl := (3999/4000), zu := 1,
      A := ⟨231246139490,231474041193⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209877443968,209877444032⟩ : DyadicInterval 40),(⟨-259620924736,-259620924672⟩ : DyadicInterval 40),(⟨737623347177,737623366506⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210065727040,210065727104⟩ : DyadicInterval 40),(⟨-259909561600,-259909561536⟩ : DyadicInterval 40),(⟨737574664699,737574684028⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209829677312,209829677376⟩ : DyadicInterval 40),(⟨-259547718592,-259547718528⟩ : DyadicInterval 40),(⟨737635688523,737635707853⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210065727040,210065727104⟩ : DyadicInterval 40),(⟨-259909561600,-259909561536⟩ : DyadicInterval 40),(⟨737574664699,737574684028⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,29897533⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29897088,29897152⟩ : DyadicInterval 40),(⟨-29897984,-29897920⟩ : DyadicInterval 40),(⟨762123383187,762123402516⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-832,0⟩ : DyadicInterval 40),(⟨762123383616,762123403296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨231217227999,231474049748⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209853556160,209853556224⟩ : DyadicInterval 40),(⟨-259584313792,-259584313728⟩ : DyadicInterval 40),(⟨737629519470,737629538799⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210065734080,210065734144⟩ : DyadicInterval 40),(⟨-259909572480,-259909572416⟩ : DyadicInterval 40),(⟨737574662904,737574682233⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-49843838336,-49730757568⟩ : DyadicInterval 40),(⟨786988762400,787045322048⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨209877443968,210065727104⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-259909561600,-259620924672⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1356_ok : ecellOkT e1356 = true := by decide +kernel
theorem e1356_pos {a z : ℝ} (ha1 : ((861459/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((215577/1024000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1356 e1356_ok ha1 ha2 hz1 hz2 hz

-- box ['215577/1024000', '863157/4096000', '999/1000', '3997/4000']  interval_lower 192441293/274877906944
noncomputable def e1357 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1330985668968,0,true,210065727040,210065727104⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨868037586584,0,false,-259909561600,-259909561536⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1331213570671,0,true,210253977792,210253977856⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨867809684881,0,false,-260198274304,-260198274240⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1330754194926,0,true,209874492416,209874492480⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨868269060626,0,false,-259616400960,-259616400896⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1331039794215,0,true,210110438336,210110438400⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨867983461337,0,false,-259978122240,-259978122176⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099601316334,0,true,89684864,89684928⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099421939218,0,false,-89692224,-89692160⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099631339769,0,true,119705472,119705536⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099391915783,0,false,-119718528,-119718464⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511614742,0,false,-13056,-12992⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620460,0,false,-7360,-7296⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1330869927986,0,true,209970110592,209970110656⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨868153327566,0,false,-259762966528,-259762966464⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1331126692047,0,true,210182218368,210182218432⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨867896563505,0,false,-260088204928,-260088204864⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1050721295193,0,false,-49905986560,-49905986496⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1050829411305,0,false,-49792855872,-49792855808⟩
    { al := (215577/1024000), au := (863157/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨231474041192,231701942895⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210065727040,210065727104⟩ : DyadicInterval 40),(⟨-259909561600,-259909561536⟩ : DyadicInterval 40),(⟨737574664699,737574684029⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210253977792,210253977856⟩ : DyadicInterval 40),(⟨-260198274304,-260198274240⟩ : DyadicInterval 40),(⟨737525932862,737525952191⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209874492416,209874492480⟩ : DyadicInterval 40),(⟨-259616400960,-259616400896⟩ : DyadicInterval 40),(⟨737624109853,737624129183⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210110438336,210110438400⟩ : DyadicInterval 40),(⟨-259978122240,-259978122176⟩ : DyadicInterval 40),(⟨737563095680,737563115010⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨89688558,119711993⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨89684864,89684928⟩ : DyadicInterval 40),(⟨-89692224,-89692160⟩ : DyadicInterval 40),(⟨762123379915,762123399245⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨119705472,119705536⟩ : DyadicInterval 40),(⟨-119718528,-119718464⟩ : DyadicInterval 40),(⟨762123377045,762123396375⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-13056,-7296⟩ : DyadicInterval 40),(⟨762123387264,762123409408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨231358300210,231615064271⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209970110592,209970110656⟩ : DyadicInterval 40),(⟨-259762966528,-259762966464⟩ : DyadicInterval 40),(⟨737599394523,737599413852⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210182218368,210182218432⟩ : DyadicInterval 40),(⟨-260088204928,-260088204864⟩ : DyadicInterval 40),(⟨737544515792,737544535121⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-49905986560,-49792855808⟩ : DyadicInterval 40),(⟨787019811520,787076396160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨210065727040,210253977856⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-260198274304,-259909561536⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1357_ok : ecellOkT e1357 = true := by decide +kernel
theorem e1357_pos {a z : ℝ} (ha1 : ((215577/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((863157/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1357 e1357_ok ha1 ha2 hz1 hz2 hz

-- box ['863157/4096000', '432003/2048000', '999/1000', '3997/4000']  interval_lower 775552195/1099511627776
noncomputable def e1358 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1331213570670,0,true,210253977792,210253977856⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨867809684882,0,false,-260198274304,-260198274240⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1331441472373,0,true,210442196416,210442196480⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨867581783179,0,false,-260487062848,-260487062784⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1330981868727,0,true,210062587648,210062587712⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨868041386825,0,false,-259904748032,-259904747968⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1331267524990,0,true,210298540288,210298540352⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨867755730562,0,false,-260266636352,-260266636288⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099601410564,0,true,89779072,89779136⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099421844988,0,false,-89786496,-89786432⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099631465437,0,true,119831104,119831168⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099391790115,0,false,-119844224,-119844160⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511614714,0,false,-13120,-13056⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620445,0,false,-7360,-7296⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1331097715727,0,true,210158283648,210158283712⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨867925539825,0,false,-260051496320,-260051496256⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1331354508291,0,true,210370378624,210370378688⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨867668747261,0,false,-260376856256,-260376856192⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1050625267788,0,false,-50006477632,-50006477568⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1050733502309,0,false,-49893212672,-49893212608⟩
    { al := (863157/4096000), au := (432003/2048000), zl := (999/1000), zu := (3997/4000),
      A := ⟨231701942894,231929844597⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210253977792,210253977856⟩ : DyadicInterval 40),(⟨-260198274304,-260198274240⟩ : DyadicInterval 40),(⟨737525932862,737525952191⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210442196416,210442196480⟩ : DyadicInterval 40),(⟨-260487062848,-260487062784⟩ : DyadicInterval 40),(⟨737477151536,737477170865⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210062587648,210062587712⟩ : DyadicInterval 40),(⟨-259904748032,-259904747968⟩ : DyadicInterval 40),(⟨737575476931,737575496261⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210298540288,210298540352⟩ : DyadicInterval 40),(⟨-260266636352,-260266636288⟩ : DyadicInterval 40),(⟨737514388657,737514407986⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨89782788,119837661⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨89779072,89779136⟩ : DyadicInterval 40),(⟨-89786496,-89786432⟩ : DyadicInterval 40),(⟨762123379932,762123399261⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨119831104,119831168⟩ : DyadicInterval 40),(⟨-119844224,-119844160⟩ : DyadicInterval 40),(⟨762123377050,762123396379⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-13120,-7296⟩ : DyadicInterval 40),(⟨762123387264,762123409440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨231586087951,231842880515⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210158283648,210158283712⟩ : DyadicInterval 40),(⟨-260051496320,-260051496256⟩ : DyadicInterval 40),(⟨737550712097,737550731426⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210370378624,210370378688⟩ : DyadicInterval 40),(⟨-260376856256,-260376856192⟩ : DyadicInterval 40),(⟨737495771646,737495790975⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-50006477632,-49893212608⟩ : DyadicInterval 40),(⟨787069989920,787126641696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨210253977792,210442196480⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-260487062848,-260198274240⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1358_ok : ecellOkT e1358 = true := by decide +kernel
theorem e1358_pos {a z : ℝ} (ha1 : ((863157/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((432003/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1358 e1358_ok ha1 ha2 hz1 hz2 hz

-- box ['215577/1024000', '863157/4096000', '3997/4000', '1999/2000']  interval_lower 768707409/1099511627776
noncomputable def e1359 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1330985668968,0,true,210065727040,210065727104⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨868037586584,0,false,-259909561600,-259909561536⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1331213570671,0,true,210253977792,210253977856⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨867809684881,0,false,-260198274304,-260198274240⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1330812063437,0,true,209922304192,209922304256⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨868211192115,0,false,-259689683776,-259689683712⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1331097719700,0,true,210158286912,210158286976⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨867925535852,0,false,-260051501376,-260051501312⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099571420563,0,true,59791104,59791168⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099451834989,0,false,-59794432,-59794368⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099601412589,0,true,89781120,89781184⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099421842963,0,false,-89788480,-89788416⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620444,0,false,-7360,-7296⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624525,0,false,-3264,-3200⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1330898861422,0,true,209994013952,209994014016⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨868124394130,0,false,-259799611136,-259799611072⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1331155654202,0,true,210206140864,210206140928⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨867867601350,0,false,-260124896832,-260124896768⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1050709092520,0,false,-49918755968,-49918755904⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1050817234246,0,false,-49805597184,-49805597120⟩
    { al := (215577/1024000), au := (863157/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨231474041192,231701942895⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210065727040,210065727104⟩ : DyadicInterval 40),(⟨-259909561600,-259909561536⟩ : DyadicInterval 40),(⟨737574664699,737574684029⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210253977792,210253977856⟩ : DyadicInterval 40),(⟨-260198274304,-260198274240⟩ : DyadicInterval 40),(⟨737525932862,737525952191⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209922304192,209922304256⟩ : DyadicInterval 40),(⟨-259689683776,-259689683712⟩ : DyadicInterval 40),(⟨737611753337,737611772667⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210158286912,210158286976⟩ : DyadicInterval 40),(⟨-260051501376,-260051501312⟩ : DyadicInterval 40),(⟨737550711267,737550730597⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨59792787,89784813⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59791104,59791168⟩ : DyadicInterval 40),(⟨-59794432,-59794368⟩ : DyadicInterval 40),(⟨762123381964,762123401293⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨89781120,89781184⟩ : DyadicInterval 40),(⟨-89788480,-89788416⟩ : DyadicInterval 40),(⟨762123379899,762123399229⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7360,-3200⟩ : DyadicInterval 40),(⟨762123385216,762123406560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨231387233646,231644026426⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209994013952,209994014016⟩ : DyadicInterval 40),(⟨-259799611136,-259799611072⟩ : DyadicInterval 40),(⟨737593213656,737593232986⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210206140864,210206140928⟩ : DyadicInterval 40),(⟨-260124896832,-260124896768⟩ : DyadicInterval 40),(⟨737538321725,737538341055⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-49918755968,-49805597120⟩ : DyadicInterval 40),(⟨787026182176,787082780864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨210065727040,210253977856⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-260198274304,-259909561536⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1359_ok : ecellOkT e1359 = true := by decide +kernel
theorem e1359_pos {a z : ℝ} (ha1 : ((215577/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((863157/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1359 e1359_ok ha1 ha2 hz1 hz2 hz

-- box ['863157/4096000', '432003/2048000', '3997/4000', '1999/2000']  interval_lower 387245217/549755813888
noncomputable def e1360 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1331213570670,0,true,210253977792,210253977856⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨867809684882,0,false,-260198274304,-260198274240⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1331441472373,0,true,210442196416,210442196480⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨867581783179,0,false,-260487062848,-260487062784⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1331039794212,0,true,210110438336,210110438400⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨867983461340,0,false,-259978122240,-259978122176⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1331325507451,0,true,210346427776,210346427840⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨867697748101,0,false,-260340106944,-260340106880⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099571483385,0,true,59853952,59854016⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099451772167,0,false,-59857280,-59857216⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099601506842,0,true,89875392,89875456⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099421748710,0,false,-89882752,-89882688⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620428,0,false,-7360,-7296⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624518,0,false,-3264,-3200⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1331126677651,0,true,210182206464,210182206528⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨867896577901,0,false,-260088186688,-260088186624⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1331383498935,0,true,210394320576,210394320640⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨867639756617,0,false,-260413593856,-260413593792⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1050613041097,0,false,-50019273280,-50019273216⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1050721301259,0,false,-49905980224,-49905980160⟩
    { al := (863157/4096000), au := (432003/2048000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨231701942894,231929844597⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210253977792,210253977856⟩ : DyadicInterval 40),(⟨-260198274304,-260198274240⟩ : DyadicInterval 40),(⟨737525932862,737525952191⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210442196416,210442196480⟩ : DyadicInterval 40),(⟨-260487062848,-260487062784⟩ : DyadicInterval 40),(⟨737477151536,737477170865⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210110438336,210110438400⟩ : DyadicInterval 40),(⟨-259978122240,-259978122176⟩ : DyadicInterval 40),(⟨737563095681,737563115010⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210346427776,210346427840⟩ : DyadicInterval 40),(⟨-260340106944,-260340106880⟩ : DyadicInterval 40),(⟨737501979468,737501998798⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨59855609,89879066⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59853952,59854016⟩ : DyadicInterval 40),(⟨-59857280,-59857216⟩ : DyadicInterval 40),(⟨762123381957,762123401286⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨89875392,89875456⟩ : DyadicInterval 40),(⟨-89882752,-89882688⟩ : DyadicInterval 40),(⟨762123379884,762123399214⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7360,-3200⟩ : DyadicInterval 40),(⟨762123385216,762123406560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨231615049875,231871871159⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210182206464,210182206528⟩ : DyadicInterval 40),(⟨-260088186688,-260088186624⟩ : DyadicInterval 40),(⟨737544518877,737544538207⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210394320576,210394320640⟩ : DyadicInterval 40),(⟨-260413593856,-260413593792⟩ : DyadicInterval 40),(⟨737489565171,737489584501⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-50019273280,-49905980160⟩ : DyadicInterval 40),(⟨787076373696,787133039520⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨210253977792,210442196480⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-260487062848,-260198274240⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1360_ok : ecellOkT e1360 = true := by decide +kernel
theorem e1360_pos {a z : ℝ} (ha1 : ((863157/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((432003/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1360 e1360_ok ha1 ha2 hz1 hz2 hz

-- box ['432003/2048000', '172971/819200', '999/1000', '3997/4000']  interval_lower 781360777/1099511627776
noncomputable def e1361 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1331441472372,0,true,210442196416,210442196480⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨867581783180,0,false,-260487062848,-260487062784⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1331669374075,0,true,210630382784,210630382848⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨867353881477,0,false,-260775927232,-260775927168⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1331209542527,0,true,210250650752,210250650816⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨867813713025,0,false,-260193170688,-260193170624⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1331495255766,0,true,210486610112,210486610176⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨867527999786,0,false,-260555226240,-260555226176⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099601504814,0,true,89873344,89873408⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099421750738,0,false,-89880768,-89880704⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099631591130,0,true,119956800,119956864⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099391664422,0,false,-119969920,-119969856⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511614687,0,false,-13120,-13056⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620430,0,false,-7360,-7296⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1331325503483,0,true,210346424448,210346424512⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨867697752069,0,false,-260340101952,-260340101888⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1331582324534,0,true,210558506752,210558506816⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨867440931018,0,false,-260665583360,-260665583296⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1050529145978,0,false,-50107076608,-50107076544⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1050637498924,0,false,-49993677440,-49993677376⟩
    { al := (432003/2048000), au := (172971/819200), zl := (999/1000), zu := (3997/4000),
      A := ⟨231929844596,232157746299⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210442196416,210442196480⟩ : DyadicInterval 40),(⟨-260487062848,-260487062784⟩ : DyadicInterval 40),(⟨737477151536,737477170865⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210630382784,210630382848⟩ : DyadicInterval 40),(⟨-260775927232,-260775927168⟩ : DyadicInterval 40),(⟨737428320784,737428340114⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210250650752,210250650816⟩ : DyadicInterval 40),(⟨-260193170688,-260193170624⟩ : DyadicInterval 40),(⟨737526794630,737526813960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210486610112,210486610176⟩ : DyadicInterval 40),(⟨-260555226240,-260555226176⟩ : DyadicInterval 40),(⟨737465632263,737465651593⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨89877038,119963354⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨89873344,89873408⟩ : DyadicInterval 40),(⟨-89880768,-89880704⟩ : DyadicInterval 40),(⟨762123379916,762123399246⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨119956800,119956864⟩ : DyadicInterval 40),(⟨-119969920,-119969856⟩ : DyadicInterval 40),(⟨762123377022,762123396352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-13120,-7296⟩ : DyadicInterval 40),(⟨762123387264,762123409440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨231813875707,232070696758⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210346424448,210346424512⟩ : DyadicInterval 40),(⟨-260340101952,-260340101888⟩ : DyadicInterval 40),(⟨737501980362,737501999692⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210558506752,210558506816⟩ : DyadicInterval 40),(⟨-260665583360,-260665583296⟩ : DyadicInterval 40),(⟨737446978052,737446997381⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-50107076608,-49993677376⟩ : DyadicInterval 40),(⟨787120222304,787176941184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨210442196416,210630382848⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-260775927232,-260487062784⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1361_ok : ecellOkT e1361 = true := by decide +kernel
theorem e1361_pos {a z : ℝ} (ha1 : ((432003/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((172971/819200 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1361 e1361_ok ha1 ha2 hz1 hz2 hz

-- box ['172971/819200', '108213/512000', '999/1000', '3997/4000']  interval_lower 787191369/1099511627776
noncomputable def e1362 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1331669374074,0,true,210630382784,210630382848⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨867353881478,0,false,-260775927232,-260775927168⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1331897275778,0,true,210818536896,210818536960⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨867125979774,0,false,-261064867584,-261064867520⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1331437216327,0,true,210438681728,210438681792⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨867586039225,0,false,-260481669056,-260481668992⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1331722986543,0,true,210674647744,210674647808⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨867300269009,0,false,-260843891840,-260843891776⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099601599080,0,true,89967616,89967680⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099421656472,0,false,-89975040,-89974976⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099631716848,0,true,120082496,120082560⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099391538704,0,false,-120095680,-120095616⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511614659,0,false,-13120,-13056⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620414,0,false,-7424,-7360⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1331553291238,0,true,210534533120,210534533184⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨867469964314,0,false,-260628783296,-260628783232⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1331810140772,0,true,210746602624,210746602688⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨867213114780,0,false,-260954386368,-260954386304⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1050432929764,0,false,-50207783680,-50207783616⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1050541401158,0,false,-50094250112,-50094250048⟩
    { al := (172971/819200), au := (108213/512000), zl := (999/1000), zu := (3997/4000),
      A := ⟨232157746298,232385648002⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210630382784,210630382848⟩ : DyadicInterval 40),(⟨-260775927232,-260775927168⟩ : DyadicInterval 40),(⟨737428320784,737428340114⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210818536896,210818536960⟩ : DyadicInterval 40),(⟨-261064867584,-261064867520⟩ : DyadicInterval 40),(⟨737379440644,737379459973⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210438681728,210438681792⟩ : DyadicInterval 40),(⟨-260481669056,-260481668992⟩ : DyadicInterval 40),(⟨737478062987,737478082317⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210674647744,210674647808⟩ : DyadicInterval 40),(⟨-260843891840,-260843891776⟩ : DyadicInterval 40),(⟨737416826500,737416845830⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨89971304,120089072⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨89967616,89967680⟩ : DyadicInterval 40),(⟨-89975040,-89974976⟩ : DyadicInterval 40),(⟨762123379901,762123399231⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨120082496,120082560⟩ : DyadicInterval 40),(⟨-120095680,-120095616⟩ : DyadicInterval 40),(⟨762123377027,762123396357⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-13120,-7360⟩ : DyadicInterval 40),(⟨762123387296,762123409440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨232041663462,232298512996⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210534533120,210534533184⟩ : DyadicInterval 40),(⟨-260628783296,-260628783232⟩ : DyadicInterval 40),(⟨737453199181,737453218510⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210746602624,210746602688⟩ : DyadicInterval 40),(⟨-260954386368,-260954386304⟩ : DyadicInterval 40),(⟨737398135124,737398154454⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-50207783680,-50094250048⟩ : DyadicInterval 40),(⟨787170508640,787227294720⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨210630382784,210818536960⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-261064867584,-260775927168⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1362_ok : ecellOkT e1362 = true := by decide +kernel
theorem e1362_pos {a z : ℝ} (ha1 : ((172971/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((108213/512000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1362 e1362_ok ha1 ha2 hz1 hz2 hz

-- box ['432003/2048000', '172971/819200', '3997/4000', '1999/2000']  interval_lower 780295059/1099511627776
noncomputable def e1363 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1331441472372,0,true,210442196416,210442196480⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨867581783180,0,false,-260487062848,-260487062784⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1331669374075,0,true,210630382784,210630382848⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨867353881477,0,false,-260775927232,-260775927168⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1331267524988,0,true,210298540288,210298540352⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨867755730564,0,false,-260266636352,-260266636288⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1331553295203,0,true,210534536448,210534536512⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨867469960349,0,false,-260628788288,-260628788224⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099571546220,0,true,59916800,59916864⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099451709332,0,false,-59920128,-59920064⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099601601115,0,true,89969600,89969664⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099421654437,0,false,-89977024,-89976960⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620413,0,false,-7424,-7360⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624511,0,false,-3328,-3264⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1331354493890,0,true,210370366720,210370366784⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨867668761662,0,false,-260376838016,-260376837952⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1331611343667,0,true,210582468096,210582468160⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨867411911885,0,false,-260702366784,-260702366720⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1050516895245,0,false,-50119898624,-50119898560⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1050625273863,0,false,-50006471232,-50006471168⟩
    { al := (432003/2048000), au := (172971/819200), zl := (3997/4000), zu := (1999/2000),
      A := ⟨231929844596,232157746299⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210442196416,210442196480⟩ : DyadicInterval 40),(⟨-260487062848,-260487062784⟩ : DyadicInterval 40),(⟨737477151536,737477170865⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210630382784,210630382848⟩ : DyadicInterval 40),(⟨-260775927232,-260775927168⟩ : DyadicInterval 40),(⟨737428320784,737428340114⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210298540288,210298540352⟩ : DyadicInterval 40),(⟨-260266636352,-260266636288⟩ : DyadicInterval 40),(⟨737514388657,737514407986⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210534536448,210534536512⟩ : DyadicInterval 40),(⟨-260628788288,-260628788224⟩ : DyadicInterval 40),(⟨737453198285,737453217615⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨59918444,89973339⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59916800,59916864⟩ : DyadicInterval 40),(⟨-59920128,-59920064⟩ : DyadicInterval 40),(⟨762123381950,762123401279⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨89969600,89969664⟩ : DyadicInterval 40),(⟨-89977024,-89976960⟩ : DyadicInterval 40),(⟨762123379901,762123399230⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7424,-3264⟩ : DyadicInterval 40),(⟨762123385248,762123406592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨231842866114,232099715891⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210370366720,210370366784⟩ : DyadicInterval 40),(⟨-260376838016,-260376837952⟩ : DyadicInterval 40),(⟨737495774739,737495794068⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210582468096,210582468160⟩ : DyadicInterval 40),(⟨-260702366784,-260702366720⟩ : DyadicInterval 40),(⟨737440759231,737440778560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-50119898624,-50006471168⟩ : DyadicInterval 40),(⟨787126619200,787183352192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨210442196416,210630382848⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-260775927232,-260487062784⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1363_ok : ecellOkT e1363 = true := by decide +kernel
theorem e1363_pos {a z : ℝ} (ha1 : ((432003/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((172971/819200 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1363 e1363_ok ha1 ha2 hz1 hz2 hz

-- box ['172971/819200', '108213/512000', '3997/4000', '1999/2000']  interval_lower 49132603/68719476736
noncomputable def e1364 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1331669374074,0,true,210630382784,210630382848⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨867353881478,0,false,-260775927232,-260775927168⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1331897275778,0,true,210818536896,210818536960⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨867125979774,0,false,-261064867584,-261064867520⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1331495255764,0,true,210486610112,210486610176⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨867527999788,0,false,-260555226240,-260555226176⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1331781082955,0,true,210722612928,210722612992⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨867242172597,0,false,-260917545472,-260917545408⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099571609065,0,true,59979648,59979712⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099451646487,0,false,-59982976,-59982912⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099601695405,0,true,90063936,90064000⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099421560147,0,false,-90071360,-90071296⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620398,0,false,-7424,-7360⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624504,0,false,-3328,-3264⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1331582310128,0,true,210558494848,210558494912⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨867440945424,0,false,-260665565120,-260665565056⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1331839188389,0,true,210770583424,210770583488⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨867184067163,0,false,-260991215488,-260991215424⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1050420654968,0,false,-50220632064,-50220632000⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1050529152060,0,false,-50107070272,-50107070208⟩
    { al := (172971/819200), au := (108213/512000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨232157746298,232385648002⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210630382784,210630382848⟩ : DyadicInterval 40),(⟨-260775927232,-260775927168⟩ : DyadicInterval 40),(⟨737428320784,737428340114⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210818536896,210818536960⟩ : DyadicInterval 40),(⟨-261064867584,-261064867520⟩ : DyadicInterval 40),(⟨737379440644,737379459973⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210486610112,210486610176⟩ : DyadicInterval 40),(⟨-260555226240,-260555226176⟩ : DyadicInterval 40),(⟨737465632264,737465651593⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210722612928,210722612992⟩ : DyadicInterval 40),(⟨-260917545472,-260917545408⟩ : DyadicInterval 40),(⟨737404367730,737404387060⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨59981289,90067629⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59979648,59979712⟩ : DyadicInterval 40),(⟨-59982976,-59982912⟩ : DyadicInterval 40),(⟨762123381943,762123401272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨90063936,90064000⟩ : DyadicInterval 40),(⟨-90071360,-90071296⟩ : DyadicInterval 40),(⟨762123379885,762123399215⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7424,-3264⟩ : DyadicInterval 40),(⟨762123385248,762123406592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨232070682352,232327560613⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210558494848,210558494912⟩ : DyadicInterval 40),(⟨-260665565120,-260665565056⟩ : DyadicInterval 40),(⟨737446981152,737447000482⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210770583424,210770583488⟩ : DyadicInterval 40),(⟨-260991215488,-260991215424⟩ : DyadicInterval 40),(⟨737391903843,737391923173⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-50220632064,-50107070208⟩ : DyadicInterval 40),(⟨787176918720,787233718912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨210630382784,210818536960⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-261064867584,-260775927168⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1364_ok : ecellOkT e1364 = true := by decide +kernel
theorem e1364_pos {a z : ℝ} (ha1 : ((172971/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((108213/512000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1364 e1364_ok ha1 ha2 hz1 hz2 hz

-- box ['215577/1024000', '863157/4096000', '1999/2000', '3999/4000']  interval_lower 191912175/274877906944
noncomputable def e1365 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1330985668968,0,true,210065727040,210065727104⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨868037586584,0,false,-259909561600,-259909561536⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1331213570671,0,true,210253977792,210253977856⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨867809684881,0,false,-260198274304,-260198274240⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1330869931947,0,true,209970113856,209970113920⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨868153323605,0,false,-259762971520,-259762971456⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1331155645186,0,true,210206133376,210206133440⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨867867610366,0,false,-260124885376,-260124885312⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541524292,0,true,29896064,29896128⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099481731260,0,false,-29896960,-29896896⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099571484906,0,true,59855488,59855552⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099451770646,0,false,-59858816,-59858752⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624517,0,false,-3264,-3200⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626964,0,false,-832,-768⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1330927795087,0,true,210017917056,210017917120⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨868095460465,0,false,-259836257344,-259836257280⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1331184616592,0,true,210230063040,210230063104⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨867838638960,0,false,-260161590208,-260161590144⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1050696888221,0,false,-49931527168,-49931527104⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1050805055567,0,false,-49818340288,-49818340224⟩
    { al := (215577/1024000), au := (863157/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨231474041192,231701942895⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210065727040,210065727104⟩ : DyadicInterval 40),(⟨-259909561600,-259909561536⟩ : DyadicInterval 40),(⟨737574664699,737574684029⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210253977792,210253977856⟩ : DyadicInterval 40),(⟨-260198274304,-260198274240⟩ : DyadicInterval 40),(⟨737525932862,737525952191⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨209970113856,209970113920⟩ : DyadicInterval 40),(⟨-259762971520,-259762971456⟩ : DyadicInterval 40),(⟨737599393672,737599413001⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210206133376,210206133440⟩ : DyadicInterval 40),(⟨-260124885376,-260124885312⟩ : DyadicInterval 40),(⟨737538323665,737538342995⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨29896516,59857130⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29896064,29896128⟩ : DyadicInterval 40),(⟨-29896960,-29896896⟩ : DyadicInterval 40),(⟨762123383187,762123402516⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59855488,59855552⟩ : DyadicInterval 40),(⟨-59858816,-59858752⟩ : DyadicInterval 40),(⟨762123381957,762123401286⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3264,-768⟩ : DyadicInterval 40),(⟨762123384000,762123404512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨231416167311,231672988816⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210017917056,210017917120⟩ : DyadicInterval 40),(⟨-259836257344,-259836257280⟩ : DyadicInterval 40),(⟨737587031935,737587051264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210230063040,210230063104⟩ : DyadicInterval 40),(⟨-260161590208,-260161590144⟩ : DyadicInterval 40),(⟨737532126787,737532146116⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-49931527168,-49818340224⟩ : DyadicInterval 40),(⟨787032553728,787089166464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨210065727040,210253977856⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-260198274304,-259909561536⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1365_ok : ecellOkT e1365 = true := by decide +kernel
theorem e1365_pos {a z : ℝ} (ha1 : ((215577/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((863157/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1365 e1365_ok ha1 ha2 hz1 hz2 hz

-- box ['863157/4096000', '432003/2048000', '1999/2000', '3999/4000']  interval_lower 773427687/1099511627776
noncomputable def e1366 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1331213570670,0,true,210253977792,210253977856⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨867809684882,0,false,-260198274304,-260198274240⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1331441472373,0,true,210442196416,210442196480⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨867581783179,0,false,-260487062848,-260487062784⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1331097719698,0,true,210158286912,210158286976⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨867925535854,0,false,-260051501376,-260051501312⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1331383489913,0,true,210394313088,210394313152⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨867639765639,0,false,-260413582464,-260413582400⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541555703,0,true,29927488,29927552⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099481699849,0,false,-29928384,-29928320⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099571547744,0,true,59918272,59918336⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099451707808,0,false,-59921664,-59921600⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624510,0,false,-3328,-3264⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626962,0,false,-832,-768⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1331155639806,0,true,210206128960,210206129024⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨867867615746,0,false,-260124878592,-260124878528⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1331412489807,0,true,210418262144,210418262208⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨867610765745,0,false,-260450332992,-260450332928⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1050600812781,0,false,-50032070784,-50032070720⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1050709098586,0,false,-49918749568,-49918749504⟩
    { al := (863157/4096000), au := (432003/2048000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨231701942894,231929844597⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210253977792,210253977856⟩ : DyadicInterval 40),(⟨-260198274304,-260198274240⟩ : DyadicInterval 40),(⟨737525932862,737525952191⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210442196416,210442196480⟩ : DyadicInterval 40),(⟨-260487062848,-260487062784⟩ : DyadicInterval 40),(⟨737477151536,737477170865⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210158286912,210158286976⟩ : DyadicInterval 40),(⟨-260051501376,-260051501312⟩ : DyadicInterval 40),(⟨737550711268,737550730597⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210394313088,210394313152⟩ : DyadicInterval 40),(⟨-260413582464,-260413582400⟩ : DyadicInterval 40),(⟨737489567141,737489586471⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨29927927,59919968⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29927488,29927552⟩ : DyadicInterval 40),(⟨-29928384,-29928320⟩ : DyadicInterval 40),(⟨762123383185,762123402514⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59918272,59918336⟩ : DyadicInterval 40),(⟨-59921664,-59921600⟩ : DyadicInterval 40),(⟨762123381982,762123401311⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3328,-768⟩ : DyadicInterval 40),(⟨762123384000,762123404544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨231644012030,231900862031⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210206128960,210206129024⟩ : DyadicInterval 40),(⟨-260124878592,-260124878528⟩ : DyadicInterval 40),(⟨737538324812,737538344141⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210418262144,210418262208⟩ : DyadicInterval 40),(⟨-260450332992,-260450332928⟩ : DyadicInterval 40),(⟨737483357885,737483377215⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-50032070784,-49918749504⟩ : DyadicInterval 40),(⟨787082758368,787139438272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨210253977792,210442196480⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-260487062848,-260198274240⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1366_ok : ecellOkT e1366 = true := by decide +kernel
theorem e1366_pos {a z : ℝ} (ha1 : ((863157/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((432003/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1366 e1366_ok ha1 ha2 hz1 hz2 hz

-- box ['215577/1024000', '863157/4096000', '3999/4000', '1']  interval_lower 191647207/274877906944
noncomputable def e1367 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1330985668968,0,true,210065727040,210065727104⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨868037586584,0,false,-259909561600,-259909561536⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1331213570671,0,true,210253977792,210253977856⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨867809684881,0,false,-260198274304,-260198274240⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1330927800457,0,true,210017921472,210017921536⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨868095455095,0,false,-259836264128,-259836264064⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541556721,0,true,29928512,29928576⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099481698831,0,false,-29929408,-29929344⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626961,0,false,-832,-768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1330956728990,0,true,210041819776,210041819840⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨868066526562,0,false,-259872905024,-259872904960⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1331213579216,0,true,210253984896,210253984960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨867809676336,0,false,-260198285184,-260198285120⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1050684682298,0,false,-49944300224,-49944300160⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1050792875266,0,false,-49831085184,-49831085120⟩
    { al := (215577/1024000), au := (863157/4096000), zl := (3999/4000), zu := 1,
      A := ⟨231474041192,231701942895⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210065727040,210065727104⟩ : DyadicInterval 40),(⟨-259909561600,-259909561536⟩ : DyadicInterval 40),(⟨737574664699,737574684029⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210253977792,210253977856⟩ : DyadicInterval 40),(⟨-260198274304,-260198274240⟩ : DyadicInterval 40),(⟨737525932862,737525952191⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210017921472,210017921536⟩ : DyadicInterval 40),(⟨-259836264128,-259836264064⟩ : DyadicInterval 40),(⟨737587030793,737587050122⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210253977792,210253977856⟩ : DyadicInterval 40),(⟨-260198274304,-260198274240⟩ : DyadicInterval 40),(⟨737525932862,737525952191⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,29928945⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29928512,29928576⟩ : DyadicInterval 40),(⟨-29929408,-29929344⟩ : DyadicInterval 40),(⟨762123383185,762123402514⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-832,0⟩ : DyadicInterval 40),(⟨762123383616,762123403296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨231445101214,231701951440⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210041819776,210041819840⟩ : DyadicInterval 40),(⟨-259872905024,-259872904960⟩ : DyadicInterval 40),(⟨737580849382,737580868711⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210253984896,210253984960⟩ : DyadicInterval 40),(⟨-260198285184,-260198285120⟩ : DyadicInterval 40),(⟨737525931027,737525950356⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-49944300224,-49831085120⟩ : DyadicInterval 40),(⟨787038926176,787095552992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨210065727040,210253977856⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-260198274304,-259909561536⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1367_ok : ecellOkT e1367 = true := by decide +kernel
theorem e1367_pos {a z : ℝ} (ha1 : ((215577/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((863157/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1367 e1367_ok ha1 ha2 hz1 hz2 hz

-- box ['863157/4096000', '432003/2048000', '3999/4000', '1']  interval_lower 386182029/549755813888
noncomputable def e1368 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1331213570670,0,true,210253977792,210253977856⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨867809684882,0,false,-260198274304,-260198274240⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1331441472373,0,true,210442196416,210442196480⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨867581783179,0,false,-260487062848,-260487062784⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1331155645184,0,true,210206133376,210206133440⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨867867610368,0,false,-260124885376,-260124885312⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541588141,0,true,29959936,29960000⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099481667411,0,false,-29960832,-29960768⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626959,0,false,-832,-768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1331184602195,0,true,210230051136,210230051200⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨867838653357,0,false,-260161571968,-260161571904⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1331441480925,0,true,210442203456,210442203520⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨867581774627,0,false,-260487073664,-260487073600⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1050588582832,0,false,-50044870208,-50044870144⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1050696894289,0,false,-49931520832,-49931520768⟩
    { al := (863157/4096000), au := (432003/2048000), zl := (3999/4000), zu := 1,
      A := ⟨231701942894,231929844597⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210253977792,210253977856⟩ : DyadicInterval 40),(⟨-260198274304,-260198274240⟩ : DyadicInterval 40),(⟨737525932862,737525952191⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210442196416,210442196480⟩ : DyadicInterval 40),(⟨-260487062848,-260487062784⟩ : DyadicInterval 40),(⟨737477151536,737477170865⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210206133376,210206133440⟩ : DyadicInterval 40),(⟨-260124885376,-260124885312⟩ : DyadicInterval 40),(⟨737538323666,737538342995⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210442196416,210442196480⟩ : DyadicInterval 40),(⟨-260487062848,-260487062784⟩ : DyadicInterval 40),(⟨737477151536,737477170865⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,29960365⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29959936,29960000⟩ : DyadicInterval 40),(⟨-29960832,-29960768⟩ : DyadicInterval 40),(⟨762123383183,762123402512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-832,0⟩ : DyadicInterval 40),(⟨762123383616,762123403296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨231672974419,231929853149⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210230051136,210230051200⟩ : DyadicInterval 40),(⟨-260161571968,-260161571904⟩ : DyadicInterval 40),(⟨737532129874,737532149204⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210442203456,210442203520⟩ : DyadicInterval 40),(⟨-260487073664,-260487073600⟩ : DyadicInterval 40),(⟨737477149709,737477169038⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-50044870208,-49931520768⟩ : DyadicInterval 40),(⟨787089144000,787145837984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨210253977792,210442196480⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-260487062848,-260198274240⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1368_ok : ecellOkT e1368 = true := by decide +kernel
theorem e1368_pos {a z : ℝ} (ha1 : ((863157/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((432003/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1368 e1368_ok ha1 ha2 hz1 hz2 hz

-- box ['432003/2048000', '172971/819200', '1999/2000', '3999/4000']  interval_lower 97403575/137438953472
noncomputable def e1369 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1331441472372,0,true,210442196416,210442196480⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨867581783180,0,false,-260487062848,-260487062784⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1331669374075,0,true,210630382784,210630382848⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨867353881477,0,false,-260775927232,-260775927168⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1331325507449,0,true,210346427776,210346427840⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨867697748103,0,false,-260340106944,-260340106880⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1331611334639,0,true,210582460608,210582460672⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨867411920913,0,false,-260702355328,-260702355264⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541587121,0,true,29958912,29958976⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099481668431,0,false,-29959808,-29959744⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099571610593,0,true,59981120,59981184⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099451644959,0,false,-59984512,-59984448⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624503,0,false,-3328,-3264⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626960,0,false,-832,-768⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1331383484533,0,true,210394308672,210394308736⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨867639771019,0,false,-260413575616,-260413575552⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1331640363024,0,true,210606429120,210606429184⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨867382892528,0,false,-260739151680,-260739151616⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1050504642886,0,false,-50132722496,-50132722432⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1050613047172,0,false,-50019266944,-50019266880⟩
    { al := (432003/2048000), au := (172971/819200), zl := (1999/2000), zu := (3999/4000),
      A := ⟨231929844596,232157746299⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210442196416,210442196480⟩ : DyadicInterval 40),(⟨-260487062848,-260487062784⟩ : DyadicInterval 40),(⟨737477151536,737477170865⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210630382784,210630382848⟩ : DyadicInterval 40),(⟨-260775927232,-260775927168⟩ : DyadicInterval 40),(⟨737428320784,737428340114⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210346427776,210346427840⟩ : DyadicInterval 40),(⟨-260340106944,-260340106880⟩ : DyadicInterval 40),(⟨737501979468,737501998798⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210582460608,210582460672⟩ : DyadicInterval 40),(⟨-260702355328,-260702355264⟩ : DyadicInterval 40),(⟨737440761181,737440780510⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨29959345,59982817⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29958912,29958976⟩ : DyadicInterval 40),(⟨-29959808,-29959744⟩ : DyadicInterval 40),(⟨762123383183,762123402512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59981120,59981184⟩ : DyadicInterval 40),(⟨-59984512,-59984448⟩ : DyadicInterval 40),(⟨762123381975,762123401304⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3328,-768⟩ : DyadicInterval 40),(⟨762123384000,762123404544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨231871856757,232128735248⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210394308672,210394308736⟩ : DyadicInterval 40),(⟨-260413575616,-260413575552⟩ : DyadicInterval 40),(⟨737489568265,737489587594⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210606429120,210606429184⟩ : DyadicInterval 40),(⟨-260739151680,-260739151616⟩ : DyadicInterval 40),(⟨737434539533,737434558862⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-50132722496,-50019266880⟩ : DyadicInterval 40),(⟨787133017056,787189764128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨210442196416,210630382848⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-260775927232,-260487062784⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1369_ok : ecellOkT e1369 = true := by decide +kernel
theorem e1369_pos {a z : ℝ} (ha1 : ((432003/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((172971/819200 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1369 e1369_ok ha1 ha2 hz1 hz2 hz

-- box ['172971/819200', '108213/512000', '1999/2000', '3999/4000']  interval_lower 785050891/1099511627776
noncomputable def e1370 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1331669374074,0,true,210630382784,210630382848⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨867353881478,0,false,-260775927232,-260775927168⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1331897275778,0,true,210818536896,210818536960⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨867125979774,0,false,-261064867584,-261064867520⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1331553295200,0,true,210534536384,210534536448⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨867469960352,0,false,-260628788288,-260628788224⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1331839179367,0,true,210770575936,210770576000⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨867184076185,0,false,-260991204032,-260991203968⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541618545,0,true,29990336,29990400⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099481637007,0,false,-29991232,-29991168⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099571673456,0,true,60044032,60044096⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099451582096,0,false,-60047360,-60047296⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624496,0,false,-3328,-3264⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626958,0,false,-832,-768⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1331611329254,0,true,210582456192,210582456256⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨867411926298,0,false,-260702348480,-260702348416⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1331868236236,0,true,210794563840,210794563904⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨867155019316,0,false,-261028046144,-261028046080⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1050408378541,0,false,-50233482304,-50233482240⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1050516901331,0,false,-50119892288,-50119892224⟩
    { al := (172971/819200), au := (108213/512000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨232157746298,232385648002⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210630382784,210630382848⟩ : DyadicInterval 40),(⟨-260775927232,-260775927168⟩ : DyadicInterval 40),(⟨737428320784,737428340114⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210818536896,210818536960⟩ : DyadicInterval 40),(⟨-261064867584,-261064867520⟩ : DyadicInterval 40),(⟨737379440644,737379459973⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210534536384,210534536448⟩ : DyadicInterval 40),(⟨-260628788288,-260628788224⟩ : DyadicInterval 40),(⟨737453198324,737453217654⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210770575936,210770576000⟩ : DyadicInterval 40),(⟨-260991204032,-260991203968⟩ : DyadicInterval 40),(⟨737391905796,737391925125⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨29990769,60045680⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29990336,29990400⟩ : DyadicInterval 40),(⟨-29991232,-29991168⟩ : DyadicInterval 40),(⟨762123383181,762123402510⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨60044032,60044096⟩ : DyadicInterval 40),(⟨-60047360,-60047296⟩ : DyadicInterval 40),(⟨762123381936,762123401265⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3328,-768⟩ : DyadicInterval 40),(⟨762123384000,762123404544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨232099701478,232356608460⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210582456192,210582456256⟩ : DyadicInterval 40),(⟨-260702348480,-260702348416⟩ : DyadicInterval 40),(⟨737440762308,737440781638⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210794563840,210794563904⟩ : DyadicInterval 40),(⟨-261028046144,-261028046080⟩ : DyadicInterval 40),(⟨737385671744,737385691074⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-50233482304,-50119892224⟩ : DyadicInterval 40),(⟨787183329728,787240144032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨210630382784,210818536960⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-261064867584,-260775927168⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1370_ok : ecellOkT e1370 = true := by decide +kernel
theorem e1370_pos {a z : ℝ} (ha1 : ((172971/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((108213/512000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1370 e1370_ok ha1 ha2 hz1 hz2 hz

-- box ['432003/2048000', '172971/819200', '3999/4000', '1']  interval_lower 389080445/549755813888
noncomputable def e1371 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1331441472372,0,true,210442196416,210442196480⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨867581783180,0,false,-260487062848,-260487062784⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1331669374075,0,true,210630382784,210630382848⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨867353881477,0,false,-260775927232,-260775927168⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1331383489910,0,true,210394313088,210394313152⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨867639765642,0,false,-260413582464,-260413582400⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541619567,0,true,29991360,29991424⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099481635985,0,false,-29992256,-29992192⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626957,0,false,-832,-768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1331412475404,0,true,210418250304,210418250368⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨867610780148,0,false,-260450314752,-260450314688⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1331669382630,0,true,210630389824,210630389888⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨867353872922,0,false,-260775938112,-260775938048⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1050492388890,0,false,-50145548224,-50145548160⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1050600818857,0,false,-50032064448,-50032064384⟩
    { al := (432003/2048000), au := (172971/819200), zl := (3999/4000), zu := 1,
      A := ⟨231929844596,232157746299⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210442196416,210442196480⟩ : DyadicInterval 40),(⟨-260487062848,-260487062784⟩ : DyadicInterval 40),(⟨737477151536,737477170865⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210630382784,210630382848⟩ : DyadicInterval 40),(⟨-260775927232,-260775927168⟩ : DyadicInterval 40),(⟨737428320784,737428340114⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210394313088,210394313152⟩ : DyadicInterval 40),(⟨-260413582464,-260413582400⟩ : DyadicInterval 40),(⟨737489567142,737489586472⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210630382784,210630382848⟩ : DyadicInterval 40),(⟨-260775927232,-260775927168⟩ : DyadicInterval 40),(⟨737428320784,737428340114⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,29991791⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29991360,29991424⟩ : DyadicInterval 40),(⟨-29992256,-29992192⟩ : DyadicInterval 40),(⟨762123383181,762123402510⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-832,0⟩ : DyadicInterval 40),(⟨762123383616,762123403296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨231900847628,232157754854⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210418250304,210418250368⟩ : DyadicInterval 40),(⟨-260450314752,-260450314688⟩ : DyadicInterval 40),(⟨737483360942,737483380271⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210630389824,210630389888⟩ : DyadicInterval 40),(⟨-260775938112,-260775938048⟩ : DyadicInterval 40),(⟨737428318978,737428338308⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-50145548224,-50032064384⟩ : DyadicInterval 40),(⟨787139415808,787196176992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨210442196416,210630382848⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-260775927232,-260487062784⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1371_ok : ecellOkT e1371 = true := by decide +kernel
theorem e1371_pos {a z : ℝ} (ha1 : ((432003/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((172971/819200 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1371 e1371_ok ha1 ha2 hz1 hz2 hz

-- box ['172971/819200', '108213/512000', '3999/4000', '1']  interval_lower 97997431/137438953472
noncomputable def e1372 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1331669374074,0,true,210630382784,210630382848⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨867353881478,0,false,-260775927232,-260775927168⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1331897275778,0,true,210818536896,210818536960⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨867125979774,0,false,-261064867584,-261064867520⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1331611334637,0,true,210582460608,210582460672⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨867411920915,0,false,-260702355328,-260702355264⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541650999,0,true,30022784,30022848⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099481604553,0,false,-30023680,-30023616⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626956,0,false,-832,-768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1331640348616,0,true,210606417216,210606417280⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨867382906936,0,false,-260739133376,-260739133312⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1331897284320,0,true,210818543936,210818544000⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨867125971232,0,false,-261064878400,-261064878336⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1050396100479,0,false,-50246334400,-50246334336⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1050504648971,0,false,-50132716160,-50132716096⟩
    { al := (172971/819200), au := (108213/512000), zl := (3999/4000), zu := 1,
      A := ⟨232157746298,232385648002⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210630382784,210630382848⟩ : DyadicInterval 40),(⟨-260775927232,-260775927168⟩ : DyadicInterval 40),(⟨737428320784,737428340114⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210818536896,210818536960⟩ : DyadicInterval 40),(⟨-261064867584,-261064867520⟩ : DyadicInterval 40),(⟨737379440644,737379459973⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210582460608,210582460672⟩ : DyadicInterval 40),(⟨-260702355328,-260702355264⟩ : DyadicInterval 40),(⟨737440761181,737440780511⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210818536896,210818536960⟩ : DyadicInterval 40),(⟨-261064867584,-261064867520⟩ : DyadicInterval 40),(⟨737379440644,737379459973⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,30023223⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨30022784,30022848⟩ : DyadicInterval 40),(⟨-30023680,-30023616⟩ : DyadicInterval 40),(⟨762123383180,762123402509⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-832,0⟩ : DyadicInterval 40),(⟨762123383616,762123403296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨232128720840,232385656544⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210606417216,210606417280⟩ : DyadicInterval 40),(⟨-260739133376,-260739133312⟩ : DyadicInterval 40),(⟨737434542610,737434561939⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210818543936,210818544000⟩ : DyadicInterval 40),(⟨-261064878400,-261064878336⟩ : DyadicInterval 40),(⟨737379438812,737379458142⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-50246334400,-50132716096⟩ : DyadicInterval 40),(⟨787189741664,787246570080⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨210630382784,210818536960⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-261064867584,-260775927168⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1372_ok : ecellOkT e1372 = true := by decide +kernel
theorem e1372_pos {a z : ℝ} (ha1 : ((172971/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((108213/512000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1372 e1372_ok ha1 ha2 hz1 hz2 hz

-- box ['108213/512000', '866553/4096000', '999/1000', '3997/4000']  interval_lower 793043497/1099511627776
noncomputable def e1373 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1331897275777,0,true,210818536896,210818536960⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨867125979775,0,false,-261064867584,-261064867520⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1332125177480,0,true,211006658880,211006658944⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨866898078072,0,false,-261353883840,-261353883776⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1331664890128,0,true,210626680512,210626680576⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨867358365424,0,false,-260770243136,-260770243072⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1331950717318,0,true,210862653248,210862653312⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨867072538234,0,false,-261132633280,-261132633216⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099601693366,0,true,90061888,90061952⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099421562186,0,false,-90069312,-90069248⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099631842590,0,true,120208192,120208256⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099391412962,0,false,-120221440,-120221376⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511614632,0,false,-13184,-13120⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620399,0,false,-7424,-7360⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1331781078984,0,true,210722609600,210722609664⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨867242176568,0,false,-260917540416,-260917540352⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1332037957016,0,true,210934666368,210934666432⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨866985298536,0,false,-261243265152,-261243265088⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1050336619141,0,false,-50308598784,-50308598720⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1050445209012,0,false,-50194930816,-50194930752⟩
    { al := (108213/512000), au := (866553/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨232385648001,232613549704⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210818536896,210818536960⟩ : DyadicInterval 40),(⟨-261064867584,-261064867520⟩ : DyadicInterval 40),(⟨737379440644,737379459974⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211006658880,211006658944⟩ : DyadicInterval 40),(⟨-261353883840,-261353883776⟩ : DyadicInterval 40),(⟨737330511000,737330530329⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210626680512,210626680576⟩ : DyadicInterval 40),(⟨-260770243136,-260770243072⟩ : DyadicInterval 40),(⟨737429282028,737429301357⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210862653248,210862653312⟩ : DyadicInterval 40),(⟨-261132633280,-261132633216⟩ : DyadicInterval 40),(⟨737367971366,737367990696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨90065590,120214814⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨90061888,90061952⟩ : DyadicInterval 40),(⟨-90069312,-90069248⟩ : DyadicInterval 40),(⟨762123379886,762123399215⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨120208192,120208256⟩ : DyadicInterval 40),(⟨-120221440,-120221376⟩ : DyadicInterval 40),(⟨762123377032,762123396361⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-13184,-7360⟩ : DyadicInterval 40),(⟨762123387296,762123409472⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨232269451208,232526329240⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210722609600,210722609664⟩ : DyadicInterval 40),(⟨-260917540416,-260917540352⟩ : DyadicInterval 40),(⟨737404368603,737404387933⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210934666368,210934666432⟩ : DyadicInterval 40),(⟨-261243265152,-261243265088⟩ : DyadicInterval 40),(⟨737349242720,737349262049⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-50308598784,-50194930752⟩ : DyadicInterval 40),(⟨787220848992,787277702272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨210818536896,211006658944⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-261353883840,-261064867520⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1373_ok : ecellOkT e1373 = true := by decide +kernel
theorem e1373_pos {a z : ℝ} (ha1 : ((108213/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((866553/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1373 e1373_ok ha1 ha2 hz1 hz2 hz

-- box ['866553/4096000', '433701/2048000', '999/1000', '3997/4000']  interval_lower 798917389/1099511627776
noncomputable def e1374 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1332125177479,0,true,211006658880,211006658944⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨866898078073,0,false,-261353883840,-261353883776⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1332353079182,0,true,211194748672,211194748736⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨866670176370,0,false,-261642976064,-261642976000⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1331892563929,0,true,210814647168,210814647232⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨867130691623,0,false,-261058892992,-261058892928⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1332178448094,0,true,211050626560,211050626624⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨866844807458,0,false,-261421450560,-261421450496⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099601787672,0,true,90156160,90156224⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099421467880,0,false,-90163648,-90163584⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099631968357,0,true,120333952,120334016⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099391287195,0,false,-120347200,-120347136⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511614604,0,false,-13184,-13120⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620383,0,false,-7424,-7360⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1332008866737,0,true,210910653952,210910654016⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨867014388815,0,false,-261206373440,-261206373376⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1332265773256,0,true,211122697920,211122697984⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨866757482296,0,false,-261532219904,-261532219840⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1050240214114,0,false,-50409521984,-50409521920⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1050348922482,0,false,-50295719488,-50295719424⟩
    { al := (866553/4096000), au := (433701/2048000), zl := (999/1000), zu := (3997/4000),
      A := ⟨232613549703,232841451406⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211006658880,211006658944⟩ : DyadicInterval 40),(⟨-261353883840,-261353883776⟩ : DyadicInterval 40),(⟨737330511000,737330530329⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211194748672,211194748736⟩ : DyadicInterval 40),(⟨-261642976064,-261642976000⟩ : DyadicInterval 40),(⟨737281531901,737281551231⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210814647168,210814647232⟩ : DyadicInterval 40),(⟨-261058892992,-261058892928⟩ : DyadicInterval 40),(⟨737380451725,737380471055⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211050626560,211050626624⟩ : DyadicInterval 40),(⟨-261421450560,-261421450496⟩ : DyadicInterval 40),(⟨737319066887,737319086216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨90159896,120340581⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨90156160,90156224⟩ : DyadicInterval 40),(⟨-90163648,-90163584⟩ : DyadicInterval 40),(⟨762123379902,762123399232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨120333952,120334016⟩ : DyadicInterval 40),(⟨-120347200,-120347136⟩ : DyadicInterval 40),(⟨762123377004,762123396334⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-13184,-7360⟩ : DyadicInterval 40),(⟨762123387296,762123409472⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨232497238961,232754145480⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210910653952,210910654016⟩ : DyadicInterval 40),(⟨-261206373440,-261206373376⟩ : DyadicInterval 40),(⟨737355488627,737355507956⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211122697920,211122697984⟩ : DyadicInterval 40),(⟨-261532219904,-261532219840⟩ : DyadicInterval 40),(⟨737300300942,737300320271⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-50409521984,-50295719424⟩ : DyadicInterval 40),(⟨787271243328,787328163872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨211006658880,211194748736⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-261642976064,-261353883776⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1374_ok : ecellOkT e1374 = true := by decide +kernel
theorem e1374_pos {a z : ℝ} (ha1 : ((866553/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((433701/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1374 e1374_ok ha1 ha2 hz1 hz2 hz

-- box ['108213/512000', '866553/4096000', '3997/4000', '1999/2000']  interval_lower 791969727/1099511627776
noncomputable def e1375 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1331897275777,0,true,210818536896,210818536960⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨867125979775,0,false,-261064867584,-261064867520⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1332125177480,0,true,211006658880,211006658944⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨866898078072,0,false,-261353883840,-261353883776⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1331722986540,0,true,210674647744,210674647808⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨867300269012,0,false,-260843891840,-260843891776⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1332008870706,0,true,210910657216,210910657280⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨867014384846,0,false,-261206378496,-261206378432⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099571671924,0,true,60042496,60042560⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099451583628,0,false,-60045824,-60045760⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099601789715,0,true,90158208,90158272⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099421465837,0,false,-90165696,-90165632⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620382,0,false,-7424,-7360⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624497,0,false,-3328,-3264⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1331810126359,0,true,210746590720,210746590784⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨867213129193,0,false,-260954368064,-260954368000⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1332067033116,0,true,210958666560,210958666624⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨866956222436,0,false,-261280140160,-261280140096⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1050324320259,0,false,-50321473536,-50321473472⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1050432935855,0,false,-50207777280,-50207777216⟩
    { al := (108213/512000), au := (866553/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨232385648001,232613549704⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210818536896,210818536960⟩ : DyadicInterval 40),(⟨-261064867584,-261064867520⟩ : DyadicInterval 40),(⟨737379440644,737379459974⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211006658880,211006658944⟩ : DyadicInterval 40),(⟨-261353883840,-261353883776⟩ : DyadicInterval 40),(⟨737330511000,737330530329⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210674647744,210674647808⟩ : DyadicInterval 40),(⟨-260843891840,-260843891776⟩ : DyadicInterval 40),(⟨737416826501,737416845830⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210910657216,210910657280⟩ : DyadicInterval 40),(⟨-261206378496,-261206378432⟩ : DyadicInterval 40),(⟨737355487791,737355507120⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨60044148,90161939⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨60042496,60042560⟩ : DyadicInterval 40),(⟨-60045824,-60045760⟩ : DyadicInterval 40),(⟨762123381936,762123401266⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨90158208,90158272⟩ : DyadicInterval 40),(⟨-90165696,-90165632⟩ : DyadicInterval 40),(⟨762123379902,762123399231⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7424,-3264⟩ : DyadicInterval 40),(⟨762123385248,762123406592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨232298498583,232555405340⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210746590720,210746590784⟩ : DyadicInterval 40),(⟨-260954368064,-260954368000⟩ : DyadicInterval 40),(⟨737398138207,737398157536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210958666560,210958666624⟩ : DyadicInterval 40),(⟨-261280140160,-261280140096⟩ : DyadicInterval 40),(⟨737342999066,737343018396⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-50321473536,-50207777216⟩ : DyadicInterval 40),(⟨787227272224,787284139648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨210818536896,211006658944⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-261353883840,-261064867520⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1375_ok : ecellOkT e1375 = true := by decide +kernel
theorem e1375_pos {a z : ℝ} (ha1 : ((108213/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((866553/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1375 e1375_ok ha1 ha2 hz1 hz2 hz

-- box ['866553/4096000', '433701/2048000', '3997/4000', '1999/2000']  interval_lower 398919811/549755813888
noncomputable def e1376 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1332125177479,0,true,211006658880,211006658944⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨866898078073,0,false,-261353883840,-261353883776⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1332353079182,0,true,211194748672,211194748736⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨866670176370,0,false,-261642976064,-261642976000⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1331950717316,0,true,210862653248,210862653312⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨867072538236,0,false,-261132633280,-261132633216⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1332236658457,0,true,211098669376,211098669440⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨866786597095,0,false,-261495287424,-261495287360⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099571734796,0,true,60105344,60105408⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099451520756,0,false,-60108672,-60108608⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099601884043,0,true,90252544,90252608⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099421371509,0,false,-90260032,-90259968⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620367,0,false,-7424,-7360⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624491,0,false,-3328,-3264⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1332037942599,0,true,210934654464,210934654528⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨866985312953,0,false,-261243246912,-261243246848⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1332294877845,0,true,211146717504,211146717568⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨866728377707,0,false,-261569140736,-261569140672⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1050227891120,0,false,-50422423168,-50422423104⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1050336625240,0,false,-50308592384,-50308592320⟩
    { al := (866553/4096000), au := (433701/2048000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨232613549703,232841451406⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211006658880,211006658944⟩ : DyadicInterval 40),(⟨-261353883840,-261353883776⟩ : DyadicInterval 40),(⟨737330511000,737330530329⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211194748672,211194748736⟩ : DyadicInterval 40),(⟨-261642976064,-261642976000⟩ : DyadicInterval 40),(⟨737281531901,737281551231⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210862653248,210862653312⟩ : DyadicInterval 40),(⟨-261132633280,-261132633216⟩ : DyadicInterval 40),(⟨737367971367,737367990696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211098669376,211098669440⟩ : DyadicInterval 40),(⟨-261495287424,-261495287360⟩ : DyadicInterval 40),(⟨737306558439,737306577768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨60107020,90256267⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨60105344,60105408⟩ : DyadicInterval 40),(⟨-60108672,-60108608⟩ : DyadicInterval 40),(⟨762123381930,762123401259⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨90252544,90252608⟩ : DyadicInterval 40),(⟨-90260032,-90259968⟩ : DyadicInterval 40),(⟨762123379886,762123399216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7424,-3264⟩ : DyadicInterval 40),(⟨762123385248,762123406592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨232526314823,232783250069⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210934654464,210934654528⟩ : DyadicInterval 40),(⟨-261243246912,-261243246848⟩ : DyadicInterval 40),(⟨737349245835,737349265165⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211146717504,211146717568⟩ : DyadicInterval 40),(⟨-261569140736,-261569140672⟩ : DyadicInterval 40),(⟨737294044863,737294064192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-50422423168,-50308592320⟩ : DyadicInterval 40),(⟨787277679776,787334614464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨211006658880,211194748736⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-261642976064,-261353883776⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1376_ok : ecellOkT e1376 = true := by decide +kernel
theorem e1376_pos {a z : ℝ} (ha1 : ((866553/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((433701/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1376 e1376_ok ha1 ha2 hz1 hz2 hz

-- box ['433701/2048000', '868251/4096000', '999/1000', '3997/4000']  interval_lower 201203271/274877906944
noncomputable def e1377 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1332353079181,0,true,211194748672,211194748736⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨866670176371,0,false,-261642976064,-261642976000⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1332580980884,0,true,211382806272,211382806336⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨866442274668,0,false,-261932144320,-261932144256⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1332120237729,0,true,211002581696,211002581760⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨866903017823,0,false,-261347618624,-261347618560⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1332406178870,0,true,211238567808,211238567872⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨866617076682,0,false,-261710343680,-261710343616⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099601881994,0,true,90250496,90250560⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099421373558,0,false,-90257984,-90257920⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099632094149,0,true,120459712,120459776⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099391161403,0,false,-120473024,-120472960⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511614577,0,false,-13248,-13184⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620368,0,false,-7424,-7360⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1332236654491,0,true,211098666112,211098666176⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨866786601061,0,false,-261495282368,-261495282304⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1332493589504,0,true,211310697344,211310697408⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨866529666048,0,false,-261821250624,-261821250560⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1050143714677,0,false,-50510553280,-50510553216⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1050252541568,0,false,-50396616256,-50396616192⟩
    { al := (433701/2048000), au := (868251/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨232841451405,233069353108⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211194748672,211194748736⟩ : DyadicInterval 40),(⟨-261642976064,-261642976000⟩ : DyadicInterval 40),(⟨737281531902,737281551231⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211382806272,211382806336⟩ : DyadicInterval 40),(⟨-261932144320,-261932144256⟩ : DyadicInterval 40),(⟨737232503360,737232522690⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211002581696,211002581760⟩ : DyadicInterval 40),(⟨-261347618624,-261347618560⟩ : DyadicInterval 40),(⟨737331572065,737331591395⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211238567808,211238567872⟩ : DyadicInterval 40),(⟨-261710343680,-261710343616⟩ : DyadicInterval 40),(⟨737270112970,737270132299⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨90254218,120466373⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨90250496,90250560⟩ : DyadicInterval 40),(⟨-90257984,-90257920⟩ : DyadicInterval 40),(⟨762123379887,762123399216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨120459712,120459776⟩ : DyadicInterval 40),(⟨-120473024,-120472960⟩ : DyadicInterval 40),(⟨762123377009,762123396338⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-13248,-7360⟩ : DyadicInterval 40),(⟨762123387296,762123409504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨232725026715,232981961728⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211098666112,211098666176⟩ : DyadicInterval 40),(⟨-261495282368,-261495282304⟩ : DyadicInterval 40),(⟨737306559276,737306578605⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211310697344,211310697408⟩ : DyadicInterval 40),(⟨-261821250624,-261821250560⟩ : DyadicInterval 40),(⟨737251309734,737251329064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-50510553280,-50396616192⟩ : DyadicInterval 40),(⟨787321691712,787378679520⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨211194748672,211382806336⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-261932144320,-261642976000⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1377_ok : ecellOkT e1377 = true := by decide +kernel
theorem e1377_pos {a z : ℝ} (ha1 : ((433701/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((868251/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1377 e1377_ok ha1 ha2 hz1 hz2 hz

-- box ['868251/4096000', '8691/40960', '999/1000', '3997/4000']  interval_lower 405365303/549755813888
noncomputable def e1378 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1332580980883,0,true,211382806272,211382806336⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨866442274669,0,false,-261932144320,-261932144256⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1332808882586,0,true,211570831744,211570831808⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨866214372966,0,false,-262221388672,-262221388608⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1332347911529,0,true,211190484096,211190484160⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨866675344023,0,false,-261636420096,-261636420032⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1332633909646,0,true,211426476928,211426476992⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨866389345906,0,false,-261999312768,-261999312704⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099601976336,0,true,90344832,90344896⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099421279216,0,false,-90352320,-90352256⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099632219966,0,true,120585536,120585600⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099391035586,0,false,-120598848,-120598784⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511614549,0,false,-13248,-13184⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620352,0,false,-7488,-7424⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1332464442242,0,true,211286646144,211286646208⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨866558813310,0,false,-261784267264,-261784267200⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1332721405750,0,true,211498664640,211498664704⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨866301849802,0,false,-262110357376,-262110357312⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1050047120836,0,false,-50611692672,-50611692608⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1050156066274,0,false,-50497621056,-50497620992⟩
    { al := (868251/4096000), au := (8691/40960), zl := (999/1000), zu := (3997/4000),
      A := ⟨233069353107,233297254810⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211382806272,211382806336⟩ : DyadicInterval 40),(⟨-261932144320,-261932144256⟩ : DyadicInterval 40),(⟨737232503361,737232522690⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211570831744,211570831808⟩ : DyadicInterval 40),(⟨-262221388672,-262221388608⟩ : DyadicInterval 40),(⟨737183425350,737183444679⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211190484096,211190484160⟩ : DyadicInterval 40),(⟨-261636420096,-261636420032⟩ : DyadicInterval 40),(⟨737282643061,737282662390⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211426476928,211426476992⟩ : DyadicInterval 40),(⟨-261999312768,-261999312704⟩ : DyadicInterval 40),(⟨737221109691,737221129021⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨90348560,120592190⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨90344832,90344896⟩ : DyadicInterval 40),(⟨-90352320,-90352256⟩ : DyadicInterval 40),(⟨762123379871,762123399201⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨120585536,120585600⟩ : DyadicInterval 40),(⟨-120598848,-120598784⟩ : DyadicInterval 40),(⟨762123376981,762123396310⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-13248,-7424⟩ : DyadicInterval 40),(⟨762123387328,762123409504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨232952814466,233209777974⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211286646144,211286646208⟩ : DyadicInterval 40),(⟨-261784267264,-261784267200⟩ : DyadicInterval 40),(⟨737257580525,737257599854⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211498664640,211498664704⟩ : DyadicInterval 40),(⟨-262110357376,-262110357312⟩ : DyadicInterval 40),(⟨737202269112,737202288442⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-50611692672,-50497620992⟩ : DyadicInterval 40),(⟨787372194112,787429249216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨211382806272,211570831808⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-262221388672,-261932144256⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1378_ok : ecellOkT e1378 = true := by decide +kernel
theorem e1378_pos {a z : ℝ} (ha1 : ((868251/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((8691/40960 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1378 e1378_ok ha1 ha2 hz1 hz2 hz

-- box ['433701/2048000', '868251/4096000', '3997/4000', '1999/2000']  interval_lower 803731307/1099511627776
noncomputable def e1379 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1332353079181,0,true,211194748672,211194748736⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨866670176371,0,false,-261642976064,-261642976000⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1332580980884,0,true,211382806272,211382806336⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨866442274668,0,false,-261932144320,-261932144256⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1332178448092,0,true,211050626560,211050626624⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨866844807460,0,false,-261421450560,-261421450496⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1332464446208,0,true,211286649408,211286649472⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨866558809344,0,false,-261784272256,-261784272192⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099571797679,0,true,60168256,60168320⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099451457873,0,false,-60171584,-60171520⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099601978388,0,true,90346880,90346944⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099421277164,0,false,-90354368,-90354304⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620351,0,false,-7488,-7424⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624484,0,false,-3328,-3264⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1332265758834,0,true,211122686016,211122686080⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨866757496718,0,false,-261532201600,-261532201536⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1332522722576,0,true,211334736320,211334736384⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨866500532976,0,false,-261858217280,-261858217216⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1050131367551,0,false,-50523480896,-50523480832⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1050240220221,0,false,-50409515584,-50409515520⟩
    { al := (433701/2048000), au := (868251/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨232841451405,233069353108⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211194748672,211194748736⟩ : DyadicInterval 40),(⟨-261642976064,-261642976000⟩ : DyadicInterval 40),(⟨737281531902,737281551231⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211382806272,211382806336⟩ : DyadicInterval 40),(⟨-261932144320,-261932144256⟩ : DyadicInterval 40),(⟨737232503360,737232522690⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211050626560,211050626624⟩ : DyadicInterval 40),(⟨-261421450560,-261421450496⟩ : DyadicInterval 40),(⟨737319066887,737319086217⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211286649408,211286649472⟩ : DyadicInterval 40),(⟨-261784272256,-261784272192⟩ : DyadicInterval 40),(⟨737257579661,737257598990⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨60169903,90350612⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨60168256,60168320⟩ : DyadicInterval 40),(⟨-60171584,-60171520⟩ : DyadicInterval 40),(⟨762123381923,762123401252⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨90346880,90346944⟩ : DyadicInterval 40),(⟨-90354368,-90354304⟩ : DyadicInterval 40),(⟨762123379871,762123399200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7488,-3264⟩ : DyadicInterval 40),(⟨762123385248,762123406624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨232754131058,233011094800⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211122686016,211122686080⟩ : DyadicInterval 40),(⟨-261532201600,-261532201536⟩ : DyadicInterval 40),(⟨737300304039,737300323368⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211334736320,211334736384⟩ : DyadicInterval 40),(⟨-261858217280,-261858217216⟩ : DyadicInterval 40),(⟨737245041205,737245060535⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-50523480896,-50409515520⟩ : DyadicInterval 40),(⟨787328141376,787385143328⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨211194748672,211382806336⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-261932144320,-261642976000⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1379_ok : ecellOkT e1379 = true := by decide +kernel
theorem e1379_pos {a z : ℝ} (ha1 : ((433701/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((868251/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1379 e1379_ok ha1 ha2 hz1 hz2 hz

end CKLaneC2R.EpCells.B022

end


