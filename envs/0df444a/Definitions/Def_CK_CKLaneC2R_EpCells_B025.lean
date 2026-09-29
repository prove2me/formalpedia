-- Prove2me | Definitions.Def_CK_CKLaneC2R_EpCells_B025
-- name    : CK_CKLaneC2R_EpCells_B025
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T14:28:45.110724+00:00
-- url     : https://prove2.me/theorems/66626c81-cb4d-4223-b56c-1a52c7b64178
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EpCells.B025` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EpCells.B025` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EpCells.B025` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EpCells.B025 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EpCells/B025.lean)

import Definitions.Def_CK_CKLaneC2R_EndpointCheckT

-- ===== source module CKLaneC2R.EpCells.B025 =====
section

namespace CKLaneC2R.EpCells.B025

open GeneralCK GeneralCK.Certificates CKLaneC2R CKLaneC2R.Endpoint

-- box ['348801/2048000', '698451/4096000', '7993/8000', '3997/4000']  interval_lower 28942995/1099511627776
noncomputable def e1500 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1286772738752,0,true,172921539904,172921539968⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨912250516800,0,false,-205286235648,-205286235584⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1287000640455,0,true,173116258368,173116258432⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨912022615097,0,false,-205560953920,-205560953856⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1286608885279,0,true,172781522752,172781522816⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨912414370273,0,false,-205088765056,-205088764992⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1286860023696,0,true,172996119936,172996120000⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨912163231856,0,false,-205391442944,-205391442880⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099583357307,0,true,71727168,71727232⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099439898245,0,false,-71731904,-71731840⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099595419263,0,true,83788288,83788352⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099427836289,0,false,-83794688,-83794624⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621390,0,false,-6400,-6336⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623097,0,false,-4736,-4672⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1286690807901,0,true,172851530048,172851530112⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨912332447651,0,false,-205187490944,-205187490880⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1286930341116,0,true,173056198528,173056198592⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨912092914436,0,false,-205476206016,-205476205952⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067564922327,0,false,-32420007488,-32420007424⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067646530048,0,false,-32335960896,-32335960832⟩
    { al := (348801/2048000), au := (698451/4096000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨187261110976,187489012679⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172921539904,172921539968⟩ : DyadicInterval 40),(⟨-205286235648,-205286235584⟩ : DyadicInterval 40),(⟨746098883200,746098902530⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173116258368,173116258432⟩ : DyadicInterval 40),(⟨-205560953920,-205560953856⟩ : DyadicInterval 40),(⟨746059662284,746059681614⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172781522752,172781522816⟩ : DyadicInterval 40),(⟨-205088765056,-205088764992⟩ : DyadicInterval 40),(⟨746127051599,746127070929⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172996119936,172996120000⟩ : DyadicInterval 40),(⟨-205391442944,-205391442880⟩ : DyadicInterval 40),(⟨746083867589,746083886919⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨71729531,83791487⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨71727168,71727232⟩ : DyadicInterval 40),(⟨-71731904,-71731840⟩ : DyadicInterval 40),(⟨762123381240,762123400569⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨83788288,83788352⟩ : DyadicInterval 40),(⟨-83794688,-83794624⟩ : DyadicInterval 40),(⟨762123380366,762123399695⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6400,-4672⟩ : DyadicInterval 40),(⟨762123385952,762123406080⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨187179180125,187418713340⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172851530048,172851530112⟩ : DyadicInterval 40),(⟨-205187490944,-205187490880⟩ : DyadicInterval 40),(⟨746112971240,746112990569⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173056198528,173056198592⟩ : DyadicInterval 40),(⟨-205476206016,-205476205952⟩ : DyadicInterval 40),(⟨746071765669,746071784999⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32420007488,-32335960832⟩ : DyadicInterval 40),(⟨778291364032,778333406624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨172921539904,173116258432⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-205560953920,-205286235584⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1500_ok : ecellOkT e1500 = true := by decide +kernel
theorem e1500_pos {a z : ℝ} (ha1 : ((348801/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((698451/4096000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1500 e1500_ok ha1 ha2 hz1 hz2 hz

-- box ['698451/4096000', '6993/40960', '999/1000', '7993/8000']  interval_lower 15878661/549755813888
noncomputable def e1501 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1287000640454,0,true,173116258368,173116258432⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨912022615098,0,false,-205560953920,-205560953856⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1287228542157,0,true,173310942272,173310942336⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨911794713395,0,false,-205835740800,-205835740736⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1286813151441,0,true,172956070848,172956070912⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨912210104111,0,false,-205334945088,-205334945024⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1287064289857,0,true,173170633984,173170634048⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨911958965695,0,false,-205637690688,-205637690624⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099595418293,0,true,83787264,83787328⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099427837259,0,false,-83793728,-83793664⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099607510624,0,true,95878656,95878720⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099415744928,0,false,-95887040,-95886976⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619414,0,false,-8384,-8320⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621391,0,false,-6400,-6336⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1286906892058,0,true,173036164224,173036164288⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨912116363494,0,false,-205447939008,-205447938944⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1287146425248,0,true,173240798272,173240798336⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨911876830304,0,false,-205736722432,-205736722368⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067491214045,0,false,-32495924096,-32495924032⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067572915908,0,false,-32411774720,-32411774656⟩
    { al := (698451/4096000), au := (6993/40960), zl := (999/1000), zu := (7993/8000),
      A := ⟨187489012678,187716914381⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173116258368,173116258432⟩ : DyadicInterval 40),(⟨-205560953920,-205560953856⟩ : DyadicInterval 40),(⟨746059662284,746059681614⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173310942272,173310942336⟩ : DyadicInterval 40),(⟨-205835740800,-205835740736⟩ : DyadicInterval 40),(⟨746020392743,746020412073⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172956070848,172956070912⟩ : DyadicInterval 40),(⟨-205334945088,-205334945024⟩ : DyadicInterval 40),(⟨746091931922,746091951252⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173170633984,173170634048⟩ : DyadicInterval 40),(⟨-205637690688,-205637690624⟩ : DyadicInterval 40),(⟨746048699822,746048719152⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨83790517,95882848⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨83787264,83787328⟩ : DyadicInterval 40),(⟨-83793728,-83793664⟩ : DyadicInterval 40),(⟨762123380398,762123399727⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨95878656,95878720⟩ : DyadicInterval 40),(⟨-95887040,-95886976⟩ : DyadicInterval 40),(⟨762123379382,762123398711⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-8384,-6336⟩ : DyadicInterval 40),(⟨762123386784,762123407072⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨187395264282,187634797472⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173036164224,173036164288⟩ : DyadicInterval 40),(⟨-205447939008,-205447938944⟩ : DyadicInterval 40),(⟨746075801876,746075821205⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173240798272,173240798336⟩ : DyadicInterval 40),(⟨-205736722432,-205736722368⟩ : DyadicInterval 40),(⟨746034547844,746034567174⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32495924096,-32411774656⟩ : DyadicInterval 40),(⟨778329270944,778371364928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨173116258368,173310942336⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-205835740800,-205560953856⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1501_ok : ecellOkT e1501 = true := by decide +kernel
theorem e1501_pos {a z : ℝ} (ha1 : ((698451/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((6993/40960 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1501 e1501_ok ha1 ha2 hz1 hz2 hz

-- box ['698451/4096000', '6993/40960', '7993/8000', '3997/4000']  interval_lower 15754427/549755813888
noncomputable def e1502 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1287000640454,0,true,173116258368,173116258432⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨912022615098,0,false,-205560953920,-205560953856⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1287228542157,0,true,173310942272,173310942336⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨911794713395,0,false,-205835740800,-205835740736⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1286836587567,0,true,172976095552,172976095616⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨912186667985,0,false,-205363193600,-205363193536⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1287087754472,0,true,173190679168,173190679232⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨911935501080,0,false,-205665981376,-205665981312⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099583448376,0,true,71818240,71818304⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099439807176,0,false,-71822976,-71822912⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099595525528,0,true,83894528,83894592⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099427730024,0,false,-83900992,-83900928⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621374,0,false,-6464,-6400⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623085,0,false,-4736,-4672⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1286918609891,0,true,173046175680,173046175744⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨912104645661,0,false,-205462064320,-205462064256⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1287158157358,0,true,173250820096,173250820160⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨911865098194,0,false,-205750868736,-205750868672⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067487209684,0,false,-32500048576,-32500048512⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067568921526,0,false,-32415888640,-32415888576⟩
    { al := (698451/4096000), au := (6993/40960), zl := (7993/8000), zu := (3997/4000),
      A := ⟨187489012678,187716914381⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173116258368,173116258432⟩ : DyadicInterval 40),(⟨-205560953920,-205560953856⟩ : DyadicInterval 40),(⟨746059662284,746059681614⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173310942272,173310942336⟩ : DyadicInterval 40),(⟨-205835740800,-205835740736⟩ : DyadicInterval 40),(⟨746020392743,746020412073⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172976095552,172976095616⟩ : DyadicInterval 40),(⟨-205363193600,-205363193536⟩ : DyadicInterval 40),(⟨746087900004,746087919334⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173190679168,173190679232⟩ : DyadicInterval 40),(⟨-205665981376,-205665981312⟩ : DyadicInterval 40),(⟨746044657473,746044676803⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨71820600,83897752⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨71818240,71818304⟩ : DyadicInterval 40),(⟨-71822976,-71822912⟩ : DyadicInterval 40),(⟨762123381228,762123400557⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨83894528,83894592⟩ : DyadicInterval 40),(⟨-83900992,-83900928⟩ : DyadicInterval 40),(⟨762123380381,762123399711⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6464,-4672⟩ : DyadicInterval 40),(⟨762123385952,762123406112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨187406982115,187646529582⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173046175680,173046175744⟩ : DyadicInterval 40),(⟨-205462064320,-205462064256⟩ : DyadicInterval 40),(⟨746073784989,746073804319⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173250820096,173250820160⟩ : DyadicInterval 40),(⟨-205750868736,-205750868672⟩ : DyadicInterval 40),(⟨746032525875,746032545204⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32500048576,-32415888576⟩ : DyadicInterval 40),(⟨778331327904,778373427168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨173116258368,173310942336⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-205835740800,-205560953856⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1502_ok : ecellOkT e1502 = true := by decide +kernel
theorem e1502_pos {a z : ℝ} (ha1 : ((698451/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((6993/40960 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1502 e1502_ok ha1 ha2 hz1 hz2 hz

-- box ['348801/2048000', '698451/4096000', '3997/4000', '1599/1600']  interval_lower 28695051/1099511627776
noncomputable def e1503 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1286772738752,0,true,172921539904,172921539968⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨912250516800,0,false,-205286235648,-205286235584⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1287000640455,0,true,173116258368,173116258432⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨912022615097,0,false,-205560953920,-205560953856⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1286632292918,0,true,172801526272,172801526336⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨912390962634,0,false,-205116972992,-205116972928⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1286883459823,0,true,173016143936,173016144000⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨912139795729,0,false,-205419692928,-205419692864⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099571402504,0,true,59773056,59773120⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099451853048,0,false,-59776384,-59776320⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099583449281,0,true,71819136,71819200⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099439806271,0,false,-71823872,-71823808⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623084,0,false,-4736,-4672⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624527,0,false,-3264,-3200⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1286702511517,0,true,172861531008,172861531072⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨912320744035,0,false,-205201595840,-205201595776⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1286942059012,0,true,173066209856,173066209920⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨912081196540,0,false,-205490331840,-205490331776⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067560927423,0,false,-32424121984,-32424121920⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067642545112,0,false,-32340064768,-32340064704⟩
    { al := (348801/2048000), au := (698451/4096000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨187261110976,187489012679⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172921539904,172921539968⟩ : DyadicInterval 40),(⟨-205286235648,-205286235584⟩ : DyadicInterval 40),(⟨746098883200,746098902530⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173116258368,173116258432⟩ : DyadicInterval 40),(⟨-205560953920,-205560953856⟩ : DyadicInterval 40),(⟨746059662284,746059681614⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172801526272,172801526336⟩ : DyadicInterval 40),(⟨-205116972992,-205116972928⟩ : DyadicInterval 40),(⟨746123029104,746123048434⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173016143936,173016144000⟩ : DyadicInterval 40),(⟨-205419692928,-205419692864⟩ : DyadicInterval 40),(⟨746079834635,746079853965⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨59774728,71821505⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59773056,59773120⟩ : DyadicInterval 40),(⟨-59776384,-59776320⟩ : DyadicInterval 40),(⟨762123381966,762123401295⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨71819136,71819200⟩ : DyadicInterval 40),(⟨-71823872,-71823808⟩ : DyadicInterval 40),(⟨762123381228,762123400557⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4736,-3200⟩ : DyadicInterval 40),(⟨762123385216,762123405248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨187190883741,187430431236⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172861531008,172861531072⟩ : DyadicInterval 40),(⟨-205201595840,-205201595776⟩ : DyadicInterval 40),(⟨746110959212,746110978542⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173066209856,173066209920⟩ : DyadicInterval 40),(⟨-205490331840,-205490331776⟩ : DyadicInterval 40),(⟨746069748545,746069767874⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32424121984,-32340064704⟩ : DyadicInterval 40),(⟨778293415968,778335463872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨172921539904,173116258432⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-205560953920,-205286235584⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1503_ok : ecellOkT e1503 = true := by decide +kernel
theorem e1503_pos {a z : ℝ} (ha1 : ((348801/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((698451/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1503 e1503_ok ha1 ha2 hz1 hz2 hz

-- box ['348801/2048000', '698451/4096000', '1599/1600', '1999/2000']  interval_lower 7111887/274877906944
noncomputable def e1504 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1286772738752,0,true,172921539904,172921539968⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨912250516800,0,false,-205286235648,-205286235584⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1287000640455,0,true,173116258368,173116258432⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨912022615097,0,false,-205560953920,-205560953856⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1286655700557,0,true,172821529472,172821529536⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨912367554995,0,false,-205145181632,-205145181568⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1286906895949,0,true,173036167552,173036167616⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨912116359603,0,false,-205447943680,-205447943616⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099559447635,0,true,47818816,47818880⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099463807917,0,false,-47820928,-47820864⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099571479235,0,true,59849792,59849856⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099451776317,0,false,-59853120,-59853056⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624518,0,false,-3264,-3200⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625697,0,false,-2112,-2048⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1286714215167,0,true,172871531968,172871532032⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨912309040385,0,false,-205215700928,-205215700864⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1286953776935,0,true,173076221120,173076221184⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨912069478617,0,false,-205504457856,-205504457792⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067556932260,0,false,-32428236736,-32428236672⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067638559916,0,false,-32344168960,-32344168896⟩
    { al := (348801/2048000), au := (698451/4096000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨187261110976,187489012679⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172921539904,172921539968⟩ : DyadicInterval 40),(⟨-205286235648,-205286235584⟩ : DyadicInterval 40),(⟨746098883200,746098902530⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173116258368,173116258432⟩ : DyadicInterval 40),(⟨-205560953920,-205560953856⟩ : DyadicInterval 40),(⟨746059662284,746059681614⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172821529472,172821529536⟩ : DyadicInterval 40),(⟨-205145181632,-205145181568⟩ : DyadicInterval 40),(⟨746119006062,746119025391⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173036167552,173036167616⟩ : DyadicInterval 40),(⟨-205447943680,-205447943616⟩ : DyadicInterval 40),(⟨746075801196,746075820526⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨47819859,59851459⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨47818816,47818880⟩ : DyadicInterval 40),(⟨-47820928,-47820864⟩ : DyadicInterval 40),(⟨762123382528,762123401857⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59849792,59849856⟩ : DyadicInterval 40),(⟨-59853120,-59853056⟩ : DyadicInterval 40),(⟨762123381957,762123401287⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3264,-2048⟩ : DyadicInterval 40),(⟨762123384640,762123404512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨187202587391,187442149159⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172871531968,172871532032⟩ : DyadicInterval 40),(⟨-205215700928,-205215700864⟩ : DyadicInterval 40),(⟨746108947003,746108966332⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173076221120,173076221184⟩ : DyadicInterval 40),(⟨-205504457856,-205504457792⟩ : DyadicInterval 40),(⟨746067731275,746067750605⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32428236736,-32344168896⟩ : DyadicInterval 40),(⟨778295468064,778337521248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨172921539904,173116258432⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-205560953920,-205286235584⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1504_ok : ecellOkT e1504 = true := by decide +kernel
theorem e1504_pos {a z : ℝ} (ha1 : ((348801/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((698451/4096000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1504 e1504_ok ha1 ha2 hz1 hz2 hz

-- box ['698451/4096000', '6993/40960', '3997/4000', '1599/1600']  interval_lower 31260009/1099511627776
noncomputable def e1505 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1287000640454,0,true,173116258368,173116258432⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨912022615098,0,false,-205560953920,-205560953856⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1287228542157,0,true,173310942272,173310942336⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨911794713395,0,false,-205835740800,-205835740736⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1286860023694,0,true,172996119936,172996120000⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨912163231858,0,false,-205391442944,-205391442880⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1287111219086,0,true,173210723904,173210723968⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨911912036466,0,false,-205694272832,-205694272768⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099571478395,0,true,59848960,59849024⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099451777157,0,false,-59852288,-59852224⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099583540365,0,true,71910208,71910272⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099439715187,0,false,-71914944,-71914880⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623072,0,false,-4736,-4672⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624519,0,false,-3264,-3200⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1286930327753,0,true,173056187072,173056187136⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨912092927799,0,false,-205476189952,-205476189888⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1287169889489,0,true,173260841856,173260841920⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨911853366063,0,false,-205765015232,-205765015168⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067483205065,0,false,-32504173376,-32504173312⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067564926883,0,false,-32420002816,-32420002752⟩
    { al := (698451/4096000), au := (6993/40960), zl := (3997/4000), zu := (1599/1600),
      A := ⟨187489012678,187716914381⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173116258368,173116258432⟩ : DyadicInterval 40),(⟨-205560953920,-205560953856⟩ : DyadicInterval 40),(⟨746059662284,746059681614⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173310942272,173310942336⟩ : DyadicInterval 40),(⟨-205835740800,-205835740736⟩ : DyadicInterval 40),(⟨746020392743,746020412073⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172996119936,172996120000⟩ : DyadicInterval 40),(⟨-205391442944,-205391442880⟩ : DyadicInterval 40),(⟨746083867589,746083886919⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173210723904,173210723968⟩ : DyadicInterval 40),(⟨-205694272832,-205694272768⟩ : DyadicInterval 40),(⟨746040614674,746040634003⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨59850619,71912589⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59848960,59849024⟩ : DyadicInterval 40),(⟨-59852288,-59852224⟩ : DyadicInterval 40),(⟨762123381958,762123401287⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨71910208,71910272⟩ : DyadicInterval 40),(⟨-71914944,-71914880⟩ : DyadicInterval 40),(⟨762123381216,762123400545⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4736,-3200⟩ : DyadicInterval 40),(⟨762123385216,762123405248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨187418699977,187658261713⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173056187072,173056187136⟩ : DyadicInterval 40),(⟨-205476189952,-205476189888⟩ : DyadicInterval 40),(⟨746071768011,746071787341⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173260841856,173260841920⟩ : DyadicInterval 40),(⟨-205765015232,-205765015168⟩ : DyadicInterval 40),(⟨746030503761,746030523091⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32504173376,-32420002752⟩ : DyadicInterval 40),(⟨778333384992,778375489568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨173116258368,173310942336⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-205835740800,-205560953856⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1505_ok : ecellOkT e1505 = true := by decide +kernel
theorem e1505_pos {a z : ℝ} (ha1 : ((698451/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((6993/40960 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1505 e1505_ok ha1 ha2 hz1 hz2 hz

-- box ['698451/4096000', '6993/40960', '1599/1600', '1999/2000']  interval_lower 7752799/274877906944
noncomputable def e1506 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1287000640454,0,true,173116258368,173116258432⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨912022615098,0,false,-205560953920,-205560953856⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1287228542157,0,true,173310942272,173310942336⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨911794713395,0,false,-205835740800,-205835740736⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1286883459820,0,true,173016143936,173016144000⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨912139795732,0,false,-205419692928,-205419692864⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1287134683700,0,true,173230768320,173230768384⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨911888571852,0,false,-205722564928,-205722564864⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099559508349,0,true,47879488,47879552⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099463747203,0,false,-47881664,-47881600⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099571555139,0,true,59925696,59925760⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099451700413,0,false,-59929024,-59928960⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624509,0,false,-3328,-3264⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625691,0,false,-2112,-2048⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1286942045649,0,true,173066198400,173066198464⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨912081209903,0,false,-205490315712,-205490315648⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1287181621659,0,true,173270863488,173270863552⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨911841633893,0,false,-205779161984,-205779161920⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067479200183,0,false,-32508298432,-32508298368⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067560931980,0,false,-32424117248,-32424117184⟩
    { al := (698451/4096000), au := (6993/40960), zl := (1599/1600), zu := (1999/2000),
      A := ⟨187489012678,187716914381⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173116258368,173116258432⟩ : DyadicInterval 40),(⟨-205560953920,-205560953856⟩ : DyadicInterval 40),(⟨746059662284,746059681614⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173310942272,173310942336⟩ : DyadicInterval 40),(⟨-205835740800,-205835740736⟩ : DyadicInterval 40),(⟨746020392743,746020412073⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173016143936,173016144000⟩ : DyadicInterval 40),(⟨-205419692928,-205419692864⟩ : DyadicInterval 40),(⟨746079834636,746079853965⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173230768320,173230768384⟩ : DyadicInterval 40),(⟨-205722564928,-205722564864⟩ : DyadicInterval 40),(⟨746036571295,746036590625⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨47880573,59927363⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨47879488,47879552⟩ : DyadicInterval 40),(⟨-47881664,-47881600⟩ : DyadicInterval 40),(⟨762123382554,762123401883⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59925696,59925760⟩ : DyadicInterval 40),(⟨-59929024,-59928960⟩ : DyadicInterval 40),(⟨762123381949,762123401278⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3328,-2048⟩ : DyadicInterval 40),(⟨762123384640,762123404544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨187430417873,187669993883⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173066198400,173066198464⟩ : DyadicInterval 40),(⟨-205490315712,-205490315648⟩ : DyadicInterval 40),(⟨746069750860,746069770190⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173270863488,173270863552⟩ : DyadicInterval 40),(⟨-205779161984,-205779161920⟩ : DyadicInterval 40),(⟨746028481564,746028500893⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32508298432,-32424117184⟩ : DyadicInterval 40),(⟨778335442208,778377552096⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨173116258368,173310942336⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-205835740800,-205560953856⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1506_ok : ecellOkT e1506 = true := by decide +kernel
theorem e1506_pos {a z : ℝ} (ha1 : ((698451/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((6993/40960 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1506 e1506_ok ha1 ha2 hz1 hz2 hz

-- box ['21747/128000', '696753/4096000', '1999/2000', '7997/8000']  interval_lower 11556577/549755813888
noncomputable def e1507 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1286316935348,0,true,172531999552,172531999616⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨912706320204,0,false,-204737004928,-204737004864⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1286544837051,0,true,172726786944,172726787008⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨912478418501,0,false,-205011585984,-205011585920⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1286223532694,0,true,172452158400,172452158464⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨912799722858,0,false,-204624491136,-204624491072⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1286474699598,0,true,172666844224,172666844288⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨912548555954,0,false,-204927075520,-204927075456⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099547401654,0,true,35773248,35773312⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099475853898,0,false,-35774464,-35774400⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099559387704,0,true,47758848,47758912⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099463867848,0,false,-47761024,-47760960⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625701,0,false,-2112,-2048⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626613,0,false,-1216,-1152⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1286270229408,0,true,172492075712,172492075776⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨912753026144,0,false,-204680741056,-204680740992⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1286509776945,0,true,172696823360,172696823424⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨912513478607,0,false,-204969340352,-204969340288⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067708137108,0,false,-32272516928,-32272516864⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067789566452,0,false,-32188665280,-32188665216⟩
    { al := (21747/128000), au := (696753/4096000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨186805307572,187033209275⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172531999552,172531999616⟩ : DyadicInterval 40),(⟨-204737004928,-204737004864⟩ : DyadicInterval 40),(⟨746177179050,746177198380⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172726786944,172726787008⟩ : DyadicInterval 40),(⟨-205011585984,-205011585920⟩ : DyadicInterval 40),(⟨746138055465,746138074794⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172452158400,172452158464⟩ : DyadicInterval 40),(⟨-204624491136,-204624491072⟩ : DyadicInterval 40),(⟨746193199316,746193218645⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172666844224,172666844288⟩ : DyadicInterval 40),(⟨-204927075520,-204927075456⟩ : DyadicInterval 40),(⟨746150101039,746150120368⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨35773878,47759928⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35773248,35773312⟩ : DyadicInterval 40),(⟨-35774464,-35774400⟩ : DyadicInterval 40),(⟨762123382996,762123402325⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨47758848,47758912⟩ : DyadicInterval 40),(⟨-47761024,-47760960⟩ : DyadicInterval 40),(⟨762123382565,762123401894⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2112,-1152⟩ : DyadicInterval 40),(⟨762123384192,762123403936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨186758601632,186998149169⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172492075712,172492075776⟩ : DyadicInterval 40),(⟨-204680741056,-204680740992⟩ : DyadicInterval 40),(⟨746185191030,746185210360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172696823360,172696823424⟩ : DyadicInterval 40),(⟨-204969340352,-204969340288⟩ : DyadicInterval 40),(⟨746144077357,746144096687⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32272516928,-32188665216⟩ : DyadicInterval 40),(⟨778217716224,778259661344⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨172531999552,172726787008⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-205011585984,-204737004864⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1507_ok : ecellOkT e1507 = true := by decide +kernel
theorem e1507_pos {a z : ℝ} (ha1 : ((21747/128000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((696753/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1507 e1507_ok ha1 ha2 hz1 hz2 hz

-- box ['21747/128000', '696753/4096000', '7997/8000', '3999/4000']  interval_lower 11433529/549755813888
noncomputable def e1508 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1286316935348,0,true,172531999552,172531999616⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨912706320204,0,false,-204737004928,-204737004864⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1286544837051,0,true,172726786944,172726787008⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨912478418501,0,false,-205011585984,-205011585920⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1286246883357,0,true,172472119232,172472119296⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨912776372195,0,false,-204652618496,-204652618432⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1286498078749,0,true,172686825472,172686825536⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨912525176803,0,false,-204955244928,-204955244864⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535477005,0,true,23848960,23849024⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487778547,0,false,-23849536,-23849472⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099547447883,0,true,35819520,35819584⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099475807669,0,false,-35820736,-35820672⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626609,0,false,-1216,-1152⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627259,0,false,-576,-512⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1286281904631,0,true,172502055744,172502055808⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨912741350921,0,false,-204694805248,-204694805184⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1286521466442,0,true,172706813696,172706813760⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨912501789110,0,false,-204983425408,-204983425344⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067704160829,0,false,-32276611648,-32276611584⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067785600115,0,false,-32192749440,-32192749376⟩
    { al := (21747/128000), au := (696753/4096000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨186805307572,187033209275⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172531999552,172531999616⟩ : DyadicInterval 40),(⟨-204737004928,-204737004864⟩ : DyadicInterval 40),(⟨746177179050,746177198380⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172726786944,172726787008⟩ : DyadicInterval 40),(⟨-205011585984,-205011585920⟩ : DyadicInterval 40),(⟨746138055465,746138074794⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172472119232,172472119296⟩ : DyadicInterval 40),(⟨-204652618496,-204652618432⟩ : DyadicInterval 40),(⟨746189195012,746189214341⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172686825472,172686825536⟩ : DyadicInterval 40),(⟨-204955244928,-204955244864⟩ : DyadicInterval 40),(⟨746146086362,746146105692⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨23849229,35820107⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23848960,23849024⟩ : DyadicInterval 40),(⟨-23849536,-23849472⟩ : DyadicInterval 40),(⟨762123383322,762123402651⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35819520,35819584⟩ : DyadicInterval 40),(⟨-35820736,-35820672⟩ : DyadicInterval 40),(⟨762123382993,762123402322⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1216,-512⟩ : DyadicInterval 40),(⟨762123383872,762123403488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨186770276855,187009838666⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172502055744,172502055808⟩ : DyadicInterval 40),(⟨-204694805248,-204694805184⟩ : DyadicInterval 40),(⟨746183188440,746183207770⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172706813696,172706813760⟩ : DyadicInterval 40),(⟨-204983425408,-204983425344⟩ : DyadicInterval 40),(⟨746142069707,746142089037⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32276611648,-32192749376⟩ : DyadicInterval 40),(⟨778219758304,778261708704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨172531999552,172726787008⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-205011585984,-204737004864⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1508_ok : ecellOkT e1508 = true := by decide +kernel
theorem e1508_pos {a z : ℝ} (ha1 : ((21747/128000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((696753/4096000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1508 e1508_ok ha1 ha2 hz1 hz2 hz

-- box ['696753/4096000', '348801/2048000', '1999/2000', '7997/8000']  interval_lower 801551/34359738368
noncomputable def e1509 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1286544837050,0,true,172726786944,172726787008⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨912478418502,0,false,-205011585984,-205011585920⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1286772738753,0,true,172921539904,172921539968⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨912250516799,0,false,-205286235648,-205286235584⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1286451320445,0,true,172646862528,172646862592⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨912571935107,0,false,-204898906816,-204898906752⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1286702515837,0,true,172861534720,172861534784⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨912320739715,0,false,-205201601024,-205201600960⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099547447174,0,true,35818752,35818816⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099475808378,0,false,-35820032,-35819968⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099559448409,0,true,47819584,47819648⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099463807143,0,false,-47821696,-47821632⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625696,0,false,-2112,-2048⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626610,0,false,-1216,-1152⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1286498074121,0,true,172686821504,172686821568⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨912525181431,0,false,-204955239360,-204955239296⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1286737635917,0,true,172891545088,172891545152⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨912285619635,0,false,-205243927936,-205243927872⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067630584193,0,false,-32352382784,-32352382720⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067712117673,0,false,-32268417792,-32268417728⟩
    { al := (696753/4096000), au := (348801/2048000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨187033209274,187261110977⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172726786944,172726787008⟩ : DyadicInterval 40),(⟨-205011585984,-205011585920⟩ : DyadicInterval 40),(⟨746138055465,746138074794⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172921539904,172921539968⟩ : DyadicInterval 40),(⟨-205286235648,-205286235584⟩ : DyadicInterval 40),(⟨746098883200,746098902530⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172646862528,172646862592⟩ : DyadicInterval 40),(⟨-204898906816,-204898906752⟩ : DyadicInterval 40),(⟨746154115247,746154134576⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172861534720,172861534784⟩ : DyadicInterval 40),(⟨-205201601024,-205201600960⟩ : DyadicInterval 40),(⟨746110958448,746110977778⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨35819398,47820633⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35818752,35818816⟩ : DyadicInterval 40),(⟨-35820032,-35819968⟩ : DyadicInterval 40),(⟨762123383025,762123402354⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨47819584,47819648⟩ : DyadicInterval 40),(⟨-47821696,-47821632⟩ : DyadicInterval 40),(⟨762123382528,762123401857⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2112,-1152⟩ : DyadicInterval 40),(⟨762123384192,762123403936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨186986446345,187226008141⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172686821504,172686821568⟩ : DyadicInterval 40),(⟨-204955239360,-204955239296⟩ : DyadicInterval 40),(⟨746146087167,746146106497⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172891545088,172891545152⟩ : DyadicInterval 40),(⟨-205243927936,-205243927872⟩ : DyadicInterval 40),(⟨746104919929,746104939259⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32352382784,-32268417728⟩ : DyadicInterval 40),(⟨778257592480,778299594272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨172726786944,172921539968⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-205286235648,-205011585920⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1509_ok : ecellOkT e1509 = true := by decide +kernel
theorem e1509_pos {a z : ℝ} (ha1 : ((696753/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((348801/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1509 e1509_ok ha1 ha2 hz1 hz2 hz

-- box ['696753/4096000', '348801/2048000', '7997/8000', '3999/4000']  interval_lower 25402815/1099511627776
noncomputable def e1510 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1286544837050,0,true,172726786944,172726787008⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨912478418502,0,false,-205011585984,-205011585920⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1286772738753,0,true,172921539904,172921539968⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨912250516799,0,false,-205286235648,-205286235584⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1286474699596,0,true,172666844224,172666844288⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨912548555956,0,false,-204927075520,-204927075456⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1286725923476,0,true,172881536832,172881536896⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨912297332076,0,false,-205229811840,-205229811776⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535507354,0,true,23879296,23879360⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487748198,0,false,-23879872,-23879808⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099547493413,0,true,35865024,35865088⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099475762139,0,false,-35866240,-35866176⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626606,0,false,-1216,-1152⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627258,0,false,-576,-512⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1286509763593,0,true,172696811968,172696812032⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨912513491959,0,false,-204969324224,-204969324160⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1286749339661,0,true,172901545856,172901545920⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨912273915891,0,false,-205258033664,-205258033600⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067626598217,0,false,-32356487808,-32356487744⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067708141651,0,false,-32272512256,-32272512192⟩
    { al := (696753/4096000), au := (348801/2048000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨187033209274,187261110977⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172726786944,172726787008⟩ : DyadicInterval 40),(⟨-205011585984,-205011585920⟩ : DyadicInterval 40),(⟨746138055465,746138074794⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172921539904,172921539968⟩ : DyadicInterval 40),(⟨-205286235648,-205286235584⟩ : DyadicInterval 40),(⟨746098883200,746098902530⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172666844224,172666844288⟩ : DyadicInterval 40),(⟨-204927075520,-204927075456⟩ : DyadicInterval 40),(⟨746150101039,746150120369⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172881536832,172881536896⟩ : DyadicInterval 40),(⟨-205229811840,-205229811776⟩ : DyadicInterval 40),(⟨746106933867,746106953196⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨23879578,35865637⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23879296,23879360⟩ : DyadicInterval 40),(⟨-23879872,-23879808⟩ : DyadicInterval 40),(⟨762123383321,762123402650⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35865024,35865088⟩ : DyadicInterval 40),(⟨-35866240,-35866176⟩ : DyadicInterval 40),(⟨762123382990,762123402319⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1216,-512⟩ : DyadicInterval 40),(⟨762123383872,762123403488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨186998135817,187237711885⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172696811968,172696812032⟩ : DyadicInterval 40),(⟨-204969324224,-204969324160⟩ : DyadicInterval 40),(⟨746144079623,746144098952⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172901545856,172901545920⟩ : DyadicInterval 40),(⟨-205258033664,-205258033600⟩ : DyadicInterval 40),(⟨746102907311,746102926640⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32356487808,-32272512192⟩ : DyadicInterval 40),(⟨778259639712,778301646784⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨172726786944,172921539968⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-205286235648,-205011585920⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1510_ok : ecellOkT e1510 = true := by decide +kernel
theorem e1510_pos {a z : ℝ} (ha1 : ((696753/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((348801/2048000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1510 e1510_ok ha1 ha2 hz1 hz2 hz

-- box ['21747/128000', '696753/4096000', '3999/4000', '7999/8000']  interval_lower 22620885/1099511627776
noncomputable def e1511 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1286316935348,0,true,172531999552,172531999616⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨912706320204,0,false,-204737004928,-204737004864⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1286544837051,0,true,172726786944,172726787008⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨912478418501,0,false,-205011585984,-205011585920⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1286270234021,0,true,172492079680,172492079744⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨912753021531,0,false,-204680746624,-204680746560⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1286521457900,0,true,172706806400,172706806464⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨912501797652,0,false,-204983415104,-204983415040⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523552294,0,true,11924416,11924480⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499703258,0,false,-11924608,-11924544⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535507997,0,true,23879936,23880000⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487747555,0,false,-23880512,-23880448⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627257,0,false,-576,-512⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627647,0,false,-192,-128⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1286293579883,0,true,172512035648,172512035712⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨912729675669,0,false,-204708869632,-204708869568⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1286533155972,0,true,172716803968,172716804032⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨912490099580,0,false,-204997510720,-204997510656⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067700184290,0,false,-32280706688,-32280706624⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067781633521,0,false,-32196833920,-32196833856⟩
    { al := (21747/128000), au := (696753/4096000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨186805307572,187033209275⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172531999552,172531999616⟩ : DyadicInterval 40),(⟨-204737004928,-204737004864⟩ : DyadicInterval 40),(⟨746177179050,746177198380⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172726786944,172726787008⟩ : DyadicInterval 40),(⟨-205011585984,-205011585920⟩ : DyadicInterval 40),(⟨746138055465,746138074794⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172492079680,172492079744⟩ : DyadicInterval 40),(⟨-204680746624,-204680746560⟩ : DyadicInterval 40),(⟨746185190229,746185209559⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172706806400,172706806464⟩ : DyadicInterval 40),(⟨-204983415104,-204983415040⟩ : DyadicInterval 40),(⟨746142071167,746142090496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11924518,23880221⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11924416,11924480⟩ : DyadicInterval 40),(⟨-11924608,-11924544⟩ : DyadicInterval 40),(⟨762123383518,762123402847⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23879936,23880000⟩ : DyadicInterval 40),(⟨-23880512,-23880448⟩ : DyadicInterval 40),(⟨762123383321,762123402650⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-576,-128⟩ : DyadicInterval 40),(⟨762123383680,762123403168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨186781952107,187021528196⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172512035648,172512035712⟩ : DyadicInterval 40),(⟨-204708869632,-204708869568⟩ : DyadicInterval 40),(⟨746181185745,746181205074⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172716803968,172716804032⟩ : DyadicInterval 40),(⟨-204997510720,-204997510656⟩ : DyadicInterval 40),(⟨746140061938,746140081268⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32280706688,-32196833856⟩ : DyadicInterval 40),(⟨778221800544,778263756224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨172531999552,172726787008⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-205011585984,-204737004864⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1511_ok : ecellOkT e1511 = true := by decide +kernel
theorem e1511_pos {a z : ℝ} (ha1 : ((21747/128000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((696753/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1511 e1511_ok ha1 ha2 hz1 hz2 hz

-- box ['21747/128000', '696753/4096000', '7999/8000', '1']  interval_lower 22374857/1099511627776
noncomputable def e1512 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1286316935348,0,true,172531999552,172531999616⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨912706320204,0,false,-204737004928,-204737004864⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1286544837051,0,true,172726786944,172726787008⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨912478418501,0,false,-205011585984,-205011585920⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1286293584684,0,true,172512039808,172512039872⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨912729670868,0,false,-204708875392,-204708875328⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523568047,0,true,11940160,11940224⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499687505,0,false,-11940352,-11940288⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627646,0,false,-192,-128⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1286305255173,0,true,172522015552,172522015616⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨912718000379,0,false,-204722934272,-204722934208⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1286544845530,0,true,172726794240,172726794304⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨912478410022,0,false,-205011596224,-205011596160⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1067696207493,0,false,-32284801984,-32284801920⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1067777666666,0,false,-32200918656,-32200918592⟩
    { al := (21747/128000), au := (696753/4096000), zl := (7999/8000), zu := 1,
      A := ⟨186805307572,187033209275⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172531999552,172531999616⟩ : DyadicInterval 40),(⟨-204737004928,-204737004864⟩ : DyadicInterval 40),(⟨746177179050,746177198380⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172726786944,172726787008⟩ : DyadicInterval 40),(⟨-205011585984,-205011585920⟩ : DyadicInterval 40),(⟨746138055465,746138074794⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172512039808,172512039872⟩ : DyadicInterval 40),(⟨-204708875392,-204708875328⟩ : DyadicInterval 40),(⟨746181184879,746181204208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172726786944,172726787008⟩ : DyadicInterval 40),(⟨-205011585984,-205011585920⟩ : DyadicInterval 40),(⟨746138055465,746138074794⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11940271⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11940160,11940224⟩ : DyadicInterval 40),(⟨-11940352,-11940288⟩ : DyadicInterval 40),(⟨762123383518,762123402847⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-192,0⟩ : DyadicInterval 40),(⟨762123383616,762123402976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨186793627397,187033217754⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172522015552,172522015616⟩ : DyadicInterval 40),(⟨-204722934272,-204722934208⟩ : DyadicInterval 40),(⟨746179182894,746179202223⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172726794240,172726794304⟩ : DyadicInterval 40),(⟨-205011596224,-205011596160⟩ : DyadicInterval 40),(⟨746138053989,746138073318⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32284801984,-32200918592⟩ : DyadicInterval 40),(⟨778223842912,778265803872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨172531999552,172726787008⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-205011585984,-204737004864⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1512_ok : ecellOkT e1512 = true := by decide +kernel
theorem e1512_pos {a z : ℝ} (ha1 : ((21747/128000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((696753/4096000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1512 e1512_ok ha1 ha2 hz1 hz2 hz

-- box ['696753/4096000', '348801/2048000', '3999/4000', '7999/8000']  interval_lower 12577783/549755813888
noncomputable def e1513 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1286544837050,0,true,172726786944,172726787008⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨912478418502,0,false,-205011585984,-205011585920⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1286772738753,0,true,172921539904,172921539968⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨912250516799,0,false,-205286235648,-205286235584⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1286498078747,0,true,172686825472,172686825536⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨912525176805,0,false,-204955244928,-204955244864⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1286749331115,0,true,172901538560,172901538624⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨912273924437,0,false,-205258023360,-205258023296⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523567468,0,true,11939584,11939648⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499688084,0,false,-11939776,-11939712⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535538350,0,true,23910272,23910336⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487717202,0,false,-23910848,-23910784⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627256,0,false,-576,-512⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627647,0,false,-192,-128⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1286521453090,0,true,172706802304,172706802368⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨912501802462,0,false,-204983409344,-204983409280⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1286761043434,0,true,172911546496,172911546560⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨912262212118,0,false,-205272139648,-205272139584⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067622611981,0,false,-32360593088,-32360593024⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067704165372,0,false,-32276606976,-32276606912⟩
    { al := (696753/4096000), au := (348801/2048000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨187033209274,187261110977⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172726786944,172726787008⟩ : DyadicInterval 40),(⟨-205011585984,-205011585920⟩ : DyadicInterval 40),(⟨746138055465,746138074794⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172921539904,172921539968⟩ : DyadicInterval 40),(⟨-205286235648,-205286235584⟩ : DyadicInterval 40),(⟨746098883200,746098902530⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172686825472,172686825536⟩ : DyadicInterval 40),(⟨-204955244928,-204955244864⟩ : DyadicInterval 40),(⟨746146086362,746146105692⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172901538560,172901538624⟩ : DyadicInterval 40),(⟨-205258023360,-205258023296⟩ : DyadicInterval 40),(⟨746102908775,746102928105⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11939692,23910574⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11939584,11939648⟩ : DyadicInterval 40),(⟨-11939776,-11939712⟩ : DyadicInterval 40),(⟨762123383518,762123402847⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23910272,23910336⟩ : DyadicInterval 40),(⟨-23910848,-23910784⟩ : DyadicInterval 40),(⟨762123383320,762123402649⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-576,-128⟩ : DyadicInterval 40),(⟨762123383680,762123403168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨187009825314,187249415658⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172706802304,172706802368⟩ : DyadicInterval 40),(⟨-204983409344,-204983409280⟩ : DyadicInterval 40),(⟨746142071999,746142091329⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172911546496,172911546560⟩ : DyadicInterval 40),(⟨-205272139648,-205272139584⟩ : DyadicInterval 40),(⟨746100894612,746100913941⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32360593088,-32276606912⟩ : DyadicInterval 40),(⟨778261687072,778303699424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨172726786944,172921539968⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-205286235648,-205011585920⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1513_ok : ecellOkT e1513 = true := by decide +kernel
theorem e1513_pos {a z : ℝ} (ha1 : ((696753/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((348801/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1513 e1513_ok ha1 ha2 hz1 hz2 hz

-- box ['696753/4096000', '348801/2048000', '7999/8000', '1']  interval_lower 24908607/1099511627776
noncomputable def e1514 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1286544837050,0,true,172726786944,172726787008⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨912478418502,0,false,-205011585984,-205011585920⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1286772738753,0,true,172921539904,172921539968⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨912250516799,0,false,-205286235648,-205286235584⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1286521457898,0,true,172706806400,172706806464⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨912501797654,0,false,-204983415104,-204983415040⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523583224,0,true,11955328,11955392⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499672328,0,false,-11955520,-11955456⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627646,0,false,-192,-128⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1286533142619,0,true,172716792576,172716792640⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨912490112933,0,false,-204997494592,-204997494528⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1286772747235,0,true,172921547136,172921547200⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨912250508317,0,false,-205286245824,-205286245760⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1067618625487,0,false,-32364698688,-32364698624⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1067700188833,0,false,-32280702016,-32280701952⟩
    { al := (696753/4096000), au := (348801/2048000), zl := (7999/8000), zu := 1,
      A := ⟨187033209274,187261110977⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172726786944,172726787008⟩ : DyadicInterval 40),(⟨-205011585984,-205011585920⟩ : DyadicInterval 40),(⟨746138055465,746138074794⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172921539904,172921539968⟩ : DyadicInterval 40),(⟨-205286235648,-205286235584⟩ : DyadicInterval 40),(⟨746098883200,746098902530⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172706806400,172706806464⟩ : DyadicInterval 40),(⟨-204983415104,-204983415040⟩ : DyadicInterval 40),(⟨746142071167,746142090497⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172921539904,172921539968⟩ : DyadicInterval 40),(⟨-205286235648,-205286235584⟩ : DyadicInterval 40),(⟨746098883200,746098902530⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11955448⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11955328,11955392⟩ : DyadicInterval 40),(⟨-11955520,-11955456⟩ : DyadicInterval 40),(⟨762123383518,762123402847⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-192,0⟩ : DyadicInterval 40),(⟨762123383616,762123402976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨187021514843,187261119459⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172716792576,172716792640⟩ : DyadicInterval 40),(⟨-204997494592,-204997494528⟩ : DyadicInterval 40),(⟨746140064204,746140083534⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172921547136,172921547200⟩ : DyadicInterval 40),(⟨-205286245824,-205286245760⟩ : DyadicInterval 40),(⟨746098881731,746098901060⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32364698688,-32280701952⟩ : DyadicInterval 40),(⟨778263734592,778305752224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨172726786944,172921539968⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-205286235648,-205011585920⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1514_ok : ecellOkT e1514 = true := by decide +kernel
theorem e1514_pos {a z : ℝ} (ha1 : ((696753/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((348801/2048000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1514 e1514_ok ha1 ha2 hz1 hz2 hz

-- box ['348801/2048000', '698451/4096000', '1999/2000', '7997/8000']  interval_lower 7049923/274877906944
noncomputable def e1515 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1286772738752,0,true,172921539904,172921539968⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨912250516800,0,false,-205286235648,-205286235584⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1287000640455,0,true,173116258368,173116258432⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨912022615097,0,false,-205560953920,-205560953856⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1286679108196,0,true,172841532288,172841532352⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨912344147356,0,false,-205173390976,-205173390912⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1286930332076,0,true,173056190784,173056190848⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨912092923476,0,false,-205476195136,-205476195072⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099547492703,0,true,35864320,35864384⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099475762849,0,false,-35865536,-35865472⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099559509124,0,true,47880256,47880320⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099463746428,0,false,-47882432,-47882368⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625690,0,false,-2112,-2048⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626607,0,false,-1216,-1152⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1286725918848,0,true,172881532864,172881532928⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨912297336704,0,false,-205229806272,-205229806208⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1286965494890,0,true,173086232320,173086232384⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨912057760662,0,false,-205518584128,-205518584064⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067552936836,0,false,-32432351744,-32432351680⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067634574459,0,false,-32348273408,-32348273344⟩
    { al := (348801/2048000), au := (698451/4096000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨187261110976,187489012679⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172921539904,172921539968⟩ : DyadicInterval 40),(⟨-205286235648,-205286235584⟩ : DyadicInterval 40),(⟨746098883200,746098902530⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173116258368,173116258432⟩ : DyadicInterval 40),(⟨-205560953920,-205560953856⟩ : DyadicInterval 40),(⟨746059662284,746059681614⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172841532288,172841532352⟩ : DyadicInterval 40),(⟨-205173390976,-205173390912⟩ : DyadicInterval 40),(⟨746114982510,746115001840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173056190784,173056190848⟩ : DyadicInterval 40),(⟨-205476195136,-205476195072⟩ : DyadicInterval 40),(⟨746071767245,746071786574⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨35864927,47881348⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35864320,35864384⟩ : DyadicInterval 40),(⟨-35865536,-35865472⟩ : DyadicInterval 40),(⟨762123382990,762123402319⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨47880256,47880320⟩ : DyadicInterval 40),(⟨-47882432,-47882368⟩ : DyadicInterval 40),(⟨762123382554,762123401883⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2112,-1152⟩ : DyadicInterval 40),(⟨762123384192,762123403936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨187214291072,187453867114⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172881532864,172881532928⟩ : DyadicInterval 40),(⟨-205229806272,-205229806208⟩ : DyadicInterval 40),(⟨746106934674,746106954004⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173086232320,173086232384⟩ : DyadicInterval 40),(⟨-205518584128,-205518584064⟩ : DyadicInterval 40),(⟨746065713887,746065733216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32432351744,-32348273344⟩ : DyadicInterval 40),(⟨778297520288,778339578752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨172921539904,173116258432⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-205560953920,-205286235584⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1515_ok : ecellOkT e1515 = true := by decide +kernel
theorem e1515_pos {a z : ℝ} (ha1 : ((348801/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((698451/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1515 e1515_ok ha1 ha2 hz1 hz2 hz

-- box ['348801/2048000', '698451/4096000', '7997/8000', '3999/4000']  interval_lower 13975881/549755813888
noncomputable def e1516 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1286772738752,0,true,172921539904,172921539968⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨912250516800,0,false,-205286235648,-205286235584⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1287000640455,0,true,173116258368,173116258432⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨912022615097,0,false,-205560953920,-205560953856⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1286702515835,0,true,172861534720,172861534784⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨912320739717,0,false,-205201601024,-205201600960⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1286953768202,0,true,173076213632,173076213696⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨912069487350,0,false,-205504447360,-205504447296⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535537706,0,true,23909632,23909696⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487717846,0,false,-23910208,-23910144⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099547538948,0,true,35910528,35910592⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099475716604,0,false,-35911808,-35911744⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626603,0,false,-1216,-1152⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627257,0,false,-576,-512⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1286737622559,0,true,172891533696,172891533760⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨912285632993,0,false,-205243911808,-205243911744⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1286977212871,0,true,173096243456,173096243520⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨912046042681,0,false,-205532710528,-205532710464⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067548941154,0,false,-32436467008,-32436466944⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067630588743,0,false,-32352378112,-32352378048⟩
    { al := (348801/2048000), au := (698451/4096000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨187261110976,187489012679⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172921539904,172921539968⟩ : DyadicInterval 40),(⟨-205286235648,-205286235584⟩ : DyadicInterval 40),(⟨746098883200,746098902530⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173116258368,173116258432⟩ : DyadicInterval 40),(⟨-205560953920,-205560953856⟩ : DyadicInterval 40),(⟨746059662284,746059681614⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172861534720,172861534784⟩ : DyadicInterval 40),(⟨-205201601024,-205201600960⟩ : DyadicInterval 40),(⟨746110958449,746110977778⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173076213632,173076213696⟩ : DyadicInterval 40),(⟨-205504447360,-205504447296⟩ : DyadicInterval 40),(⟨746067732808,746067752137⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨23909930,35911172⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23909632,23909696⟩ : DyadicInterval 40),(⟨-23910208,-23910144⟩ : DyadicInterval 40),(⟨762123383320,762123402649⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35910528,35910592⟩ : DyadicInterval 40),(⟨-35911808,-35911744⟩ : DyadicInterval 40),(⟨762123383019,762123402348⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1216,-512⟩ : DyadicInterval 40),(⟨762123383872,762123403488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨187225994783,187465585095⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172891533696,172891533760⟩ : DyadicInterval 40),(⟨-205243911808,-205243911744⟩ : DyadicInterval 40),(⟨746104922201,746104941531⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173096243456,173096243520⟩ : DyadicInterval 40),(⟨-205532710528,-205532710464⟩ : DyadicInterval 40),(⟨746063696327,746063715657⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32436467008,-32352378048⟩ : DyadicInterval 40),(⟨778299572640,778341636384⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨172921539904,173116258432⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-205560953920,-205286235584⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1516_ok : ecellOkT e1516 = true := by decide +kernel
theorem e1516_pos {a z : ℝ} (ha1 : ((348801/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((698451/4096000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1516 e1516_ok ha1 ha2 hz1 hz2 hz

-- box ['698451/4096000', '6993/40960', '1999/2000', '7997/8000']  interval_lower 15381311/549755813888
noncomputable def e1517 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1287000640454,0,true,173116258368,173116258432⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨912022615098,0,false,-205560953920,-205560953856⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1287228542157,0,true,173310942272,173310942336⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨911794713395,0,false,-205835740800,-205835740736⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1286906895947,0,true,173036167552,173036167616⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨912116359605,0,false,-205447943680,-205447943616⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1287158148315,0,true,173250812352,173250812416⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨911865107237,0,false,-205750857856,-205750857792⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099547538238,0,true,35909824,35909888⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099475717314,0,false,-35911104,-35911040⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099559569848,0,true,47940992,47941056⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099463685704,0,false,-47943168,-47943104⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625685,0,false,-2112,-2048⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626604,0,false,-1216,-1152⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1286953763572,0,true,173076209728,173076209792⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨912069491980,0,false,-205504441728,-205504441664⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1287193353854,0,true,173280885120,173280885184⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨911829901698,0,false,-205793308864,-205793308800⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067475195041,0,false,-32512423744,-32512423680⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067556936817,0,false,-32428232000,-32428231936⟩
    { al := (698451/4096000), au := (6993/40960), zl := (1999/2000), zu := (7997/8000),
      A := ⟨187489012678,187716914381⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173116258368,173116258432⟩ : DyadicInterval 40),(⟨-205560953920,-205560953856⟩ : DyadicInterval 40),(⟨746059662284,746059681614⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173310942272,173310942336⟩ : DyadicInterval 40),(⟨-205835740800,-205835740736⟩ : DyadicInterval 40),(⟨746020392743,746020412073⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173036167552,173036167616⟩ : DyadicInterval 40),(⟨-205447943680,-205447943616⟩ : DyadicInterval 40),(⟨746075801197,746075820526⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173250812352,173250812416⟩ : DyadicInterval 40),(⟨-205750857856,-205750857792⟩ : DyadicInterval 40),(⟨746032527455,746032546784⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨35910462,47942072⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35909824,35909888⟩ : DyadicInterval 40),(⟨-35911104,-35911040⟩ : DyadicInterval 40),(⟨762123383019,762123402348⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨47940992,47941056⟩ : DyadicInterval 40),(⟨-47943168,-47943104⟩ : DyadicInterval 40),(⟨762123382549,762123401878⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2112,-1152⟩ : DyadicInterval 40),(⟨762123384192,762123403936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨187442135796,187681726078⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173076209728,173076209792⟩ : DyadicInterval 40),(⟨-205504441728,-205504441664⟩ : DyadicInterval 40),(⟨746067733553,746067752883⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173280885120,173280885184⟩ : DyadicInterval 40),(⟨-205793308864,-205793308800⟩ : DyadicInterval 40),(⟨746026459157,746026478487⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32512423744,-32428231936⟩ : DyadicInterval 40),(⟨778337499584,778379614752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨173116258368,173310942336⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-205835740800,-205560953856⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1517_ok : ecellOkT e1517 = true := by decide +kernel
theorem e1517_pos {a z : ℝ} (ha1 : ((698451/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((6993/40960 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1517 e1517_ok ha1 ha2 hz1 hz2 hz

-- box ['698451/4096000', '6993/40960', '7997/8000', '3999/4000']  interval_lower 30513285/1099511627776
noncomputable def e1518 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1287000640454,0,true,173116258368,173116258432⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨912022615098,0,false,-205560953920,-205560953856⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1287228542157,0,true,173310942272,173310942336⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨911794713395,0,false,-205835740800,-205835740736⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1286930332074,0,true,173056190784,173056190848⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨912092923478,0,false,-205476195136,-205476195072⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1287181612929,0,true,173270856064,173270856128⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨911841642623,0,false,-205779151424,-205779151360⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535568063,0,true,23939968,23940032⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487687489,0,false,-23940608,-23940544⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099547584492,0,true,35956096,35956160⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099475671060,0,false,-35957312,-35957248⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626600,0,false,-1216,-1152⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627255,0,false,-576,-512⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1286965481526,0,true,173086220928,173086220992⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨912057774026,0,false,-205518568000,-205518567936⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1287205086088,0,true,173290906688,173290906752⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨911818169464,0,false,-205807456064,-205807456000⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067471189636,0,false,-32516549376,-32516549312⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067552941394,0,false,-32432347008,-32432346944⟩
    { al := (698451/4096000), au := (6993/40960), zl := (7997/8000), zu := (3999/4000),
      A := ⟨187489012678,187716914381⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173116258368,173116258432⟩ : DyadicInterval 40),(⟨-205560953920,-205560953856⟩ : DyadicInterval 40),(⟨746059662284,746059681614⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173310942272,173310942336⟩ : DyadicInterval 40),(⟨-205835740800,-205835740736⟩ : DyadicInterval 40),(⟨746020392743,746020412073⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173056190784,173056190848⟩ : DyadicInterval 40),(⟨-205476195136,-205476195072⟩ : DyadicInterval 40),(⟨746071767245,746071786574⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173270856064,173270856128⟩ : DyadicInterval 40),(⟨-205779151424,-205779151360⟩ : DyadicInterval 40),(⟨746028483035,746028502365⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨23940287,35956716⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23939968,23940032⟩ : DyadicInterval 40),(⟨-23940608,-23940544⟩ : DyadicInterval 40),(⟨762123383350,762123402679⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35956096,35956160⟩ : DyadicInterval 40),(⟨-35957312,-35957248⟩ : DyadicInterval 40),(⟨762123382984,762123402313⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1216,-512⟩ : DyadicInterval 40),(⟨762123383872,762123403488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨187453853750,187693458312⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173086220928,173086220992⟩ : DyadicInterval 40),(⟨-205518568000,-205518567936⟩ : DyadicInterval 40),(⟨746065716166,746065735495⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173290906688,173290906752⟩ : DyadicInterval 40),(⟨-205807456064,-205807456000⟩ : DyadicInterval 40),(⟨746024436656,746024455986⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32516549376,-32432346944⟩ : DyadicInterval 40),(⟨778339557088,778381677568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨173116258368,173310942336⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-205835740800,-205560953856⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1518_ok : ecellOkT e1518 = true := by decide +kernel
theorem e1518_pos {a z : ℝ} (ha1 : ((698451/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((6993/40960 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1518 e1518_ok ha1 ha2 hz1 hz2 hz

-- box ['348801/2048000', '698451/4096000', '3999/4000', '7999/8000']  interval_lower 216433/8589934592
noncomputable def e1519 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1286772738752,0,true,172921539904,172921539968⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨912250516800,0,false,-205286235648,-205286235584⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1287000640455,0,true,173116258368,173116258432⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨912022615097,0,false,-205560953920,-205560953856⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1286725923474,0,true,172881536832,172881536896⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨912297332078,0,false,-205229811840,-205229811776⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1286977204329,0,true,173096236160,173096236224⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨912046051223,0,false,-205532700224,-205532700160⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523582645,0,true,11954752,11954816⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499672907,0,false,-11954944,-11954880⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535568708,0,true,23940608,23940672⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487686844,0,false,-23941248,-23941184⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627254,0,false,-576,-512⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627647,0,false,-192,-128⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1286749326303,0,true,172901534400,172901534464⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨912273929249,0,false,-205258017600,-205258017536⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1286988930891,0,true,173106254592,173106254656⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨912034324661,0,false,-205546837248,-205546837184⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067544945209,0,false,-32440582656,-32440582592⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067626602767,0,false,-32356483136,-32356483072⟩
    { al := (348801/2048000), au := (698451/4096000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨187261110976,187489012679⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172921539904,172921539968⟩ : DyadicInterval 40),(⟨-205286235648,-205286235584⟩ : DyadicInterval 40),(⟨746098883200,746098902530⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173116258368,173116258432⟩ : DyadicInterval 40),(⟨-205560953920,-205560953856⟩ : DyadicInterval 40),(⟨746059662284,746059681614⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172881536832,172881536896⟩ : DyadicInterval 40),(⟨-205229811840,-205229811776⟩ : DyadicInterval 40),(⟨746106933867,746106953196⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173096236160,173096236224⟩ : DyadicInterval 40),(⟨-205532700224,-205532700160⟩ : DyadicInterval 40),(⟨746063697794,746063717124⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11954869,23940932⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11954752,11954816⟩ : DyadicInterval 40),(⟨-11954944,-11954880⟩ : DyadicInterval 40),(⟨762123383518,762123402847⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23940608,23940672⟩ : DyadicInterval 40),(⟨-23941248,-23941184⟩ : DyadicInterval 40),(⟨762123383350,762123402679⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-576,-128⟩ : DyadicInterval 40),(⟨762123383680,762123403168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨187237698527,187477303115⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172901534400,172901534464⟩ : DyadicInterval 40),(⟨-205258017600,-205258017536⟩ : DyadicInterval 40),(⟨746102909647,746102928977⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173106254592,173106254656⟩ : DyadicInterval 40),(⟨-205546837248,-205546837184⟩ : DyadicInterval 40),(⟨746061678636,746061697966⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32440582656,-32356483072⟩ : DyadicInterval 40),(⟨778301625152,778343694208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨172921539904,173116258432⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-205560953920,-205286235584⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1519_ok : ecellOkT e1519 = true := by decide +kernel
theorem e1519_pos {a z : ℝ} (ha1 : ((348801/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((698451/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1519 e1519_ok ha1 ha2 hz1 hz2 hz

-- box ['348801/2048000', '698451/4096000', '7999/8000', '1']  interval_lower 27455213/1099511627776
noncomputable def e1520 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1286772738752,0,true,172921539904,172921539968⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨912250516800,0,false,-205286235648,-205286235584⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1287000640455,0,true,173116258368,173116258432⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨912022615097,0,false,-205560953920,-205560953856⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1286749331113,0,true,172901538560,172901538624⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨912273924439,0,false,-205258023360,-205258023296⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523598404,0,true,11970560,11970624⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499657148,0,false,-11970752,-11970688⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627645,0,false,-192,-128⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1286761030076,0,true,172911535104,172911535168⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨912262225476,0,false,-205272123584,-205272123520⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1287000648939,0,true,173116265600,173116265664⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨912022606613,0,false,-205560964096,-205560964032⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1067540949004,0,false,-32444698496,-32444698432⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1067622616532,0,false,-32360588416,-32360588352⟩
    { al := (348801/2048000), au := (698451/4096000), zl := (7999/8000), zu := 1,
      A := ⟨187261110976,187489012679⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172921539904,172921539968⟩ : DyadicInterval 40),(⟨-205286235648,-205286235584⟩ : DyadicInterval 40),(⟨746098883200,746098902530⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173116258368,173116258432⟩ : DyadicInterval 40),(⟨-205560953920,-205560953856⟩ : DyadicInterval 40),(⟨746059662284,746059681614⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172901538560,172901538624⟩ : DyadicInterval 40),(⟨-205258023360,-205258023296⟩ : DyadicInterval 40),(⟨746102908775,746102928105⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173116258368,173116258432⟩ : DyadicInterval 40),(⟨-205560953920,-205560953856⟩ : DyadicInterval 40),(⟨746059662284,746059681614⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11970628⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11970560,11970624⟩ : DyadicInterval 40),(⟨-11970752,-11970688⟩ : DyadicInterval 40),(⟨762123383517,762123402846⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-192,0⟩ : DyadicInterval 40),(⟨762123383616,762123402976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨187249402300,187489021163⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨172911535104,172911535168⟩ : DyadicInterval 40),(⟨-205272123584,-205272123520⟩ : DyadicInterval 40),(⟨746100896911,746100916241⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173116265600,173116265664⟩ : DyadicInterval 40),(⟨-205560964096,-205560964032⟩ : DyadicInterval 40),(⟨746059660811,746059680141⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32444698496,-32360588352⟩ : DyadicInterval 40),(⟨778303677792,778345752128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨172921539904,173116258432⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-205560953920,-205286235584⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1520_ok : ecellOkT e1520 = true := by decide +kernel
theorem e1520_pos {a z : ℝ} (ha1 : ((348801/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((698451/4096000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1520 e1520_ok ha1 ha2 hz1 hz2 hz

-- box ['698451/4096000', '6993/40960', '3999/4000', '7999/8000']  interval_lower 3783019/137438953472
noncomputable def e1521 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1287000640454,0,true,173116258368,173116258432⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨912022615098,0,false,-205560953920,-205560953856⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1287228542157,0,true,173310942272,173310942336⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨911794713395,0,false,-205835740800,-205835740736⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1286953768200,0,true,173076213632,173076213696⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨912069487352,0,false,-205504447360,-205504447296⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1287205077543,0,true,173290899328,173290899392⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨911818178009,0,false,-205807445760,-205807445696⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523597823,0,true,11969920,11969984⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499657729,0,false,-11970176,-11970112⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535599071,0,true,23971008,23971072⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487656481,0,false,-23971584,-23971520⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627253,0,false,-576,-512⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627646,0,false,-192,-128⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1286977199507,0,true,173096232064,173096232128⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨912046056045,0,false,-205532694464,-205532694400⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1287216818345,0,true,173300928128,173300928192⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨911806437207,0,false,-205821603456,-205821603392⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067467183973,0,false,-32520675264,-32520675200⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067548945712,0,false,-32436462336,-32436462272⟩
    { al := (698451/4096000), au := (6993/40960), zl := (3999/4000), zu := (7999/8000),
      A := ⟨187489012678,187716914381⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173116258368,173116258432⟩ : DyadicInterval 40),(⟨-205560953920,-205560953856⟩ : DyadicInterval 40),(⟨746059662284,746059681614⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173310942272,173310942336⟩ : DyadicInterval 40),(⟨-205835740800,-205835740736⟩ : DyadicInterval 40),(⟨746020392743,746020412073⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173076213632,173076213696⟩ : DyadicInterval 40),(⟨-205504447360,-205504447296⟩ : DyadicInterval 40),(⟨746067732808,746067752137⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173290899328,173290899392⟩ : DyadicInterval 40),(⟨-205807445760,-205807445696⟩ : DyadicInterval 40),(⟨746024438165,746024457495⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11970047,23971295⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11969920,11969984⟩ : DyadicInterval 40),(⟨-11970176,-11970112⟩ : DyadicInterval 40),(⟨762123383549,762123402878⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23971008,23971072⟩ : DyadicInterval 40),(⟨-23971584,-23971520⟩ : DyadicInterval 40),(⟨762123383317,762123402646⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-576,-128⟩ : DyadicInterval 40),(⟨762123383680,762123403168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨187465571731,187705190569⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173096232064,173096232128⟩ : DyadicInterval 40),(⟨-205532694464,-205532694400⟩ : DyadicInterval 40),(⟨746063698633,746063717962⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173300928128,173300928192⟩ : DyadicInterval 40),(⟨-205821603456,-205821603392⟩ : DyadicInterval 40),(⟨746022414049,746022433378⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32520675264,-32436462272⟩ : DyadicInterval 40),(⟨778341614752,778383740512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨173116258368,173310942336⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-205835740800,-205560953856⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1521_ok : ecellOkT e1521 = true := by decide +kernel
theorem e1521_pos {a z : ℝ} (ha1 : ((698451/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((6993/40960 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1521 e1521_ok ha1 ha2 hz1 hz2 hz

-- box ['698451/4096000', '6993/40960', '7999/8000', '1']  interval_lower 15007515/549755813888
noncomputable def e1522 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1287000640454,0,true,173116258368,173116258432⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨912022615098,0,false,-205560953920,-205560953856⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1287228542157,0,true,173310942272,173310942336⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨911794713395,0,false,-205835740800,-205835740736⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1286977204327,0,true,173096236160,173096236224⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨912046051225,0,false,-205532700224,-205532700160⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523613585,0,true,11985728,11985792⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499641967,0,false,-11985920,-11985856⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627645,0,false,-192,-128⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1286988917527,0,true,173106243136,173106243200⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨912034338025,0,false,-205546821120,-205546821056⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1287228550637,0,true,173310949568,173310949632⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨911794704915,0,false,-205835751040,-205835750976⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1067463178047,0,false,-32524801472,-32524801408⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1067544949767,0,false,-32440577920,-32440577856⟩
    { al := (698451/4096000), au := (6993/40960), zl := (7999/8000), zu := 1,
      A := ⟨187489012678,187716914381⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173116258368,173116258432⟩ : DyadicInterval 40),(⟨-205560953920,-205560953856⟩ : DyadicInterval 40),(⟨746059662284,746059681614⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173310942272,173310942336⟩ : DyadicInterval 40),(⟨-205835740800,-205835740736⟩ : DyadicInterval 40),(⟨746020392743,746020412073⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173096236160,173096236224⟩ : DyadicInterval 40),(⟨-205532700224,-205532700160⟩ : DyadicInterval 40),(⟨746063697795,746063717124⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173310942272,173310942336⟩ : DyadicInterval 40),(⟨-205835740800,-205835740736⟩ : DyadicInterval 40),(⟨746020392743,746020412073⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11985809⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11985728,11985792⟩ : DyadicInterval 40),(⟨-11985920,-11985856⟩ : DyadicInterval 40),(⟨762123383517,762123402846⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-192,0⟩ : DyadicInterval 40),(⟨762123383616,762123402976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨187477289751,187716922861⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173106243136,173106243200⟩ : DyadicInterval 40),(⟨-205546821120,-205546821056⟩ : DyadicInterval 40),(⟨746061680953,746061700282⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173310949568,173310949632⟩ : DyadicInterval 40),(⟨-205835751040,-205835750976⟩ : DyadicInterval 40),(⟨746020391256,746020410585⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32524801472,-32440577856⟩ : DyadicInterval 40),(⟨778343672544,778385803616⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨173116258368,173310942336⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-205835740800,-205560953856⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1522_ok : ecellOkT e1522 = true := by decide +kernel
theorem e1522_pos {a z : ℝ} (ha1 : ((698451/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((6993/40960 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1522 e1522_ok ha1 ha2 hz1 hz2 hz

-- box ['6993/40960', '700149/4096000', '3999/4000', '7999/8000']  interval_lower 4104769/137438953472
noncomputable def e1523 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1287228542156,0,true,173310942272,173310942336⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨911794713396,0,false,-205835740800,-205835740736⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1287456443859,0,true,173505591808,173505591872⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨911566811693,0,false,-206110596416,-206110596352⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1287181612927,0,true,173270856064,173270856128⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨911841642625,0,false,-205779151424,-205779151360⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1287432950758,0,true,173485528064,173485528128⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨911590304794,0,false,-206082259904,-206082259840⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523613005,0,true,11985152,11985216⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499642547,0,false,-11985344,-11985280⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535629439,0,true,24001344,24001408⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099487626113,0,false,-24001984,-24001920⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627252,0,false,-576,-512⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627646,0,false,-192,-128⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1287205072719,0,true,173290895232,173290895296⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨911818182833,0,false,-205807439936,-205807439872⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1287444705809,0,true,173495567232,173495567296⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨911578549743,0,false,-206096438336,-206096438272⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1067389328268,0,false,-32600871040,-32600870976⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1067471194202,0,false,-32516544640,-32516544576⟩
    { al := (6993/40960), au := (700149/4096000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨187716914380,187944816083⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173310942272,173310942336⟩ : DyadicInterval 40),(⟨-205835740800,-205835740736⟩ : DyadicInterval 40),(⟨746020392743,746020412073⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173505591808,173505591872⟩ : DyadicInterval 40),(⟨-206110596416,-206110596352⟩ : DyadicInterval 40),(⟨745981074506,745981093836⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173270856064,173270856128⟩ : DyadicInterval 40),(⟨-205779151424,-205779151360⟩ : DyadicInterval 40),(⟨746028483036,746028502365⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173485528064,173485528128⟩ : DyadicInterval 40),(⟨-206082259904,-206082259840⟩ : DyadicInterval 40),(⟨745985129851,745985149181⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11985229,24001663⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11985152,11985216⟩ : DyadicInterval 40),(⟨-11985344,-11985280⟩ : DyadicInterval 40),(⟨762123383517,762123402846⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24001344,24001408⟩ : DyadicInterval 40),(⟨-24001984,-24001920⟩ : DyadicInterval 40),(⟨762123383348,762123402677⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-576,-128⟩ : DyadicInterval 40),(⟨762123383680,762123403168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨187693444943,187933078033⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173290895232,173290895296⟩ : DyadicInterval 40),(⟨-205807439936,-205807439872⟩ : DyadicInterval 40),(⟨746024438980,746024458309⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173495567232,173495567296⟩ : DyadicInterval 40),(⟨-206096438336,-206096438272⟩ : DyadicInterval 40),(⟨745983100788,745983120117⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32600871040,-32516544576⟩ : DyadicInterval 40),(⟨778381655904,778423838400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨173310942272,173505591872⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-206110596416,-205835740736⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1523_ok : ecellOkT e1523 = true := by decide +kernel
theorem e1523_pos {a z : ℝ} (ha1 : ((6993/40960 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((700149/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1523 e1523_ok ha1 ha2 hz1 hz2 hz

-- box ['6993/40960', '700149/4096000', '7999/8000', '1']  interval_lower 32588005/1099511627776
noncomputable def e1524 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1287228542156,0,true,173310942272,173310942336⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨911794713396,0,false,-205835740800,-205835740736⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1287456443859,0,true,173505591808,173505591872⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨911566811693,0,false,-206110596416,-206110596352⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1287205077541,0,true,173290899328,173290899392⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨911818178011,0,false,-205807445760,-205807445696⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523628769,0,true,12000896,12000960⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499626783,0,false,-12001088,-12001024⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627645,0,false,-192,-128⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1287216804976,0,true,173300916736,173300916800⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨911806450576,0,false,-205821587328,-205821587264⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1287456452344,0,true,173505599040,173505599104⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨911566803208,0,false,-206110606656,-206110606592⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1067385312610,0,false,-32605007552,-32605007488⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1067467188539,0,false,-32520670592,-32520670528⟩
    { al := (6993/40960), au := (700149/4096000), zl := (7999/8000), zu := 1,
      A := ⟨187716914380,187944816083⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173310942272,173310942336⟩ : DyadicInterval 40),(⟨-205835740800,-205835740736⟩ : DyadicInterval 40),(⟨746020392743,746020412073⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173505591808,173505591872⟩ : DyadicInterval 40),(⟨-206110596416,-206110596352⟩ : DyadicInterval 40),(⟨745981074506,745981093836⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173290899328,173290899392⟩ : DyadicInterval 40),(⟨-205807445760,-205807445696⟩ : DyadicInterval 40),(⟨746024438166,746024457495⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173505591808,173505591872⟩ : DyadicInterval 40),(⟨-206110596416,-206110596352⟩ : DyadicInterval 40),(⟨745981074506,745981093836⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,12000993⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨12000896,12000960⟩ : DyadicInterval 40),(⟨-12001088,-12001024⟩ : DyadicInterval 40),(⟨762123383517,762123402846⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-192,0⟩ : DyadicInterval 40),(⟨762123383616,762123402976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨187705177200,187944824568⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173300916736,173300916800⟩ : DyadicInterval 40),(⟨-205821587328,-205821587264⟩ : DyadicInterval 40),(⟨746022416335,746022435664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨173505599040,173505599104⟩ : DyadicInterval 40),(⟨-206110606656,-206110606592⟩ : DyadicInterval 40),(⟨745981073052,745981092382⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-32605007552,-32520670528⟩ : DyadicInterval 40),(⟨778383718880,778425906656⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨173310942272,173505591872⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-206110596416,-205835740736⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1524_ok : ecellOkT e1524 = true := by decide +kernel
theorem e1524_pos {a z : ℝ} (ha1 : ((6993/40960 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((700149/4096000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1524 e1524_ok ha1 ha2 hz1 hz2 hz

-- box ['2045103/2048000', '818211/819200', '3999/4000', '7999/8000']  interval_lower 16239132519604977/549755813888
noncomputable def e1525 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨2197467940519,0,true,761345451008,761345469888⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨1555315033,9,false,-7213833573888,-7213833400448⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨2197695842223,0,true,761459476608,761459495552⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨1327413329,9,false,-7388046722432,-7388046548928⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨2197193451440,0,true,761208100736,761208119616⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨1829804112,9,false,-7035129069568,-7035128896128⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨2197558569197,0,true,761390796480,761390815424⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1464686355,9,false,-7279844943872,-7279844770432⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1107079242791,0,true,7541691008,7541691072⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1091944012761,0,false,-7593777984,-7593777920⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1117435035125,0,true,17778888832,17778888896⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1081588220427,0,false,-18071101568,-18071101504⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099219453939,0,false,-292212672,-292212608⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099459542109,0,false,-52086912,-52086848⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨2197331458659,0,true,761277159680,761277178560⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1691796893,9,false,-7121350247104,-7121350073664⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨2197627448159,0,true,761425258368,761425277312⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨1395807393,9,false,-7332806333440,-7332806160000⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨2789842837,8,false,-6571381055936,-6571380901760⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨3380990652,8,false,-6360073068032,-6360072913856⟩
    { al := (2045103/2048000), au := (818211/819200), zl := (3999/4000), zu := (7999/8000),
      A := ⟨1097956312743,1098184214447⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761345451008,761345469888⟩ : DyadicInterval 40),(⟨-7213833573888,-7213833400448⟩ : DyadicInterval 40),(⟨6418561481,6418599736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761459476608,761459495552⟩ : DyadicInterval 40),(⟨-7388046722432,-7388046548928⟩ : DyadicInterval 40),(⟨5583237107,5583275409⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761208100736,761208119616⟩ : DyadicInterval 40),(⟨-7035129069568,-7035128896128⟩ : DyadicInterval 40),(⟨7402584901,7402623176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761390796480,761390815424⟩ : DyadicInterval 40),(⟨-7279844943872,-7279844770432⟩ : DyadicInterval 40),(⟨6088531576,6088569889⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨7567615015,17923407349⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨7541691008,7541691072⟩ : DyadicInterval 40),(⟨-7593777984,-7593777920⟩ : DyadicInterval 40),(⟨762097340549,762097359879⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨17778888832,17778888896⟩ : DyadicInterval 40),(⟨-18071101568,-18071101504⟩ : DyadicInterval 40),(⟨761977290198,761977309528⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-292212672,-52086848⟩ : DyadicInterval 40),(⟨762149427040,762269509216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨1097819830883,1098115820383⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761277159680,761277178560⟩ : DyadicInterval 40),(⟨-7121350247104,-7121350073664⟩ : DyadicInterval 40),(⟨6910626730,6910664994⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761425258368,761425277312⟩ : DyadicInterval 40),(⟨-7332806333440,-7332806160000⟩ : DyadicInterval 40),(⟨5835836453,5835874761⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6571381055936,-6360072913856⟩ : DyadicInterval 40),(⟨3942159840544,4047813930848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨761345451008,761459495552⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-7388046722432,-7213833400448⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1525_ok : ecellOkT e1525 = true := by decide +kernel
theorem e1525_pos {a z : ℝ} (ha1 : ((2045103/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((818211/819200 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1525 e1525_ok ha1 ha2 hz1 hz2 hz

-- box ['2045103/2048000', '818211/819200', '7999/8000', '1']  interval_lower 5083266972602417/549755813888
noncomputable def e1526 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨2197467940519,0,true,761345451008,761345469888⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨1555315033,9,false,-7213833573888,-7213833400448⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨2197695842223,0,true,761459476608,761459495552⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨1327413329,9,false,-7388046722432,-7388046548928⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨2197330695979,0,true,761276778048,761276796928⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨1692559573,9,false,-7120854687296,-7120854513856⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1108880163141,0,true,9328847680,9328847744⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1090143092411,0,false,-9408676480,-9408676416⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431801921,0,false,-79828800,-79828736⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨2197399505661,0,true,761311208832,761311227712⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1623749891,9,false,-7166488489728,-7166488316288⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨2197695855534,0,true,761459483264,761459502208⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1327400018,9,false,-7388057748160,-7388057574656⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨2653197514,8,false,-6626598245952,-6626598091776⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨3245101842,8,false,-6405177261440,-6405177107264⟩
    { al := (2045103/2048000), au := (818211/819200), zl := (7999/8000), zu := 1,
      A := ⟨1097956312743,1098184214447⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761345451008,761345469888⟩ : DyadicInterval 40),(⟨-7213833573888,-7213833400448⟩ : DyadicInterval 40),(⟨6418561481,6418599736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761459476608,761459495552⟩ : DyadicInterval 40),(⟨-7388046722432,-7388046548928⟩ : DyadicInterval 40),(⟨5583237107,5583275409⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761276778048,761276796928⟩ : DyadicInterval 40),(⟨-7120854687296,-7120854513856⟩ : DyadicInterval 40),(⟨6913360548,6913398812⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761459476608,761459495552⟩ : DyadicInterval 40),(⟨-7388046722432,-7388046548928⟩ : DyadicInterval 40),(⟨5583237107,5583275409⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,9368535365⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨9328847680,9328847744⟩ : DyadicInterval 40),(⟨-9408676480,-9408676416⟩ : DyadicInterval 40),(⟨762083470165,762083489495⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-79828800,0⟩ : DyadicInterval 40),(⟨762123383616,762163317280⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨1097887877885,1098184227758⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761311208832,761311227712⟩ : DyadicInterval 40),(⟨-7166488489728,-7166488316288⟩ : DyadicInterval 40),(⟨6666011069,6666049329⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761459483264,761459502208⟩ : DyadicInterval 40),(⟨-7388057748160,-7388057574656⟩ : DyadicInterval 40),(⟨5583187780,5583226083⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6626598245952,-6405177107264⟩ : DyadicInterval 40),(⟨3964711937248,4075422525856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨761345451008,761459495552⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-7388046722432,-7213833400448⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1526_ok : ecellOkT e1526 = true := by decide +kernel
theorem e1526_pos {a z : ℝ} (ha1 : ((2045103/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((818211/819200 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1526 e1526_ok ha1 ha2 hz1 hz2 hz

-- box ['818211/819200', '999/1000', '3999/4000', '7999/8000']  interval_lower 9257457113914901/549755813888
noncomputable def e1527 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨2197695842222,0,true,761459476608,761459495552⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨1327413330,9,false,-7388046721600,-7388046548160⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨2197923743925,0,true,761573490368,761573509376⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627,9,false,-7595157425088,-7595157240640⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨2197421296168,0,true,761322112064,761322131008⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨1601959384,9,false,-7181343691008,-7181343517568⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨2197786442411,0,true,761504803136,761504822080⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1236813141,9,false,-7465775773056,-7465775599104⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1108107224194,0,true,8562171776,8562171840⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1090916031358,0,false,-8629371264,-8629371200⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1120488534844,0,true,20779313472,20779313536⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1078534720708,0,false,-21179591936,-21179591872⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099111422249,0,false,-400278400,-400278336⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099444430417,0,false,-67199424,-67199360⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨2197559435809,0,true,761391230080,761391249024⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1463819743,9,false,-7280495685248,-7280495511808⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨2197855373918,0,true,761539287744,761539306688⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨1167881634,9,false,-7528828902208,-7528828726400⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨2334522764,8,false,-6767289595776,-6767289439168⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨2925690650,8,false,-6519104435776,-6519104281600⟩
    { al := (818211/819200), au := (999/1000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨1098184214446,1098412116149⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761459476608,761459495552⟩ : DyadicInterval 40),(⟨-7388046721600,-7388046548160⟩ : DyadicInterval 40),(⟨5583237109,5583275413⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761573490368,761573509376⟩ : DyadicInterval 40),(⟨-7595157425088,-7595157240640⟩ : DyadicInterval 40),(⟨4728239611,4728277967⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761322112064,761322131008⟩ : DyadicInterval 40),(⟨-7181343691008,-7181343517568⟩ : DyadicInterval 40),(⟨6587379579,6587417901⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761504803136,761504822080⟩ : DyadicInterval 40),(⟨-7465775773056,-7465775599104⟩ : DyadicInterval 40),(⟨5245892562,5245930859⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨8595596418,20976907068⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨8562171776,8562171840⟩ : DyadicInterval 40),(⟨-8629371264,-8629371200⟩ : DyadicInterval 40),(⟨762089784567,762089803896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨20779313472,20779313536⟩ : DyadicInterval 40),(⟨-21179591936,-21179591872⟩ : DyadicInterval 40),(⟨761923268690,761923288020⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-400278400,-67199360⟩ : DyadicInterval 40),(⟨762156983296,762323542080⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨1098047808033,1098343746142⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761391230080,761391249024⟩ : DyadicInterval 40),(⟨-7280495685248,-7280495511808⟩ : DyadicInterval 40),(⟨6085362476,6085400789⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761539287744,761539306688⟩ : DyadicInterval 40),(⟨-7528828902208,-7528828726400⟩ : DyadicInterval 40),(⟨4987017433,4987055726⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6767289595776,-6519104281600⟩ : DyadicInterval 40),(⟨4021675524416,4145768200768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨761459476608,761573509376⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-7595157425088,-7388046548160⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1527_ok : ecellOkT e1527 = true := by decide +kernel
theorem e1527_pos {a z : ℝ} (ha1 : ((818211/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1527 e1527_ok ha1 ha2 hz1 hz2 hz

-- box ['3/20', '1229649/8192000', '999/1000', '7993/8000']  interval_lower 14294117/137438953472
noncomputable def e1528 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1264438371942,0,true,153669880704,153669880768⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨934584883610,0,false,-178691452736,-178691452672⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1264552322794,0,true,153768963968,153768964032⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨934470932758,0,false,-178825520768,-178825520704⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1264273445197,0,true,153526456832,153526456896⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨934749810355,0,false,-178497438400,-178497438336⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1264407912186,0,true,153643393664,153643393728⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨934615343366,0,false,-178655618304,-178655618240⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099584976755,0,true,73346496,73346560⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099438278797,0,false,-73351488,-73351424⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099595515752,0,true,83884736,83884800⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099427739800,0,false,-83891200,-83891136⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621375,0,false,-6464,-6400⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622883,0,false,-4928,-4864⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1264355904872,0,true,153598167872,153598167936⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨934667350680,0,false,-178594436928,-178594436864⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1264480122360,0,true,153706184832,153706184896⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨934543133192,0,false,-178740571968,-178740571904⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074760089440,0,false,-25034387136,-25034387072⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074797350087,0,false,-24996268992,-24996268928⟩
    { al := (3/20), au := (1229649/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨164926744166,165040695018⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153669880704,153669880768⟩ : DyadicInterval 40),(⟨-178691452736,-178691452672⟩ : DyadicInterval 40),(⟨749707069559,749707088889⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153768963968,153768964032⟩ : DyadicInterval 40),(⟨-178825520768,-178825520704⟩ : DyadicInterval 40),(⟨749689840933,749689860262⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153526456832,153526456896⟩ : DyadicInterval 40),(⟨-178497438400,-178497438336⟩ : DyadicInterval 40),(⟨749731983985,749732003314⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153643393664,153643393728⟩ : DyadicInterval 40),(⟨-178655618304,-178655618240⟩ : DyadicInterval 40),(⟨749711672811,749711692141⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨73348979,83887976⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73346496,73346560⟩ : DyadicInterval 40),(⟨-73351488,-73351424⟩ : DyadicInterval 40),(⟨762123381154,762123400484⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨83884736,83884800⟩ : DyadicInterval 40),(⟨-83891200,-83891136⟩ : DyadicInterval 40),(⟨762123380383,762123399712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6464,-4864⟩ : DyadicInterval 40),(⟨762123386048,762123406112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨164844277096,164968494584⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153598167872,153598167936⟩ : DyadicInterval 40),(⟨-178594436928,-178594436864⟩ : DyadicInterval 40),(⟨749719530500,749719549830⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153706184832,153706184896⟩ : DyadicInterval 40),(⟨-178740571968,-178740571904⟩ : DyadicInterval 40),(⟨749700758561,749700777891⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25034387136,-24996268928⟩ : DyadicInterval 40),(⟨774621518080,774640596448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨153669880704,153768964032⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-178825520768,-178691452672⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1528_ok : ecellOkT e1528 = true := by decide +kernel
theorem e1528_pos {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1229649/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1528 e1528_ok ha1 ha2 hz1 hz2 hz

-- box ['1229649/8192000', '615249/4096000', '999/1000', '7993/8000']  interval_lower 115288569/1099511627776
noncomputable def e1529 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1264552322793,0,true,153768963968,153768964032⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨934470932759,0,false,-178825520768,-178825520704⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1264666273645,0,true,153868038272,153868038336⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨934356981907,0,false,-178959605120,-178959605056⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1264387282097,0,true,153625453888,153625453952⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨934635973455,0,false,-178631348672,-178631348608⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1264521763330,0,true,153742392576,153742392640⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨934501492222,0,false,-178789564672,-178789564608⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585029118,0,true,73398848,73398912⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099438226434,0,false,-73403840,-73403776⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099595575600,0,true,83944576,83944640⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099427679952,0,false,-83951040,-83950976⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621366,0,false,-6464,-6400⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622876,0,false,-4928,-4864⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1264469799003,0,true,153697208256,153697208320⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨934553456549,0,false,-178728426368,-178728426304⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1264594023356,0,true,153805221440,153805221504⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨934429232196,0,false,-178874587328,-178874587264⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074725898692,0,false,-25069365824,-25069365760⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074763187135,0,false,-25031218112,-25031218048⟩
    { al := (1229649/8192000), au := (615249/4096000), zl := (999/1000), zu := (7993/8000),
      A := ⟨165040695017,165154645869⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153768963968,153768964032⟩ : DyadicInterval 40),(⟨-178825520768,-178825520704⟩ : DyadicInterval 40),(⟨749689840933,749689860263⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153868038272,153868038336⟩ : DyadicInterval 40),(⟨-178959605120,-178959605056⟩ : DyadicInterval 40),(⟨749672600231,749672619560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153625453888,153625453952⟩ : DyadicInterval 40),(⟨-178631348672,-178631348608⟩ : DyadicInterval 40),(⟨749714790064,749714809394⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153742392576,153742392640⟩ : DyadicInterval 40),(⟨-178789564672,-178789564608⟩ : DyadicInterval 40),(⟨749694462525,749694481854⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨73401342,83947824⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73398848,73398912⟩ : DyadicInterval 40),(⟨-73403840,-73403776⟩ : DyadicInterval 40),(⟨762123381147,762123400477⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨83944576,83944640⟩ : DyadicInterval 40),(⟨-83951040,-83950976⟩ : DyadicInterval 40),(⟨762123380374,762123399703⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6464,-4864⟩ : DyadicInterval 40),(⟨762123386048,762123406112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨164958171227,165082395580⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153697208256,153697208320⟩ : DyadicInterval 40),(⟨-178728426368,-178728426304⟩ : DyadicInterval 40),(⟨749702319192,749702338521⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153805221440,153805221504⟩ : DyadicInterval 40),(⟨-178874587328,-178874587264⟩ : DyadicInterval 40),(⟨749683533073,749683552402⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25069365824,-25031218048⟩ : DyadicInterval 40),(⟨774638992640,774658085792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨153768963968,153868038336⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-178959605120,-178825520704⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1529_ok : ecellOkT e1529 = true := by decide +kernel
theorem e1529_pos {a z : ℝ} (ha1 : ((1229649/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((615249/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1529 e1529_ok ha1 ha2 hz1 hz2 hz

-- box ['3/20', '1229649/8192000', '7993/8000', '3997/4000']  interval_lower 114217629/1099511627776
noncomputable def e1530 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1264438371942,0,true,153669880704,153669880768⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨934584883610,0,false,-178691452736,-178691452672⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1264552322794,0,true,153768963968,153768964032⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨934470932758,0,false,-178825520768,-178825520704⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1264294061040,0,true,153544385856,153544385920⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨934729194512,0,false,-178521688320,-178521688256⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1264428542273,0,true,153661333184,153661333248⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨934594713279,0,false,-178679888512,-178679888448⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099574498422,0,true,62868800,62868864⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099448757130,0,false,-62872448,-62872384⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585029940,0,true,73399680,73399744⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099438225612,0,false,-73404672,-73404608⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622875,0,false,-4928,-4864⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624182,0,false,-3648,-3584⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1264366212637,0,true,153607131712,153607131776⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨934657042915,0,false,-178606562752,-178606562688⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1264490437267,0,true,153715153984,153715154048⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨934532818285,0,false,-178752707776,-178752707712⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074756994088,0,false,-25037553728,-25037553664⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074794259207,0,false,-24999430976,-24999430912⟩
    { al := (3/20), au := (1229649/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨164926744166,165040695018⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153669880704,153669880768⟩ : DyadicInterval 40),(⟨-178691452736,-178691452672⟩ : DyadicInterval 40),(⟨749707069559,749707088889⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153768963968,153768964032⟩ : DyadicInterval 40),(⟨-178825520768,-178825520704⟩ : DyadicInterval 40),(⟨749689840933,749689860262⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153544385856,153544385920⟩ : DyadicInterval 40),(⟨-178521688320,-178521688256⟩ : DyadicInterval 40),(⟨749728871056,749728890386⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153661333184,153661333248⟩ : DyadicInterval 40),(⟨-178679888512,-178679888448⟩ : DyadicInterval 40),(⟨749708555159,749708574488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨62870646,73402164⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨62868800,62868864⟩ : DyadicInterval 40),(⟨-62872448,-62872384⟩ : DyadicInterval 40),(⟨762123381780,762123401110⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73399680,73399744⟩ : DyadicInterval 40),(⟨-73404672,-73404608⟩ : DyadicInterval 40),(⟨762123381147,762123400476⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4928,-3584⟩ : DyadicInterval 40),(⟨762123385408,762123405344⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨164854584861,164978809491⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153607131712,153607131776⟩ : DyadicInterval 40),(⟨-178606562752,-178606562688⟩ : DyadicInterval 40),(⟨749717973331,749717992660⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153715153984,153715154048⟩ : DyadicInterval 40),(⟨-178752707776,-178752707712⟩ : DyadicInterval 40),(⟨749699199117,749699218447⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25037553728,-24999430912⟩ : DyadicInterval 40),(⟨774623099072,774642179744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨153669880704,153768964032⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-178825520768,-178691452672⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1530_ok : ecellOkT e1530 = true := by decide +kernel
theorem e1530_pos {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1229649/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1530 e1530_ok ha1 ha2 hz1 hz2 hz

-- box ['1229649/8192000', '615249/4096000', '7993/8000', '3997/4000']  interval_lower 115152465/1099511627776
noncomputable def e1531 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1264552322793,0,true,153768963968,153768964032⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨934470932759,0,false,-178825520768,-178825520704⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1264666273645,0,true,153868038272,153868038336⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨934356981907,0,false,-178959605120,-178959605056⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1264407912184,0,true,153643393664,153643393728⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨934615343368,0,false,-178655618304,-178655618240⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1264542407661,0,true,153760342848,153760342912⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨934480847891,0,false,-178813854528,-178813854464⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099574543306,0,true,62913728,62913792⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099448712246,0,false,-62917376,-62917312⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585082308,0,true,73452032,73452096⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099438173244,0,false,-73457024,-73456960⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622868,0,false,-4928,-4864⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624176,0,false,-3648,-3584⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1264480113631,0,true,153706177280,153706177344⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨934543141921,0,false,-178740561728,-178740561664⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1264604345385,0,true,153814195968,153814196032⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨934418910167,0,false,-178886732992,-178886732928⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074722799064,0,false,-25072536960,-25072536896⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074760092060,0,false,-25034384448,-25034384384⟩
    { al := (1229649/8192000), au := (615249/4096000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨165040695017,165154645869⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153768963968,153768964032⟩ : DyadicInterval 40),(⟨-178825520768,-178825520704⟩ : DyadicInterval 40),(⟨749689840933,749689860263⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153868038272,153868038336⟩ : DyadicInterval 40),(⟨-178959605120,-178959605056⟩ : DyadicInterval 40),(⟨749672600231,749672619560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153643393664,153643393728⟩ : DyadicInterval 40),(⟨-178655618304,-178655618240⟩ : DyadicInterval 40),(⟨749711672812,749711692141⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153760342848,153760342912⟩ : DyadicInterval 40),(⟨-178813854528,-178813854464⟩ : DyadicInterval 40),(⟨749691340514,749691359843⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨62915530,73454532⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨62913728,62913792⟩ : DyadicInterval 40),(⟨-62917376,-62917312⟩ : DyadicInterval 40),(⟨762123381775,762123401104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73452032,73452096⟩ : DyadicInterval 40),(⟨-73457024,-73456960⟩ : DyadicInterval 40),(⟨762123381140,762123400469⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4928,-3584⟩ : DyadicInterval 40),(⟨762123385408,762123405344⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨164968485855,165092717609⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153706177280,153706177344⟩ : DyadicInterval 40),(⟨-178740561728,-178740561664⟩ : DyadicInterval 40),(⟨749700759871,749700779201⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153814195968,153814196032⟩ : DyadicInterval 40),(⟨-178886732992,-178886732928⟩ : DyadicInterval 40),(⟨749681971461,749681990791⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25072536960,-25034384384⟩ : DyadicInterval 40),(⟨774640575808,774659671360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨153768963968,153868038336⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-178959605120,-178825520704⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1531_ok : ecellOkT e1531 = true := by decide +kernel
theorem e1531_pos {a z : ℝ} (ha1 : ((1229649/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((615249/4096000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1531 e1531_ok ha1 ha2 hz1 hz2 hz

-- box ['615249/4096000', '1231347/8192000', '999/1000', '7993/8000']  interval_lower 14528265/137438953472
noncomputable def e1532 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1264666273644,0,true,153868038272,153868038336⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨934356981908,0,false,-178959605120,-178959605056⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1264780224496,0,true,153967103616,153967103680⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨934243031056,0,false,-179093705792,-179093705728⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1264501118998,0,true,153724442048,153724442112⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨934522136554,0,false,-178765275264,-178765275200⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1264635614474,0,true,153841382592,153841382656⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨934387641078,0,false,-178923527296,-178923527232⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585081485,0,true,73451200,73451264⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099438174067,0,false,-73456192,-73456128⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099595635453,0,true,84004416,84004480⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099427620099,0,false,-84010944,-84010880⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621357,0,false,-6464,-6400⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622869,0,false,-4928,-4864⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1264583692879,0,true,153796239488,153796239552⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨934439562673,0,false,-178862431872,-178862431808⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1264707924354,0,true,153904249152,153904249216⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨934315331198,0,false,-179008618944,-179008618880⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074691684345,0,false,-25104369792,-25104369728⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074729000664,0,false,-25066192320,-25066192256⟩
    { al := (615249/4096000), au := (1231347/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨165154645868,165268596720⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153868038272,153868038336⟩ : DyadicInterval 40),(⟨-178959605120,-178959605056⟩ : DyadicInterval 40),(⟨749672600231,749672619561⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153967103616,153967103680⟩ : DyadicInterval 40),(⟨-179093705792,-179093705728⟩ : DyadicInterval 40),(⟨749655347452,749655366781⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153724442048,153724442112⟩ : DyadicInterval 40),(⟨-178765275264,-178765275200⟩ : DyadicInterval 40),(⟨749697584080,749697603410⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153841382592,153841382656⟩ : DyadicInterval 40),(⟨-178923527296,-178923527232⟩ : DyadicInterval 40),(⟨749677240141,749677259470⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨73453709,84007677⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73451200,73451264⟩ : DyadicInterval 40),(⟨-73456192,-73456128⟩ : DyadicInterval 40),(⟨762123381140,762123400470⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨84004416,84004480⟩ : DyadicInterval 40),(⟨-84010944,-84010880⟩ : DyadicInterval 40),(⟨762123380397,762123399726⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6464,-4864⟩ : DyadicInterval 40),(⟨762123386048,762123406112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165072065103,165196296578⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153796239488,153796239552⟩ : DyadicInterval 40),(⟨-178862431872,-178862431808⟩ : DyadicInterval 40),(⟨749685095872,749685115202⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153904249152,153904249216⟩ : DyadicInterval 40),(⟨-179008618944,-179008618880⟩ : DyadicInterval 40),(⟨749666295465,749666314794⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25104369792,-25066192256⟩ : DyadicInterval 40),(⟨774656479744,774675587776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨153868038272,153967103680⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179093705792,-178959605056⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1532_ok : ecellOkT e1532 = true := by decide +kernel
theorem e1532_pos {a z : ℝ} (ha1 : ((615249/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1231347/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1532 e1532_ok ha1 ha2 hz1 hz2 hz

-- box ['1231347/8192000', '308049/2048000', '999/1000', '7993/8000']  interval_lower 58582903/549755813888
noncomputable def e1533 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1264780224495,0,true,153967103616,153967103680⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨934243031057,0,false,-179093705792,-179093705728⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1264894175347,0,true,154066160064,154066160128⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨934129080205,0,false,-179227822848,-179227822784⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1264614955898,0,true,153823421248,153823421312⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨934408299654,0,false,-178899218176,-178899218112⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1264749465618,0,true,153940363712,153940363776⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨934273789934,0,false,-179057506240,-179057506176⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585133856,0,true,73503616,73503680⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099438121696,0,false,-73508544,-73508480⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099595695309,0,true,84064256,84064320⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099427560243,0,false,-84070784,-84070720⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621348,0,false,-6464,-6400⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622862,0,false,-4928,-4864⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1264697586493,0,true,153895261568,153895261632⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨934325669059,0,false,-178996453312,-178996453248⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1264821825355,0,true,154003267904,154003267968⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨934201430197,0,false,-179142667008,-179142666944⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074657446398,0,false,-25139399040,-25139398976⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074694790675,0,false,-25101191744,-25101191680⟩
    { al := (1231347/8192000), au := (308049/2048000), zl := (999/1000), zu := (7993/8000),
      A := ⟨165268596719,165382547571⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153967103616,153967103680⟩ : DyadicInterval 40),(⟨-179093705792,-179093705728⟩ : DyadicInterval 40),(⟨749655347452,749655366781⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154066160064,154066160128⟩ : DyadicInterval 40),(⟨-179227822848,-179227822784⟩ : DyadicInterval 40),(⟨749638082584,749638101914⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153823421248,153823421312⟩ : DyadicInterval 40),(⟨-178899218176,-178899218112⟩ : DyadicInterval 40),(⟨749680366069,749680385399⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153940363712,153940363776⟩ : DyadicInterval 40),(⟨-179057506240,-179057506176⟩ : DyadicInterval 40),(⟨749660005685,749660025014⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨73506080,84067533⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73503616,73503680⟩ : DyadicInterval 40),(⟨-73508544,-73508480⟩ : DyadicInterval 40),(⟨762123381101,762123400431⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨84064256,84064320⟩ : DyadicInterval 40),(⟨-84070784,-84070720⟩ : DyadicInterval 40),(⟨762123380388,762123399717⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6464,-4864⟩ : DyadicInterval 40),(⟨762123386048,762123406112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165185958717,165310197579⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153895261568,153895261632⟩ : DyadicInterval 40),(⟨-178996453312,-178996453248⟩ : DyadicInterval 40),(⟨749667860487,749667879817⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154003267904,154003267968⟩ : DyadicInterval 40),(⟨-179142667008,-179142666944⟩ : DyadicInterval 40),(⟨749649045854,749649065184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25139399040,-25101191680⟩ : DyadicInterval 40),(⟨774673979456,774693102400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨153967103616,154066160128⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179227822848,-179093705728⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1533_ok : ecellOkT e1533 = true := by decide +kernel
theorem e1533_pos {a z : ℝ} (ha1 : ((1231347/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((308049/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1533 e1533_ok ha1 ha2 hz1 hz2 hz

-- box ['615249/4096000', '1231347/8192000', '7993/8000', '3997/4000']  interval_lower 14511239/137438953472
noncomputable def e1534 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1264666273644,0,true,153868038272,153868038336⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨934356981908,0,false,-178959605120,-178959605056⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1264780224496,0,true,153967103616,153967103680⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨934243031056,0,false,-179093705792,-179093705728⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1264521763328,0,true,153742392576,153742392640⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨934501492224,0,false,-178789564608,-178789564544⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1264656273049,0,true,153859343616,153859343680⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨934366982503,0,false,-178947836864,-178947836800⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099574588193,0,true,62958592,62958656⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099448667359,0,false,-62962240,-62962176⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585134679,0,true,73504384,73504448⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099438120873,0,false,-73509376,-73509312⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622861,0,false,-4928,-4864⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624171,0,false,-3648,-3584⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1264594014884,0,true,153805214080,153805214144⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨934429240668,0,false,-178874577344,-178874577280⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1264718253506,0,true,153913229056,153913229120⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨934305002046,0,false,-179020774464,-179020774400⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074688580437,0,false,-25107545408,-25107545344⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074725901237,0,false,-25069363200,-25069363136⟩
    { al := (615249/4096000), au := (1231347/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨165154645868,165268596720⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153868038272,153868038336⟩ : DyadicInterval 40),(⟨-178959605120,-178959605056⟩ : DyadicInterval 40),(⟨749672600231,749672619561⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153967103616,153967103680⟩ : DyadicInterval 40),(⟨-179093705792,-179093705728⟩ : DyadicInterval 40),(⟨749655347452,749655366781⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153742392576,153742392640⟩ : DyadicInterval 40),(⟨-178789564608,-178789564544⟩ : DyadicInterval 40),(⟨749694462498,749694481827⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153859343616,153859343680⟩ : DyadicInterval 40),(⟨-178947836864,-178947836800⟩ : DyadicInterval 40),(⟨749674113792,749674133121⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨62960417,73506903⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨62958592,62958656⟩ : DyadicInterval 40),(⟨-62962240,-62962176⟩ : DyadicInterval 40),(⟨762123381770,762123401099⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73504384,73504448⟩ : DyadicInterval 40),(⟨-73509376,-73509312⟩ : DyadicInterval 40),(⟨762123381133,762123400462⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4928,-3584⟩ : DyadicInterval 40),(⟨762123385408,762123405344⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165082387108,165206625730⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153805214080,153805214144⟩ : DyadicInterval 40),(⟨-178874577344,-178874577280⟩ : DyadicInterval 40),(⟨749683534345,749683553674⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153913229056,153913229120⟩ : DyadicInterval 40),(⟨-179020774464,-179020774400⟩ : DyadicInterval 40),(⟨749664731683,749664751013⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25107545408,-25069363136⟩ : DyadicInterval 40),(⟨774658065184,774677175584⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨153868038272,153967103680⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179093705792,-178959605056⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1534_ok : ecellOkT e1534 = true := by decide +kernel
theorem e1534_pos {a z : ℝ} (ha1 : ((615249/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1231347/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1534 e1534_ok ha1 ha2 hz1 hz2 hz

-- box ['1231347/8192000', '308049/2048000', '7993/8000', '3997/4000']  interval_lower 117029637/1099511627776
noncomputable def e1535 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1264780224495,0,true,153967103616,153967103680⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨934243031057,0,false,-179093705792,-179093705728⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1264894175347,0,true,154066160064,154066160128⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨934129080205,0,false,-179227822848,-179227822784⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1264635614472,0,true,153841382592,153841382656⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨934387641080,0,false,-178923527296,-178923527232⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1264770138437,0,true,153958335488,153958335552⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨934253117115,0,false,-179081835584,-179081835520⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099574633081,0,true,63003456,63003520⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099448622471,0,false,-63007168,-63007104⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585187053,0,true,73556800,73556864⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099438068499,0,false,-73561792,-73561728⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622854,0,false,-4928,-4864⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624166,0,false,-3648,-3584⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1264707915877,0,true,153904241792,153904241856⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨934315339675,0,false,-179008609024,-179008608960⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1264832161625,0,true,154012253248,154012253312⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨934191093927,0,false,-179154832384,-179154832320⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074654338210,0,false,-25142579072,-25142579008⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074691686893,0,false,-25104367168,-25104367104⟩
    { al := (1231347/8192000), au := (308049/2048000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨165268596719,165382547571⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153967103616,153967103680⟩ : DyadicInterval 40),(⟨-179093705792,-179093705728⟩ : DyadicInterval 40),(⟨749655347452,749655366781⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154066160064,154066160128⟩ : DyadicInterval 40),(⟨-179227822848,-179227822784⟩ : DyadicInterval 40),(⟨749638082584,749638101914⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153841382592,153841382656⟩ : DyadicInterval 40),(⟨-178923527296,-178923527232⟩ : DyadicInterval 40),(⟨749677240141,749677259470⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153958335488,153958335552⟩ : DyadicInterval 40),(⟨-179081835584,-179081835520⟩ : DyadicInterval 40),(⟨749656875020,749656894349⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨63005305,73559277⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63003456,63003520⟩ : DyadicInterval 40),(⟨-63007168,-63007104⟩ : DyadicInterval 40),(⟨762123381797,762123401126⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73556800,73556864⟩ : DyadicInterval 40),(⟨-73561792,-73561728⟩ : DyadicInterval 40),(⟨762123381126,762123400455⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4928,-3584⟩ : DyadicInterval 40),(⟨762123385408,762123405344⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165196288101,165320533849⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153904241792,153904241856⟩ : DyadicInterval 40),(⟨-179008609024,-179008608960⟩ : DyadicInterval 40),(⟨749666296766,749666316096⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154012253248,154012253312⟩ : DyadicInterval 40),(⟨-179154832384,-179154832320⟩ : DyadicInterval 40),(⟨749647479863,749647499192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25142579072,-25104367104⟩ : DyadicInterval 40),(⟨774675567168,774694692416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨153967103616,154066160128⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179227822848,-179093705728⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1535_ok : ecellOkT e1535 = true := by decide +kernel
theorem e1535_pos {a z : ℝ} (ha1 : ((1231347/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((308049/2048000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1535 e1535_ok ha1 ha2 hz1 hz2 hz

-- box ['3/20', '1229649/8192000', '3997/4000', '1599/1600']  interval_lower 57041115/549755813888
noncomputable def e1536 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1264438371942,0,true,153669880704,153669880768⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨934584883610,0,false,-178691452736,-178691452672⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1264552322794,0,true,153768963968,153768964032⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨934470932758,0,false,-178825520768,-178825520704⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1264314676883,0,true,153562314560,153562314624⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨934708578669,0,false,-178545938752,-178545938688⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1264449172360,0,true,153679272384,153679272448⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨934574083192,0,false,-178704159168,-178704159104⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564020048,0,true,52390976,52391040⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099459235504,0,false,-52393536,-52393472⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099574544084,0,true,62914496,62914560⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099448711468,0,false,-62918144,-62918080⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624175,0,false,-3648,-3584⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625280,0,false,-2560,-2496⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1264376520677,0,true,153616095680,153616095744⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨934646734875,0,false,-178618688960,-178618688896⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1264500752196,0,true,153724123072,153724123136⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨934522503356,0,false,-178764843712,-178764843648⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074753898535,0,false,-25040720640,-25040720576⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074791168052,0,false,-25002593216,-25002593152⟩
    { al := (3/20), au := (1229649/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨164926744166,165040695018⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153669880704,153669880768⟩ : DyadicInterval 40),(⟨-178691452736,-178691452672⟩ : DyadicInterval 40),(⟨749707069559,749707088889⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153768963968,153768964032⟩ : DyadicInterval 40),(⟨-178825520768,-178825520704⟩ : DyadicInterval 40),(⟨749689840933,749689860262⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153562314560,153562314624⟩ : DyadicInterval 40),(⟨-178545938752,-178545938688⟩ : DyadicInterval 40),(⟨749725757738,749725777068⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153679272384,153679272448⟩ : DyadicInterval 40),(⟨-178704159168,-178704159104⟩ : DyadicInterval 40),(⟨749705437089,749705456418⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨52392272,62916308⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52390976,52391040⟩ : DyadicInterval 40),(⟨-52393536,-52393472⟩ : DyadicInterval 40),(⟨762123382335,762123401664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨62914496,62914560⟩ : DyadicInterval 40),(⟨-62918144,-62918080⟩ : DyadicInterval 40),(⟨762123381775,762123401104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3648,-2496⟩ : DyadicInterval 40),(⟨762123384864,762123404704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨164864892901,164989124420⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153616095680,153616095744⟩ : DyadicInterval 40),(⟨-178618688960,-178618688896⟩ : DyadicInterval 40),(⟨749716416011,749716435341⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153724123072,153724123136⟩ : DyadicInterval 40),(⟨-178764843712,-178764843648⟩ : DyadicInterval 40),(⟨749697639563,749697658893⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25040720640,-25002593152⟩ : DyadicInterval 40),(⟨774624680192,774643763200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨153669880704,153768964032⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-178825520768,-178691452672⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1536_ok : ecellOkT e1536 = true := by decide +kernel
theorem e1536_pos {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1229649/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1536 e1536_ok ha1 ha2 hz1 hz2 hz

-- box ['1229649/8192000', '615249/4096000', '3997/4000', '1599/1600']  interval_lower 115016431/1099511627776
noncomputable def e1537 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1264552322793,0,true,153768963968,153768964032⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨934470932759,0,false,-178825520768,-178825520704⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1264666273645,0,true,153868038272,153868038336⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨934356981907,0,false,-178959605120,-178959605056⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1264428542271,0,true,153661333184,153661333248⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨934594713281,0,false,-178679888512,-178679888448⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1264563051992,0,true,153778292800,153778292864⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨934460203560,0,false,-178838144960,-178838144896⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564057451,0,true,52428416,52428480⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099459198101,0,false,-52430976,-52430912⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099574588971,0,true,62959360,62959424⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099448666581,0,false,-62963008,-62962944⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624170,0,false,-3648,-3584⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625276,0,false,-2560,-2496⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1264490428538,0,true,153715146432,153715146496⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨934532827014,0,false,-178752697536,-178752697472⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1264614667433,0,true,153823170496,153823170560⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨934408588119,0,false,-178898878784,-178898878720⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074719699236,0,false,-25075708288,-25075708224⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074756996708,0,false,-25037551104,-25037551040⟩
    { al := (1229649/8192000), au := (615249/4096000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨165040695017,165154645869⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153768963968,153768964032⟩ : DyadicInterval 40),(⟨-178825520768,-178825520704⟩ : DyadicInterval 40),(⟨749689840933,749689860263⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153868038272,153868038336⟩ : DyadicInterval 40),(⟨-178959605120,-178959605056⟩ : DyadicInterval 40),(⟨749672600231,749672619560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153661333184,153661333248⟩ : DyadicInterval 40),(⟨-178679888512,-178679888448⟩ : DyadicInterval 40),(⟨749708555159,749708574488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153778292800,153778292864⟩ : DyadicInterval 40),(⟨-178838144960,-178838144896⟩ : DyadicInterval 40),(⟨749688218139,749688237468⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨52429675,62961195⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52428416,52428480⟩ : DyadicInterval 40),(⟨-52430976,-52430912⟩ : DyadicInterval 40),(⟨762123382331,762123401660⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨62959360,62959424⟩ : DyadicInterval 40),(⟨-62963008,-62962944⟩ : DyadicInterval 40),(⟨762123381770,762123401099⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3648,-2496⟩ : DyadicInterval 40),(⟨762123384864,762123404704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨164978800762,165103039657⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153715146432,153715146496⟩ : DyadicInterval 40),(⟨-178752697536,-178752697472⟩ : DyadicInterval 40),(⟨749699200428,749699219757⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153823170496,153823170560⟩ : DyadicInterval 40),(⟨-178898878784,-178898878720⟩ : DyadicInterval 40),(⟨749680409703,749680429033⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25075708288,-25037551040⟩ : DyadicInterval 40),(⟨774642159136,774661257024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨153768963968,153868038336⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-178959605120,-178825520704⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1537_ok : ecellOkT e1537 = true := by decide +kernel
theorem e1537_pos {a z : ℝ} (ha1 : ((1229649/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((615249/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1537 e1537_ok ha1 ha2 hz1 hz2 hz

-- box ['3/20', '1229649/8192000', '1599/1600', '1999/2000']  interval_lower 113946561/1099511627776
noncomputable def e1538 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1264438371942,0,true,153669880704,153669880768⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨934584883610,0,false,-178691452736,-178691452672⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1264552322794,0,true,153768963968,153768964032⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨934470932758,0,false,-178825520768,-178825520704⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1264335292726,0,true,153580242944,153580243008⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨934687962826,0,false,-178570189760,-178570189696⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1264469802447,0,true,153697211264,153697211328⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨934553453105,0,false,-178728430464,-178728430400⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099553541628,0,true,41913024,41913088⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099469713924,0,false,-41914688,-41914624⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564058185,0,true,52429120,52429184⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099459197367,0,false,-52431680,-52431616⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625275,0,false,-2560,-2496⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626179,0,false,-1600,-1536⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1264386828479,0,true,153625059392,153625059456⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨934636427073,0,false,-178630815040,-178630814976⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1264511067141,0,true,153733092160,153733092224⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨934512188411,0,false,-178776979840,-178776979776⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074750802785,0,false,-25043887680,-25043887616⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074788076774,0,false,-25005755584,-25005755520⟩
    { al := (3/20), au := (1229649/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨164926744166,165040695018⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153669880704,153669880768⟩ : DyadicInterval 40),(⟨-178691452736,-178691452672⟩ : DyadicInterval 40),(⟨749707069559,749707088889⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153768963968,153768964032⟩ : DyadicInterval 40),(⟨-178825520768,-178825520704⟩ : DyadicInterval 40),(⟨749689840933,749689860262⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153580242944,153580243008⟩ : DyadicInterval 40),(⟨-178570189760,-178570189696⟩ : DyadicInterval 40),(⟨749722644058,749722663388⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153697211264,153697211328⟩ : DyadicInterval 40),(⟨-178728430464,-178728430400⟩ : DyadicInterval 40),(⟨749702318682,749702338012⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨41913852,52430409⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨41913024,41913088⟩ : DyadicInterval 40),(⟨-41914688,-41914624⟩ : DyadicInterval 40),(⟨762123382786,762123402115⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52429120,52429184⟩ : DyadicInterval 40),(⟨-52431680,-52431616⟩ : DyadicInterval 40),(⟨762123382331,762123401660⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2560,-1536⟩ : DyadicInterval 40),(⟨762123384384,762123404160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨164875200703,164999439365⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153625059392,153625059456⟩ : DyadicInterval 40),(⟨-178630815040,-178630814976⟩ : DyadicInterval 40),(⟨749714858623,749714877952⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153733092160,153733092224⟩ : DyadicInterval 40),(⟨-178776979840,-178776979776⟩ : DyadicInterval 40),(⟨749696079890,749696099220⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25043887680,-25005755520⟩ : DyadicInterval 40),(⟨774626261376,774645346720⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨153669880704,153768964032⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-178825520768,-178691452672⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1538_ok : ecellOkT e1538 = true := by decide +kernel
theorem e1538_pos {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1229649/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1538 e1538_ok ha1 ha2 hz1 hz2 hz

-- box ['1229649/8192000', '615249/4096000', '1599/1600', '1999/2000']  interval_lower 14360091/137438953472
noncomputable def e1539 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1264552322793,0,true,153768963968,153768964032⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨934470932759,0,false,-178825520768,-178825520704⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1264666273645,0,true,153868038272,153868038336⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨934356981907,0,false,-178959605120,-178959605056⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1264449172358,0,true,153679272384,153679272448⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨934574083194,0,false,-178704159168,-178704159104⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1264583696323,0,true,153796242496,153796242560⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨934439559229,0,false,-178862435904,-178862435840⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099553571551,0,true,41942912,41942976⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099469684001,0,false,-41944576,-41944512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564095591,0,true,52466560,52466624⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099459159961,0,false,-52469120,-52469056⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625272,0,false,-2560,-2496⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626176,0,false,-1664,-1600⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1264500743723,0,true,153724115712,153724115776⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨934522511829,0,false,-178764833792,-178764833728⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1264624989506,0,true,153832144896,153832144960⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨934398266046,0,false,-178911024768,-178911024704⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074716599207,0,false,-25078879808,-25078879744⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074753901079,0,false,-25040718016,-25040717952⟩
    { al := (1229649/8192000), au := (615249/4096000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨165040695017,165154645869⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153768963968,153768964032⟩ : DyadicInterval 40),(⟨-178825520768,-178825520704⟩ : DyadicInterval 40),(⟨749689840933,749689860263⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153868038272,153868038336⟩ : DyadicInterval 40),(⟨-178959605120,-178959605056⟩ : DyadicInterval 40),(⟨749672600231,749672619560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153679272384,153679272448⟩ : DyadicInterval 40),(⟨-178704159168,-178704159104⟩ : DyadicInterval 40),(⟨749705437089,749705456419⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153796242496,153796242560⟩ : DyadicInterval 40),(⟨-178862435904,-178862435840⟩ : DyadicInterval 40),(⟨749685095335,749685114664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨41943775,52467815⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨41942912,41942976⟩ : DyadicInterval 40),(⟨-41944576,-41944512⟩ : DyadicInterval 40),(⟨762123382783,762123402112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52466560,52466624⟩ : DyadicInterval 40),(⟨-52469120,-52469056⟩ : DyadicInterval 40),(⟨762123382328,762123401657⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2560,-1600⟩ : DyadicInterval 40),(⟨762123384416,762123404160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨164989115947,165113361730⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153724115712,153724115776⟩ : DyadicInterval 40),(⟨-178764833792,-178764833728⟩ : DyadicInterval 40),(⟨749697640861,749697660190⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153832144896,153832144960⟩ : DyadicInterval 40),(⟨-178911024768,-178911024704⟩ : DyadicInterval 40),(⟨749678847899,749678867228⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25078879808,-25040717952⟩ : DyadicInterval 40),(⟨774643742592,774662842784⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨153768963968,153868038336⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-178959605120,-178825520704⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1539_ok : ecellOkT e1539 = true := by decide +kernel
theorem e1539_pos {a z : ℝ} (ha1 : ((1229649/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((615249/4096000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1539 e1539_ok ha1 ha2 hz1 hz2 hz

-- box ['615249/4096000', '1231347/8192000', '3997/4000', '1599/1600']  interval_lower 14494207/137438953472
noncomputable def e1540 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1264666273644,0,true,153868038272,153868038336⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨934356981908,0,false,-178959605120,-178959605056⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1264780224496,0,true,153967103616,153967103680⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨934243031056,0,false,-179093705792,-179093705728⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1264542407659,0,true,153760342848,153760342912⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨934480847893,0,false,-178813854528,-178813854464⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1264676931624,0,true,153877304384,153877304448⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨934346323928,0,false,-178972147008,-178972146944⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564094856,0,true,52465792,52465856⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099459160696,0,false,-52468352,-52468288⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099574633861,0,true,63004224,63004288⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099448621691,0,false,-63007936,-63007872⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624165,0,false,-3648,-3584⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625273,0,false,-2560,-2496⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1264604336910,0,true,153814188608,153814188672⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨934418918642,0,false,-178886723008,-178886722944⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1264728582678,0,true,153922208960,153922209024⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨934294672874,0,false,-179032930176,-179032930112⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074685476330,0,false,-25110721216,-25110721152⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074722801610,0,false,-25072534336,-25072534272⟩
    { al := (615249/4096000), au := (1231347/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨165154645868,165268596720⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153868038272,153868038336⟩ : DyadicInterval 40),(⟨-178959605120,-178959605056⟩ : DyadicInterval 40),(⟨749672600231,749672619561⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153967103616,153967103680⟩ : DyadicInterval 40),(⟨-179093705792,-179093705728⟩ : DyadicInterval 40),(⟨749655347452,749655366781⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153760342848,153760342912⟩ : DyadicInterval 40),(⟨-178813854528,-178813854464⟩ : DyadicInterval 40),(⟨749691340514,749691359843⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153877304384,153877304448⟩ : DyadicInterval 40),(⟨-178972147008,-178972146944⟩ : DyadicInterval 40),(⟨749670987041,749671006371⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨52467080,63006085⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52465792,52465856⟩ : DyadicInterval 40),(⟨-52468352,-52468288⟩ : DyadicInterval 40),(⟨762123382328,762123401657⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63004224,63004288⟩ : DyadicInterval 40),(⟨-63007936,-63007872⟩ : DyadicInterval 40),(⟨762123381797,762123401126⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3648,-2496⟩ : DyadicInterval 40),(⟨762123384864,762123404704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165092709134,165216954902⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153814188608,153814188672⟩ : DyadicInterval 40),(⟨-178886723008,-178886722944⟩ : DyadicInterval 40),(⟨749681972734,749681992064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153922208960,153922209024⟩ : DyadicInterval 40),(⟨-179032930176,-179032930112⟩ : DyadicInterval 40),(⟨749663167781,749663187111⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25110721216,-25072534272⟩ : DyadicInterval 40),(⟨774659650752,774678763488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨153868038272,153967103680⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179093705792,-178959605056⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1540_ok : ecellOkT e1540 = true := by decide +kernel
theorem e1540_pos {a z : ℝ} (ha1 : ((615249/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1231347/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1540 e1540_ok ha1 ha2 hz1 hz2 hz

-- box ['1231347/8192000', '308049/2048000', '3997/4000', '1599/1600']  interval_lower 58446469/549755813888
noncomputable def e1541 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1264780224495,0,true,153967103616,153967103680⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨934243031057,0,false,-179093705792,-179093705728⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1264894175347,0,true,154066160064,154066160128⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨934129080205,0,false,-179227822848,-179227822784⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1264656273047,0,true,153859343616,153859343680⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨934366982505,0,false,-178947836864,-178947836800⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1264790811255,0,true,153976307008,153976307072⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨934232444297,0,false,-179106165440,-179106165376⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564132264,0,true,52503232,52503296⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099459123288,0,false,-52505792,-52505728⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099574678754,0,true,63049152,63049216⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099448576798,0,false,-63052800,-63052736⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624160,0,false,-3648,-3584⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625269,0,false,-2560,-2496⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1264718245028,0,true,153913221696,153913221760⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨934305010524,0,false,-179020764544,-179020764480⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1264842497919,0,true,154021238464,154021238528⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨934180757633,0,false,-179166997888,-179166997824⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074651229821,0,false,-25145759360,-25145759296⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074688582986,0,false,-25107542784,-25107542720⟩
    { al := (1231347/8192000), au := (308049/2048000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨165268596719,165382547571⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153967103616,153967103680⟩ : DyadicInterval 40),(⟨-179093705792,-179093705728⟩ : DyadicInterval 40),(⟨749655347452,749655366781⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154066160064,154066160128⟩ : DyadicInterval 40),(⟨-179227822848,-179227822784⟩ : DyadicInterval 40),(⟨749638082584,749638101914⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153859343616,153859343680⟩ : DyadicInterval 40),(⟨-178947836864,-178947836800⟩ : DyadicInterval 40),(⟨749674113792,749674133122⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153976307008,153976307072⟩ : DyadicInterval 40),(⟨-179106165440,-179106165376⟩ : DyadicInterval 40),(⟨749653743925,749653763254⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨52504488,63050978⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52503232,52503296⟩ : DyadicInterval 40),(⟨-52505792,-52505728⟩ : DyadicInterval 40),(⟨762123382324,762123401653⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63049152,63049216⟩ : DyadicInterval 40),(⟨-63052800,-63052736⟩ : DyadicInterval 40),(⟨762123381760,762123401089⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3648,-2496⟩ : DyadicInterval 40),(⟨762123384864,762123404704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165206617252,165330870143⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153913221696,153913221760⟩ : DyadicInterval 40),(⟨-179020764544,-179020764480⟩ : DyadicInterval 40),(⟨749664732985,749664752314⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154021238464,154021238528⟩ : DyadicInterval 40),(⟨-179166997888,-179166997824⟩ : DyadicInterval 40),(⟨749645913796,749645933126⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25145759360,-25107542720⟩ : DyadicInterval 40),(⟨774677154976,774696282560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨153967103616,154066160128⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179227822848,-179093705728⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1541_ok : ecellOkT e1541 = true := by decide +kernel
theorem e1541_pos {a z : ℝ} (ha1 : ((1231347/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((308049/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1541 e1541_ok ha1 ha2 hz1 hz2 hz

-- box ['615249/4096000', '1231347/8192000', '1599/1600', '1999/2000']  interval_lower 14477153/137438953472
noncomputable def e1542 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1264666273644,0,true,153868038272,153868038336⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨934356981908,0,false,-178959605120,-178959605056⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1264780224496,0,true,153967103616,153967103680⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨934243031056,0,false,-179093705792,-179093705728⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1264563051990,0,true,153778292800,153778292864⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨934460203562,0,false,-178838144960,-178838144896⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1264697590198,0,true,153895264832,153895264896⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨934325665354,0,false,-178996457728,-178996457664⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099553601476,0,true,41972864,41972928⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099469654076,0,false,-41974528,-41974464⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564132999,0,true,52503936,52504000⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099459122553,0,false,-52506496,-52506432⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625268,0,false,-2560,-2496⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626174,0,false,-1664,-1600⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1264614658958,0,true,153823163072,153823163136⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨934408596594,0,false,-178898868800,-178898868736⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1264738911869,0,true,153931188736,153931188800⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨934284343683,0,false,-179045086016,-179045085952⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074682372023,0,false,-25113897216,-25113897152⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074719701782,0,false,-25075705664,-25075705600⟩
    { al := (615249/4096000), au := (1231347/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨165154645868,165268596720⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153868038272,153868038336⟩ : DyadicInterval 40),(⟨-178959605120,-178959605056⟩ : DyadicInterval 40),(⟨749672600231,749672619561⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153967103616,153967103680⟩ : DyadicInterval 40),(⟨-179093705792,-179093705728⟩ : DyadicInterval 40),(⟨749655347452,749655366781⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153778292800,153778292864⟩ : DyadicInterval 40),(⟨-178838144960,-178838144896⟩ : DyadicInterval 40),(⟨749688218139,749688237468⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153895264832,153895264896⟩ : DyadicInterval 40),(⟨-178996457728,-178996457664⟩ : DyadicInterval 40),(⟨749667859925,749667879255⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨41973700,52505223⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨41972864,41972928⟩ : DyadicInterval 40),(⟨-41974528,-41974464⟩ : DyadicInterval 40),(⟨762123382781,762123402110⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52503936,52504000⟩ : DyadicInterval 40),(⟨-52506496,-52506432⟩ : DyadicInterval 40),(⟨762123382324,762123401653⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2560,-1600⟩ : DyadicInterval 40),(⟨762123384416,762123404160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165103031182,165227284093⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153823163072,153823163136⟩ : DyadicInterval 40),(⟨-178898868800,-178898868736⟩ : DyadicInterval 40),(⟨749680411013,749680430342⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153931188736,153931188800⟩ : DyadicInterval 40),(⟨-179045086016,-179045085952⟩ : DyadicInterval 40),(⟨749661603806,749661623135⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25113897216,-25075705600⟩ : DyadicInterval 40),(⟨774661236416,774680351488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨153868038272,153967103680⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179093705792,-178959605056⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1542_ok : ecellOkT e1542 = true := by decide +kernel
theorem e1542_pos {a z : ℝ} (ha1 : ((615249/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1231347/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1542 e1542_ok ha1 ha2 hz1 hz2 hz

-- box ['1231347/8192000', '308049/2048000', '1599/1600', '1999/2000']  interval_lower 58378147/549755813888
noncomputable def e1543 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1264780224495,0,true,153967103616,153967103680⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨934243031057,0,false,-179093705792,-179093705728⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1264894175347,0,true,154066160064,154066160128⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨934129080205,0,false,-179227822848,-179227822784⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1264676931621,0,true,153877304384,153877304448⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨934346323931,0,false,-178972147008,-178972146944⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1264811484074,0,true,153994278208,153994278272⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨934211771478,0,false,-179130495872,-179130495808⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099553631403,0,true,42002816,42002880⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099469624149,0,false,-42004480,-42004416⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564170411,0,true,52541376,52541440⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099459085141,0,false,-52543936,-52543872⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625265,0,false,-2560,-2496⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626172,0,false,-1664,-1600⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1264728574200,0,true,153922201536,153922201600⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨934294681352,0,false,-179032920192,-179032920128⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1264852834232,0,true,154030223680,154030223744⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨934170421320,0,false,-179179163584,-179179163520⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074648121232,0,false,-25148939904,-25148939840⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074685478879,0,false,-25110718592,-25110718528⟩
    { al := (1231347/8192000), au := (308049/2048000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨165268596719,165382547571⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153967103616,153967103680⟩ : DyadicInterval 40),(⟨-179093705792,-179093705728⟩ : DyadicInterval 40),(⟨749655347452,749655366781⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154066160064,154066160128⟩ : DyadicInterval 40),(⟨-179227822848,-179227822784⟩ : DyadicInterval 40),(⟨749638082584,749638101914⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153877304384,153877304448⟩ : DyadicInterval 40),(⟨-178972147008,-178972146944⟩ : DyadicInterval 40),(⟨749670987042,749671006371⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153994278208,153994278272⟩ : DyadicInterval 40),(⟨-179130495872,-179130495808⟩ : DyadicInterval 40),(⟨749650612463,749650631792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨42003627,52542635⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42002816,42002880⟩ : DyadicInterval 40),(⟨-42004480,-42004416⟩ : DyadicInterval 40),(⟨762123382779,762123402108⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52541376,52541440⟩ : DyadicInterval 40),(⟨-52543936,-52543872⟩ : DyadicInterval 40),(⟨762123382321,762123401650⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2560,-1600⟩ : DyadicInterval 40),(⟨762123384416,762123404160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165216946424,165341206456⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153922201536,153922201600⟩ : DyadicInterval 40),(⟨-179032920192,-179032920128⟩ : DyadicInterval 40),(⟨749663169092,749663188422⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154030223680,154030223744⟩ : DyadicInterval 40),(⟨-179179163584,-179179163520⟩ : DyadicInterval 40),(⟨749644347610,749644366939⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25148939904,-25110718528⟩ : DyadicInterval 40),(⟨774678742880,774697872832⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨153967103616,154066160128⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179227822848,-179093705728⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1543_ok : ecellOkT e1543 = true := by decide +kernel
theorem e1543_pos {a z : ℝ} (ha1 : ((1231347/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((308049/2048000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1543 e1543_ok ha1 ha2 hz1 hz2 hz

-- box ['308049/2048000', '246609/1638400', '999/1000', '7993/8000']  interval_lower 59054297/549755813888
noncomputable def e1544 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1264894175346,0,true,154066160064,154066160128⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨934129080206,0,false,-179227822848,-179227822784⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265008126198,0,true,154165207616,154165207680⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨934015129354,0,false,-179361956288,-179361956224⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1264728792798,0,true,153922391616,153922391680⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨934294462754,0,false,-179033177472,-179033177408⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1264863316762,0,true,154039335872,154039335936⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨934159938790,0,false,-179191501504,-179191501440⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585186230,0,true,73555968,73556032⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099438069322,0,false,-73560960,-73560896⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099595755170,0,true,84124160,84124224⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099427500382,0,false,-84130624,-84130560⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621339,0,false,-6464,-6400⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622855,0,false,-4928,-4864⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1264811480623,0,true,153994275200,153994275264⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨934211774929,0,false,-179130491776,-179130491712⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1264935726353,0,true,154102277824,154102277888⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨934087529199,0,false,-179276731328,-179276731264⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074623184853,0,false,-25174453504,-25174453440⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074660556937,0,false,-25136216576,-25136216512⟩
    { al := (308049/2048000), au := (246609/1638400), zl := (999/1000), zu := (7993/8000),
      A := ⟨165382547570,165496498422⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154066160064,154066160128⟩ : DyadicInterval 40),(⟨-179227822848,-179227822784⟩ : DyadicInterval 40),(⟨749638082584,749638101914⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154165207616,154165207680⟩ : DyadicInterval 40),(⟨-179361956288,-179361956224⟩ : DyadicInterval 40),(⟨749620805628,749620824957⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153922391616,153922391680⟩ : DyadicInterval 40),(⟨-179033177472,-179033177408⟩ : DyadicInterval 40),(⟨749663135983,749663155313⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154039335872,154039335936⟩ : DyadicInterval 40),(⟨-179191501504,-179191501440⟩ : DyadicInterval 40),(⟨749642759194,749642778523⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨73558454,84127394⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73555968,73556032⟩ : DyadicInterval 40),(⟨-73560960,-73560896⟩ : DyadicInterval 40),(⟨762123381126,762123400456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨84124160,84124224⟩ : DyadicInterval 40),(⟨-84130624,-84130560⟩ : DyadicInterval 40),(⟨762123380346,762123399676⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6464,-4864⟩ : DyadicInterval 40),(⟨762123386048,762123406112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165299852847,165424098577⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153994275200,153994275264⟩ : DyadicInterval 40),(⟨-179130491776,-179130491712⟩ : DyadicInterval 40),(⟨749650612976,749650632305⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154102277824,154102277888⟩ : DyadicInterval 40),(⟨-179276731328,-179276731264⟩ : DyadicInterval 40),(⟨749631784086,749631803415⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25174453504,-25136216512⟩ : DyadicInterval 40),(⟨774691491872,774710629632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154066160064,154165207680⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179361956288,-179227822784⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1544_ok : ecellOkT e1544 = true := by decide +kernel
theorem e1544_pos {a z : ℝ} (ha1 : ((308049/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((246609/1638400 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1544 e1544_ok ha1 ha2 hz1 hz2 hz

-- box ['246609/1638400', '616947/4096000', '999/1000', '7993/8000']  interval_lower 119053441/1099511627776
noncomputable def e1545 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265008126197,0,true,154165207616,154165207680⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨934015129355,0,false,-179361956288,-179361956224⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265122077049,0,true,154264246208,154264246272⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933901178503,0,false,-179496106048,-179496105984⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1264842629698,0,true,154021353024,154021353088⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨934180625854,0,false,-179167153024,-179167152960⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1264977167906,0,true,154138299136,154138299200⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨934046087646,0,false,-179325513152,-179325513088⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585238608,0,true,73608320,73608384⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099438016944,0,false,-73613312,-73613248⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099595815035,0,true,84184000,84184064⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099427440517,0,false,-84190528,-84190464⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621329,0,false,-6464,-6400⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622848,0,false,-4992,-4928⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1264925374241,0,true,154093279488,154093279552⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨934097881311,0,false,-179264545984,-179264545920⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265049627351,0,true,154201278720,154201278784⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933973628201,0,false,-179410812032,-179410811968⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074588899711,0,false,-25209533248,-25209533184⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074626299756,0,false,-25171266496,-25171266432⟩
    { al := (246609/1638400), au := (616947/4096000), zl := (999/1000), zu := (7993/8000),
      A := ⟨165496498421,165610449273⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154165207616,154165207680⟩ : DyadicInterval 40),(⟨-179361956288,-179361956224⟩ : DyadicInterval 40),(⟨749620805628,749620824958⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154264246208,154264246272⟩ : DyadicInterval 40),(⟨-179496106048,-179496105984⟩ : DyadicInterval 40),(⟨749603516591,749603535921⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154021353024,154021353088⟩ : DyadicInterval 40),(⟨-179167153024,-179167152960⟩ : DyadicInterval 40),(⟨749645893841,749645913170⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154138299136,154138299200⟩ : DyadicInterval 40),(⟨-179325513152,-179325513088⟩ : DyadicInterval 40),(⟨749625500656,749625519986⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨73610832,84187259⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73608320,73608384⟩ : DyadicInterval 40),(⟨-73613312,-73613248⟩ : DyadicInterval 40),(⟨762123381119,762123400449⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨84184000,84184064⟩ : DyadicInterval 40),(⟨-84190528,-84190464⟩ : DyadicInterval 40),(⟨762123380369,762123399699⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6464,-4928⟩ : DyadicInterval 40),(⟨762123386080,762123406112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165413746465,165537999575⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154093279488,154093279552⟩ : DyadicInterval 40),(⟨-179264545984,-179264545920⟩ : DyadicInterval 40),(⟨749633353463,749633372793⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154201278720,154201278784⟩ : DyadicInterval 40),(⟨-179410812032,-179410811968⟩ : DyadicInterval 40),(⟨749614510323,749614529652⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25209533248,-25171266432⟩ : DyadicInterval 40),(⟨774709016832,774728169504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154165207616,154264246272⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179496106048,-179361956224⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1545_ok : ecellOkT e1545 = true := by decide +kernel
theorem e1545_pos {a z : ℝ} (ha1 : ((246609/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((616947/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1545 e1545_ok ha1 ha2 hz1 hz2 hz

-- box ['308049/2048000', '246609/1638400', '7993/8000', '3997/4000']  interval_lower 117971623/1099511627776
noncomputable def e1546 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1264894175346,0,true,154066160064,154066160128⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨934129080206,0,false,-179227822848,-179227822784⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265008126198,0,true,154165207616,154165207680⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨934015129354,0,false,-179361956288,-179361956224⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1264749465616,0,true,153940363712,153940363776⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨934273789936,0,false,-179057506240,-179057506176⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1264884003825,0,true,154057318464,154057318528⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨934139251727,0,false,-179215850560,-179215850496⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099574677975,0,true,63048384,63048448⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099448577577,0,false,-63052032,-63051968⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585239432,0,true,73609152,73609216⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099438016120,0,false,-73614144,-73614080⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622847,0,false,-4992,-4928⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624161,0,false,-3648,-3584⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1264821816875,0,true,154003260544,154003260608⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨934201438677,0,false,-179142657024,-179142656960⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1264946069750,0,true,154111268480,154111268544⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨934077185802,0,false,-179288906560,-179288906496⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074620072380,0,false,-25177638080,-25177638016⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074657448949,0,false,-25139396416,-25139396352⟩
    { al := (308049/2048000), au := (246609/1638400), zl := (7993/8000), zu := (3997/4000),
      A := ⟨165382547570,165496498422⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154066160064,154066160128⟩ : DyadicInterval 40),(⟨-179227822848,-179227822784⟩ : DyadicInterval 40),(⟨749638082584,749638101914⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154165207616,154165207680⟩ : DyadicInterval 40),(⟨-179361956288,-179361956224⟩ : DyadicInterval 40),(⟨749620805628,749620824957⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153940363712,153940363776⟩ : DyadicInterval 40),(⟨-179057506240,-179057506176⟩ : DyadicInterval 40),(⟨749660005685,749660025015⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154057318464,154057318528⟩ : DyadicInterval 40),(⟨-179215850560,-179215850496⟩ : DyadicInterval 40),(⟨749639624142,749639643472⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨63050199,73611656⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63048384,63048448⟩ : DyadicInterval 40),(⟨-63052032,-63051968⟩ : DyadicInterval 40),(⟨762123381760,762123401089⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73609152,73609216⟩ : DyadicInterval 40),(⟨-73614144,-73614080⟩ : DyadicInterval 40),(⟨762123381119,762123400448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4992,-3584⟩ : DyadicInterval 40),(⟨762123385408,762123405376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165310189099,165434441974⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154003260544,154003260608⟩ : DyadicInterval 40),(⟨-179142657024,-179142656960⟩ : DyadicInterval 40),(⟨749649047131,749649066460⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154111268480,154111268544⟩ : DyadicInterval 40),(⟨-179288906560,-179288906496⟩ : DyadicInterval 40),(⟨749630215954,749630235283⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25177638080,-25139396352⟩ : DyadicInterval 40),(⟨774693081792,774712221920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154066160064,154165207680⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179361956288,-179227822784⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1546_ok : ecellOkT e1546 = true := by decide +kernel
theorem e1546_pos {a z : ℝ} (ha1 : ((308049/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((246609/1638400 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1546 e1546_ok ha1 ha2 hz1 hz2 hz

-- box ['246609/1638400', '616947/4096000', '7993/8000', '3997/4000']  interval_lower 118916333/1099511627776
noncomputable def e1547 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265008126197,0,true,154165207616,154165207680⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨934015129355,0,false,-179361956288,-179361956224⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265122077049,0,true,154264246208,154264246272⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933901178503,0,false,-179496106048,-179496105984⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1264863316760,0,true,154039335872,154039335936⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨934159938792,0,false,-179191501504,-179191501440⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1264997869213,0,true,154156292480,154156292544⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨934025386339,0,false,-179349881920,-179349881856⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099574722870,0,true,63093248,63093312⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099448532682,0,false,-63096960,-63096896⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585291814,0,true,73661568,73661632⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437963738,0,false,-73666560,-73666496⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622840,0,false,-4992,-4928⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624156,0,false,-3648,-3584⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1264935717870,0,true,154102270400,154102270464⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨934087537682,0,false,-179276721344,-179276721280⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265059977868,0,true,154210274816,154210274880⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933963277684,0,false,-179422997120,-179422997056⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074585782950,0,false,-25212722304,-25212722240⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074623187407,0,false,-25174450880,-25174450816⟩
    { al := (246609/1638400), au := (616947/4096000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨165496498421,165610449273⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154165207616,154165207680⟩ : DyadicInterval 40),(⟨-179361956288,-179361956224⟩ : DyadicInterval 40),(⟨749620805628,749620824958⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154264246208,154264246272⟩ : DyadicInterval 40),(⟨-179496106048,-179496105984⟩ : DyadicInterval 40),(⟨749603516591,749603535921⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154039335872,154039335936⟩ : DyadicInterval 40),(⟨-179191501504,-179191501440⟩ : DyadicInterval 40),(⟨749642759194,749642778524⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154156292480,154156292544⟩ : DyadicInterval 40),(⟨-179349881920,-179349881856⟩ : DyadicInterval 40),(⟨749622361248,749622380578⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨63095094,73664038⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63093248,63093312⟩ : DyadicInterval 40),(⟨-63096960,-63096896⟩ : DyadicInterval 40),(⟨762123381787,762123401116⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73661568,73661632⟩ : DyadicInterval 40),(⟨-73666560,-73666496⟩ : DyadicInterval 40),(⟨762123381112,762123400441⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4992,-3584⟩ : DyadicInterval 40),(⟨762123385408,762123405376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165424090094,165548350092⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154102270400,154102270464⟩ : DyadicInterval 40),(⟨-179276721344,-179276721280⟩ : DyadicInterval 40),(⟨749631785402,749631804731⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154210274816,154210274880⟩ : DyadicInterval 40),(⟨-179422997120,-179422997056⟩ : DyadicInterval 40),(⟨749612939974,749612959303⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25212722304,-25174450816⟩ : DyadicInterval 40),(⟨774710609024,774729764032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154165207616,154264246272⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179496106048,-179361956224⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1547_ok : ecellOkT e1547 = true := by decide +kernel
theorem e1547_pos {a z : ℝ} (ha1 : ((246609/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((616947/4096000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1547 e1547_ok ha1 ha2 hz1 hz2 hz

-- box ['616947/4096000', '1234743/8192000', '999/1000', '7993/8000']  interval_lower 120000893/1099511627776
noncomputable def e1548 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265122077048,0,true,154264246208,154264246272⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933901178504,0,false,-179496106048,-179496105984⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265236027900,0,true,154363275904,154363275968⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933787227652,0,false,-179630272192,-179630272128⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1264956466598,0,true,154120305536,154120305600⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨934066788954,0,false,-179301144896,-179301144832⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265091019050,0,true,154237253568,154237253632⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933932236502,0,false,-179459541120,-179459541056⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585290989,0,true,73660736,73660800⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437964563,0,false,-73665728,-73665664⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099595874905,0,true,84243840,84243904⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099427380647,0,false,-84250368,-84250304⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621320,0,false,-6464,-6400⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622841,0,false,-4992,-4928⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265039268116,0,true,154192275008,154192275072⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933983987436,0,false,-179398616768,-179398616704⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265163528353,0,true,154300270784,154300270848⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933859727199,0,false,-179544909056,-179544908992⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074554590968,0,false,-25244638272,-25244638208⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074592018903,0,false,-25206341760,-25206341696⟩
    { al := (616947/4096000), au := (1234743/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨165610449272,165724400124⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154264246208,154264246272⟩ : DyadicInterval 40),(⟨-179496106048,-179496105984⟩ : DyadicInterval 40),(⟨749603516591,749603535921⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154363275904,154363275968⟩ : DyadicInterval 40),(⟨-179630272192,-179630272128⟩ : DyadicInterval 40),(⟨749586215462,749586234792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154120305536,154120305600⟩ : DyadicInterval 40),(⟨-179301144896,-179301144832⟩ : DyadicInterval 40),(⟨749628639631,749628658961⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154237253568,154237253632⟩ : DyadicInterval 40),(⟨-179459541120,-179459541056⟩ : DyadicInterval 40),(⟨749608230007,749608249336⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨73663213,84247129⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73660736,73660800⟩ : DyadicInterval 40),(⟨-73665728,-73665664⟩ : DyadicInterval 40),(⟨762123381112,762123400442⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨84243840,84243904⟩ : DyadicInterval 40),(⟨-84250368,-84250304⟩ : DyadicInterval 40),(⟨762123380360,762123399690⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6464,-4928⟩ : DyadicInterval 40),(⟨762123386080,762123406112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165527640340,165651900577⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154192275008,154192275072⟩ : DyadicInterval 40),(⟨-179398616768,-179398616704⟩ : DyadicInterval 40),(⟨749616081855,749616101184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154300270784,154300270848⟩ : DyadicInterval 40),(⟨-179544909056,-179544908992⟩ : DyadicInterval 40),(⟨749597224426,749597243755⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25244638272,-25206341696⟩ : DyadicInterval 40),(⟨774726554464,774745722016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154264246208,154363275968⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179630272192,-179496105984⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1548_ok : ecellOkT e1548 = true := by decide +kernel
theorem e1548_pos {a z : ℝ} (ha1 : ((616947/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1234743/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1548 e1548_ok ha1 ha2 hz1 hz2 hz

-- box ['1234743/8192000', '154449/1024000', '999/1000', '7993/8000']  interval_lower 30237693/274877906944
noncomputable def e1549 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265236027899,0,true,154363275904,154363275968⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933787227653,0,false,-179630272192,-179630272128⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265349978751,0,true,154462296704,154462296768⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933673276801,0,false,-179764454720,-179764454656⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265070303498,0,true,154219249152,154219249216⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933952952054,0,false,-179435153088,-179435153024⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265204870194,0,true,154336199040,154336199104⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933818385358,0,false,-179593585408,-179593585344⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585343375,0,true,73713088,73713152⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437912177,0,false,-73718080,-73718016⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099595934777,0,true,84303744,84303808⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099427320775,0,false,-84310272,-84310208⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621311,0,false,-6528,-6464⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622834,0,false,-4992,-4928⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265153161993,0,true,154291261696,154291261760⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933870093559,0,false,-179532703936,-179532703872⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265277429354,0,true,154399253888,154399253952⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933745826198,0,false,-179679022464,-179679022400⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074520258627,0,false,-25279768576,-25279768512⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074557714453,0,false,-25241442240,-25241442176⟩
    { al := (1234743/8192000), au := (154449/1024000), zl := (999/1000), zu := (7993/8000),
      A := ⟨165724400123,165838350975⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154363275904,154363275968⟩ : DyadicInterval 40),(⟨-179630272192,-179630272128⟩ : DyadicInterval 40),(⟨749586215463,749586234792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154462296704,154462296768⟩ : DyadicInterval 40),(⟨-179764454720,-179764454656⟩ : DyadicInterval 40),(⟨749568902242,749568921571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154219249152,154219249216⟩ : DyadicInterval 40),(⟨-179435153088,-179435153024⟩ : DyadicInterval 40),(⟨749611373352,749611392682⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154336199040,154336199104⟩ : DyadicInterval 40),(⟨-179593585408,-179593585344⟩ : DyadicInterval 40),(⟨749590947318,749590966647⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨73715599,84307001⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73713088,73713152⟩ : DyadicInterval 40),(⟨-73718080,-73718016⟩ : DyadicInterval 40),(⟨762123381105,762123400434⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨84303744,84303808⟩ : DyadicInterval 40),(⟨-84310272,-84310208⟩ : DyadicInterval 40),(⟨762123380351,762123399680⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6528,-4928⟩ : DyadicInterval 40),(⟨762123386080,762123406144⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165641534217,165765801578⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154291261696,154291261760⟩ : DyadicInterval 40),(⟨-179532703936,-179532703872⟩ : DyadicInterval 40),(⟨749598798142,749598817472⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154399253888,154399253952⟩ : DyadicInterval 40),(⟨-179679022464,-179679022400⟩ : DyadicInterval 40),(⟨749579926495,749579945824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25279768576,-25241442176⟩ : DyadicInterval 40),(⟨774744104704,774763287168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154363275904,154462296768⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179764454720,-179630272128⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1549_ok : ecellOkT e1549 = true := by decide +kernel
theorem e1549_pos {a z : ℝ} (ha1 : ((1234743/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((154449/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1549 e1549_ok ha1 ha2 hz1 hz2 hz

-- box ['616947/4096000', '1234743/8192000', '7993/8000', '3997/4000']  interval_lower 14982941/137438953472
noncomputable def e1550 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265122077048,0,true,154264246208,154264246272⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933901178504,0,false,-179496106048,-179496105984⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265236027900,0,true,154363275904,154363275968⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933787227652,0,false,-179630272192,-179630272128⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1264977167904,0,true,154138299136,154138299200⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨934046087648,0,false,-179325513152,-179325513088⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265111734601,0,true,154255257600,154255257664⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933911520951,0,false,-179483929664,-179483929600⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099574767768,0,true,63138176,63138240⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099448487784,0,false,-63141824,-63141760⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585344200,0,true,73713920,73713984⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437911352,0,false,-73718912,-73718848⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622833,0,false,-4992,-4928⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624151,0,false,-3648,-3584⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265049618864,0,true,154201271360,154201271424⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933973636688,0,false,-179410802048,-179410801984⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265173885987,0,true,154309272192,154309272256⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933849369565,0,false,-179557104064,-179557104000⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074551469918,0,false,-25247831808,-25247831744⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074588902267,0,false,-25209530624,-25209530560⟩
    { al := (616947/4096000), au := (1234743/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨165610449272,165724400124⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154264246208,154264246272⟩ : DyadicInterval 40),(⟨-179496106048,-179496105984⟩ : DyadicInterval 40),(⟨749603516591,749603535921⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154363275904,154363275968⟩ : DyadicInterval 40),(⟨-179630272192,-179630272128⟩ : DyadicInterval 40),(⟨749586215462,749586234792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154138299136,154138299200⟩ : DyadicInterval 40),(⟨-179325513152,-179325513088⟩ : DyadicInterval 40),(⟨749625500656,749625519986⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154255257600,154255257664⟩ : DyadicInterval 40),(⟨-179483929664,-179483929600⟩ : DyadicInterval 40),(⟨749605086300,749605105630⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨63139992,73716424⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63138176,63138240⟩ : DyadicInterval 40),(⟨-63141824,-63141760⟩ : DyadicInterval 40),(⟨762123381750,762123401079⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73713920,73713984⟩ : DyadicInterval 40),(⟨-73718912,-73718848⟩ : DyadicInterval 40),(⟨762123381105,762123400434⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4992,-3584⟩ : DyadicInterval 40),(⟨762123385408,762123405376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165537991088,165662258211⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154201271360,154201271424⟩ : DyadicInterval 40),(⟨-179410802048,-179410801984⟩ : DyadicInterval 40),(⟨749614511604,749614530934⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154309272192,154309272256⟩ : DyadicInterval 40),(⟨-179557104064,-179557104000⟩ : DyadicInterval 40),(⟨749595651958,749595671288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25247831808,-25209530560⟩ : DyadicInterval 40),(⟨774728148896,774747318784⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154264246208,154363275968⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179630272192,-179496105984⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1550_ok : ecellOkT e1550 = true := by decide +kernel
theorem e1550_pos {a z : ℝ} (ha1 : ((616947/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1234743/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1550 e1550_ok ha1 ha2 hz1 hz2 hz

-- box ['1234743/8192000', '154449/1024000', '7993/8000', '3997/4000']  interval_lower 120812827/1099511627776
noncomputable def e1551 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265236027899,0,true,154363275904,154363275968⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933787227653,0,false,-179630272192,-179630272128⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265349978751,0,true,154462296704,154462296768⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933673276801,0,false,-179764454720,-179764454656⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265091019048,0,true,154237253568,154237253632⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933932236504,0,false,-179459541120,-179459541056⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265225599988,0,true,154354213824,154354213888⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933797655564,0,false,-179617993664,-179617993600⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099574812670,0,true,63183040,63183104⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099448442882,0,false,-63186752,-63186688⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585396589,0,true,73766336,73766400⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437858963,0,false,-73771328,-73771264⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622826,0,false,-4992,-4928⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624145,0,false,-3648,-3584⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265163519608,0,true,154300263168,154300263232⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933859735944,0,false,-179544898816,-179544898752⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265287794110,0,true,154408260736,154408260800⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933735461442,0,false,-179691227328,-179691227264⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074517133283,0,false,-25282966592,-25282966528⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074554593604,0,false,-25244635584,-25244635520⟩
    { al := (1234743/8192000), au := (154449/1024000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨165724400123,165838350975⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154363275904,154363275968⟩ : DyadicInterval 40),(⟨-179630272192,-179630272128⟩ : DyadicInterval 40),(⟨749586215463,749586234792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154462296704,154462296768⟩ : DyadicInterval 40),(⟨-179764454720,-179764454656⟩ : DyadicInterval 40),(⟨749568902242,749568921571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154237253568,154237253632⟩ : DyadicInterval 40),(⟨-179459541120,-179459541056⟩ : DyadicInterval 40),(⟨749608230007,749608249336⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154354213824,154354213888⟩ : DyadicInterval 40),(⟨-179617993664,-179617993600⟩ : DyadicInterval 40),(⟨749587799243,749587818573⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨63184894,73768813⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63183040,63183104⟩ : DyadicInterval 40),(⟨-63186752,-63186688⟩ : DyadicInterval 40),(⟨762123381776,762123401106⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73766336,73766400⟩ : DyadicInterval 40),(⟨-73771328,-73771264⟩ : DyadicInterval 40),(⟨762123381098,762123400427⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4992,-3584⟩ : DyadicInterval 40),(⟨762123385408,762123405376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165651891832,165776166334⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154300263168,154300263232⟩ : DyadicInterval 40),(⟨-179544898816,-179544898752⟩ : DyadicInterval 40),(⟨749597225786,749597245116⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154408260736,154408260800⟩ : DyadicInterval 40),(⟨-179691227328,-179691227264⟩ : DyadicInterval 40),(⟨749578351805,749578371134⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25282966592,-25244635520⟩ : DyadicInterval 40),(⟨774745701376,774764886176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154363275904,154462296768⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179764454720,-179630272128⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1551_ok : ecellOkT e1551 = true := by decide +kernel
theorem e1551_pos {a z : ℝ} (ha1 : ((1234743/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((154449/1024000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1551 e1551_ok ha1 ha2 hz1 hz2 hz

-- box ['308049/2048000', '246609/1638400', '3997/4000', '1599/1600']  interval_lower 117834471/1099511627776
noncomputable def e1552 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1264894175346,0,true,154066160064,154066160128⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨934129080206,0,false,-179227822848,-179227822784⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265008126198,0,true,154165207616,154165207680⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨934015129354,0,false,-179361956288,-179361956224⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1264770138435,0,true,153958335488,153958335552⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨934253117117,0,false,-179081835584,-179081835520⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1264904690887,0,true,154075300736,154075300800⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨934118564665,0,false,-179240200192,-179240200128⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564169675,0,true,52540608,52540672⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099459085877,0,false,-52543168,-52543104⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099574723650,0,true,63094016,63094080⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099448531902,0,false,-63097728,-63097664⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624155,0,false,-3648,-3584⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625266,0,false,-2560,-2496⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1264832152888,0,true,154012245632,154012245696⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨934191102664,0,false,-179154822080,-179154822016⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1264956413163,0,true,154120259072,154120259136⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨934066842389,0,false,-179301081984,-179301081920⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074616959706,0,false,-25180822848,-25180822784⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074654340838,0,false,-25142576384,-25142576320⟩
    { al := (308049/2048000), au := (246609/1638400), zl := (3997/4000), zu := (1599/1600),
      A := ⟨165382547570,165496498422⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154066160064,154066160128⟩ : DyadicInterval 40),(⟨-179227822848,-179227822784⟩ : DyadicInterval 40),(⟨749638082584,749638101914⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154165207616,154165207680⟩ : DyadicInterval 40),(⟨-179361956288,-179361956224⟩ : DyadicInterval 40),(⟨749620805628,749620824957⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153958335488,153958335552⟩ : DyadicInterval 40),(⟨-179081835584,-179081835520⟩ : DyadicInterval 40),(⟨749656875020,749656894350⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154075300736,154075300800⟩ : DyadicInterval 40),(⟨-179240200192,-179240200128⟩ : DyadicInterval 40),(⟨749636488723,749636508052⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨52541899,63095874⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52540608,52540672⟩ : DyadicInterval 40),(⟨-52543168,-52543104⟩ : DyadicInterval 40),(⟨762123382321,762123401650⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63094016,63094080⟩ : DyadicInterval 40),(⟨-63097728,-63097664⟩ : DyadicInterval 40),(⟨762123381787,762123401116⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3648,-2496⟩ : DyadicInterval 40),(⟨762123384864,762123404704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165320525112,165444785387⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154012245632,154012245696⟩ : DyadicInterval 40),(⟨-179154822080,-179154822016⟩ : DyadicInterval 40),(⟨749647481190,749647500519⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154120259072,154120259136⟩ : DyadicInterval 40),(⟨-179301081984,-179301081920⟩ : DyadicInterval 40),(⟨749628647738,749628667067⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25180822848,-25142576320⟩ : DyadicInterval 40),(⟨774694671776,774713814304⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154066160064,154165207680⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179361956288,-179227822784⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1552_ok : ecellOkT e1552 = true := by decide +kernel
theorem e1552_pos {a z : ℝ} (ha1 : ((308049/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((246609/1638400 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1552 e1552_ok ha1 ha2 hz1 hz2 hz

-- box ['246609/1638400', '616947/4096000', '3997/4000', '1599/1600']  interval_lower 59389381/549755813888
noncomputable def e1553 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265008126197,0,true,154165207616,154165207680⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨934015129355,0,false,-179361956288,-179361956224⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265122077049,0,true,154264246208,154264246272⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933901178503,0,false,-179496106048,-179496105984⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1264884003823,0,true,154057318464,154057318528⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨934139251729,0,false,-179215850560,-179215850496⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265018570519,0,true,154174285504,154174285568⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨934004685033,0,false,-179374251264,-179374251200⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564207087,0,true,52578048,52578112⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099459048465,0,false,-52580608,-52580544⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099574768549,0,true,63138944,63139008⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099448487003,0,false,-63142592,-63142528⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624150,0,false,-3648,-3584⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625262,0,false,-2560,-2496⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1264946061010,0,true,154111260864,154111260928⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨934077194542,0,false,-179288896320,-179288896256⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265070328403,0,true,154219270784,154219270848⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933952927149,0,false,-179435182400,-179435182336⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074582665988,0,false,-25215911552,-25215911488⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074620075011,0,false,-25177635392,-25177635328⟩
    { al := (246609/1638400), au := (616947/4096000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨165496498421,165610449273⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154165207616,154165207680⟩ : DyadicInterval 40),(⟨-179361956288,-179361956224⟩ : DyadicInterval 40),(⟨749620805628,749620824958⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154264246208,154264246272⟩ : DyadicInterval 40),(⟨-179496106048,-179496105984⟩ : DyadicInterval 40),(⟨749603516591,749603535921⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154057318464,154057318528⟩ : DyadicInterval 40),(⟨-179215850560,-179215850496⟩ : DyadicInterval 40),(⟨749639624143,749639643472⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154174285504,154174285568⟩ : DyadicInterval 40),(⟨-179374251264,-179374251200⟩ : DyadicInterval 40),(⟨749619221472,749619240801⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨52579311,63140773⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52578048,52578112⟩ : DyadicInterval 40),(⟨-52580608,-52580544⟩ : DyadicInterval 40),(⟨762123382317,762123401646⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63138944,63139008⟩ : DyadicInterval 40),(⟨-63142592,-63142528⟩ : DyadicInterval 40),(⟨762123381749,762123401079⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3648,-2496⟩ : DyadicInterval 40),(⟨762123384864,762123404704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165434433234,165558700627⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154111260864,154111260928⟩ : DyadicInterval 40),(⟨-179288896320,-179288896256⟩ : DyadicInterval 40),(⟨749630217310,749630236640⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154219270784,154219270848⟩ : DyadicInterval 40),(⟨-179435182400,-179435182336⟩ : DyadicInterval 40),(⟨749611369578,749611388907⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25215911552,-25177635328⟩ : DyadicInterval 40),(⟨774712201280,774731358656⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154165207616,154264246272⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179496106048,-179361956224⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1553_ok : ecellOkT e1553 = true := by decide +kernel
theorem e1553_pos {a z : ℝ} (ha1 : ((246609/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((616947/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1553 e1553_ok ha1 ha2 hz1 hz2 hz

-- box ['308049/2048000', '246609/1638400', '1599/1600', '1999/2000']  interval_lower 7356095/68719476736
noncomputable def e1554 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1264894175346,0,true,154066160064,154066160128⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨934129080206,0,false,-179227822848,-179227822784⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265008126198,0,true,154165207616,154165207680⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨934015129354,0,false,-179361956288,-179361956224⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1264790811253,0,true,153976307008,153976307072⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨934232444299,0,false,-179106165440,-179106165376⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1264925377949,0,true,154093282688,154093282752⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨934097877603,0,false,-179264550336,-179264550272⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099553661331,0,true,42032704,42032768⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099469594221,0,false,-42034368,-42034304⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564207824,0,true,52578752,52578816⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099459047728,0,false,-52581312,-52581248⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625261,0,false,-2560,-2496⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626170,0,false,-1664,-1600⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1264842489182,0,true,154021230912,154021230976⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨934180766370,0,false,-179166987584,-179166987520⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1264966756597,0,true,154129249664,154129249728⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨934056498955,0,false,-179313257536,-179313257472⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074613846832,0,false,-25184007872,-25184007808⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074651232449,0,false,-25145756672,-25145756608⟩
    { al := (308049/2048000), au := (246609/1638400), zl := (1599/1600), zu := (1999/2000),
      A := ⟨165382547570,165496498422⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154066160064,154066160128⟩ : DyadicInterval 40),(⟨-179227822848,-179227822784⟩ : DyadicInterval 40),(⟨749638082584,749638101914⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154165207616,154165207680⟩ : DyadicInterval 40),(⟨-179361956288,-179361956224⟩ : DyadicInterval 40),(⟨749620805628,749620824957⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153976307008,153976307072⟩ : DyadicInterval 40),(⟨-179106165440,-179106165376⟩ : DyadicInterval 40),(⟨749653743925,749653763254⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154093282688,154093282752⟩ : DyadicInterval 40),(⟨-179264550336,-179264550272⟩ : DyadicInterval 40),(⟨749633352909,749633372238⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨42033555,52580048⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42032704,42032768⟩ : DyadicInterval 40),(⟨-42034368,-42034304⟩ : DyadicInterval 40),(⟨762123382777,762123402106⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52578752,52578816⟩ : DyadicInterval 40),(⟨-52581312,-52581248⟩ : DyadicInterval 40),(⟨762123382317,762123401646⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2560,-1600⟩ : DyadicInterval 40),(⟨762123384416,762123404160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165330861406,165455128821⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154021230912,154021230976⟩ : DyadicInterval 40),(⟨-179166987584,-179166987520⟩ : DyadicInterval 40),(⟨749645915087,749645934416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154129249664,154129249728⟩ : DyadicInterval 40),(⟨-179313257536,-179313257472⟩ : DyadicInterval 40),(⟨749627079374,749627098704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25184007872,-25145756608⟩ : DyadicInterval 40),(⟨774696261920,774715406816⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154066160064,154165207680⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179361956288,-179227822784⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1554_ok : ecellOkT e1554 = true := by decide +kernel
theorem e1554_pos {a z : ℝ} (ha1 : ((308049/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((246609/1638400 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1554 e1554_ok ha1 ha2 hz1 hz2 hz

-- box ['246609/1638400', '616947/4096000', '1599/1600', '1999/2000']  interval_lower 29660455/274877906944
noncomputable def e1555 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265008126197,0,true,154165207616,154165207680⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨934015129355,0,false,-179361956288,-179361956224⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265122077049,0,true,154264246208,154264246272⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933901178503,0,false,-179496106048,-179496105984⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1264904690885,0,true,154075300736,154075300800⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨934118564667,0,false,-179240200192,-179240200128⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265039271825,0,true,154192278272,154192278336⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933983983727,0,false,-179398621120,-179398621056⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099553691262,0,true,42062656,42062720⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099469564290,0,false,-42064320,-42064256⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564245240,0,true,52616192,52616256⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099459010312,0,false,-52618752,-52618688⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625257,0,false,-2560,-2496⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626167,0,false,-1664,-1600⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1264956404679,0,true,154120251712,154120251776⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨934066850873,0,false,-179301072000,-179301071936⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265080678963,0,true,154228266752,154228266816⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933942576589,0,false,-179447367872,-179447367808⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074579548825,0,false,-25219101056,-25219100992⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074616962260,0,false,-25180820224,-25180820160⟩
    { al := (246609/1638400), au := (616947/4096000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨165496498421,165610449273⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154165207616,154165207680⟩ : DyadicInterval 40),(⟨-179361956288,-179361956224⟩ : DyadicInterval 40),(⟨749620805628,749620824958⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154264246208,154264246272⟩ : DyadicInterval 40),(⟨-179496106048,-179496105984⟩ : DyadicInterval 40),(⟨749603516591,749603535921⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154075300736,154075300800⟩ : DyadicInterval 40),(⟨-179240200192,-179240200128⟩ : DyadicInterval 40),(⟨749636488723,749636508053⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154192278272,154192278336⟩ : DyadicInterval 40),(⟨-179398621120,-179398621056⟩ : DyadicInterval 40),(⟨749616081262,749616100592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨42063486,52617464⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42062656,42062720⟩ : DyadicInterval 40),(⟨-42064320,-42064256⟩ : DyadicInterval 40),(⟨762123382774,762123402103⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52616192,52616256⟩ : DyadicInterval 40),(⟨-52618752,-52618688⟩ : DyadicInterval 40),(⟨762123382313,762123401643⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2560,-1600⟩ : DyadicInterval 40),(⟨762123384416,762123404160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165444776903,165569051187⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154120251712,154120251776⟩ : DyadicInterval 40),(⟨-179301072000,-179301071936⟩ : DyadicInterval 40),(⟨749628649017,749628668347⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154228266752,154228266816⟩ : DyadicInterval 40),(⟨-179447367872,-179447367808⟩ : DyadicInterval 40),(⟨749609799060,749609818390⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25219101056,-25180820160⟩ : DyadicInterval 40),(⟨774713793696,774732953408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154165207616,154264246272⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179496106048,-179361956224⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1555_ok : ecellOkT e1555 = true := by decide +kernel
theorem e1555_pos {a z : ℝ} (ha1 : ((246609/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((616947/4096000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1555 e1555_ok ha1 ha2 hz1 hz2 hz

-- box ['616947/4096000', '1234743/8192000', '3997/4000', '1599/1600']  interval_lower 59862847/549755813888
noncomputable def e1556 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265122077048,0,true,154264246208,154264246272⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933901178504,0,false,-179496106048,-179496105984⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265236027900,0,true,154363275904,154363275968⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933787227652,0,false,-179630272192,-179630272128⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1264997869211,0,true,154156292480,154156292544⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨934025386341,0,false,-179349881920,-179349881856⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265132450150,0,true,154273261440,154273261504⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933890805402,0,false,-179508318720,-179508318656⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564244503,0,true,52615424,52615488⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099459011049,0,false,-52618048,-52617984⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099574813452,0,true,63183808,63183872⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099448442100,0,false,-63187520,-63187456⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624144,0,false,-3648,-3584⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625259,0,false,-2560,-2496⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265059969125,0,true,154210267200,154210267264⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933963286427,0,false,-179422986880,-179422986816⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265184243648,0,true,154318273600,154318273664⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933839011904,0,false,-179569299200,-179569299136⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074548348665,0,false,-25251025600,-25251025536⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074585785583,0,false,-25212719616,-25212719552⟩
    { al := (616947/4096000), au := (1234743/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨165610449272,165724400124⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154264246208,154264246272⟩ : DyadicInterval 40),(⟨-179496106048,-179496105984⟩ : DyadicInterval 40),(⟨749603516591,749603535921⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154363275904,154363275968⟩ : DyadicInterval 40),(⟨-179630272192,-179630272128⟩ : DyadicInterval 40),(⟨749586215462,749586234792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154156292480,154156292544⟩ : DyadicInterval 40),(⟨-179349881920,-179349881856⟩ : DyadicInterval 40),(⟨749622361248,749622380578⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154273261440,154273261504⟩ : DyadicInterval 40),(⟨-179508318720,-179508318656⟩ : DyadicInterval 40),(⟨749601942124,749601961453⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨52616727,63185676⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52615424,52615488⟩ : DyadicInterval 40),(⟨-52618048,-52617984⟩ : DyadicInterval 40),(⟨762123382345,762123401675⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63183808,63183872⟩ : DyadicInterval 40),(⟨-63187520,-63187456⟩ : DyadicInterval 40),(⟨762123381776,762123401106⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3648,-2496⟩ : DyadicInterval 40),(⟨762123384864,762123404704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165548341349,165672615872⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154210267200,154210267264⟩ : DyadicInterval 40),(⟨-179422986880,-179422986816⟩ : DyadicInterval 40),(⟨749612941333,749612960662⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154318273600,154318273664⟩ : DyadicInterval 40),(⟨-179569299200,-179569299136⟩ : DyadicInterval 40),(⟨749594079342,749594098671⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25251025600,-25212719552⟩ : DyadicInterval 40),(⟨774729743392,774748915680⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154264246208,154363275968⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179630272192,-179496105984⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1556_ok : ecellOkT e1556 = true := by decide +kernel
theorem e1556_pos {a z : ℝ} (ha1 : ((616947/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1234743/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1556 e1556_ok ha1 ha2 hz1 hz2 hz

-- box ['1234743/8192000', '154449/1024000', '3997/4000', '1599/1600']  interval_lower 60337727/549755813888
noncomputable def e1557 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265236027899,0,true,154363275904,154363275968⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933787227653,0,false,-179630272192,-179630272128⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265349978751,0,true,154462296704,154462296768⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933673276801,0,false,-179764454720,-179764454656⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265111734598,0,true,154255257600,154255257664⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933911520954,0,false,-179483929600,-179483929536⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265246329782,0,true,154372228416,154372228480⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933776925770,0,false,-179642402496,-179642402432⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564281922,0,true,52652864,52652928⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458973630,0,false,-52655424,-52655360⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099574858356,0,true,63228736,63228800⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099448397196,0,false,-63232448,-63232384⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624139,0,false,-3648,-3584⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625255,0,false,-2560,-2496⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265173877499,0,true,154309264832,154309264896⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933849378053,0,false,-179557094080,-179557094016⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265298158892,0,true,154417267456,154417267520⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933725096660,0,false,-179703432384,-179703432320⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074514007737,0,false,-25286164864,-25286164800⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074551472477,0,false,-25247829184,-25247829120⟩
    { al := (1234743/8192000), au := (154449/1024000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨165724400123,165838350975⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154363275904,154363275968⟩ : DyadicInterval 40),(⟨-179630272192,-179630272128⟩ : DyadicInterval 40),(⟨749586215463,749586234792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154462296704,154462296768⟩ : DyadicInterval 40),(⟨-179764454720,-179764454656⟩ : DyadicInterval 40),(⟨749568902242,749568921571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154255257600,154255257664⟩ : DyadicInterval 40),(⟨-179483929600,-179483929536⟩ : DyadicInterval 40),(⟨749605086274,749605105603⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154372228416,154372228480⟩ : DyadicInterval 40),(⟨-179642402496,-179642402432⟩ : DyadicInterval 40),(⟨749584650724,749584670053⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨52654146,63230580⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52652864,52652928⟩ : DyadicInterval 40),(⟨-52655424,-52655360⟩ : DyadicInterval 40),(⟨762123382310,762123401639⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63228736,63228800⟩ : DyadicInterval 40),(⟨-63232448,-63232384⟩ : DyadicInterval 40),(⟨762123381771,762123401100⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3648,-2496⟩ : DyadicInterval 40),(⟨762123384864,762123404704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165662249723,165786531116⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154309264832,154309264896⟩ : DyadicInterval 40),(⟨-179557094080,-179557094016⟩ : DyadicInterval 40),(⟨749595653242,749595672571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154417267456,154417267520⟩ : DyadicInterval 40),(⟨-179703432384,-179703432320⟩ : DyadicInterval 40),(⟨749576777065,749576796395⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25286164864,-25247829120⟩ : DyadicInterval 40),(⟨774747298176,774766485312⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154363275904,154462296768⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179764454720,-179630272128⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1557_ok : ecellOkT e1557 = true := by decide +kernel
theorem e1557_pos {a z : ℝ} (ha1 : ((1234743/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((154449/1024000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1557 e1557_ok ha1 ha2 hz1 hz2 hz

-- box ['616947/4096000', '1234743/8192000', '1599/1600', '1999/2000']  interval_lower 59794113/549755813888
noncomputable def e1558 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265122077048,0,true,154264246208,154264246272⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933901178504,0,false,-179496106048,-179496105984⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265236027900,0,true,154363275904,154363275968⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933787227652,0,false,-179630272192,-179630272128⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265018570517,0,true,154174285504,154174285568⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨934004685035,0,false,-179374251264,-179374251200⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265153165701,0,true,154291264896,154291264960⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933870089851,0,false,-179532708352,-179532708288⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099553721195,0,true,42092608,42092672⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099469534357,0,false,-42094272,-42094208⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564282659,0,true,52653568,52653632⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458972893,0,false,-52656192,-52656128⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625254,0,false,-2560,-2496⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626165,0,false,-1664,-1600⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265070319661,0,true,154219263232,154219263296⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933952935891,0,false,-179435172096,-179435172032⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265194601324,0,true,154327274944,154327275008⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933828654228,0,false,-179581494528,-179581494464⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074545227212,0,false,-25254219584,-25254219520⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074582668622,0,false,-25215908864,-25215908800⟩
    { al := (616947/4096000), au := (1234743/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨165610449272,165724400124⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154264246208,154264246272⟩ : DyadicInterval 40),(⟨-179496106048,-179496105984⟩ : DyadicInterval 40),(⟨749603516591,749603535921⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154363275904,154363275968⟩ : DyadicInterval 40),(⟨-179630272192,-179630272128⟩ : DyadicInterval 40),(⟨749586215462,749586234792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154174285504,154174285568⟩ : DyadicInterval 40),(⟨-179374251264,-179374251200⟩ : DyadicInterval 40),(⟨749619221472,749619240801⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154291264896,154291264960⟩ : DyadicInterval 40),(⟨-179532708352,-179532708288⟩ : DyadicInterval 40),(⟨749598797614,749598816943⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨42093419,52654883⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42092608,42092672⟩ : DyadicInterval 40),(⟨-42094272,-42094208⟩ : DyadicInterval 40),(⟨762123382772,762123402101⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52653568,52653632⟩ : DyadicInterval 40),(⟨-52656192,-52656128⟩ : DyadicInterval 40),(⟨762123382342,762123401671⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2560,-1600⟩ : DyadicInterval 40),(⟨762123384416,762123404160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165558691885,165682973548⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154219263232,154219263296⟩ : DyadicInterval 40),(⟨-179435172096,-179435172032⟩ : DyadicInterval 40),(⟨749611370873,749611390202⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154327274944,154327275008⟩ : DyadicInterval 40),(⟨-179581494528,-179581494464⟩ : DyadicInterval 40),(⟨749592506642,749592525971⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25254219584,-25215908800⟩ : DyadicInterval 40),(⟨774731338016,774750512672⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154264246208,154363275968⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179630272192,-179496105984⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1558_ok : ecellOkT e1558 = true := by decide +kernel
theorem e1558_pos {a z : ℝ} (ha1 : ((616947/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1234743/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1558 e1558_ok ha1 ha2 hz1 hz2 hz

-- box ['1234743/8192000', '154449/1024000', '1599/1600', '1999/2000']  interval_lower 120537087/1099511627776
noncomputable def e1559 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265236027899,0,true,154363275904,154363275968⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933787227653,0,false,-179630272192,-179630272128⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265349978751,0,true,154462296704,154462296768⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933673276801,0,false,-179764454720,-179764454656⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265132450148,0,true,154273261376,154273261440⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933890805404,0,false,-179508318720,-179508318656⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265267059576,0,true,154390242624,154390242688⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933756195976,0,false,-179666811840,-179666811776⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099553751129,0,true,42122496,42122560⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099469504423,0,false,-42124160,-42124096⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564320080,0,true,52691008,52691072⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458935472,0,false,-52693568,-52693504⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625250,0,false,-2560,-2496⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626163,0,false,-1664,-1600⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265184234898,0,true,154318265984,154318266048⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933839020654,0,false,-179569288896,-179569288832⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265308523691,0,true,154426274176,154426274240⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933714731861,0,false,-179715637568,-179715637504⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074510881989,0,false,-25289363328,-25289363264⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074548351302,0,false,-25251022912,-25251022848⟩
    { al := (1234743/8192000), au := (154449/1024000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨165724400123,165838350975⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154363275904,154363275968⟩ : DyadicInterval 40),(⟨-179630272192,-179630272128⟩ : DyadicInterval 40),(⟨749586215463,749586234792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154462296704,154462296768⟩ : DyadicInterval 40),(⟨-179764454720,-179764454656⟩ : DyadicInterval 40),(⟨749568902242,749568921571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154273261376,154273261440⟩ : DyadicInterval 40),(⟨-179508318720,-179508318656⟩ : DyadicInterval 40),(⟨749601942161,749601961490⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154390242624,154390242688⟩ : DyadicInterval 40),(⟨-179666811840,-179666811776⟩ : DyadicInterval 40),(⟨749581501843,749581521172⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨42123353,52692304⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42122496,42122560⟩ : DyadicInterval 40),(⟨-42124160,-42124096⟩ : DyadicInterval 40),(⟨762123382770,762123402099⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52691008,52691072⟩ : DyadicInterval 40),(⟨-52693568,-52693504⟩ : DyadicInterval 40),(⟨762123382306,762123401635⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2560,-1600⟩ : DyadicInterval 40),(⟨762123384416,762123404160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165672607122,165796895915⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154318265984,154318266048⟩ : DyadicInterval 40),(⟨-179569288896,-179569288832⟩ : DyadicInterval 40),(⟨749594080676,749594100006⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154426274176,154426274240⟩ : DyadicInterval 40),(⟨-179715637568,-179715637504⟩ : DyadicInterval 40),(⟨749575202178,749575221508⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25289363328,-25251022848⟩ : DyadicInterval 40),(⟨774748895040,774768084544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154363275904,154462296768⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179764454720,-179630272128⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1559_ok : ecellOkT e1559 = true := by decide +kernel
theorem e1559_pos {a z : ℝ} (ha1 : ((1234743/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((154449/1024000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1559 e1559_ok ha1 ha2 hz1 hz2 hz

end CKLaneC2R.EpCells.B025

end


