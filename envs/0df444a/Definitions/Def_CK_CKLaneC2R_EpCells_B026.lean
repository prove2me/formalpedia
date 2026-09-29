-- Prove2me | Definitions.Def_CK_CKLaneC2R_EpCells_B026
-- name    : CK_CKLaneC2R_EpCells_B026
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T14:15:38.257306+00:00
-- url     : https://prove2.me/theorems/e98ff6c0-3951-461e-b95b-93ff389b4419
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EpCells.B026` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EpCells.B026` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EpCells.B026` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EpCells.B026 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EpCells/B026.lean)

import Definitions.Def_CK_CKLaneC2R_EndpointCheckT

-- ===== source module CKLaneC2R.EpCells.B026 =====
section

namespace CKLaneC2R.EpCells.B026

open GeneralCK GeneralCK.Certificates CKLaneC2R CKLaneC2R.Endpoint

-- box ['3/20', '1229649/8192000', '1999/2000', '7997/8000']  interval_lower 56905319/549755813888
noncomputable def e1560 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1264438371942,0,true,153669880704,153669880768⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨934584883610,0,false,-178691452736,-178691452672⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1264552322794,0,true,153768963968,153768964032⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨934470932758,0,false,-178825520768,-178825520704⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1264355908569,0,true,153598171136,153598171200⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨934667346983,0,false,-178594441280,-178594441216⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1264490432534,0,true,153715149888,153715149952⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨934532823018,0,false,-178752702208,-178752702144⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543063166,0,true,31434880,31434944⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099480192386,0,false,-31435840,-31435776⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099553572241,0,true,41943616,41943680⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099469683311,0,false,-41945280,-41945216⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626175,0,false,-1664,-1600⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626878,0,false,-960,-896⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1264397136053,0,true,153634022848,153634022912⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨934626119499,0,false,-178642940992,-178642940928⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1264521382112,0,true,153742061120,153742061184⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨934501873440,0,false,-178789116096,-178789116032⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074747706833,0,false,-25047054976,-25047054912⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074784985372,0,false,-25008918144,-25008918080⟩
    { al := (3/20), au := (1229649/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨164926744166,165040695018⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153669880704,153669880768⟩ : DyadicInterval 40),(⟨-178691452736,-178691452672⟩ : DyadicInterval 40),(⟨749707069559,749707088889⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153768963968,153768964032⟩ : DyadicInterval 40),(⟨-178825520768,-178825520704⟩ : DyadicInterval 40),(⟨749689840933,749689860262⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153598171136,153598171200⟩ : DyadicInterval 40),(⟨-178594441280,-178594441216⟩ : DyadicInterval 40),(⟨749719529915,749719549245⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153715149888,153715149952⟩ : DyadicInterval 40),(⟨-178752702208,-178752702144⟩ : DyadicInterval 40),(⟨749699199822,749699219151⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨31435390,41944465⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨31434880,31434944⟩ : DyadicInterval 40),(⟨-31435840,-31435776⟩ : DyadicInterval 40),(⟨762123383133,762123402462⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨41943616,41943680⟩ : DyadicInterval 40),(⟨-41945280,-41945216⟩ : DyadicInterval 40),(⟨762123382783,762123402112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1664,-896⟩ : DyadicInterval 40),(⟨762123384064,762123403712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨164885508277,165009754336⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153634022848,153634022912⟩ : DyadicInterval 40),(⟨-178642940992,-178642940928⟩ : DyadicInterval 40),(⟨749713301164,749713320493⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153742061120,153742061184⟩ : DyadicInterval 40),(⟨-178789116096,-178789116032⟩ : DyadicInterval 40),(⟨749694520143,749694539473⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25047054976,-25008918080⟩ : DyadicInterval 40),(⟨774627842656,774646930368⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨153669880704,153768964032⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-178825520768,-178691452672⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1560_ok : ecellOkT e1560 = true := by decide +kernel
theorem e1560_pos {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1229649/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1560 e1560_ok ha1 ha2 hz1 hz2 hz

-- box ['1229649/8192000', '615249/4096000', '1999/2000', '7997/8000']  interval_lower 57372317/549755813888
noncomputable def e1561 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1264552322793,0,true,153768963968,153768964032⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨934470932759,0,false,-178825520768,-178825520704⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1264666273645,0,true,153868038272,153868038336⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨934356981907,0,false,-178959605120,-178959605056⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1264469802445,0,true,153697211264,153697211328⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨934553453107,0,false,-178728430464,-178728430400⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1264604340653,0,true,153814191872,153814191936⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨934418914899,0,false,-178886727424,-178886727360⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543085609,0,true,31457344,31457408⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099480169943,0,false,-31458304,-31458240⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099553602166,0,true,41973568,41973632⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099469653386,0,false,-41975232,-41975168⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626173,0,false,-1664,-1600⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626876,0,false,-960,-896⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1264511058668,0,true,153733084736,153733084800⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨934512196884,0,false,-178776969856,-178776969792⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1264635311595,0,true,153841119296,153841119360⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨934387943957,0,false,-178923170880,-178923170816⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074713498980,0,false,-25082051584,-25082051520⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074750805329,0,false,-25043885056,-25043884992⟩
    { al := (1229649/8192000), au := (615249/4096000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨165040695017,165154645869⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153768963968,153768964032⟩ : DyadicInterval 40),(⟨-178825520768,-178825520704⟩ : DyadicInterval 40),(⟨749689840933,749689860263⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153868038272,153868038336⟩ : DyadicInterval 40),(⟨-178959605120,-178959605056⟩ : DyadicInterval 40),(⟨749672600231,749672619560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153697211264,153697211328⟩ : DyadicInterval 40),(⟨-178728430464,-178728430400⟩ : DyadicInterval 40),(⟨749702318683,749702338012⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153814191872,153814191936⟩ : DyadicInterval 40),(⟨-178886727424,-178886727360⟩ : DyadicInterval 40),(⟨749681972167,749681991496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨31457833,41974390⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨31457344,31457408⟩ : DyadicInterval 40),(⟨-31458304,-31458240⟩ : DyadicInterval 40),(⟨762123383131,762123402460⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨41973568,41973632⟩ : DyadicInterval 40),(⟨-41975232,-41975168⟩ : DyadicInterval 40),(⟨762123382781,762123402110⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1664,-896⟩ : DyadicInterval 40),(⟨762123384064,762123403712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨164999430892,165123683819⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153733084736,153733084800⟩ : DyadicInterval 40),(⟨-178776969856,-178776969792⟩ : DyadicInterval 40),(⟨749696081197,749696100527⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153841119296,153841119360⟩ : DyadicInterval 40),(⟨-178923170880,-178923170816⟩ : DyadicInterval 40),(⟨749677285947,749677305277⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25082051584,-25043884992⟩ : DyadicInterval 40),(⟨774645326112,774664428672⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨153768963968,153868038336⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-178959605120,-178825520704⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1561_ok : ecellOkT e1561 = true := by decide +kernel
theorem e1561_pos {a z : ℝ} (ha1 : ((1229649/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((615249/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1561 e1561_ok ha1 ha2 hz1 hz2 hz

-- box ['3/20', '1229649/8192000', '7997/8000', '3999/4000']  interval_lower 28418707/274877906944
noncomputable def e1562 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1264438371942,0,true,153669880704,153669880768⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨934584883610,0,false,-178691452736,-178691452672⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1264552322794,0,true,153768963968,153768964032⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨934470932758,0,false,-178825520768,-178825520704⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1264376524412,0,true,153616098944,153616099008⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨934646731140,0,false,-178618693376,-178618693312⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1264511062621,0,true,153733088192,153733088256⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨934512192931,0,false,-178776974528,-178776974464⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099532584660,0,true,20956672,20956736⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490670892,0,false,-20957120,-20957056⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543086255,0,true,31457984,31458048⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099480169297,0,false,-31458944,-31458880⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626875,0,false,-960,-896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627377,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1264407443898,0,true,153642986432,153642986496⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨934615811654,0,false,-178655067392,-178655067328⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1264531697102,0,true,153751030080,153751030144⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨934491558450,0,false,-178801252544,-178801252480⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074744610681,0,false,-25050222464,-25050222400⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074781893695,0,false,-25012080960,-25012080896⟩
    { al := (3/20), au := (1229649/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨164926744166,165040695018⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153669880704,153669880768⟩ : DyadicInterval 40),(⟨-178691452736,-178691452672⟩ : DyadicInterval 40),(⟨749707069559,749707088889⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153768963968,153768964032⟩ : DyadicInterval 40),(⟨-178825520768,-178825520704⟩ : DyadicInterval 40),(⟨749689840933,749689860262⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153616098944,153616099008⟩ : DyadicInterval 40),(⟨-178618693376,-178618693312⟩ : DyadicInterval 40),(⟨749716415447,749716434777⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153733088192,153733088256⟩ : DyadicInterval 40),(⟨-178776974528,-178776974464⟩ : DyadicInterval 40),(⟨749696080598,749696099928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨20956884,31458479⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨20956672,20956736⟩ : DyadicInterval 40),(⟨-20957120,-20957056⟩ : DyadicInterval 40),(⟨762123383376,762123402705⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨31457984,31458048⟩ : DyadicInterval 40),(⟨-31458944,-31458880⟩ : DyadicInterval 40),(⟨762123383131,762123402460⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-960,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨164895816122,165020069326⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153642986432,153642986496⟩ : DyadicInterval 40),(⟨-178655067392,-178655067328⟩ : DyadicInterval 40),(⟨749711743582,749711762912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153751030080,153751030144⟩ : DyadicInterval 40),(⟨-178801252544,-178801252480⟩ : DyadicInterval 40),(⟨749692960277,749692979607⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25050222464,-25012080896⟩ : DyadicInterval 40),(⟨774629424064,774648514112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨153669880704,153768964032⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-178825520768,-178691452672⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1562_ok : ecellOkT e1562 = true := by decide +kernel
theorem e1562_pos {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1229649/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1562 e1562_ok ha1 ha2 hz1 hz2 hz

-- box ['1229649/8192000', '615249/4096000', '7997/8000', '3999/4000']  interval_lower 55961/536870912
noncomputable def e1563 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1264552322793,0,true,153768963968,153768964032⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨934470932759,0,false,-178825520768,-178825520704⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1264666273645,0,true,153868038272,153868038336⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨934356981907,0,false,-178959605120,-178959605056⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1264490432532,0,true,153715149888,153715149952⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨934532823020,0,false,-178752702208,-178752702144⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1264624984984,0,true,153832140992,153832141056⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨934398270568,0,false,-178911019456,-178911019392⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099532599622,0,true,20971584,20971648⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490655930,0,false,-20972096,-20972032⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543108699,0,true,31480448,31480512⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099480146853,0,false,-31481408,-31481344⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626874,0,false,-960,-896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627376,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1264521373383,0,true,153742053504,153742053568⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨934501882169,0,false,-178789105856,-178789105792⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1264645633710,0,true,153850093568,153850093632⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨934377621842,0,false,-178935317184,-178935317120⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074710398551,0,false,-25085223552,-25085223488⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074747709454,0,false,-25047052288,-25047052224⟩
    { al := (1229649/8192000), au := (615249/4096000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨165040695017,165154645869⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153768963968,153768964032⟩ : DyadicInterval 40),(⟨-178825520768,-178825520704⟩ : DyadicInterval 40),(⟨749689840933,749689860263⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153868038272,153868038336⟩ : DyadicInterval 40),(⟨-178959605120,-178959605056⟩ : DyadicInterval 40),(⟨749672600231,749672619560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153715149888,153715149952⟩ : DyadicInterval 40),(⟨-178752702208,-178752702144⟩ : DyadicInterval 40),(⟨749699199822,749699219152⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153832140992,153832141056⟩ : DyadicInterval 40),(⟨-178911019456,-178911019392⟩ : DyadicInterval 40),(⟨749678848571,749678867900⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨20971846,31480923⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨20971584,20971648⟩ : DyadicInterval 40),(⟨-20972096,-20972032⟩ : DyadicInterval 40),(⟨762123383407,762123402736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨31480448,31480512⟩ : DyadicInterval 40),(⟨-31481408,-31481344⟩ : DyadicInterval 40),(⟨762123383130,762123402459⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-960,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165009745607,165134005934⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153742053504,153742053568⟩ : DyadicInterval 40),(⟨-178789105856,-178789105792⟩ : DyadicInterval 40),(⟨749694521491,749694540821⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153850093568,153850093632⟩ : DyadicInterval 40),(⟨-178935317184,-178935317120⟩ : DyadicInterval 40),(⟨749675723949,749675743278⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25085223552,-25047052224⟩ : DyadicInterval 40),(⟨774646909728,774666014656⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨153768963968,153868038336⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-178959605120,-178825520704⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1563_ok : ecellOkT e1563 = true := by decide +kernel
theorem e1563_pos {a z : ℝ} (ha1 : ((1229649/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((615249/4096000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1563 e1563_ok ha1 ha2 hz1 hz2 hz

-- box ['615249/4096000', '1231347/8192000', '1999/2000', '7997/8000']  interval_lower 28920253/274877906944
noncomputable def e1564 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1264666273644,0,true,153868038272,153868038336⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨934356981908,0,false,-178959605120,-178959605056⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1264780224496,0,true,153967103616,153967103680⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨934243031056,0,false,-179093705792,-179093705728⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1264583696321,0,true,153796242496,153796242560⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨934439559231,0,false,-178862435904,-178862435840⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1264718248773,0,true,153913224960,153913225024⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨934305006779,0,false,-179020768896,-179020768832⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543108053,0,true,31479808,31479872⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099480147499,0,false,-31480768,-31480704⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099553632094,0,true,42003456,42003520⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099469623458,0,false,-42005184,-42005120⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626171,0,false,-1664,-1600⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626875,0,false,-960,-896⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1264624981030,0,true,153832137536,153832137600⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨934398274522,0,false,-178911014784,-178911014720⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1264749241083,0,true,153940168512,153940168576⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨934274014469,0,false,-179057241984,-179057241920⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074679267515,0,false,-25117073472,-25117073408⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074716601754,0,false,-25078877184,-25078877120⟩
    { al := (615249/4096000), au := (1231347/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨165154645868,165268596720⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153868038272,153868038336⟩ : DyadicInterval 40),(⟨-178959605120,-178959605056⟩ : DyadicInterval 40),(⟨749672600231,749672619561⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153967103616,153967103680⟩ : DyadicInterval 40),(⟨-179093705792,-179093705728⟩ : DyadicInterval 40),(⟨749655347452,749655366781⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153796242496,153796242560⟩ : DyadicInterval 40),(⟨-178862435904,-178862435840⟩ : DyadicInterval 40),(⟨749685095335,749685114664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153913224960,153913225024⟩ : DyadicInterval 40),(⟨-179020768896,-179020768832⟩ : DyadicInterval 40),(⟨749664732390,749664751719⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨31480277,42004318⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨31479808,31479872⟩ : DyadicInterval 40),(⟨-31480768,-31480704⟩ : DyadicInterval 40),(⟨762123383130,762123402459⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42003456,42003520⟩ : DyadicInterval 40),(⟨-42005184,-42005120⟩ : DyadicInterval 40),(⟨762123382811,762123402140⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1664,-896⟩ : DyadicInterval 40),(⟨762123384064,762123403712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165113353254,165237613307⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153832137536,153832137600⟩ : DyadicInterval 40),(⟨-178911014784,-178911014720⟩ : DyadicInterval 40),(⟨749678849171,749678868501⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153940168512,153940168576⟩ : DyadicInterval 40),(⟨-179057241984,-179057241920⟩ : DyadicInterval 40),(⟨749660039683,749660059012⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25117073472,-25078877120⟩ : DyadicInterval 40),(⟨774662822176,774681939616⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨153868038272,153967103680⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179093705792,-178959605056⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1564_ok : ecellOkT e1564 = true := by decide +kernel
theorem e1564_pos {a z : ℝ} (ha1 : ((615249/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1231347/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1564 e1564_ok ha1 ha2 hz1 hz2 hz

-- box ['1231347/8192000', '308049/2048000', '1999/2000', '7997/8000']  interval_lower 116619601/1099511627776
noncomputable def e1565 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1264780224495,0,true,153967103616,153967103680⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨934243031057,0,false,-179093705792,-179093705728⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1264894175347,0,true,154066160064,154066160128⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨934129080205,0,false,-179227822848,-179227822784⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1264697590196,0,true,153895264832,153895264896⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨934325665356,0,false,-178996457728,-178996457664⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1264832156892,0,true,154012249088,154012249152⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨934191098660,0,false,-179154826816,-179154826752⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543130497,0,true,31502208,31502272⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099480125055,0,false,-31503232,-31503168⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099553662023,0,true,42033408,42033472⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099469593529,0,false,-42035072,-42035008⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626169,0,false,-1664,-1600⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626874,0,false,-960,-896⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1264738903390,0,true,153931181376,153931181440⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨934284352162,0,false,-179045076032,-179045075968⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1264863170564,0,true,154039208768,154039208832⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨934160084988,0,false,-179191329472,-179191329408⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074645012442,0,false,-25152120640,-25152120576⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074682374572,0,false,-25113894592,-25113894528⟩
    { al := (1231347/8192000), au := (308049/2048000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨165268596719,165382547571⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153967103616,153967103680⟩ : DyadicInterval 40),(⟨-179093705792,-179093705728⟩ : DyadicInterval 40),(⟨749655347452,749655366781⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154066160064,154066160128⟩ : DyadicInterval 40),(⟨-179227822848,-179227822784⟩ : DyadicInterval 40),(⟨749638082584,749638101914⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153895264832,153895264896⟩ : DyadicInterval 40),(⟨-178996457728,-178996457664⟩ : DyadicInterval 40),(⟨749667859926,749667879255⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154012249088,154012249152⟩ : DyadicInterval 40),(⟨-179154826816,-179154826752⟩ : DyadicInterval 40),(⟨749647480607,749647499936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨31502721,42034247⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨31502208,31502272⟩ : DyadicInterval 40),(⟨-31503232,-31503168⟩ : DyadicInterval 40),(⟨762123383161,762123402490⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42033408,42033472⟩ : DyadicInterval 40),(⟨-42035072,-42035008⟩ : DyadicInterval 40),(⟨762123382777,762123402106⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1664,-896⟩ : DyadicInterval 40),(⟨762123384064,762123403712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165227275614,165351542788⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153931181376,153931181440⟩ : DyadicInterval 40),(⟨-179045076032,-179045075968⟩ : DyadicInterval 40),(⟨749661605081,749661624410⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154039208768,154039208832⟩ : DyadicInterval 40),(⟨-179191329472,-179191329408⟩ : DyadicInterval 40),(⟨749642781377,749642800706⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25152120640,-25113894528⟩ : DyadicInterval 40),(⟨774680330880,774699463200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨153967103616,154066160128⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179227822848,-179093705728⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1565_ok : ecellOkT e1565 = true := by decide +kernel
theorem e1565_pos {a z : ℝ} (ha1 : ((1231347/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((308049/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1565 e1565_ok ha1 ha2 hz1 hz2 hz

-- box ['615249/4096000', '1231347/8192000', '7997/8000', '3999/4000']  interval_lower 115544409/1099511627776
noncomputable def e1566 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1264666273644,0,true,153868038272,153868038336⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨934356981908,0,false,-178959605120,-178959605056⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1264780224496,0,true,153967103616,153967103680⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨934243031056,0,false,-179093705792,-179093705728⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1264604340651,0,true,153814191872,153814191936⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨934418914901,0,false,-178886727424,-178886727360⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1264738907347,0,true,153931184832,153931184896⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨934284348205,0,false,-179045080704,-179045080640⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099532614585,0,true,20986560,20986624⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490640967,0,false,-20987072,-20987008⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543131144,0,true,31502912,31502976⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099480124408,0,false,-31503872,-31503808⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626873,0,false,-960,-896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627376,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1264635303119,0,true,153841111872,153841111936⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨934387952433,0,false,-178923160896,-178923160832⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1264759570316,0,true,153949148224,153949148288⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨934263685236,0,false,-179069398144,-179069398080⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074676162807,0,false,-25120249920,-25120249856⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074713501527,0,false,-25082048960,-25082048896⟩
    { al := (615249/4096000), au := (1231347/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨165154645868,165268596720⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153868038272,153868038336⟩ : DyadicInterval 40),(⟨-178959605120,-178959605056⟩ : DyadicInterval 40),(⟨749672600231,749672619561⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153967103616,153967103680⟩ : DyadicInterval 40),(⟨-179093705792,-179093705728⟩ : DyadicInterval 40),(⟨749655347452,749655366781⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153814191872,153814191936⟩ : DyadicInterval 40),(⟨-178886727424,-178886727360⟩ : DyadicInterval 40),(⟨749681972167,749681991497⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153931184832,153931184896⟩ : DyadicInterval 40),(⟨-179045080704,-179045080640⟩ : DyadicInterval 40),(⟨749661604479,749661623808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨20986809,31503368⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨20986560,20986624⟩ : DyadicInterval 40),(⟨-20987072,-20987008⟩ : DyadicInterval 40),(⟨762123383407,762123402736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨31502912,31502976⟩ : DyadicInterval 40),(⟨-31503872,-31503808⟩ : DyadicInterval 40),(⟨762123383129,762123402458⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-960,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165123675343,165247942540⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153841111872,153841111936⟩ : DyadicInterval 40),(⟨-178923160896,-178923160832⟩ : DyadicInterval 40),(⟨749677287257,749677306586⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153949148224,153949148288⟩ : DyadicInterval 40),(⟨-179069398144,-179069398080⟩ : DyadicInterval 40),(⟨749658475476,749658494806⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25120249920,-25082048896⟩ : DyadicInterval 40),(⟨774664408064,774683527840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨153868038272,153967103680⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179093705792,-178959605056⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1566_ok : ecellOkT e1566 = true := by decide +kernel
theorem e1566_pos {a z : ℝ} (ha1 : ((615249/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1231347/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1566 e1566_ok ha1 ha2 hz1 hz2 hz

-- box ['1231347/8192000', '308049/2048000', '7997/8000', '3999/4000']  interval_lower 116482555/1099511627776
noncomputable def e1567 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1264780224495,0,true,153967103616,153967103680⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨934243031057,0,false,-179093705792,-179093705728⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1264894175347,0,true,154066160064,154066160128⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨934129080205,0,false,-179227822848,-179227822784⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1264718248771,0,true,153913224960,153913225024⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨934305006781,0,false,-179020768896,-179020768832⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1264852829711,0,true,154030219712,154030219776⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨934170425841,0,false,-179179158272,-179179158208⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099532629548,0,true,21001536,21001600⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490626004,0,false,-21001984,-21001920⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543153591,0,true,31525312,31525376⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099480101961,0,false,-31526272,-31526208⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626872,0,false,-960,-896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627375,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1264749232349,0,true,153940160896,153940160960⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨934274023203,0,false,-179057231680,-179057231616⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1264873506922,0,true,154048193856,154048193920⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨934149748630,0,false,-179203495488,-179203495424⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074641903451,0,false,-25155301568,-25155301504⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074679270141,0,false,-25117070784,-25117070720⟩
    { al := (1231347/8192000), au := (308049/2048000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨165268596719,165382547571⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153967103616,153967103680⟩ : DyadicInterval 40),(⟨-179093705792,-179093705728⟩ : DyadicInterval 40),(⟨749655347452,749655366781⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154066160064,154066160128⟩ : DyadicInterval 40),(⟨-179227822848,-179227822784⟩ : DyadicInterval 40),(⟨749638082584,749638101914⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153913224960,153913225024⟩ : DyadicInterval 40),(⟨-179020768896,-179020768832⟩ : DyadicInterval 40),(⟨749664732390,749664751719⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154030219712,154030219776⟩ : DyadicInterval 40),(⟨-179179158272,-179179158208⟩ : DyadicInterval 40),(⟨749644348321,749644367650⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21001772,31525815⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21001536,21001600⟩ : DyadicInterval 40),(⟨-21001984,-21001920⟩ : DyadicInterval 40),(⟨762123383374,762123402703⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨31525312,31525376⟩ : DyadicInterval 40),(⟨-31526272,-31526208⟩ : DyadicInterval 40),(⟨762123383128,762123402457⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-960,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165237604573,165361879146⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153940160896,153940160960⟩ : DyadicInterval 40),(⟨-179057231680,-179057231616⟩ : DyadicInterval 40),(⟨749660041007,749660060337⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154048193856,154048193920⟩ : DyadicInterval 40),(⟨-179203495488,-179203495424⟩ : DyadicInterval 40),(⟨749641214995,749641234325⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25155301568,-25117070720⟩ : DyadicInterval 40),(⟨774681918976,774701053664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨153967103616,154066160128⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179227822848,-179093705728⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1567_ok : ecellOkT e1567 = true := by decide +kernel
theorem e1567_pos {a z : ℝ} (ha1 : ((1231347/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((308049/2048000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1567 e1567_ok ha1 ha2 hz1 hz2 hz

-- box ['3/20', '1229649/8192000', '3999/4000', '7999/8000']  interval_lower 113539285/1099511627776
noncomputable def e1568 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1264438371942,0,true,153669880704,153669880768⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨934584883610,0,false,-178691452736,-178691452672⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1264552322794,0,true,153768963968,153768964032⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨934470932758,0,false,-178825520768,-178825520704⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1264397140255,0,true,153634026496,153634026560⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨934626115297,0,false,-178642945920,-178642945856⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1264531692708,0,true,153751026240,153751026304⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨934491562844,0,false,-178801247360,-178801247296⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522106112,0,true,10478272,10478336⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099501149440,0,false,-10478400,-10478336⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099532600224,0,true,20972224,20972288⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490655328,0,false,-20972672,-20972608⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627375,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627677,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1264417752024,0,true,153651950208,153651950272⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨934605503528,0,false,-178667194304,-178667194240⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1264542012115,0,true,153759998912,153759998976⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨934481243437,0,false,-178813389120,-178813389056⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074741514330,0,false,-25053390144,-25053390080⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074778801740,0,false,-25015244032,-25015243968⟩
    { al := (3/20), au := (1229649/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨164926744166,165040695018⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153669880704,153669880768⟩ : DyadicInterval 40),(⟨-178691452736,-178691452672⟩ : DyadicInterval 40),(⟨749707069559,749707088889⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153768963968,153768964032⟩ : DyadicInterval 40),(⟨-178825520768,-178825520704⟩ : DyadicInterval 40),(⟨749689840933,749689860262⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153634026496,153634026560⟩ : DyadicInterval 40),(⟨-178642945920,-178642945856⟩ : DyadicInterval 40),(⟨749713300526,749713319855⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153751026240,153751026304⟩ : DyadicInterval 40),(⟨-178801247360,-178801247296⟩ : DyadicInterval 40),(⟨749692960947,749692980277⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10478336,20972448⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10478272,10478336⟩ : DyadicInterval 40),(⟨-10478400,-10478336⟩ : DyadicInterval 40),(⟨762123383516,762123402845⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨20972224,20972288⟩ : DyadicInterval 40),(⟨-20972672,-20972608⟩ : DyadicInterval 40),(⟨762123383375,762123402704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨164906124248,165030384339⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153651950208,153651950272⟩ : DyadicInterval 40),(⟨-178667194304,-178667194240⟩ : DyadicInterval 40),(⟨749710185869,749710205198⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153759998912,153759998976⟩ : DyadicInterval 40),(⟨-178813389120,-178813389056⟩ : DyadicInterval 40),(⟨749691400338,749691419667⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25053390144,-25015243968⟩ : DyadicInterval 40),(⟨774631005600,774650097952⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨153669880704,153768964032⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-178825520768,-178691452672⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1568_ok : ecellOkT e1568 = true := by decide +kernel
theorem e1568_pos {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1229649/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1568 e1568_ok ha1 ha2 hz1 hz2 hz

-- box ['1229649/8192000', '615249/4096000', '3999/4000', '7999/8000']  interval_lower 114472339/1099511627776
noncomputable def e1569 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1264552322793,0,true,153768963968,153768964032⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨934470932759,0,false,-178825520768,-178825520704⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1264666273645,0,true,153868038272,153868038336⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨934356981907,0,false,-178959605120,-178959605056⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1264511062619,0,true,153733088192,153733088256⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨934512192933,0,false,-178776974528,-178776974464⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1264645629315,0,true,153850089792,153850089856⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨934377626237,0,false,-178935312000,-178935311936⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522113592,0,true,10485760,10485824⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099501141960,0,false,-10485888,-10485824⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099532615187,0,true,20987200,20987264⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490640365,0,false,-20987648,-20987584⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627375,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627676,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1264531688629,0,true,153751022656,153751022720⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨934491566923,0,false,-178801242560,-178801242496⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1264655955844,0,true,153859067840,153859067904⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨934367299708,0,false,-178947463616,-178947463552⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074707297922,0,false,-25088395712,-25088395648⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074744613226,0,false,-25050219840,-25050219776⟩
    { al := (1229649/8192000), au := (615249/4096000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨165040695017,165154645869⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153768963968,153768964032⟩ : DyadicInterval 40),(⟨-178825520768,-178825520704⟩ : DyadicInterval 40),(⟨749689840933,749689860263⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153868038272,153868038336⟩ : DyadicInterval 40),(⟨-178959605120,-178959605056⟩ : DyadicInterval 40),(⟨749672600231,749672619560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153733088192,153733088256⟩ : DyadicInterval 40),(⟨-178776974528,-178776974464⟩ : DyadicInterval 40),(⟨749696080598,749696099928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153850089792,153850089856⟩ : DyadicInterval 40),(⟨-178935312000,-178935311936⟩ : DyadicInterval 40),(⟨749675724583,749675743912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10485816,20987411⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10485760,10485824⟩ : DyadicInterval 40),(⟨-10485888,-10485824⟩ : DyadicInterval 40),(⟨762123383515,762123402844⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨20987200,20987264⟩ : DyadicInterval 40),(⟨-20987648,-20987584⟩ : DyadicInterval 40),(⟨762123383375,762123402704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165020060853,165144328068⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153751022656,153751022720⟩ : DyadicInterval 40),(⟨-178801242560,-178801242496⟩ : DyadicInterval 40),(⟨749692961585,749692980915⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153859067840,153859067904⟩ : DyadicInterval 40),(⟨-178947463616,-178947463552⟩ : DyadicInterval 40),(⟨749674161804,749674181133⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25088395712,-25050219776⟩ : DyadicInterval 40),(⟨774648493504,774667600736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨153768963968,153868038336⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-178959605120,-178825520704⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1569_ok : ecellOkT e1569 = true := by decide +kernel
theorem e1569_pos {a z : ℝ} (ha1 : ((1229649/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((615249/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1569 e1569_ok ha1 ha2 hz1 hz2 hz

-- box ['3/20', '1229649/8192000', '7999/8000', '1']  interval_lower 113403249/1099511627776
noncomputable def e1570 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1264438371942,0,true,153669880704,153669880768⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨934584883610,0,false,-178691452736,-178691452672⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1264552322794,0,true,153768963968,153768964032⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨934470932758,0,false,-178825520768,-178825520704⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1264417756098,0,true,153651953792,153651953856⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨934605499454,0,false,-178667199104,-178667199040⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522114151,0,true,10486272,10486336⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099501141401,0,false,-10486464,-10486400⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627675,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1264428059658,0,true,153660913472,153660913536⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨934595195894,0,false,-178679320704,-178679320640⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1264552327146,0,true,153768967744,153768967808⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨934470928406,0,false,-178825525888,-178825525824⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1074738417779,0,false,-25056558080,-25056558016⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1074775709740,0,false,-25018407168,-25018407104⟩
    { al := (3/20), au := (1229649/8192000), zl := (7999/8000), zu := 1,
      A := ⟨164926744166,165040695018⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153669880704,153669880768⟩ : DyadicInterval 40),(⟨-178691452736,-178691452672⟩ : DyadicInterval 40),(⟨749707069559,749707088889⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153768963968,153768964032⟩ : DyadicInterval 40),(⟨-178825520768,-178825520704⟩ : DyadicInterval 40),(⟨749689840933,749689860262⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153651953792,153651953856⟩ : DyadicInterval 40),(⟨-178667199104,-178667199040⟩ : DyadicInterval 40),(⟨749710185232,749710204562⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153768963968,153768964032⟩ : DyadicInterval 40),(⟨-178825520768,-178825520704⟩ : DyadicInterval 40),(⟨749689840933,749689860262⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10486375⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10486272,10486336⟩ : DyadicInterval 40),(⟨-10486464,-10486400⟩ : DyadicInterval 40),(⟨762123383547,762123402876⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨164916431882,165040699370⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153660913472,153660913536⟩ : DyadicInterval 40),(⟨-178679320704,-178679320640⟩ : DyadicInterval 40),(⟨749708628108,749708647438⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153768967744,153768967808⟩ : DyadicInterval 40),(⟨-178825525888,-178825525824⟩ : DyadicInterval 40),(⟨749689840279,749689859609⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25056558080,-25018407104⟩ : DyadicInterval 40),(⟨774632587168,774651681920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨153669880704,153768964032⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-178825520768,-178691452672⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1570_ok : ecellOkT e1570 = true := by decide +kernel
theorem e1570_pos {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1229649/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1570 e1570_ok ha1 ha2 hz1 hz2 hz

-- box ['1229649/8192000', '615249/4096000', '7999/8000', '1']  interval_lower 114336037/1099511627776
noncomputable def e1571 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1264552322793,0,true,153768963968,153768964032⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨934470932759,0,false,-178825520768,-178825520704⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1264666273645,0,true,153868038272,153868038336⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨934356981907,0,false,-178959605120,-178959605056⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1264531692706,0,true,153751026240,153751026304⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨934491562846,0,false,-178801247360,-178801247296⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522121633,0,true,10493760,10493824⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099501133919,0,false,-10493952,-10493888⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627675,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1264542003386,0,true,153759991360,153759991424⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨934481252166,0,false,-178813378880,-178813378816⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1264666277996,0,true,153868042048,153868042112⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨934356977556,0,false,-178959610240,-178959610176⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1074704197094,0,false,-25091568128,-25091568064⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1074741516951,0,false,-25053387456,-25053387392⟩
    { al := (1229649/8192000), au := (615249/4096000), zl := (7999/8000), zu := 1,
      A := ⟨165040695017,165154645869⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153768963968,153768964032⟩ : DyadicInterval 40),(⟨-178825520768,-178825520704⟩ : DyadicInterval 40),(⟨749689840933,749689860263⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153868038272,153868038336⟩ : DyadicInterval 40),(⟨-178959605120,-178959605056⟩ : DyadicInterval 40),(⟨749672600231,749672619560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153751026240,153751026304⟩ : DyadicInterval 40),(⟨-178801247360,-178801247296⟩ : DyadicInterval 40),(⟨749692960948,749692980277⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153868038272,153868038336⟩ : DyadicInterval 40),(⟨-178959605120,-178959605056⟩ : DyadicInterval 40),(⟨749672600231,749672619560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10493857⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10493760,10493824⟩ : DyadicInterval 40),(⟨-10493952,-10493888⟩ : DyadicInterval 40),(⟨762123383547,762123402876⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨165030375610,165154650220⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153759991360,153759991424⟩ : DyadicInterval 40),(⟨-178813378880,-178813378816⟩ : DyadicInterval 40),(⟨749691401649,749691420979⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153868042048,153868042112⟩ : DyadicInterval 40),(⟨-178959610240,-178959610176⟩ : DyadicInterval 40),(⟨749672599576,749672618906⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25091568128,-25053387392⟩ : DyadicInterval 40),(⟨774650077312,774669186944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨153768963968,153868038336⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-178959605120,-178825520704⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1571_ok : ecellOkT e1571 = true := by decide +kernel
theorem e1571_pos {a z : ℝ} (ha1 : ((1229649/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((615249/4096000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1571 e1571_ok ha1 ha2 hz1 hz2 hz

-- box ['615249/4096000', '1231347/8192000', '3999/4000', '7999/8000']  interval_lower 57704051/549755813888
noncomputable def e1572 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1264666273644,0,true,153868038272,153868038336⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨934356981908,0,false,-178959605120,-178959605056⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1264780224496,0,true,153967103616,153967103680⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨934243031056,0,false,-179093705792,-179093705728⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1264624984982,0,true,153832140992,153832141056⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨934398270570,0,false,-178911019392,-178911019328⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1264759565922,0,true,153949144384,153949144448⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨934263689630,0,false,-179069392960,-179069392896⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522121074,0,true,10493184,10493248⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099501134478,0,false,-10493376,-10493312⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099532630151,0,true,21002112,21002176⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490625401,0,false,-21002624,-21002560⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627374,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627676,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1264645625237,0,true,153850086208,153850086272⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨934377630315,0,false,-178935307200,-178935307136⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1264769899572,0,true,153958127808,153958127872⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨934253355980,0,false,-179081554432,-179081554368⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074673057899,0,false,-25123426560,-25123426496⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074710401097,0,false,-25085220928,-25085220864⟩
    { al := (615249/4096000), au := (1231347/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨165154645868,165268596720⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153868038272,153868038336⟩ : DyadicInterval 40),(⟨-178959605120,-178959605056⟩ : DyadicInterval 40),(⟨749672600231,749672619561⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153967103616,153967103680⟩ : DyadicInterval 40),(⟨-179093705792,-179093705728⟩ : DyadicInterval 40),(⟨749655347452,749655366781⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153832140992,153832141056⟩ : DyadicInterval 40),(⟨-178911019392,-178911019328⟩ : DyadicInterval 40),(⟨749678848544,749678867873⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153949144384,153949144448⟩ : DyadicInterval 40),(⟨-179069392960,-179069392896⟩ : DyadicInterval 40),(⟨749658476148,749658495477⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10493298,21002375⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10493184,10493248⟩ : DyadicInterval 40),(⟨-10493376,-10493312⟩ : DyadicInterval 40),(⟨762123383547,762123402876⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21002112,21002176⟩ : DyadicInterval 40),(⟨-21002624,-21002560⟩ : DyadicInterval 40),(⟨762123383406,762123402735⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165133997461,165258271796⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153850086208,153850086272⟩ : DyadicInterval 40),(⟨-178935307200,-178935307136⟩ : DyadicInterval 40),(⟨749675725222,749675744551⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153958127808,153958127872⟩ : DyadicInterval 40),(⟨-179081554432,-179081554368⟩ : DyadicInterval 40),(⟨749656911196,749656930526⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25123426560,-25085220864⟩ : DyadicInterval 40),(⟨774665994048,774685116160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨153868038272,153967103680⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179093705792,-178959605056⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1572_ok : ecellOkT e1572 = true := by decide +kernel
theorem e1572_pos {a z : ℝ} (ha1 : ((615249/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1231347/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1572 e1572_ok ha1 ha2 hz1 hz2 hz

-- box ['1231347/8192000', '308049/2048000', '3999/4000', '7999/8000']  interval_lower 3635817/34359738368
noncomputable def e1573 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1264780224495,0,true,153967103616,153967103680⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨934243031057,0,false,-179093705792,-179093705728⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1264894175347,0,true,154066160064,154066160128⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨934129080205,0,false,-179227822848,-179227822784⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1264738907345,0,true,153931184832,153931184896⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨934284348207,0,false,-179045080640,-179045080576⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1264873502529,0,true,154048190080,154048190144⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨934149753023,0,false,-179203490304,-179203490240⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522128556,0,true,10500672,10500736⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099501126996,0,false,-10500864,-10500800⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099532645116,0,true,21017088,21017152⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490610436,0,false,-21017600,-21017536⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627374,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627676,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1264759561840,0,true,153949140800,153949140864⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨934263693712,0,false,-179069388160,-179069388096⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1264883843301,0,true,154057178880,154057178944⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨934139412251,0,false,-179215661632,-179215661568⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074638794259,0,false,-25158482688,-25158482624⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074676165356,0,false,-25120247296,-25120247232⟩
    { al := (1231347/8192000), au := (308049/2048000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨165268596719,165382547571⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153967103616,153967103680⟩ : DyadicInterval 40),(⟨-179093705792,-179093705728⟩ : DyadicInterval 40),(⟨749655347452,749655366781⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154066160064,154066160128⟩ : DyadicInterval 40),(⟨-179227822848,-179227822784⟩ : DyadicInterval 40),(⟨749638082584,749638101914⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153931184832,153931184896⟩ : DyadicInterval 40),(⟨-179045080640,-179045080576⟩ : DyadicInterval 40),(⟨749661604452,749661623781⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154048190080,154048190144⟩ : DyadicInterval 40),(⟨-179203490304,-179203490240⟩ : DyadicInterval 40),(⟨749641215631,749641234960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10500780,21017340⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10500672,10500736⟩ : DyadicInterval 40),(⟨-10500864,-10500800⟩ : DyadicInterval 40),(⟨762123383547,762123402876⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21017088,21017152⟩ : DyadicInterval 40),(⟨-21017600,-21017536⟩ : DyadicInterval 40),(⟨762123383406,762123402735⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165247934064,165372215525⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153949140800,153949140864⟩ : DyadicInterval 40),(⟨-179069388160,-179069388096⟩ : DyadicInterval 40),(⟨749658476788,749658496117⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154057178880,154057178944⟩ : DyadicInterval 40),(⟨-179215661632,-179215661568⟩ : DyadicInterval 40),(⟨749639648503,749639667833⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25158482688,-25120247232⟩ : DyadicInterval 40),(⟨774683507232,774702644224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨153967103616,154066160128⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179227822848,-179093705728⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1573_ok : ecellOkT e1573 = true := by decide +kernel
theorem e1573_pos {a z : ℝ} (ha1 : ((1231347/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((308049/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1573 e1573_ok ha1 ha2 hz1 hz2 hz

-- box ['615249/4096000', '1231347/8192000', '7999/8000', '1']  interval_lower 115271253/1099511627776
noncomputable def e1574 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1264666273644,0,true,153868038272,153868038336⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨934356981908,0,false,-178959605120,-178959605056⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1264780224496,0,true,153967103616,153967103680⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨934243031056,0,false,-179093705792,-179093705728⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1264645629313,0,true,153850089792,153850089856⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨934377626239,0,false,-178935312000,-178935311936⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522129115,0,true,10501248,10501312⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099501126437,0,false,-10501440,-10501376⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627675,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1264655947112,0,true,153859060224,153859060288⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨934367308440,0,false,-178947453312,-178947453248⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1264780228846,0,true,153967107456,153967107520⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨934243026706,0,false,-179093710912,-179093710848⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1074669952790,0,false,-25126603456,-25126603392⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1074707300546,0,false,-25088393024,-25088392960⟩
    { al := (615249/4096000), au := (1231347/8192000), zl := (7999/8000), zu := 1,
      A := ⟨165154645868,165268596720⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153868038272,153868038336⟩ : DyadicInterval 40),(⟨-178959605120,-178959605056⟩ : DyadicInterval 40),(⟨749672600231,749672619561⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153967103616,153967103680⟩ : DyadicInterval 40),(⟨-179093705792,-179093705728⟩ : DyadicInterval 40),(⟨749655347452,749655366781⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153850089792,153850089856⟩ : DyadicInterval 40),(⟨-178935312000,-178935311936⟩ : DyadicInterval 40),(⟨749675724583,749675743913⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153967103616,153967103680⟩ : DyadicInterval 40),(⟨-179093705792,-179093705728⟩ : DyadicInterval 40),(⟨749655347452,749655366781⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10501339⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10501248,10501312⟩ : DyadicInterval 40),(⟨-10501440,-10501376⟩ : DyadicInterval 40),(⟨762123383547,762123402876⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨165144319336,165268601070⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153859060224,153859060288⟩ : DyadicInterval 40),(⟨-178947453312,-178947453248⟩ : DyadicInterval 40),(⟨749674163127,749674182457⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153967107456,153967107520⟩ : DyadicInterval 40),(⟨-179093710912,-179093710848⟩ : DyadicInterval 40),(⟨749655346759,749655366089⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25126603456,-25088392960⟩ : DyadicInterval 40),(⟨774667580096,774686704608⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨153868038272,153967103680⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179093705792,-178959605056⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1574_ok : ecellOkT e1574 = true := by decide +kernel
theorem e1574_pos {a z : ℝ} (ha1 : ((615249/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1231347/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1574 e1574_ok ha1 ha2 hz1 hz2 hz

-- box ['1231347/8192000', '308049/2048000', '7999/8000', '1']  interval_lower 116209519/1099511627776
noncomputable def e1575 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1264780224495,0,true,153967103616,153967103680⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨934243031057,0,false,-179093705792,-179093705728⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1264894175347,0,true,154066160064,154066160128⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨934129080205,0,false,-179227822848,-179227822784⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1264759565920,0,true,153949144384,153949144448⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨934263689632,0,false,-179069392960,-179069392896⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522136597,0,true,10508736,10508800⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099501118955,0,false,-10508928,-10508864⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627675,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1264769891093,0,true,153958120448,153958120512⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨934253364459,0,false,-179081544448,-179081544384⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1264894179698,0,true,154066163904,154066163968⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨934129075854,0,false,-179227827968,-179227827904⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1074635684867,0,false,-25161664064,-25161664000⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1074673060448,0,false,-25123424000,-25123423936⟩
    { al := (1231347/8192000), au := (308049/2048000), zl := (7999/8000), zu := 1,
      A := ⟨165268596719,165382547571⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153967103616,153967103680⟩ : DyadicInterval 40),(⟨-179093705792,-179093705728⟩ : DyadicInterval 40),(⟨749655347452,749655366781⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154066160064,154066160128⟩ : DyadicInterval 40),(⟨-179227822848,-179227822784⟩ : DyadicInterval 40),(⟨749638082584,749638101914⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153949144384,153949144448⟩ : DyadicInterval 40),(⟨-179069392960,-179069392896⟩ : DyadicInterval 40),(⟨749658476148,749658495478⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154066160064,154066160128⟩ : DyadicInterval 40),(⟨-179227822848,-179227822784⟩ : DyadicInterval 40),(⟨749638082584,749638101914⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10508821⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10508736,10508800⟩ : DyadicInterval 40),(⟨-10508928,-10508864⟩ : DyadicInterval 40),(⟨762123383547,762123402876⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨165258263317,165382551922⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153958120448,153958120512⟩ : DyadicInterval 40),(⟨-179081544448,-179081544384⟩ : DyadicInterval 40),(⟨749656912472,749656931801⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154066163904,154066163968⟩ : DyadicInterval 40),(⟨-179227827968,-179227827904⟩ : DyadicInterval 40),(⟨749638081891,749638101221⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25161664064,-25123423936⟩ : DyadicInterval 40),(⟨774685095584,774704234912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨153967103616,154066160128⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179227822848,-179093705728⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1575_ok : ecellOkT e1575 = true := by decide +kernel
theorem e1575_pos {a z : ℝ} (ha1 : ((1231347/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((308049/2048000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1575 e1575_ok ha1 ha2 hz1 hz2 hz

-- box ['308049/2048000', '246609/1638400', '1999/2000', '7997/8000']  interval_lower 117560491/1099511627776
noncomputable def e1576 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1264894175346,0,true,154066160064,154066160128⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨934129080206,0,false,-179227822848,-179227822784⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265008126198,0,true,154165207616,154165207680⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨934015129354,0,false,-179361956288,-179361956224⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1264811484072,0,true,153994278208,153994278272⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨934211771480,0,false,-179130495872,-179130495808⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1264946065012,0,true,154111264384,154111264448⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨934077190540,0,false,-179288900992,-179288900928⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543152944,0,true,31524672,31524736⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099480102608,0,false,-31525632,-31525568⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099553691954,0,true,42063360,42063424⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099469563598,0,false,-42065024,-42064960⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626166,0,false,-1664,-1600⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626873,0,false,-960,-896⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1264852825495,0,true,154030216064,154030216128⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨934170430057,0,false,-179179153280,-179179153216⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1264977100055,0,true,154138240192,154138240256⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨934046155497,0,false,-179325433280,-179325433216⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074610733756,0,false,-25187193024,-25187192960⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074648123860,0,false,-25148937216,-25148937152⟩
    { al := (308049/2048000), au := (246609/1638400), zl := (1999/2000), zu := (7997/8000),
      A := ⟨165382547570,165496498422⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154066160064,154066160128⟩ : DyadicInterval 40),(⟨-179227822848,-179227822784⟩ : DyadicInterval 40),(⟨749638082584,749638101914⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154165207616,154165207680⟩ : DyadicInterval 40),(⟨-179361956288,-179361956224⟩ : DyadicInterval 40),(⟨749620805628,749620824957⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨153994278208,153994278272⟩ : DyadicInterval 40),(⟨-179130495872,-179130495808⟩ : DyadicInterval 40),(⟨749650612463,749650631792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154111264384,154111264448⟩ : DyadicInterval 40),(⟨-179288900992,-179288900928⟩ : DyadicInterval 40),(⟨749630216663,749630235992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨31525168,42064178⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨31524672,31524736⟩ : DyadicInterval 40),(⟨-31525632,-31525568⟩ : DyadicInterval 40),(⟨762123383128,762123402457⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42063360,42063424⟩ : DyadicInterval 40),(⟨-42065024,-42064960⟩ : DyadicInterval 40),(⟨762123382774,762123402103⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1664,-896⟩ : DyadicInterval 40),(⟨762123384064,762123403712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165341197719,165465472279⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154030216064,154030216128⟩ : DyadicInterval 40),(⟨-179179153280,-179179153216⟩ : DyadicInterval 40),(⟨749644348937,749644368266⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154138240192,154138240256⟩ : DyadicInterval 40),(⟨-179325433280,-179325433216⟩ : DyadicInterval 40),(⟨749625510926,749625530256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25187193024,-25148937152⟩ : DyadicInterval 40),(⟨774697852192,774716999392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154066160064,154165207680⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179361956288,-179227822784⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1576_ok : ecellOkT e1576 = true := by decide +kernel
theorem e1576_pos {a z : ℝ} (ha1 : ((308049/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((246609/1638400 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1576 e1576_ok ha1 ha2 hz1 hz2 hz

-- box ['246609/1638400', '616947/4096000', '1999/2000', '7997/8000']  interval_lower 118504217/1099511627776
noncomputable def e1577 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265008126197,0,true,154165207616,154165207680⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨934015129355,0,false,-179361956288,-179361956224⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265122077049,0,true,154264246208,154264246272⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933901178503,0,false,-179496106048,-179496105984⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1264925377947,0,true,154093282688,154093282752⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨934097877605,0,false,-179264550336,-179264550272⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265059973131,0,true,154210270656,154210270720⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933963282421,0,false,-179422991552,-179422991488⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543175393,0,true,31547136,31547200⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099480080159,0,false,-31548096,-31548032⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099553721887,0,true,42093248,42093312⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099469533665,0,false,-42094976,-42094912⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626164,0,false,-1664,-1600⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626871,0,false,-960,-896⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1264966747857,0,true,154129242048,154129242112⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨934056507695,0,false,-179313247232,-179313247168⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265091029538,0,true,154237262656,154237262720⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933932226014,0,false,-179459553472,-179459553408⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074576431462,0,false,-25222290752,-25222290688⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074613849463,0,false,-25184005120,-25184005056⟩
    { al := (246609/1638400), au := (616947/4096000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨165496498421,165610449273⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154165207616,154165207680⟩ : DyadicInterval 40),(⟨-179361956288,-179361956224⟩ : DyadicInterval 40),(⟨749620805628,749620824958⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154264246208,154264246272⟩ : DyadicInterval 40),(⟨-179496106048,-179496105984⟩ : DyadicInterval 40),(⟨749603516591,749603535921⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154093282688,154093282752⟩ : DyadicInterval 40),(⟨-179264550336,-179264550272⟩ : DyadicInterval 40),(⟨749633352909,749633372239⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154210270656,154210270720⟩ : DyadicInterval 40),(⟨-179422991552,-179422991488⟩ : DyadicInterval 40),(⟨749612940721,749612960051⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨31547617,42094111⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨31547136,31547200⟩ : DyadicInterval 40),(⟨-31548096,-31548032⟩ : DyadicInterval 40),(⟨762123383126,762123402455⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42093248,42093312⟩ : DyadicInterval 40),(⟨-42094976,-42094912⟩ : DyadicInterval 40),(⟨762123382804,762123402133⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1664,-896⟩ : DyadicInterval 40),(⟨762123384064,762123403712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165455120081,165579401762⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154129242048,154129242112⟩ : DyadicInterval 40),(⟨-179313247232,-179313247168⟩ : DyadicInterval 40),(⟨749627080704,749627100033⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154237262656,154237262720⟩ : DyadicInterval 40),(⟨-179459553472,-179459553408⟩ : DyadicInterval 40),(⟨749608228433,749608247762⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25222290752,-25184005056⟩ : DyadicInterval 40),(⟨774715386144,774734548256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154165207616,154264246272⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179496106048,-179361956224⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1577_ok : ecellOkT e1577 = true := by decide +kernel
theorem e1577_pos {a z : ℝ} (ha1 : ((246609/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((616947/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1577 e1577_ok ha1 ha2 hz1 hz2 hz

-- box ['308049/2048000', '246609/1638400', '7997/8000', '3999/4000']  interval_lower 58711807/549755813888
noncomputable def e1578 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1264894175346,0,true,154066160064,154066160128⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨934129080206,0,false,-179227822848,-179227822784⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265008126198,0,true,154165207616,154165207680⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨934015129354,0,false,-179361956288,-179361956224⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1264832156890,0,true,154012249088,154012249152⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨934191098662,0,false,-179154826816,-179154826752⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1264966752074,0,true,154129245760,154129245824⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨934056503478,0,false,-179313252224,-179313252160⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099532644513,0,true,21016512,21016576⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490611039,0,false,-21016960,-21016896⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543176040,0,true,31547776,31547840⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099480079512,0,false,-31548736,-31548672⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626870,0,false,-960,-896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627375,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1264863162083,0,true,154039201408,154039201472⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨934160093469,0,false,-179191319488,-179191319424⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1264987443532,0,true,154147230656,154147230720⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨934035812020,0,false,-179337609152,-179337609088⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074607620480,0,false,-25190378496,-25190378432⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074645014994,0,false,-25152118016,-25152117952⟩
    { al := (308049/2048000), au := (246609/1638400), zl := (7997/8000), zu := (3999/4000),
      A := ⟨165382547570,165496498422⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154066160064,154066160128⟩ : DyadicInterval 40),(⟨-179227822848,-179227822784⟩ : DyadicInterval 40),(⟨749638082584,749638101914⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154165207616,154165207680⟩ : DyadicInterval 40),(⟨-179361956288,-179361956224⟩ : DyadicInterval 40),(⟨749620805628,749620824957⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154012249088,154012249152⟩ : DyadicInterval 40),(⟨-179154826816,-179154826752⟩ : DyadicInterval 40),(⟨749647480607,749647499937⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154129245760,154129245824⟩ : DyadicInterval 40),(⟨-179313252224,-179313252160⟩ : DyadicInterval 40),(⟨749627080049,749627099379⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21016737,31548264⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21016512,21016576⟩ : DyadicInterval 40),(⟨-21016960,-21016896⟩ : DyadicInterval 40),(⟨762123383374,762123402703⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨31547776,31547840⟩ : DyadicInterval 40),(⟨-31548736,-31548672⟩ : DyadicInterval 40),(⟨762123383126,762123402455⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-960,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165351534307,165475815756⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154039201408,154039201472⟩ : DyadicInterval 40),(⟨-179191319488,-179191319424⟩ : DyadicInterval 40),(⟨749642782654,749642801984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154147230656,154147230720⟩ : DyadicInterval 40),(⟨-179337609152,-179337609088⟩ : DyadicInterval 40),(⟨749623942367,749623961697⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25190378496,-25152117952⟩ : DyadicInterval 40),(⟨774699442592,774718592128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154066160064,154165207680⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179361956288,-179227822784⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1578_ok : ecellOkT e1578 = true := by decide +kernel
theorem e1578_pos {a z : ℝ} (ha1 : ((308049/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((246609/1638400 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1578 e1578_ok ha1 ha2 hz1 hz2 hz

-- box ['246609/1638400', '616947/4096000', '7997/8000', '3999/4000']  interval_lower 14795831/137438953472
noncomputable def e1579 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265008126197,0,true,154165207616,154165207680⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨934015129355,0,false,-179361956288,-179361956224⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265122077049,0,true,154264246208,154264246272⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933901178503,0,false,-179496106048,-179496105984⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1264946065010,0,true,154111264384,154111264448⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨934077190542,0,false,-179288900992,-179288900928⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265080674437,0,true,154228262848,154228262912⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933942581115,0,false,-179447362496,-179447362432⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099532659479,0,true,21031488,21031552⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490596073,0,false,-21031936,-21031872⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543198490,0,true,31570240,31570304⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099480057062,0,false,-31571200,-31571136⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626869,0,false,-960,-896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627374,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1264977091315,0,true,154138232576,154138232640⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨934046164237,0,false,-179325422976,-179325422912⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265101380141,0,true,154246258496,154246258560⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933921875411,0,false,-179471739200,-179471739136⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074573313895,0,false,-25225480640,-25225480576⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074610736388,0,false,-25187190336,-25187190272⟩
    { al := (246609/1638400), au := (616947/4096000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨165496498421,165610449273⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154165207616,154165207680⟩ : DyadicInterval 40),(⟨-179361956288,-179361956224⟩ : DyadicInterval 40),(⟨749620805628,749620824958⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154264246208,154264246272⟩ : DyadicInterval 40),(⟨-179496106048,-179496105984⟩ : DyadicInterval 40),(⟨749603516591,749603535921⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154111264384,154111264448⟩ : DyadicInterval 40),(⟨-179288900992,-179288900928⟩ : DyadicInterval 40),(⟨749630216663,749630235993⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154228262848,154228262912⟩ : DyadicInterval 40),(⟨-179447362496,-179447362432⟩ : DyadicInterval 40),(⟨749609799710,749609819040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21031703,31570714⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21031488,21031552⟩ : DyadicInterval 40),(⟨-21031936,-21031872⟩ : DyadicInterval 40),(⟨762123383373,762123402702⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨31570240,31570304⟩ : DyadicInterval 40),(⟨-31571200,-31571136⟩ : DyadicInterval 40),(⟨762123383125,762123402454⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-960,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165465463539,165589752365⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154138232576,154138232640⟩ : DyadicInterval 40),(⟨-179325422976,-179325422912⟩ : DyadicInterval 40),(⟨749625512256,749625531585⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154246258496,154246258560⟩ : DyadicInterval 40),(⟨-179471739200,-179471739136⟩ : DyadicInterval 40),(⟨749606657692,749606677021⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25225480640,-25187190272⟩ : DyadicInterval 40),(⟨774716978752,774736143200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154165207616,154264246272⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179496106048,-179361956224⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1579_ok : ecellOkT e1579 = true := by decide +kernel
theorem e1579_pos {a z : ℝ} (ha1 : ((246609/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((616947/4096000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1579 e1579_ok ha1 ha2 hz1 hz2 hz

-- box ['616947/4096000', '1234743/8192000', '1999/2000', '7997/8000']  interval_lower 59725351/549755813888
noncomputable def e1580 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265122077048,0,true,154264246208,154264246272⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933901178504,0,false,-179496106048,-179496105984⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265236027900,0,true,154363275904,154363275968⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933787227652,0,false,-179630272192,-179630272128⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265039271823,0,true,154192278272,154192278336⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933983983729,0,false,-179398621120,-179398621056⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265173881251,0,true,154309268096,154309268160⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933849374301,0,false,-179557098496,-179557098432⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543197842,0,true,31569600,31569664⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099480057710,0,false,-31570560,-31570496⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099553751822,0,true,42123200,42123264⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099469503730,0,false,-42124864,-42124800⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626162,0,false,-1664,-1600⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626870,0,false,-960,-896⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265080670476,0,true,154228259392,154228259456⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933942585076,0,false,-179447357888,-179447357824⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265204959026,0,true,154336276224,154336276288⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933818296526,0,false,-179593689984,-179593689920⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074542105556,0,false,-25257413760,-25257413696⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074579551382,0,false,-25219098432,-25219098368⟩
    { al := (616947/4096000), au := (1234743/8192000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨165610449272,165724400124⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154264246208,154264246272⟩ : DyadicInterval 40),(⟨-179496106048,-179496105984⟩ : DyadicInterval 40),(⟨749603516591,749603535921⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154363275904,154363275968⟩ : DyadicInterval 40),(⟨-179630272192,-179630272128⟩ : DyadicInterval 40),(⟨749586215462,749586234792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154192278272,154192278336⟩ : DyadicInterval 40),(⟨-179398621120,-179398621056⟩ : DyadicInterval 40),(⟨749616081262,749616100592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154309268096,154309268160⟩ : DyadicInterval 40),(⟨-179557098496,-179557098432⟩ : DyadicInterval 40),(⟨749595652670,749595671999⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨31570066,42124046⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨31569600,31569664⟩ : DyadicInterval 40),(⟨-31570560,-31570496⟩ : DyadicInterval 40),(⟨762123383125,762123402454⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42123200,42123264⟩ : DyadicInterval 40),(⟨-42124864,-42124800⟩ : DyadicInterval 40),(⟨762123382770,762123402099⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1664,-896⟩ : DyadicInterval 40),(⟨762123384064,762123403712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165569042700,165693331250⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154228259392,154228259456⟩ : DyadicInterval 40),(⟨-179447357888,-179447357824⟩ : DyadicInterval 40),(⟨749609800342,749609819672⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154336276224,154336276288⟩ : DyadicInterval 40),(⟨-179593689984,-179593689920⟩ : DyadicInterval 40),(⟨749590933829,749590953159⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25257413760,-25219098368⟩ : DyadicInterval 40),(⟨774732932800,774752109760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154264246208,154363275968⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179630272192,-179496105984⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1580_ok : ecellOkT e1580 = true := by decide +kernel
theorem e1580_pos {a z : ℝ} (ha1 : ((616947/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1234743/8192000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1580 e1580_ok ha1 ha2 hz1 hz2 hz

-- box ['1234743/8192000', '154449/1024000', '1999/2000', '7997/8000']  interval_lower 940617/8589934592
noncomputable def e1581 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265236027899,0,true,154363275904,154363275968⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933787227653,0,false,-179630272192,-179630272128⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265349978751,0,true,154462296704,154462296768⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933673276801,0,false,-179764454720,-179764454656⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265153165698,0,true,154291264896,154291264960⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933870089854,0,false,-179532708352,-179532708288⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265287789370,0,true,154408256576,154408256640⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933735466182,0,false,-179691221760,-179691221696⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543220293,0,true,31592000,31592064⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099480035259,0,false,-31593024,-31592960⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099553781759,0,true,42153152,42153216⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099469473793,0,false,-42154816,-42154752⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626159,0,false,-1664,-1600⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626869,0,false,-960,-896⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265194592578,0,true,154327267328,154327267392⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933828662974,0,false,-179581484224,-179581484160⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265318888512,0,true,154435280832,154435280896⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933704367040,0,false,-179727842880,-179727842816⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074507756040,0,false,-25292561984,-25292561920⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074545229848,0,false,-25254216832,-25254216768⟩
    { al := (1234743/8192000), au := (154449/1024000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨165724400123,165838350975⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154363275904,154363275968⟩ : DyadicInterval 40),(⟨-179630272192,-179630272128⟩ : DyadicInterval 40),(⟨749586215463,749586234792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154462296704,154462296768⟩ : DyadicInterval 40),(⟨-179764454720,-179764454656⟩ : DyadicInterval 40),(⟨749568902242,749568921571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154291264896,154291264960⟩ : DyadicInterval 40),(⟨-179532708352,-179532708288⟩ : DyadicInterval 40),(⟨749598797614,749598816943⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154408256576,154408256640⟩ : DyadicInterval 40),(⟨-179691221760,-179691221696⟩ : DyadicInterval 40),(⟨749578352554,749578371883⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨31592517,42153983⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨31592000,31592064⟩ : DyadicInterval 40),(⟨-31593024,-31592960⟩ : DyadicInterval 40),(⟨762123383156,762123402485⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42153152,42153216⟩ : DyadicInterval 40),(⟨-42154816,-42154752⟩ : DyadicInterval 40),(⟨762123382767,762123402096⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1664,-896⟩ : DyadicInterval 40),(⟨762123384064,762123403712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165682964802,165807260736⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154327267328,154327267392⟩ : DyadicInterval 40),(⟨-179581484224,-179581484160⟩ : DyadicInterval 40),(⟨749592507976,749592527305⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154435280832,154435280896⟩ : DyadicInterval 40),(⟨-179727842880,-179727842816⟩ : DyadicInterval 40),(⟨749573627179,749573646509⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25292561984,-25254216768⟩ : DyadicInterval 40),(⟨774750492000,774769683872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154363275904,154462296768⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179764454720,-179630272128⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1581_ok : ecellOkT e1581 = true := by decide +kernel
theorem e1581_pos {a z : ℝ} (ha1 : ((1234743/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((154449/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1581 e1581_ok ha1 ha2 hz1 hz2 hz

-- box ['616947/4096000', '1234743/8192000', '7997/8000', '3999/4000']  interval_lower 119312539/1099511627776
noncomputable def e1582 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265122077048,0,true,154264246208,154264246272⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933901178504,0,false,-179496106048,-179496105984⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265236027900,0,true,154363275904,154363275968⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933787227652,0,false,-179630272192,-179630272128⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265059973129,0,true,154210270656,154210270720⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933963282423,0,false,-179422991552,-179422991488⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265194596801,0,true,154327270976,154327271040⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933828658751,0,false,-179581489216,-179581489152⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099532674445,0,true,21046464,21046528⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490581107,0,false,-21046912,-21046848⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543220941,0,true,31592704,31592768⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099480034611,0,false,-31593664,-31593600⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626868,0,false,-960,-896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627374,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265091020795,0,true,154237255040,154237255104⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933932234757,0,false,-179459543168,-179459543104⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265215316745,0,true,154345277440,154345277504⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933807938807,0,false,-179605885632,-179605885568⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074538983699,0,false,-25260608128,-25260608064⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074576434096,0,false,-25222288064,-25222288000⟩
    { al := (616947/4096000), au := (1234743/8192000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨165610449272,165724400124⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154264246208,154264246272⟩ : DyadicInterval 40),(⟨-179496106048,-179496105984⟩ : DyadicInterval 40),(⟨749603516591,749603535921⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154363275904,154363275968⟩ : DyadicInterval 40),(⟨-179630272192,-179630272128⟩ : DyadicInterval 40),(⟨749586215462,749586234792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154210270656,154210270720⟩ : DyadicInterval 40),(⟨-179422991552,-179422991488⟩ : DyadicInterval 40),(⟨749612940722,749612960051⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154327270976,154327271040⟩ : DyadicInterval 40),(⟨-179581489216,-179581489152⟩ : DyadicInterval 40),(⟨749592507356,749592526685⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21046669,31593165⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21046464,21046528⟩ : DyadicInterval 40),(⟨-21046912,-21046848⟩ : DyadicInterval 40),(⟨762123383373,762123402702⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨31592704,31592768⟩ : DyadicInterval 40),(⟨-31593664,-31593600⟩ : DyadicInterval 40),(⟨762123383124,762123402453⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-960,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165579393019,165703688969⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154237255040,154237255104⟩ : DyadicInterval 40),(⟨-179459543168,-179459543104⟩ : DyadicInterval 40),(⟨749608229764,749608249094⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154345277440,154345277504⟩ : DyadicInterval 40),(⟨-179605885632,-179605885568⟩ : DyadicInterval 40),(⟨749589360932,749589380262⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25260608128,-25222288000⟩ : DyadicInterval 40),(⟨774734527616,774753706944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154264246208,154363275968⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179630272192,-179496105984⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1582_ok : ecellOkT e1582 = true := by decide +kernel
theorem e1582_pos {a z : ℝ} (ha1 : ((616947/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1234743/8192000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1582 e1582_ok ha1 ha2 hz1 hz2 hz

-- box ['1234743/8192000', '154449/1024000', '7997/8000', '3999/4000']  interval_lower 15032675/137438953472
noncomputable def e1583 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265236027899,0,true,154363275904,154363275968⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933787227653,0,false,-179630272192,-179630272128⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265349978751,0,true,154462296704,154462296768⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933673276801,0,false,-179764454720,-179764454656⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265173881248,0,true,154309268096,154309268160⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933849374304,0,false,-179557098496,-179557098432⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265308519164,0,true,154426270272,154426270336⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933714736388,0,false,-179715632192,-179715632128⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099532689412,0,true,21061376,21061440⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490566140,0,false,-21061888,-21061824⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099543243394,0,true,31615104,31615168⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099480012158,0,false,-31616128,-31616064⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626866,0,false,-960,-896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627373,0,false,-448,-384⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265204950535,0,true,154336268800,154336268864⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933818305017,0,false,-179593680000,-179593679936⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265329253359,0,true,154444287424,154444287488⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933694002193,0,false,-179740048384,-179740048320⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074504629887,0,false,-25295760896,-25295760832⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074542108116,0,false,-25257411136,-25257411072⟩
    { al := (1234743/8192000), au := (154449/1024000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨165724400123,165838350975⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154363275904,154363275968⟩ : DyadicInterval 40),(⟨-179630272192,-179630272128⟩ : DyadicInterval 40),(⟨749586215463,749586234792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154462296704,154462296768⟩ : DyadicInterval 40),(⟨-179764454720,-179764454656⟩ : DyadicInterval 40),(⟨749568902242,749568921571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154309268096,154309268160⟩ : DyadicInterval 40),(⟨-179557098496,-179557098432⟩ : DyadicInterval 40),(⟨749595652670,749595671999⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154426270272,154426270336⟩ : DyadicInterval 40),(⟨-179715632192,-179715632128⟩ : DyadicInterval 40),(⟨749575202830,749575222160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨21061636,31615618⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21061376,21061440⟩ : DyadicInterval 40),(⟨-21061888,-21061824⟩ : DyadicInterval 40),(⟨762123383404,762123402733⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨31615104,31615168⟩ : DyadicInterval 40),(⟨-31616128,-31616064⟩ : DyadicInterval 40),(⟨762123383154,762123402483⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-960,-384⟩ : DyadicInterval 40),(⟨762123383808,762123403360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165693322759,165817625583⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154336268800,154336268864⟩ : DyadicInterval 40),(⟨-179593680000,-179593679936⟩ : DyadicInterval 40),(⟨749590935150,749590954479⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154444287424,154444287488⟩ : DyadicInterval 40),(⟨-179740048384,-179740048320⟩ : DyadicInterval 40),(⟨749572052095,749572071424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25295760896,-25257411072⟩ : DyadicInterval 40),(⟨774752089152,774771283328⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154363275904,154462296768⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179764454720,-179630272128⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1583_ok : ecellOkT e1583 = true := by decide +kernel
theorem e1583_pos {a z : ℝ} (ha1 : ((1234743/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((154449/1024000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1583 e1583_ok ha1 ha2 hz1 hz2 hz

-- box ['308049/2048000', '246609/1638400', '3999/4000', '7999/8000']  interval_lower 117286503/1099511627776
noncomputable def e1584 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1264894175346,0,true,154066160064,154066160128⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨934129080206,0,false,-179227822848,-179227822784⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265008126198,0,true,154165207616,154165207680⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨934015129354,0,false,-179361956288,-179361956224⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1264852829709,0,true,154030219712,154030219776⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨934170425843,0,false,-179179158272,-179179158208⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1264987439136,0,true,154147226816,154147226880⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨934035816416,0,false,-179337603968,-179337603904⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522136038,0,true,10508160,10508224⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099501119514,0,false,-10508352,-10508288⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099532660082,0,true,21032064,21032128⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490595470,0,false,-21032512,-21032448⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627373,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627676,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1264873498440,0,true,154048186496,154048186560⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨934149757112,0,false,-179203485504,-179203485440⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1264997787030,0,true,154156221056,154156221120⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨934025468522,0,false,-179349785216,-179349785152⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074604507002,0,false,-25193564096,-25193564032⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074641906003,0,false,-25155298944,-25155298880⟩
    { al := (308049/2048000), au := (246609/1638400), zl := (3999/4000), zu := (7999/8000),
      A := ⟨165382547570,165496498422⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154066160064,154066160128⟩ : DyadicInterval 40),(⟨-179227822848,-179227822784⟩ : DyadicInterval 40),(⟨749638082584,749638101914⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154165207616,154165207680⟩ : DyadicInterval 40),(⟨-179361956288,-179361956224⟩ : DyadicInterval 40),(⟨749620805628,749620824957⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154030219712,154030219776⟩ : DyadicInterval 40),(⟨-179179158272,-179179158208⟩ : DyadicInterval 40),(⟨749644348321,749644367650⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154147226816,154147226880⟩ : DyadicInterval 40),(⟨-179337603968,-179337603904⟩ : DyadicInterval 40),(⟨749623943041,749623962371⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10508262,21032306⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10508160,10508224⟩ : DyadicInterval 40),(⟨-10508352,-10508288⟩ : DyadicInterval 40),(⟨762123383547,762123402876⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21032064,21032128⟩ : DyadicInterval 40),(⟨-21032512,-21032448⟩ : DyadicInterval 40),(⟨762123383373,762123402702⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165361870664,165486159254⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154048186496,154048186560⟩ : DyadicInterval 40),(⟨-179203485504,-179203485440⟩ : DyadicInterval 40),(⟨749641216273,749641235603⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154156221056,154156221120⟩ : DyadicInterval 40),(⟨-179349785216,-179349785152⟩ : DyadicInterval 40),(⟨749622373725,749622393054⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25193564096,-25155298880⟩ : DyadicInterval 40),(⟨774701033056,774720184928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154066160064,154165207680⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179361956288,-179227822784⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1584_ok : ecellOkT e1584 = true := by decide +kernel
theorem e1584_pos {a z : ℝ} (ha1 : ((308049/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((246609/1638400 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1584 e1584_ok ha1 ha2 hz1 hz2 hz

-- box ['246609/1638400', '616947/4096000', '3999/4000', '7999/8000']  interval_lower 14778663/137438953472
noncomputable def e1585 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265008126197,0,true,154165207616,154165207680⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨934015129355,0,false,-179361956288,-179361956224⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265122077049,0,true,154264246208,154264246272⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933901178503,0,false,-179496106048,-179496105984⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1264966752072,0,true,154129245760,154129245824⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨934056503480,0,false,-179313252224,-179313252160⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265101375743,0,true,154246254656,154246254720⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933921879809,0,false,-179471734016,-179471733952⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522143521,0,true,10515648,10515712⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099501112031,0,false,-10515840,-10515776⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099532675049,0,true,21047040,21047104⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490580503,0,false,-21047488,-21047424⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627373,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627676,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1264987434792,0,true,154147223040,154147223104⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨934035820760,0,false,-179337598848,-179337598784⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265111730759,0,true,154255254272,154255254336⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933911524793,0,false,-179483925120,-179483925056⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074570196130,0,false,-25228670784,-25228670720⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074607623111,0,false,-25190375808,-25190375744⟩
    { al := (246609/1638400), au := (616947/4096000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨165496498421,165610449273⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154165207616,154165207680⟩ : DyadicInterval 40),(⟨-179361956288,-179361956224⟩ : DyadicInterval 40),(⟨749620805628,749620824958⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154264246208,154264246272⟩ : DyadicInterval 40),(⟨-179496106048,-179496105984⟩ : DyadicInterval 40),(⟨749603516591,749603535921⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154129245760,154129245824⟩ : DyadicInterval 40),(⟨-179313252224,-179313252160⟩ : DyadicInterval 40),(⟨749627080050,749627099379⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154246254656,154246254720⟩ : DyadicInterval 40),(⟨-179471734016,-179471733952⟩ : DyadicInterval 40),(⟨749606658367,749606677697⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10515745,21047273⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10515648,10515712⟩ : DyadicInterval 40),(⟨-10515840,-10515776⟩ : DyadicInterval 40),(⟨762123383547,762123402876⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21047040,21047104⟩ : DyadicInterval 40),(⟨-21047488,-21047424⟩ : DyadicInterval 40),(⟨762123383373,762123402702⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165475807016,165600102983⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154147223040,154147223104⟩ : DyadicInterval 40),(⟨-179337598848,-179337598784⟩ : DyadicInterval 40),(⟨749623943697,749623963027⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154255254272,154255254336⟩ : DyadicInterval 40),(⟨-179483925120,-179483925056⟩ : DyadicInterval 40),(⟨749605086868,749605106197⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25228670784,-25190375744⟩ : DyadicInterval 40),(⟨774718571488,774737738272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154165207616,154264246272⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179496106048,-179361956224⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1585_ok : ecellOkT e1585 = true := by decide +kernel
theorem e1585_pos {a z : ℝ} (ha1 : ((246609/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((616947/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1585 e1585_ok ha1 ha2 hz1 hz2 hz

-- box ['308049/2048000', '246609/1638400', '7999/8000', '1']  interval_lower 58574789/549755813888
noncomputable def e1586 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1264894175346,0,true,154066160064,154066160128⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨934129080206,0,false,-179227822848,-179227822784⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265008126198,0,true,154165207616,154165207680⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨934015129354,0,false,-179361956288,-179361956224⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1264873502527,0,true,154048190080,154048190144⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨934149753025,0,false,-179203490304,-179203490240⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522144080,0,true,10516224,10516288⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099501111472,0,false,-10516416,-10516352⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627675,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1264883834819,0,true,154057171520,154057171584⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨934139420733,0,false,-179215651648,-179215651584⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1265008130549,0,true,154165211392,154165211456⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨934015125003,0,false,-179361961408,-179361961344⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1074601393324,0,false,-25196749952,-25196749888⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1074638796811,0,false,-25158480064,-25158480000⟩
    { al := (308049/2048000), au := (246609/1638400), zl := (7999/8000), zu := 1,
      A := ⟨165382547570,165496498422⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154066160064,154066160128⟩ : DyadicInterval 40),(⟨-179227822848,-179227822784⟩ : DyadicInterval 40),(⟨749638082584,749638101914⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154165207616,154165207680⟩ : DyadicInterval 40),(⟨-179361956288,-179361956224⟩ : DyadicInterval 40),(⟨749620805628,749620824957⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154048190080,154048190144⟩ : DyadicInterval 40),(⟨-179203490304,-179203490240⟩ : DyadicInterval 40),(⟨749641215631,749641234961⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154165207616,154165207680⟩ : DyadicInterval 40),(⟨-179361956288,-179361956224⟩ : DyadicInterval 40),(⟨749620805628,749620824957⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10516304⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10516224,10516288⟩ : DyadicInterval 40),(⟨-10516416,-10516352⟩ : DyadicInterval 40),(⟨762123383547,762123402876⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨165372207043,165496502773⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154057171520,154057171584⟩ : DyadicInterval 40),(⟨-179215651648,-179215651584⟩ : DyadicInterval 40),(⟨749639649781,749639669110⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154165211392,154165211456⟩ : DyadicInterval 40),(⟨-179361961408,-179361961344⟩ : DyadicInterval 40),(⟨749620804971,749620824300⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25196749952,-25158480000⟩ : DyadicInterval 40),(⟨774702623616,774721777856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨154066160064,154165207680⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179361956288,-179227822784⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1586_ok : ecellOkT e1586 = true := by decide +kernel
theorem e1586_pos {a z : ℝ} (ha1 : ((308049/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((246609/1638400 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1586 e1586_ok ha1 ha2 hz1 hz2 hz

-- box ['246609/1638400', '616947/4096000', '7999/8000', '1']  interval_lower 59046089/549755813888
noncomputable def e1587 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265008126197,0,true,154165207616,154165207680⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨934015129355,0,false,-179361956288,-179361956224⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265122077049,0,true,154264246208,154264246272⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933901178503,0,false,-179496106048,-179496105984⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1264987439134,0,true,154147226816,154147226880⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨934035816418,0,false,-179337603968,-179337603904⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522151564,0,true,10523712,10523776⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099501103988,0,false,-10523840,-10523776⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627675,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1264997778545,0,true,154156213696,154156213760⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨934025477007,0,false,-179349775232,-179349775168⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1265122081401,0,true,154264249984,154264250048⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨933901174151,0,false,-179496111168,-179496111104⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1074567078162,0,false,-25231861120,-25231861056⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1074604509557,0,false,-25193561472,-25193561408⟩
    { al := (246609/1638400), au := (616947/4096000), zl := (7999/8000), zu := 1,
      A := ⟨165496498421,165610449273⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154165207616,154165207680⟩ : DyadicInterval 40),(⟨-179361956288,-179361956224⟩ : DyadicInterval 40),(⟨749620805628,749620824958⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154264246208,154264246272⟩ : DyadicInterval 40),(⟨-179496106048,-179496105984⟩ : DyadicInterval 40),(⟨749603516591,749603535921⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154147226816,154147226880⟩ : DyadicInterval 40),(⟨-179337603968,-179337603904⟩ : DyadicInterval 40),(⟨749623943041,749623962371⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154264246208,154264246272⟩ : DyadicInterval 40),(⟨-179496106048,-179496105984⟩ : DyadicInterval 40),(⟨749603516591,749603535921⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10523788⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10523712,10523776⟩ : DyadicInterval 40),(⟨-10523840,-10523776⟩ : DyadicInterval 40),(⟨762123383515,762123402844⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨165486150769,165610453625⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154156213696,154156213760⟩ : DyadicInterval 40),(⟨-179349775232,-179349775168⟩ : DyadicInterval 40),(⟨749622375005,749622394334⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154264249984,154264250048⟩ : DyadicInterval 40),(⟨-179496111168,-179496111104⟩ : DyadicInterval 40),(⟨749603515933,749603535262⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25231861120,-25193561408⟩ : DyadicInterval 40),(⟨774720164320,774739333440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨154165207616,154264246272⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179496106048,-179361956224⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1587_ok : ecellOkT e1587 = true := by decide +kernel
theorem e1587_pos {a z : ℝ} (ha1 : ((246609/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((616947/4096000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1587 e1587_ok ha1 ha2 hz1 hz2 hz

-- box ['616947/4096000', '1234743/8192000', '3999/4000', '7999/8000']  interval_lower 59587353/549755813888
noncomputable def e1588 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265122077048,0,true,154264246208,154264246272⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933901178504,0,false,-179496106048,-179496105984⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265236027900,0,true,154363275904,154363275968⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933787227652,0,false,-179630272192,-179630272128⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265080674435,0,true,154228262848,154228262912⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933942581117,0,false,-179447362496,-179447362432⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265215312351,0,true,154345273600,154345273664⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933807943201,0,false,-179605880448,-179605880384⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522151004,0,true,10523136,10523200⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099501104548,0,false,-10523328,-10523264⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099532690017,0,true,21062016,21062080⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490565535,0,false,-21062464,-21062400⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627372,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627676,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265101371398,0,true,154246250880,154246250944⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933921884154,0,false,-179471728896,-179471728832⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265225674490,0,true,154354278592,154354278656⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933797581062,0,false,-179618081408,-179618081344⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074535861640,0,false,-25263802752,-25263802688⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074573316530,0,false,-25225477952,-25225477888⟩
    { al := (616947/4096000), au := (1234743/8192000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨165610449272,165724400124⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154264246208,154264246272⟩ : DyadicInterval 40),(⟨-179496106048,-179496105984⟩ : DyadicInterval 40),(⟨749603516591,749603535921⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154363275904,154363275968⟩ : DyadicInterval 40),(⟨-179630272192,-179630272128⟩ : DyadicInterval 40),(⟨749586215462,749586234792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154228262848,154228262912⟩ : DyadicInterval 40),(⟨-179447362496,-179447362432⟩ : DyadicInterval 40),(⟨749609799710,749609819040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154345273600,154345273664⟩ : DyadicInterval 40),(⟨-179605880448,-179605880384⟩ : DyadicInterval 40),(⟨749589361608,749589380937⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10523228,21062241⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10523136,10523200⟩ : DyadicInterval 40),(⟨-10523328,-10523264⟩ : DyadicInterval 40),(⟨762123383547,762123402876⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21062016,21062080⟩ : DyadicInterval 40),(⟨-21062464,-21062400⟩ : DyadicInterval 40),(⟨762123383372,762123402701⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165589743622,165714046714⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154246250880,154246250944⟩ : DyadicInterval 40),(⟨-179471728896,-179471728832⟩ : DyadicInterval 40),(⟨749606659024,749606678354⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154354278592,154354278656⟩ : DyadicInterval 40),(⟨-179618081408,-179618081344⟩ : DyadicInterval 40),(⟨749587787923,749587807253⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25263802752,-25225477888⟩ : DyadicInterval 40),(⟨774736122560,774755304256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154264246208,154363275968⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179630272192,-179496105984⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1588_ok : ecellOkT e1588 = true := by decide +kernel
theorem e1588_pos {a z : ℝ} (ha1 : ((616947/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1234743/8192000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1588 e1588_ok ha1 ha2 hz1 hz2 hz

-- box ['1234743/8192000', '154449/1024000', '3999/4000', '7999/8000']  interval_lower 120123017/1099511627776
noncomputable def e1589 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265236027899,0,true,154363275904,154363275968⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933787227653,0,false,-179630272192,-179630272128⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265349978751,0,true,154462296704,154462296768⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933673276801,0,false,-179764454720,-179764454656⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265194596798,0,true,154327270976,154327271040⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933828658754,0,false,-179581489216,-179581489152⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265329248958,0,true,154444283648,154444283712⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933694006594,0,false,-179740043200,-179740043136⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522158487,0,true,10530624,10530688⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099501097065,0,false,-10530816,-10530752⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099532704984,0,true,21076992,21077056⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099490550568,0,false,-21077440,-21077376⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627371,0,false,-448,-384⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627676,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265215308254,0,true,154345270016,154345270080⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933807947298,0,false,-179605875584,-179605875520⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265339618224,0,true,154453294016,154453294080⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933683637328,0,false,-179752254080,-179752254016⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074501503534,0,false,-25298960064,-25298960000⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074538986260,0,false,-25260605504,-25260605440⟩
    { al := (1234743/8192000), au := (154449/1024000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨165724400123,165838350975⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154363275904,154363275968⟩ : DyadicInterval 40),(⟨-179630272192,-179630272128⟩ : DyadicInterval 40),(⟨749586215463,749586234792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154462296704,154462296768⟩ : DyadicInterval 40),(⟨-179764454720,-179764454656⟩ : DyadicInterval 40),(⟨749568902242,749568921571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154327270976,154327271040⟩ : DyadicInterval 40),(⟨-179581489216,-179581489152⟩ : DyadicInterval 40),(⟨749592507356,749592526686⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154444283648,154444283712⟩ : DyadicInterval 40),(⟨-179740043200,-179740043136⟩ : DyadicInterval 40),(⟨749572052735,749572072064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10530711,21077208⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10530624,10530688⟩ : DyadicInterval 40),(⟨-10530816,-10530752⟩ : DyadicInterval 40),(⟨762123383547,762123402876⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨21076992,21077056⟩ : DyadicInterval 40),(⟨-21077440,-21077376⟩ : DyadicInterval 40),(⟨762123383371,762123402700⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-448,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165703680478,165827990448⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154345270016,154345270080⟩ : DyadicInterval 40),(⟨-179605875584,-179605875520⟩ : DyadicInterval 40),(⟨749589362226,749589381556⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154453294016,154453294080⟩ : DyadicInterval 40),(⟨-179752254080,-179752254016⟩ : DyadicInterval 40),(⟨749570476888,749570496218⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25298960064,-25260605440⟩ : DyadicInterval 40),(⟨774753686336,774772882912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154363275904,154462296768⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179764454720,-179630272128⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1589_ok : ecellOkT e1589 = true := by decide +kernel
theorem e1589_pos {a z : ℝ} (ha1 : ((1234743/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((154449/1024000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1589 e1589_ok ha1 ha2 hz1 hz2 hz

-- box ['616947/4096000', '1234743/8192000', '7999/8000', '1']  interval_lower 119037327/1099511627776
noncomputable def e1590 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265122077048,0,true,154264246208,154264246272⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933901178504,0,false,-179496106048,-179496105984⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265236027900,0,true,154363275904,154363275968⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933787227652,0,false,-179630272192,-179630272128⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265101375741,0,true,154246254656,154246254720⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933921879811,0,false,-179471734016,-179471733952⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522159047,0,true,10531200,10531264⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099501096505,0,false,-10531328,-10531264⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627675,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1265111722271,0,true,154255246912,154255246976⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨933911533281,0,false,-179483915136,-179483915072⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1265236032254,0,true,154363279680,154363279744⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨933787223298,0,false,-179630277312,-179630277248⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1074532739380,0,false,-25266997632,-25266997568⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1074570198687,0,false,-25228668160,-25228668096⟩
    { al := (616947/4096000), au := (1234743/8192000), zl := (7999/8000), zu := 1,
      A := ⟨165610449272,165724400124⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154264246208,154264246272⟩ : DyadicInterval 40),(⟨-179496106048,-179496105984⟩ : DyadicInterval 40),(⟨749603516591,749603535921⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154363275904,154363275968⟩ : DyadicInterval 40),(⟨-179630272192,-179630272128⟩ : DyadicInterval 40),(⟨749586215462,749586234792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154246254656,154246254720⟩ : DyadicInterval 40),(⟨-179471734016,-179471733952⟩ : DyadicInterval 40),(⟨749606658367,749606677697⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154363275904,154363275968⟩ : DyadicInterval 40),(⟨-179630272192,-179630272128⟩ : DyadicInterval 40),(⟨749586215462,749586234792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10531271⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10531200,10531264⟩ : DyadicInterval 40),(⟨-10531328,-10531264⟩ : DyadicInterval 40),(⟨762123383515,762123402844⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨165600094495,165724404478⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154255246912,154255246976⟩ : DyadicInterval 40),(⟨-179483915136,-179483915072⟩ : DyadicInterval 40),(⟨749605088150,749605107480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154363279680,154363279744⟩ : DyadicInterval 40),(⟨-179630277312,-179630277248⟩ : DyadicInterval 40),(⟨749586214803,749586234132⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25266997632,-25228668096⟩ : DyadicInterval 40),(⟨774737717664,774756901696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨154264246208,154363275968⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179630272192,-179496105984⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1590_ok : ecellOkT e1590 = true := by decide +kernel
theorem e1590_pos {a z : ℝ} (ha1 : ((616947/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1234743/8192000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1590 e1590_ok ha1 ha2 hz1 hz2 hz

-- box ['1234743/8192000', '154449/1024000', '7999/8000', '1']  interval_lower 119985033/1099511627776
noncomputable def e1591 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265236027899,0,true,154363275904,154363275968⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933787227653,0,false,-179630272192,-179630272128⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265349978751,0,true,154462296704,154462296768⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933673276801,0,false,-179764454720,-179764454656⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265215312348,0,true,154345273600,154345273664⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933807943204,0,false,-179605880448,-179605880384⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099522166531,0,true,10538688,10538752⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099501089021,0,false,-10538816,-10538752⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627674,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1265225665998,0,true,154354271232,154354271296⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨933797589554,0,false,-179618071424,-179618071360⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1265349983109,0,true,154462300480,154462300544⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨933673272443,0,false,-179764459904,-179764459840⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1074498376979,0,false,-25302159360,-25302159296⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1074535864201,0,false,-25263800128,-25263800064⟩
    { al := (1234743/8192000), au := (154449/1024000), zl := (7999/8000), zu := 1,
      A := ⟨165724400123,165838350975⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154363275904,154363275968⟩ : DyadicInterval 40),(⟨-179630272192,-179630272128⟩ : DyadicInterval 40),(⟨749586215463,749586234792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154462296704,154462296768⟩ : DyadicInterval 40),(⟨-179764454720,-179764454656⟩ : DyadicInterval 40),(⟨749568902242,749568921571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154345273600,154345273664⟩ : DyadicInterval 40),(⟨-179605880448,-179605880384⟩ : DyadicInterval 40),(⟨749589361608,749589380937⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154462296704,154462296768⟩ : DyadicInterval 40),(⟨-179764454720,-179764454656⟩ : DyadicInterval 40),(⟨749568902242,749568921571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10538755⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10538688,10538752⟩ : DyadicInterval 40),(⟨-10538816,-10538752⟩ : DyadicInterval 40),(⟨762123383514,762123402843⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨165714038222,165838355333⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154354271232,154354271296⟩ : DyadicInterval 40),(⟨-179618071424,-179618071360⟩ : DyadicInterval 40),(⟨749587789208,749587808537⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154462300480,154462300544⟩ : DyadicInterval 40),(⟨-179764459904,-179764459840⟩ : DyadicInterval 40),(⟨749568901607,749568920937⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25302159360,-25263800064⟩ : DyadicInterval 40),(⟨774755283648,774774482560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨154363275904,154462296768⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179764454720,-179630272128⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1591_ok : ecellOkT e1591 = true := by decide +kernel
theorem e1591_pos {a z : ℝ} (ha1 : ((1234743/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((154449/1024000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1591 e1591_ok ha1 ha2 hz1 hz2 hz

-- box ['154449/1024000', '1236441/8192000', '999/1000', '7993/8000']  interval_lower 121903775/1099511627776
noncomputable def e1592 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265349978750,0,true,154462296704,154462296768⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933673276802,0,false,-179764454720,-179764454656⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265463929603,0,true,154561308544,154561308608⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933559325949,0,false,-179898653632,-179898653568⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265184140398,0,true,154318183872,154318183936⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933839115154,0,false,-179569177664,-179569177600⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265318721339,0,true,154435135552,154435135616⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933704534213,0,false,-179727646016,-179727645952⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585395763,0,true,73765504,73765568⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437859789,0,false,-73770496,-73770432⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099595994653,0,true,84363584,84363648⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099427260899,0,false,-84370176,-84370112⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621302,0,false,-6528,-6464⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622827,0,false,-4992,-4928⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265267056124,0,true,154390239616,154390239680⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933756199428,0,false,-179666807808,-179666807744⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265391330351,0,true,154498228096,154498228160⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933631925201,0,false,-179813152256,-179813152192⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074485902689,0,false,-25314924096,-25314924032⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074523386331,0,false,-25276568128,-25276568064⟩
    { al := (154449/1024000), au := (1236441/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨165838350974,165952301827⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154462296704,154462296768⟩ : DyadicInterval 40),(⟨-179764454720,-179764454656⟩ : DyadicInterval 40),(⟨749568902242,749568921571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154561308544,154561308608⟩ : DyadicInterval 40),(⟨-179898653632,-179898653568⟩ : DyadicInterval 40),(⟨749551576964,749551596293⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154318183872,154318183936⟩ : DyadicInterval 40),(⟨-179569177664,-179569177600⟩ : DyadicInterval 40),(⟨749594095031,749594114361⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154435135552,154435135616⟩ : DyadicInterval 40),(⟨-179727646016,-179727645952⟩ : DyadicInterval 40),(⟨749573652588,749573671918⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨73767987,84366877⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73765504,73765568⟩ : DyadicInterval 40),(⟨-73770496,-73770432⟩ : DyadicInterval 40),(⟨762123381098,762123400427⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨84363584,84363648⟩ : DyadicInterval 40),(⟨-84370176,-84370112⟩ : DyadicInterval 40),(⟨762123380374,762123399703⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6528,-4928⟩ : DyadicInterval 40),(⟨762123386080,762123406144⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165755428348,165879702575⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154390239616,154390239680⟩ : DyadicInterval 40),(⟨-179666807808,-179666807744⟩ : DyadicInterval 40),(⟨749581502386,749581521715⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154498228096,154498228160⟩ : DyadicInterval 40),(⟨-179813152256,-179813152192⟩ : DyadicInterval 40),(⟨749562616492,749562635822⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25314924096,-25276568064⟩ : DyadicInterval 40),(⟨774761667648,774780864928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154462296704,154561308608⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179898653632,-179764454656⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1592_ok : ecellOkT e1592 = true := by decide +kernel
theorem e1592_pos {a z : ℝ} (ha1 : ((154449/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1236441/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1592 e1592_ok ha1 ha2 hz1 hz2 hz

-- box ['1236441/8192000', '123729/819200', '999/1000', '7993/8000']  interval_lower 122858643/1099511627776
noncomputable def e1593 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265463929602,0,true,154561308544,154561308608⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933559325950,0,false,-179898653632,-179898653568⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265577880454,0,true,154660311488,154660311552⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933445375098,0,false,-180032868928,-180032868864⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265297977300,0,true,154417109696,154417109760⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933725278252,0,false,-179703218560,-179703218496⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265432572483,0,true,154534063232,154534063296⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933590683069,0,false,-179861723008,-179861722944⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585448155,0,true,73817856,73817920⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437807397,0,false,-73822912,-73822848⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099596054536,0,true,84423488,84423552⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099427201016,0,false,-84430016,-84429952⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621293,0,false,-6528,-6464⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622820,0,false,-4992,-4928⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265380950000,0,true,154489208448,154489208512⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933642305552,0,false,-179800927680,-179800927616⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265505231351,0,true,154597193408,154597193472⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933518024201,0,false,-179947298368,-179947298304⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074451523151,0,false,-25350104960,-25350104896⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074489034691,0,false,-25311719168,-25311719104⟩
    { al := (1236441/8192000), au := (123729/819200), zl := (999/1000), zu := (7993/8000),
      A := ⟨165952301826,166066252678⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154561308544,154561308608⟩ : DyadicInterval 40),(⟨-179898653632,-179898653568⟩ : DyadicInterval 40),(⟨749551576964,749551596293⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154660311488,154660311552⟩ : DyadicInterval 40),(⟨-180032868928,-180032868864⟩ : DyadicInterval 40),(⟨749534239591,749534258920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154417109696,154417109760⟩ : DyadicInterval 40),(⟨-179703218560,-179703218496⟩ : DyadicInterval 40),(⟨749576804639,749576823968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154534063232,154534063296⟩ : DyadicInterval 40),(⟨-179861723008,-179861722944⟩ : DyadicInterval 40),(⟨749556345771,749556365101⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨73820379,84426760⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73817856,73817920⟩ : DyadicInterval 40),(⟨-73822912,-73822848⟩ : DyadicInterval 40),(⟨762123381123,762123400452⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨84423488,84423552⟩ : DyadicInterval 40),(⟨-84430016,-84429952⟩ : DyadicInterval 40),(⟨762123380332,762123399662⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6528,-4928⟩ : DyadicInterval 40),(⟨762123386080,762123406144⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165869322224,165993603575⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154489208448,154489208512⟩ : DyadicInterval 40),(⟨-179800927680,-179800927616⟩ : DyadicInterval 40),(⟨749564194547,749564213876⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154597193408,154597193472⟩ : DyadicInterval 40),(⟨-179947298368,-179947298304⟩ : DyadicInterval 40),(⟨749545294389,749545313719⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25350104960,-25311719104⟩ : DyadicInterval 40),(⟨774779243168,774798455360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154561308544,154660311552⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180032868928,-179898653568⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1593_ok : ecellOkT e1593 = true := by decide +kernel
theorem e1593_pos {a z : ℝ} (ha1 : ((1236441/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((123729/819200 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1593 e1593_ok ha1 ha2 hz1 hz2 hz

-- box ['154449/1024000', '1236441/8192000', '7993/8000', '3997/4000']  interval_lower 60882637/549755813888
noncomputable def e1594 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265349978750,0,true,154462296704,154462296768⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933673276802,0,false,-179764454720,-179764454656⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265463929603,0,true,154561308544,154561308608⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933559325949,0,false,-179898653632,-179898653568⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265204870192,0,true,154336198976,154336199040⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933818385360,0,false,-179593585408,-179593585344⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265339465377,0,true,154453161152,154453161216⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933683790175,0,false,-179752074048,-179752073984⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099574857574,0,true,63227968,63228032⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099448397978,0,false,-63231680,-63231616⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585448982,0,true,73818688,73818752⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437806570,0,false,-73823744,-73823680⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622819,0,false,-4992,-4928⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624140,0,false,-3648,-3584⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265277420603,0,true,154399246272,154399246336⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933745834949,0,false,-179679012160,-179679012096⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265401702231,0,true,154507240320,154507240384⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933621553321,0,false,-179825366976,-179825366912⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074482773048,0,false,-25318126656,-25318126592⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074520261267,0,false,-25279765888,-25279765824⟩
    { al := (154449/1024000), au := (1236441/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨165838350974,165952301827⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154462296704,154462296768⟩ : DyadicInterval 40),(⟨-179764454720,-179764454656⟩ : DyadicInterval 40),(⟨749568902242,749568921571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154561308544,154561308608⟩ : DyadicInterval 40),(⟨-179898653632,-179898653568⟩ : DyadicInterval 40),(⟨749551576964,749551596293⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154336198976,154336199040⟩ : DyadicInterval 40),(⟨-179593585408,-179593585344⟩ : DyadicInterval 40),(⟨749590947355,749590966684⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154453161152,154453161216⟩ : DyadicInterval 40),(⟨-179752074048,-179752073984⟩ : DyadicInterval 40),(⟨749570500129,749570519459⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨63229798,73821206⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63227968,63228032⟩ : DyadicInterval 40),(⟨-63231680,-63231616⟩ : DyadicInterval 40),(⟨762123381771,762123401100⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73818688,73818752⟩ : DyadicInterval 40),(⟨-73823744,-73823680⟩ : DyadicInterval 40),(⟨762123381123,762123400452⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4992,-3584⟩ : DyadicInterval 40),(⟨762123385408,762123405376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165765792827,165890074455⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154399246272,154399246336⟩ : DyadicInterval 40),(⟨-179679012160,-179679012096⟩ : DyadicInterval 40),(⟨749579927831,749579947161⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154507240320,154507240384⟩ : DyadicInterval 40),(⟨-179825366976,-179825366912⟩ : DyadicInterval 40),(⟨749561039613,749561058942⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25318126656,-25279765824⟩ : DyadicInterval 40),(⟨774763266528,774782466208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154462296704,154561308608⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179898653632,-179764454656⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1594_ok : ecellOkT e1594 = true := by decide +kernel
theorem e1594_pos {a z : ℝ} (ha1 : ((154449/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1236441/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1594 e1594_ok ha1 ha2 hz1 hz2 hz

-- box ['1236441/8192000', '123729/819200', '7993/8000', '3997/4000']  interval_lower 61359865/549755813888
noncomputable def e1595 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265463929602,0,true,154561308544,154561308608⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933559325950,0,false,-179898653632,-179898653568⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265577880454,0,true,154660311488,154660311552⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933445375098,0,false,-180032868928,-180032868864⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265318721337,0,true,154435135552,154435135616⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933704534215,0,false,-179727646016,-179727645952⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265453330765,0,true,154552099584,154552099648⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933569924787,0,false,-179886170816,-179886170752⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099574902483,0,true,63272832,63272896⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099448353069,0,false,-63276544,-63276480⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585501378,0,true,73871104,73871168⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437754174,0,false,-73876096,-73876032⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622812,0,false,-4992,-4928⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624135,0,false,-3648,-3584⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265391321600,0,true,154498220480,154498220544⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933631933952,0,false,-179813141952,-179813141888⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265515610351,0,true,154606211008,154606211072⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933507645201,0,false,-179959523008,-179959522944⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074448389212,0,false,-25353312000,-25353311936⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074485905330,0,false,-25314921408,-25314921344⟩
    { al := (1236441/8192000), au := (123729/819200), zl := (7993/8000), zu := (3997/4000),
      A := ⟨165952301826,166066252678⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154561308544,154561308608⟩ : DyadicInterval 40),(⟨-179898653632,-179898653568⟩ : DyadicInterval 40),(⟨749551576964,749551596293⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154660311488,154660311552⟩ : DyadicInterval 40),(⟨-180032868928,-180032868864⟩ : DyadicInterval 40),(⟨749534239591,749534258920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154435135552,154435135616⟩ : DyadicInterval 40),(⟨-179727646016,-179727645952⟩ : DyadicInterval 40),(⟨749573652589,749573671918⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154552099584,154552099648⟩ : DyadicInterval 40),(⟨-179886170816,-179886170752⟩ : DyadicInterval 40),(⟨749553188959,749553208288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨63274707,73873602⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63272832,63272896⟩ : DyadicInterval 40),(⟨-63276544,-63276480⟩ : DyadicInterval 40),(⟨762123381766,762123401095⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73871104,73871168⟩ : DyadicInterval 40),(⟨-73876096,-73876032⟩ : DyadicInterval 40),(⟨762123381084,762123400413⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4992,-3584⟩ : DyadicInterval 40),(⟨762123385408,762123405376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165879693824,166003982575⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154498220480,154498220544⟩ : DyadicInterval 40),(⟨-179813141952,-179813141888⟩ : DyadicInterval 40),(⟨749562617830,749562637160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154606211008,154606211072⟩ : DyadicInterval 40),(⟨-179959523008,-179959522944⟩ : DyadicInterval 40),(⟨749543715345,749543734674⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25353312000,-25314921344⟩ : DyadicInterval 40),(⟨774780844288,774800058880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154561308544,154660311552⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180032868928,-179898653568⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1595_ok : ecellOkT e1595 = true := by decide +kernel
theorem e1595_pos {a z : ℝ} (ha1 : ((1236441/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((123729/819200 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1595 e1595_ok ha1 ha2 hz1 hz2 hz

-- box ['123729/819200', '1238139/8192000', '999/1000', '7993/8000']  interval_lower 123816267/1099511627776
noncomputable def e1596 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265577880453,0,true,154660311488,154660311552⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933445375099,0,false,-180032868928,-180032868864⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265691831305,0,true,154759305472,154759305536⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933331424247,0,false,-180167100608,-180167100544⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265411814200,0,true,154516026624,154516026688⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933611441352,0,false,-179837275776,-179837275712⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265546423627,0,true,154632982016,154632982080⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933476831925,0,false,-179995816320,-179995816256⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585500551,0,true,73870272,73870336⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437755001,0,false,-73875264,-73875200⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099596114420,0,true,84483392,84483456⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099427141132,0,false,-84489920,-84489856⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621284,0,false,-6528,-6464⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622813,0,false,-4992,-4928⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265494843876,0,true,154588168384,154588168448⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933528411676,0,false,-179935063936,-179935063872⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265619132349,0,true,154696149824,154696149888⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933404123203,0,false,-180081460928,-180081460864⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074417120015,0,false,-25385311040,-25385310976⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074454659454,0,false,-25346895488,-25346895424⟩
    { al := (123729/819200), au := (1238139/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨166066252677,166180203529⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154660311488,154660311552⟩ : DyadicInterval 40),(⟨-180032868928,-180032868864⟩ : DyadicInterval 40),(⟨749534239591,749534258920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154759305472,154759305536⟩ : DyadicInterval 40),(⟨-180167100608,-180167100544⟩ : DyadicInterval 40),(⟨749516890159,749516909488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154516026624,154516026688⟩ : DyadicInterval 40),(⟨-179837275776,-179837275712⟩ : DyadicInterval 40),(⟨749559502174,749559521504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154632982016,154632982080⟩ : DyadicInterval 40),(⟨-179995816320,-179995816256⟩ : DyadicInterval 40),(⟨749539026875,749539046205⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨73872775,84486644⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73870272,73870336⟩ : DyadicInterval 40),(⟨-73875264,-73875200⟩ : DyadicInterval 40),(⟨762123381084,762123400413⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨84483392,84483456⟩ : DyadicInterval 40),(⟨-84489920,-84489856⟩ : DyadicInterval 40),(⟨762123380323,762123399653⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6528,-4928⟩ : DyadicInterval 40),(⟨762123386080,762123406144⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165983216100,166107504573⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154588168384,154588168448⟩ : DyadicInterval 40),(⟨-179935063936,-179935063872⟩ : DyadicInterval 40),(⟨749546874638,749546893968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154696149824,154696149888⟩ : DyadicInterval 40),(⟨-180081460928,-180081460864⟩ : DyadicInterval 40),(⟨749527960240,749527979569⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25385311040,-25346895424⟩ : DyadicInterval 40),(⟨774796831328,774816058400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154660311488,154759305536⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180167100608,-180032868864⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1596_ok : ecellOkT e1596 = true := by decide +kernel
theorem e1596_pos {a z : ℝ} (ha1 : ((123729/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1238139/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1596 e1596_ok ha1 ha2 hz1 hz2 hz

-- box ['1238139/8192000', '309747/2048000', '999/1000', '7993/8000']  interval_lower 7798527/68719476736
noncomputable def e1597 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265691831304,0,true,154759305472,154759305536⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933331424248,0,false,-180167100608,-180167100544⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265805782156,0,true,154858290624,154858290688⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933217473396,0,false,-180301348672,-180301348608⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265525651100,0,true,154614934592,154614934656⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933497604452,0,false,-179971349376,-179971349312⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265660274771,0,true,154731891840,154731891904⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933362980781,0,false,-180129926016,-180129925952⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585552950,0,true,73922688,73922752⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437702602,0,false,-73927680,-73927616⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099596174310,0,true,84543232,84543296⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099427081242,0,false,-84549824,-84549760⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621274,0,false,-6528,-6464⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622806,0,false,-4992,-4928⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265608737744,0,true,154687119424,154687119488⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933414517808,0,false,-180069216576,-180069216512⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265733033347,0,true,154795097280,154795097344⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933290222205,0,false,-180215639744,-180215639680⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074382693281,0,false,-25420542464,-25420542400⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074420260625,0,false,-25382097088,-25382097024⟩
    { al := (1238139/8192000), au := (309747/2048000), zl := (999/1000), zu := (7993/8000),
      A := ⟨166180203528,166294154380⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154759305472,154759305536⟩ : DyadicInterval 40),(⟨-180167100608,-180167100544⟩ : DyadicInterval 40),(⟨749516890159,749516909488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154858290624,154858290688⟩ : DyadicInterval 40),(⟨-180301348672,-180301348608⟩ : DyadicInterval 40),(⟨749499528592,749499547922⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154614934592,154614934656⟩ : DyadicInterval 40),(⟨-179971349376,-179971349312⟩ : DyadicInterval 40),(⟨749542187701,749542207031⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154731891840,154731891904⟩ : DyadicInterval 40),(⟨-180129926016,-180129925952⟩ : DyadicInterval 40),(⟨749521695962,749521715292⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨73925174,84546534⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73922688,73922752⟩ : DyadicInterval 40),(⟨-73927680,-73927616⟩ : DyadicInterval 40),(⟨762123381077,762123400406⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨84543232,84543296⟩ : DyadicInterval 40),(⟨-84549824,-84549760⟩ : DyadicInterval 40),(⟨762123380346,762123399676⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6528,-4928⟩ : DyadicInterval 40),(⟨762123386080,762123406144⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166097109968,166221405571⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154687119424,154687119488⟩ : DyadicInterval 40),(⟨-180069216576,-180069216512⟩ : DyadicInterval 40),(⟨749529542660,749529561989⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154795097280,154795097344⟩ : DyadicInterval 40),(⟨-180215639744,-180215639680⟩ : DyadicInterval 40),(⟨749510613998,749510633327⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25420542464,-25382097024⟩ : DyadicInterval 40),(⟨774814432128,774833674112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154759305472,154858290688⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180301348672,-180167100544⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1597_ok : ecellOkT e1597 = true := by decide +kernel
theorem e1597_pos {a z : ℝ} (ha1 : ((1238139/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((309747/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1597 e1597_ok ha1 ha2 hz1 hz2 hz

-- box ['123729/819200', '1238139/8192000', '7993/8000', '3997/4000']  interval_lower 7729829/68719476736
noncomputable def e1598 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265577880453,0,true,154660311488,154660311552⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933445375099,0,false,-180032868928,-180032868864⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265691831305,0,true,154759305472,154759305536⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933331424247,0,false,-180167100608,-180167100544⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265432572481,0,true,154534063232,154534063296⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933590683071,0,false,-179861723008,-179861722944⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265567196153,0,true,154651029120,154651029184⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933456059399,0,false,-180020283904,-180020283840⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099574947393,0,true,63317760,63317824⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099448308159,0,false,-63321472,-63321408⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585553779,0,true,73923456,73923520⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437701773,0,false,-73928512,-73928448⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622805,0,false,-4992,-4928⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624130,0,false,-3648,-3584⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265505222598,0,true,154597185792,154597185856⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933518032954,0,false,-179947288064,-179947288000⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265629518470,0,true,154705172736,154705172800⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933393737082,0,false,-180093695360,-180093695296⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074413981774,0,false,-25388522624,-25388522560⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074451525795,0,false,-25350102272,-25350102208⟩
    { al := (123729/819200), au := (1238139/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨166066252677,166180203529⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154660311488,154660311552⟩ : DyadicInterval 40),(⟨-180032868928,-180032868864⟩ : DyadicInterval 40),(⟨749534239591,749534258920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154759305472,154759305536⟩ : DyadicInterval 40),(⟨-180167100608,-180167100544⟩ : DyadicInterval 40),(⟨749516890159,749516909488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154534063232,154534063296⟩ : DyadicInterval 40),(⟨-179861723008,-179861722944⟩ : DyadicInterval 40),(⟨749556345772,749556365101⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154651029120,154651029184⟩ : DyadicInterval 40),(⟨-180020283904,-180020283840⟩ : DyadicInterval 40),(⟨749535865702,749535885031⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨63319617,73926003⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63317760,63317824⟩ : DyadicInterval 40),(⟨-63321472,-63321408⟩ : DyadicInterval 40),(⟨762123381761,762123401090⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73923456,73923520⟩ : DyadicInterval 40),(⟨-73928512,-73928448⟩ : DyadicInterval 40),(⟨762123381109,762123400438⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4992,-3584⟩ : DyadicInterval 40),(⟨762123385408,762123405376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165993594822,166117890694⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154597185792,154597185856⟩ : DyadicInterval 40),(⟨-179947288064,-179947288000⟩ : DyadicInterval 40),(⟨749545295730,749545315059⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154705172736,154705172800⟩ : DyadicInterval 40),(⟨-180093695360,-180093695296⟩ : DyadicInterval 40),(⟨749526379009,749526398339⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25388522624,-25350102208⟩ : DyadicInterval 40),(⟨774798434720,774817664192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154660311488,154759305536⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180167100608,-180032868864⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1598_ok : ecellOkT e1598 = true := by decide +kernel
theorem e1598_pos {a z : ℝ} (ha1 : ((123729/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1238139/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1598 e1598_ok ha1 ha2 hz1 hz2 hz

-- box ['1238139/8192000', '309747/2048000', '7993/8000', '3997/4000']  interval_lower 124637371/1099511627776
noncomputable def e1599 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265691831304,0,true,154759305472,154759305536⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933331424248,0,false,-180167100608,-180167100544⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265805782156,0,true,154858290624,154858290688⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933217473396,0,false,-180301348672,-180301348608⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265546423625,0,true,154632982016,154632982080⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933476831927,0,false,-179995816320,-179995816256⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265681061541,0,true,154749949696,154749949760⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933342194011,0,false,-180154413376,-180154413312⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099574992308,0,true,63362688,63362752⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099448263244,0,false,-63366400,-63366336⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585606181,0,true,73975872,73975936⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437649371,0,false,-73980928,-73980864⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622798,0,false,-4992,-4928⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624125,0,false,-3712,-3648⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265619123849,0,true,154696142400,154696142464⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933404131703,0,false,-180081450880,-180081450816⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265743426590,0,true,154804125632,154804125696⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933279828962,0,false,-180227884160,-180227884096⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074379550734,0,false,-25423758464,-25423758400⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074417122585,0,false,-25385308416,-25385308352⟩
    { al := (1238139/8192000), au := (309747/2048000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨166180203528,166294154380⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154759305472,154759305536⟩ : DyadicInterval 40),(⟨-180167100608,-180167100544⟩ : DyadicInterval 40),(⟨749516890159,749516909488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154858290624,154858290688⟩ : DyadicInterval 40),(⟨-180301348672,-180301348608⟩ : DyadicInterval 40),(⟨749499528592,749499547922⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154632982016,154632982080⟩ : DyadicInterval 40),(⟨-179995816320,-179995816256⟩ : DyadicInterval 40),(⟨749539026875,749539046205⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154749949696,154749949760⟩ : DyadicInterval 40),(⟨-180154413376,-180154413312⟩ : DyadicInterval 40),(⟨749518530422,749518549752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨63364532,73978405⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63362688,63362752⟩ : DyadicInterval 40),(⟨-63366400,-63366336⟩ : DyadicInterval 40),(⟨762123381756,762123401085⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73975872,73975936⟩ : DyadicInterval 40),(⟨-73980928,-73980864⟩ : DyadicInterval 40),(⟨762123381102,762123400431⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4992,-3648⟩ : DyadicInterval 40),(⟨762123385440,762123405376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166107496073,166231798814⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154696142400,154696142464⟩ : DyadicInterval 40),(⟨-180081450880,-180081450816⟩ : DyadicInterval 40),(⟨749527961542,749527980871⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154804125632,154804125696⟩ : DyadicInterval 40),(⟨-180227884160,-180227884096⟩ : DyadicInterval 40),(⟨749509030586,749509049915⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25423758464,-25385308352⟩ : DyadicInterval 40),(⟨774816037792,774835282112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154759305472,154858290688⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180301348672,-180167100544⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1599_ok : ecellOkT e1599 = true := by decide +kernel
theorem e1599_pos {a z : ℝ} (ha1 : ((1238139/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((309747/2048000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1599 e1599_ok ha1 ha2 hz1 hz2 hz

-- box ['154449/1024000', '1236441/8192000', '3997/4000', '1599/1600']  interval_lower 30406803/274877906944
noncomputable def e1600 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265349978750,0,true,154462296704,154462296768⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933673276802,0,false,-179764454720,-179764454656⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265463929603,0,true,154561308544,154561308608⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933559325949,0,false,-179898653632,-179898653568⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265225599986,0,true,154354213824,154354213888⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933797655566,0,false,-179617993664,-179617993600⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265360209415,0,true,154471186496,154471186560⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933663046137,0,false,-179776502656,-179776502592⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564319343,0,true,52690304,52690368⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458936209,0,false,-52692864,-52692800⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099574903265,0,true,63273664,63273728⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099448352287,0,false,-63277312,-63277248⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624134,0,false,-3648,-3584⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625251,0,false,-2560,-2496⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265287785618,0,true,154408253312,154408253376⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933735469934,0,false,-179691217344,-179691217280⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265412074133,0,true,154516252416,154516252480⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933611181419,0,false,-179837581888,-179837581824⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074479643205,0,false,-25321329408,-25321329344⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074517135845,0,false,-25282963968,-25282963904⟩
    { al := (154449/1024000), au := (1236441/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨165838350974,165952301827⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154462296704,154462296768⟩ : DyadicInterval 40),(⟨-179764454720,-179764454656⟩ : DyadicInterval 40),(⟨749568902242,749568921571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154561308544,154561308608⟩ : DyadicInterval 40),(⟨-179898653632,-179898653568⟩ : DyadicInterval 40),(⟨749551576964,749551596293⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154354213824,154354213888⟩ : DyadicInterval 40),(⟨-179617993664,-179617993600⟩ : DyadicInterval 40),(⟨749587799243,749587818573⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154471186496,154471186560⟩ : DyadicInterval 40),(⟨-179776502656,-179776502592⟩ : DyadicInterval 40),(⟨749567347261,749567366591⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨52691567,63275489⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52690304,52690368⟩ : DyadicInterval 40),(⟨-52692864,-52692800⟩ : DyadicInterval 40),(⟨762123382306,762123401635⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63273664,63273728⟩ : DyadicInterval 40),(⟨-63277312,-63277248⟩ : DyadicInterval 40),(⟨762123381734,762123401063⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3648,-2496⟩ : DyadicInterval 40),(⟨762123384864,762123404704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165776157842,165900446357⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154408253312,154408253376⟩ : DyadicInterval 40),(⟨-179691217344,-179691217280⟩ : DyadicInterval 40),(⟨749578353127,749578372456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154516252416,154516252480⟩ : DyadicInterval 40),(⟨-179837581888,-179837581824⟩ : DyadicInterval 40),(⟨749559462685,749559482014⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25321329408,-25282963904⟩ : DyadicInterval 40),(⟨774764865568,774784067584⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154462296704,154561308608⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179898653632,-179764454656⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1600_ok : ecellOkT e1600 = true := by decide +kernel
theorem e1600_pos {a z : ℝ} (ha1 : ((154449/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1236441/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1600 e1600_ok ha1 ha2 hz1 hz2 hz

-- box ['1236441/8192000', '123729/819200', '3997/4000', '1599/1600']  interval_lower 61290883/549755813888
noncomputable def e1601 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265463929602,0,true,154561308544,154561308608⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933559325950,0,false,-179898653632,-179898653568⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265577880454,0,true,154660311488,154660311552⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933445375098,0,false,-180032868928,-180032868864⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265339465375,0,true,154453161152,154453161216⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933683790177,0,false,-179752074048,-179752073984⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265474089047,0,true,154570135616,154570135680⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933549166505,0,false,-179910619136,-179910619072⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564356766,0,true,52727680,52727744⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458898786,0,false,-52730304,-52730240⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099574948177,0,true,63318528,63318592⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099448307375,0,false,-63322240,-63322176⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624129,0,false,-3648,-3584⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625248,0,false,-2560,-2496⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265401693736,0,true,154507232896,154507232960⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933621561816,0,false,-179825356992,-179825356928⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265525989373,0,true,154615228480,154615228544⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933497266179,0,false,-179971747776,-179971747712⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074445255069,0,false,-25356519232,-25356519168⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074482775612,0,false,-25318124032,-25318123968⟩
    { al := (1236441/8192000), au := (123729/819200), zl := (3997/4000), zu := (1599/1600),
      A := ⟨165952301826,166066252678⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154561308544,154561308608⟩ : DyadicInterval 40),(⟨-179898653632,-179898653568⟩ : DyadicInterval 40),(⟨749551576964,749551596293⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154660311488,154660311552⟩ : DyadicInterval 40),(⟨-180032868928,-180032868864⟩ : DyadicInterval 40),(⟨749534239591,749534258920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154453161152,154453161216⟩ : DyadicInterval 40),(⟨-179752074048,-179752073984⟩ : DyadicInterval 40),(⟨749570500130,749570519459⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154570135616,154570135680⟩ : DyadicInterval 40),(⟨-179910619136,-179910619072⟩ : DyadicInterval 40),(⟨749550031745,749550051074⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨52728990,63320401⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52727680,52727744⟩ : DyadicInterval 40),(⟨-52730304,-52730240⟩ : DyadicInterval 40),(⟨762123382335,762123401664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63318528,63318592⟩ : DyadicInterval 40),(⟨-63322240,-63322176⟩ : DyadicInterval 40),(⟨762123381761,762123401090⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3648,-2496⟩ : DyadicInterval 40),(⟨762123384864,762123404704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165890065960,166014361597⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154507232896,154507232960⟩ : DyadicInterval 40),(⟨-179825356992,-179825356928⟩ : DyadicInterval 40),(⟨749561040937,749561060267⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154615228480,154615228544⟩ : DyadicInterval 40),(⟨-179971747776,-179971747712⟩ : DyadicInterval 40),(⟨749542136224,749542155554⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25356519232,-25318123968⟩ : DyadicInterval 40),(⟨774782445600,774801662496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154561308544,154660311552⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180032868928,-179898653568⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1601_ok : ecellOkT e1601 = true := by decide +kernel
theorem e1601_pos {a z : ℝ} (ha1 : ((1236441/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((123729/819200 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1601 e1601_ok ha1 ha2 hz1 hz2 hz

-- box ['154449/1024000', '1236441/8192000', '1599/1600', '1999/2000']  interval_lower 121489015/1099511627776
noncomputable def e1602 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265349978750,0,true,154462296704,154462296768⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933673276802,0,false,-179764454720,-179764454656⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265463929603,0,true,154561308544,154561308608⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933559325949,0,false,-179898653632,-179898653568⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265246329780,0,true,154372228416,154372228480⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933776925772,0,false,-179642402496,-179642402432⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265380953453,0,true,154489211456,154489211520⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933642302099,0,false,-179800931776,-179800931712⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099553781066,0,true,42152448,42152512⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099469474486,0,false,-42154112,-42154048⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564357504,0,true,52728448,52728512⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458898048,0,false,-52731008,-52730944⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625247,0,false,-2560,-2496⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626160,0,false,-1664,-1600⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265298150400,0,true,154417260096,154417260160⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933725105152,0,false,-179703422400,-179703422336⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265422446052,0,true,154525264512,154525264576⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933600809500,0,false,-179849796928,-179849796864⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074476513161,0,false,-25324532352,-25324532288⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074514010298,0,false,-25286162240,-25286162176⟩
    { al := (154449/1024000), au := (1236441/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨165838350974,165952301827⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154462296704,154462296768⟩ : DyadicInterval 40),(⟨-179764454720,-179764454656⟩ : DyadicInterval 40),(⟨749568902242,749568921571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154561308544,154561308608⟩ : DyadicInterval 40),(⟨-179898653632,-179898653568⟩ : DyadicInterval 40),(⟨749551576964,749551596293⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154372228416,154372228480⟩ : DyadicInterval 40),(⟨-179642402496,-179642402432⟩ : DyadicInterval 40),(⟨749584650724,749584670054⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154489211456,154489211520⟩ : DyadicInterval 40),(⟨-179800931776,-179800931712⟩ : DyadicInterval 40),(⟨749564194030,749564213360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨42153290,52729728⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42152448,42152512⟩ : DyadicInterval 40),(⟨-42154112,-42154048⟩ : DyadicInterval 40),(⟨762123382767,762123402096⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52728448,52728512⟩ : DyadicInterval 40),(⟨-52731008,-52730944⟩ : DyadicInterval 40),(⟨762123382303,762123401632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2560,-1600⟩ : DyadicInterval 40),(⟨762123384416,762123404160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165786522624,165910818276⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154417260096,154417260160⟩ : DyadicInterval 40),(⟨-179703422400,-179703422336⟩ : DyadicInterval 40),(⟨749576778352,749576797681⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154525264512,154525264576⟩ : DyadicInterval 40),(⟨-179849796928,-179849796864⟩ : DyadicInterval 40),(⟨749557885608,749557904938⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25324532352,-25286162176⟩ : DyadicInterval 40),(⟨774766464704,774785669056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154462296704,154561308608⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-179898653632,-179764454656⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1602_ok : ecellOkT e1602 = true := by decide +kernel
theorem e1602_pos {a z : ℝ} (ha1 : ((154449/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1236441/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1602 e1602_ok ha1 ha2 hz1 hz2 hz

-- box ['1236441/8192000', '123729/819200', '1599/1600', '1999/2000']  interval_lower 30610757/274877906944
noncomputable def e1603 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265463929602,0,true,154561308544,154561308608⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933559325950,0,false,-179898653632,-179898653568⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265577880454,0,true,154660311488,154660311552⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933445375098,0,false,-180032868928,-180032868864⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265360209413,0,true,154471186496,154471186560⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933663046139,0,false,-179776502656,-179776502592⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265494847328,0,true,154588171392,154588171456⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933528408224,0,false,-179935068032,-179935067968⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099553811005,0,true,42182400,42182464⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099469444547,0,false,-42184064,-42184000⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564394931,0,true,52765888,52765952⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458860621,0,false,-52768448,-52768384⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625243,0,false,-2560,-2496⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626158,0,false,-1664,-1600⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265412065638,0,true,154516245056,154516245120⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933611189914,0,false,-179837571904,-179837571840⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265536368417,0,true,154624245952,154624246016⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933486887135,0,false,-179983972736,-179983972672⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074442120725,0,false,-25359726720,-25359726656⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074479645770,0,false,-25321326784,-25321326720⟩
    { al := (1236441/8192000), au := (123729/819200), zl := (1599/1600), zu := (1999/2000),
      A := ⟨165952301826,166066252678⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154561308544,154561308608⟩ : DyadicInterval 40),(⟨-179898653632,-179898653568⟩ : DyadicInterval 40),(⟨749551576964,749551596293⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154660311488,154660311552⟩ : DyadicInterval 40),(⟨-180032868928,-180032868864⟩ : DyadicInterval 40),(⟨749534239591,749534258920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154471186496,154471186560⟩ : DyadicInterval 40),(⟨-179776502656,-179776502592⟩ : DyadicInterval 40),(⟨749567347261,749567366591⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154588171392,154588171456⟩ : DyadicInterval 40),(⟨-179935068032,-179935067968⟩ : DyadicInterval 40),(⟨749546874121,749546893450⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨42183229,52767155⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42182400,42182464⟩ : DyadicInterval 40),(⟨-42184064,-42184000⟩ : DyadicInterval 40),(⟨762123382765,762123402094⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52765888,52765952⟩ : DyadicInterval 40),(⟨-52768448,-52768384⟩ : DyadicInterval 40),(⟨762123382299,762123401628⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2560,-1600⟩ : DyadicInterval 40),(⟨762123384416,762123404160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨165900437862,166024740641⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154516245056,154516245120⟩ : DyadicInterval 40),(⟨-179837571904,-179837571840⟩ : DyadicInterval 40),(⟨749559463973,749559483302⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154624245952,154624246016⟩ : DyadicInterval 40),(⟨-179983972736,-179983972672⟩ : DyadicInterval 40),(⟨749540556981,749540576311⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25359726720,-25321326720⟩ : DyadicInterval 40),(⟨774784046976,774803266240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154561308544,154660311552⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180032868928,-179898653568⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1603_ok : ecellOkT e1603 = true := by decide +kernel
theorem e1603_pos {a z : ℝ} (ha1 : ((1236441/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((123729/819200 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1603 e1603_ok ha1 ha2 hz1 hz2 hz

-- box ['123729/819200', '1238139/8192000', '3997/4000', '1599/1600']  interval_lower 61769291/549755813888
noncomputable def e1604 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265577880453,0,true,154660311488,154660311552⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933445375099,0,false,-180032868928,-180032868864⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265691831305,0,true,154759305472,154759305536⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933331424247,0,false,-180167100608,-180167100544⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265453330763,0,true,154552099584,154552099648⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933569924789,0,false,-179886170816,-179886170752⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265587968678,0,true,154669075904,154669075968⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933435286874,0,false,-180044752000,-180044751936⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564394191,0,true,52765120,52765184⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458861361,0,false,-52767744,-52767680⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099574993091,0,true,63363456,63363520⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099448262461,0,false,-63367168,-63367104⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624124,0,false,-3712,-3648⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625244,0,false,-2560,-2496⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265515601854,0,true,154606203584,154606203648⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933507653698,0,false,-179959513024,-179959512960⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265639904613,0,true,154714195648,154714195712⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933383350939,0,false,-180105930048,-180105929984⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074410843329,0,false,-25391734336,-25391734272⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074448391778,0,false,-25353309376,-25353309312⟩
    { al := (123729/819200), au := (1238139/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨166066252677,166180203529⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154660311488,154660311552⟩ : DyadicInterval 40),(⟨-180032868928,-180032868864⟩ : DyadicInterval 40),(⟨749534239591,749534258920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154759305472,154759305536⟩ : DyadicInterval 40),(⟨-180167100608,-180167100544⟩ : DyadicInterval 40),(⟨749516890159,749516909488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154552099584,154552099648⟩ : DyadicInterval 40),(⟨-179886170816,-179886170752⟩ : DyadicInterval 40),(⟨749553188959,749553208288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154669075904,154669075968⟩ : DyadicInterval 40),(⟨-180044752000,-180044751936⟩ : DyadicInterval 40),(⟨749532704127,749532723457⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨52766415,63365315⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52765120,52765184⟩ : DyadicInterval 40),(⟨-52767744,-52767680⟩ : DyadicInterval 40),(⟨762123382331,762123401660⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63363456,63363520⟩ : DyadicInterval 40),(⟨-63367168,-63367104⟩ : DyadicInterval 40),(⟨762123381756,762123401085⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3712,-2496⟩ : DyadicInterval 40),(⟨762123384864,762123404736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166003974078,166128276837⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154606203584,154606203648⟩ : DyadicInterval 40),(⟨-179959513024,-179959512960⟩ : DyadicInterval 40),(⟨749543716672,749543736001⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154714195648,154714195712⟩ : DyadicInterval 40),(⟨-180105930048,-180105929984⟩ : DyadicInterval 40),(⟨749524797683,749524817013⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25391734336,-25353309312⟩ : DyadicInterval 40),(⟨774800038272,774819270048⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154660311488,154759305536⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180167100608,-180032868864⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1604_ok : ecellOkT e1604 = true := by decide +kernel
theorem e1604_pos {a z : ℝ} (ha1 : ((123729/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1238139/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1604 e1604_ok ha1 ha2 hz1 hz2 hz

-- box ['1238139/8192000', '309747/2048000', '3997/4000', '1599/1600']  interval_lower 62248737/549755813888
noncomputable def e1605 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265691831304,0,true,154759305472,154759305536⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933331424248,0,false,-180167100608,-180167100544⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265805782156,0,true,154858290624,154858290688⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933217473396,0,false,-180301348672,-180301348608⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265567196151,0,true,154651029120,154651029184⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933456059401,0,false,-180020283904,-180020283840⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265701848310,0,true,154768007296,154768007360⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933321407242,0,false,-180178901184,-180178901120⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564431621,0,true,52802560,52802624⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458823931,0,false,-52805120,-52805056⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575038008,0,true,63408384,63408448⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099448217544,0,false,-63412096,-63412032⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624119,0,false,-3712,-3648⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625241,0,false,-2560,-2496⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265629509714,0,true,154705165120,154705165184⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933393745838,0,false,-180093685056,-180093684992⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265753819861,0,true,154813153920,154813153984⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933269435691,0,false,-180240128704,-180240128640⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074376407982,0,false,-25426974784,-25426974720⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074413984421,0,false,-25388519872,-25388519808⟩
    { al := (1238139/8192000), au := (309747/2048000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨166180203528,166294154380⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154759305472,154759305536⟩ : DyadicInterval 40),(⟨-180167100608,-180167100544⟩ : DyadicInterval 40),(⟨749516890159,749516909488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154858290624,154858290688⟩ : DyadicInterval 40),(⟨-180301348672,-180301348608⟩ : DyadicInterval 40),(⟨749499528592,749499547922⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154651029120,154651029184⟩ : DyadicInterval 40),(⟨-180020283904,-180020283840⟩ : DyadicInterval 40),(⟨749535865702,749535885032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154768007296,154768007360⟩ : DyadicInterval 40),(⟨-180178901184,-180178901120⟩ : DyadicInterval 40),(⟨749515364416,749515383745⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨52803845,63410232⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52802560,52802624⟩ : DyadicInterval 40),(⟨-52805120,-52805056⟩ : DyadicInterval 40),(⟨762123382296,762123401625⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63408384,63408448⟩ : DyadicInterval 40),(⟨-63412096,-63412032⟩ : DyadicInterval 40),(⟨762123381750,762123401080⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3712,-2496⟩ : DyadicInterval 40),(⟨762123384864,762123404736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166117881938,166242192085⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154705165120,154705165184⟩ : DyadicInterval 40),(⟨-180093685056,-180093684992⟩ : DyadicInterval 40),(⟨749526380352,749526399682⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154813153920,154813153984⟩ : DyadicInterval 40),(⟨-180240128704,-180240128640⟩ : DyadicInterval 40),(⟨749507447060,749507466389⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25426974784,-25388519808⟩ : DyadicInterval 40),(⟨774817643520,774836890272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154759305472,154858290688⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180301348672,-180167100544⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1605_ok : ecellOkT e1605 = true := by decide +kernel
theorem e1605_pos {a z : ℝ} (ha1 : ((1238139/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((309747/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1605 e1605_ok ha1 ha2 hz1 hz2 hz

-- box ['123729/819200', '1238139/8192000', '1599/1600', '1999/2000']  interval_lower 30849927/274877906944
noncomputable def e1606 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265577880453,0,true,154660311488,154660311552⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933445375099,0,false,-180032868928,-180032868864⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265691831305,0,true,154759305472,154759305536⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933331424247,0,false,-180167100608,-180167100544⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265474089044,0,true,154570135616,154570135680⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933549166508,0,false,-179910619136,-179910619072⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265608741204,0,true,154687122432,154687122496⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933414514348,0,false,-180069220608,-180069220544⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099553840947,0,true,42212352,42212416⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099469414605,0,false,-42214016,-42213952⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564432360,0,true,52803264,52803328⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458823192,0,false,-52805888,-52805824⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625240,0,false,-2560,-2496⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626156,0,false,-1664,-1600⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265525980875,0,true,154615221120,154615221184⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933497274677,0,false,-179971737792,-179971737728⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265650290781,0,true,154723218496,154723218560⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933372964771,0,false,-180118164864,-180118164800⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074407704681,0,false,-25394946368,-25394946304⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074445257637,0,false,-25356516608,-25356516544⟩
    { al := (123729/819200), au := (1238139/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨166066252677,166180203529⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154660311488,154660311552⟩ : DyadicInterval 40),(⟨-180032868928,-180032868864⟩ : DyadicInterval 40),(⟨749534239591,749534258920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154759305472,154759305536⟩ : DyadicInterval 40),(⟨-180167100608,-180167100544⟩ : DyadicInterval 40),(⟨749516890159,749516909488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154570135616,154570135680⟩ : DyadicInterval 40),(⟨-179910619136,-179910619072⟩ : DyadicInterval 40),(⟨749550031745,749550051075⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154687122432,154687122496⟩ : DyadicInterval 40),(⟨-180069220608,-180069220544⟩ : DyadicInterval 40),(⟨749529542113,749529561443⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨42213171,52804584⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42212352,42212416⟩ : DyadicInterval 40),(⟨-42214016,-42213952⟩ : DyadicInterval 40),(⟨762123382763,762123402092⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52803264,52803328⟩ : DyadicInterval 40),(⟨-52805888,-52805824⟩ : DyadicInterval 40),(⟨762123382327,762123401657⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2560,-1600⟩ : DyadicInterval 40),(⟨762123384416,762123404160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166014353099,166138663005⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154615221120,154615221184⟩ : DyadicInterval 40),(⟨-179971737792,-179971737728⟩ : DyadicInterval 40),(⟨749542137514,749542156844⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154723218496,154723218560⟩ : DyadicInterval 40),(⟨-180118164864,-180118164800⟩ : DyadicInterval 40),(⟨749523216244,749523235574⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25394946368,-25356516544⟩ : DyadicInterval 40),(⟨774801641888,774820876064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154660311488,154759305536⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180167100608,-180032868864⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1606_ok : ecellOkT e1606 = true := by decide +kernel
theorem e1606_pos {a z : ℝ} (ha1 : ((123729/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1238139/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1606 e1606_ok ha1 ha2 hz1 hz2 hz

-- box ['1238139/8192000', '309747/2048000', '1599/1600', '1999/2000']  interval_lower 15544803/137438953472
noncomputable def e1607 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265691831304,0,true,154759305472,154759305536⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933331424248,0,false,-180167100608,-180167100544⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265805782156,0,true,154858290624,154858290688⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933217473396,0,false,-180301348672,-180301348608⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265587968676,0,true,154669075904,154669075968⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933435286876,0,false,-180044752000,-180044751936⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265722635079,0,true,154786064512,154786064576⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933300620473,0,false,-180203389632,-180203389568⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099553870889,0,true,42242240,42242304⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099469384663,0,false,-42243968,-42243904⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564469792,0,true,52840704,52840768⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458785760,0,false,-52843328,-52843264⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625236,0,false,-2560,-2496⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626154,0,false,-1664,-1600⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265639895857,0,true,154714188032,154714188096⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933383359695,0,false,-180105919744,-180105919680⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265764213144,0,true,154822182080,154822182144⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933259042408,0,false,-180252373376,-180252373312⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074373265030,0,false,-25430191232,-25430191168⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074410845976,0,false,-25391731648,-25391731584⟩
    { al := (1238139/8192000), au := (309747/2048000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨166180203528,166294154380⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154759305472,154759305536⟩ : DyadicInterval 40),(⟨-180167100608,-180167100544⟩ : DyadicInterval 40),(⟨749516890159,749516909488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154858290624,154858290688⟩ : DyadicInterval 40),(⟨-180301348672,-180301348608⟩ : DyadicInterval 40),(⟨749499528592,749499547922⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154669075904,154669075968⟩ : DyadicInterval 40),(⟨-180044752000,-180044751936⟩ : DyadicInterval 40),(⟨749532704127,749532723457⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154786064512,154786064576⟩ : DyadicInterval 40),(⟨-180203389632,-180203389568⟩ : DyadicInterval 40),(⟨749512198098,749512217427⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨42243113,52842016⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42242240,42242304⟩ : DyadicInterval 40),(⟨-42243968,-42243904⟩ : DyadicInterval 40),(⟨762123382792,762123402122⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52840704,52840768⟩ : DyadicInterval 40),(⟨-52843328,-52843264⟩ : DyadicInterval 40),(⟨762123382324,762123401653⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2560,-1600⟩ : DyadicInterval 40),(⟨762123384416,762123404160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166128268081,166252585368⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154714188032,154714188096⟩ : DyadicInterval 40),(⟨-180105919744,-180105919680⟩ : DyadicInterval 40),(⟨749524799026,749524818356⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154822182080,154822182144⟩ : DyadicInterval 40),(⟨-180252373376,-180252373312⟩ : DyadicInterval 40),(⟨749505863460,749505882789⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25430191232,-25391731584⟩ : DyadicInterval 40),(⟨774819249408,774838498496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154759305472,154858290688⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180301348672,-180167100544⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1607_ok : ecellOkT e1607 = true := by decide +kernel
theorem e1607_pos {a z : ℝ} (ha1 : ((1238139/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((309747/2048000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1607 e1607_ok ha1 ha2 hz1 hz2 hz

-- box ['309747/2048000', '1239837/8192000', '999/1000', '7993/8000']  interval_lower 125739091/1099511627776
noncomputable def e1608 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265805782155,0,true,154858290624,154858290688⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933217473397,0,false,-180301348672,-180301348608⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265919733007,0,true,154957266816,154957266880⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933103522545,0,false,-180435613120,-180435613056⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265639488000,0,true,154713833728,154713833792⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933383767552,0,false,-180105439296,-180105439232⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265774125915,0,true,154830792832,154830792896⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933249129637,0,false,-180264052096,-180264052032⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585605352,0,true,73975040,73975104⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437650200,0,false,-73980096,-73980032⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099596234204,0,true,84603136,84603200⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099427021348,0,false,-84609728,-84609664⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621265,0,false,-6528,-6464⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622799,0,false,-4992,-4928⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265722631623,0,true,154786061504,154786061568⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933300623929,0,false,-180203385536,-180203385472⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265846934346,0,true,154894035904,154894035968⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933176321206,0,false,-180349835008,-180349834944⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074348242948,0,false,-25455799104,-25455799040⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074385838197,0,false,-25417323968,-25417323904⟩
    { al := (309747/2048000), au := (1239837/8192000), zl := (999/1000), zu := (7993/8000),
      A := ⟨166294154379,166408105231⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154858290624,154858290688⟩ : DyadicInterval 40),(⟨-180301348672,-180301348608⟩ : DyadicInterval 40),(⟨749499528593,749499547922⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154957266816,154957266880⟩ : DyadicInterval 40),(⟨-180435613120,-180435613056⟩ : DyadicInterval 40),(⟨749482154965,749482174294⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154713833728,154713833792⟩ : DyadicInterval 40),(⟨-180105439296,-180105439232⟩ : DyadicInterval 40),(⟨749524861117,749524880446⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154830792832,154830792896⟩ : DyadicInterval 40),(⟨-180264052096,-180264052032⟩ : DyadicInterval 40),(⟨749504352957,749504372287⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨73977576,84606428⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨73975040,73975104⟩ : DyadicInterval 40),(⟨-73980096,-73980032⟩ : DyadicInterval 40),(⟨762123381102,762123400431⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨84603136,84603200⟩ : DyadicInterval 40),(⟨-84609728,-84609664⟩ : DyadicInterval 40),(⟨762123380337,762123399666⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6528,-4928⟩ : DyadicInterval 40),(⟨762123386080,762123406144⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166211003847,166335306570⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154786061504,154786061568⟩ : DyadicInterval 40),(⟨-180203385536,-180203385472⟩ : DyadicInterval 40),(⟨749512198617,749512217947⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154894035904,154894035968⟩ : DyadicInterval 40),(⟨-180349835008,-180349834944⟩ : DyadicInterval 40),(⟨749493255669,749493274998⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25455799104,-25417323904⟩ : DyadicInterval 40),(⟨774832045568,774851302432⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154858290624,154957266880⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180435613120,-180301348608⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1608_ok : ecellOkT e1608 = true := by decide +kernel
theorem e1608_pos {a z : ℝ} (ha1 : ((309747/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1239837/8192000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1608 e1608_ok ha1 ha2 hz1 hz2 hz

-- box ['1239837/8192000', '620343/4096000', '999/1000', '7993/8000']  interval_lower 31675969/274877906944
noncomputable def e1609 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265919733006,0,true,154957266816,154957266880⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933103522546,0,false,-180435613120,-180435613056⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266033683858,0,true,155056234112,155056234176⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932989571694,0,false,-180569893952,-180569893888⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265753324900,0,true,154812723968,154812724032⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933269930652,0,false,-180239545536,-180239545472⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265887977059,0,true,154929684928,154929684992⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933135278493,0,false,-180398194496,-180398194432⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585657760,0,true,74027456,74027520⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437597792,0,false,-74032512,-74032448⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099596294102,0,true,84663040,84663104⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099426961450,0,false,-84669632,-84669568⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621256,0,false,-6528,-6464⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622792,0,false,-4992,-4928⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265836525245,0,true,154884994496,154884994560⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933186730307,0,false,-180337570624,-180337570560⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265960835349,0,true,154992965568,154992965632⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933062420203,0,false,-180484046656,-180484046592⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074313769015,0,false,-25491081024,-25491080960⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074351392251,0,false,-25452576064,-25452576000⟩
    { al := (1239837/8192000), au := (620343/4096000), zl := (999/1000), zu := (7993/8000),
      A := ⟨166408105230,166522056082⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154957266816,154957266880⟩ : DyadicInterval 40),(⟨-180435613120,-180435613056⟩ : DyadicInterval 40),(⟨749482154965,749482174294⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155056234112,155056234176⟩ : DyadicInterval 40),(⟨-180569893952,-180569893888⟩ : DyadicInterval 40),(⟨749464769237,749464788567⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154812723968,154812724032⟩ : DyadicInterval 40),(⟨-180239545536,-180239545472⟩ : DyadicInterval 40),(⟨749507522456,749507541786⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154929684928,154929684992⟩ : DyadicInterval 40),(⟨-180398194496,-180398194432⟩ : DyadicInterval 40),(⟨749486997870,749487017199⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨74029984,84666326⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74027456,74027520⟩ : DyadicInterval 40),(⟨-74032512,-74032448⟩ : DyadicInterval 40),(⟨762123381095,762123400424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨84663040,84663104⟩ : DyadicInterval 40),(⟨-84669632,-84669568⟩ : DyadicInterval 40),(⟨762123380328,762123399657⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6528,-4928⟩ : DyadicInterval 40),(⟨762123386080,762123406144⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166324897469,166449207573⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154884994496,154884994560⟩ : DyadicInterval 40),(⟨-180337570624,-180337570560⟩ : DyadicInterval 40),(⟨749494842542,749494861871⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154992965568,154992965632⟩ : DyadicInterval 40),(⟨-180484046656,-180484046592⟩ : DyadicInterval 40),(⟨749475885298,749475904628⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25491081024,-25452576000⟩ : DyadicInterval 40),(⟨774849671616,774868943392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154957266816,155056234176⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180569893952,-180435613056⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1609_ok : ecellOkT e1609 = true := by decide +kernel
theorem e1609_pos {a z : ℝ} (ha1 : ((1239837/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((620343/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1609 e1609_ok ha1 ha2 hz1 hz2 hz

-- box ['309747/2048000', '1239837/8192000', '7993/8000', '3997/4000']  interval_lower 125599225/1099511627776
noncomputable def e1610 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265805782155,0,true,154858290624,154858290688⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933217473397,0,false,-180301348672,-180301348608⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265919733007,0,true,154957266816,154957266880⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933103522545,0,false,-180435613120,-180435613056⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265660274769,0,true,154731891840,154731891904⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933362980783,0,false,-180129926016,-180129925952⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265794926929,0,true,154848861440,154848861504⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933228328623,0,false,-180288559168,-180288559104⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575037224,0,true,63407616,63407680⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099448218328,0,false,-63411328,-63411264⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585658590,0,true,74028288,74028352⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437596962,0,false,-74033344,-74033280⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622791,0,false,-4992,-4928⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624120,0,false,-3712,-3648⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265733024589,0,true,154795089664,154795089728⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933290230963,0,false,-180215629440,-180215629376⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265857334713,0,true,154903069568,154903069632⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933165920839,0,false,-180362089280,-180362089216⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074345096092,0,false,-25459019648,-25459019584⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074382695930,0,false,-25420539712,-25420539648⟩
    { al := (309747/2048000), au := (1239837/8192000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨166294154379,166408105231⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154858290624,154858290688⟩ : DyadicInterval 40),(⟨-180301348672,-180301348608⟩ : DyadicInterval 40),(⟨749499528593,749499547922⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154957266816,154957266880⟩ : DyadicInterval 40),(⟨-180435613120,-180435613056⟩ : DyadicInterval 40),(⟨749482154965,749482174294⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154731891840,154731891904⟩ : DyadicInterval 40),(⟨-180129926016,-180129925952⟩ : DyadicInterval 40),(⟨749521695962,749521715292⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154848861440,154848861504⟩ : DyadicInterval 40),(⟨-180288559168,-180288559104⟩ : DyadicInterval 40),(⟨749501183018,749501202347⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨63409448,74030814⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63407616,63407680⟩ : DyadicInterval 40),(⟨-63411328,-63411264⟩ : DyadicInterval 40),(⟨762123381751,762123401080⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74028288,74028352⟩ : DyadicInterval 40),(⟨-74033344,-74033280⟩ : DyadicInterval 40),(⟨762123381095,762123400424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4992,-3648⟩ : DyadicInterval 40),(⟨762123385440,762123405376⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166221396813,166345706937⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154795089664,154795089728⟩ : DyadicInterval 40),(⟨-180215629440,-180215629376⟩ : DyadicInterval 40),(⟨749510615342,749510634672⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154903069568,154903069632⟩ : DyadicInterval 40),(⟨-180362089280,-180362089216⟩ : DyadicInterval 40),(⟨749491670092,749491689421⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25459019648,-25420539648⟩ : DyadicInterval 40),(⟨774833653440,774852912704⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154858290624,154957266880⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180435613120,-180301348608⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1610_ok : ecellOkT e1610 = true := by decide +kernel
theorem e1610_pos {a z : ℝ} (ha1 : ((309747/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1239837/8192000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1610 e1610_ok ha1 ha2 hz1 hz2 hz

-- box ['1239837/8192000', '620343/4096000', '7993/8000', '3997/4000']  interval_lower 126564305/1099511627776
noncomputable def e1611 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265919733006,0,true,154957266816,154957266880⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933103522546,0,false,-180435613120,-180435613056⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266033683858,0,true,155056234112,155056234176⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932989571694,0,false,-180569893952,-180569893888⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265774125913,0,true,154830792832,154830792896⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933249129639,0,false,-180264052096,-180264052032⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265908792317,0,true,154947764288,154947764352⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933114463235,0,false,-180422721344,-180422721280⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575082145,0,true,63452480,63452544⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099448173407,0,false,-63456256,-63456192⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585711000,0,true,74080704,74080768⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437544552,0,false,-74085760,-74085696⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622784,0,false,-5056,-4992⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624114,0,false,-3712,-3648⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265846925841,0,true,154894028480,154894028544⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933176329711,0,false,-180349825024,-180349824960⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265971242838,0,true,155002004672,155002004736⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933052012714,0,false,-180496310784,-180496310720⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074310617848,0,false,-25494306112,-25494306048⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074348245523,0,false,-25455796480,-25455796416⟩
    { al := (1239837/8192000), au := (620343/4096000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨166408105230,166522056082⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154957266816,154957266880⟩ : DyadicInterval 40),(⟨-180435613120,-180435613056⟩ : DyadicInterval 40),(⟨749482154965,749482174294⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155056234112,155056234176⟩ : DyadicInterval 40),(⟨-180569893952,-180569893888⟩ : DyadicInterval 40),(⟨749464769237,749464788567⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154830792832,154830792896⟩ : DyadicInterval 40),(⟨-180264052096,-180264052032⟩ : DyadicInterval 40),(⟨749504352958,749504372287⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154947764288,154947764352⟩ : DyadicInterval 40),(⟨-180422721344,-180422721280⟩ : DyadicInterval 40),(⟨749483823551,749483842881⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨63454369,74083224⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63452480,63452544⟩ : DyadicInterval 40),(⟨-63456256,-63456192⟩ : DyadicInterval 40),(⟨762123381777,762123401107⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74080704,74080768⟩ : DyadicInterval 40),(⟨-74085760,-74085696⟩ : DyadicInterval 40),(⟨762123381088,762123400417⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5056,-3648⟩ : DyadicInterval 40),(⟨762123385440,762123405408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166335298065,166459615062⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154894028480,154894028544⟩ : DyadicInterval 40),(⟨-180349825024,-180349824960⟩ : DyadicInterval 40),(⟨749493257002,749493276331⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155002004672,155002004736⟩ : DyadicInterval 40),(⟨-180496310784,-180496310720⟩ : DyadicInterval 40),(⟨749474297480,749474316809⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25494306112,-25455796416⟩ : DyadicInterval 40),(⟨774851281824,774870555936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154957266816,155056234176⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180569893952,-180435613056⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1611_ok : ecellOkT e1611 = true := by decide +kernel
theorem e1611_pos {a z : ℝ} (ha1 : ((1239837/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((620343/4096000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1611 e1611_ok ha1 ha2 hz1 hz2 hz

-- box ['620343/4096000', '248307/1638400', '999/1000', '7993/8000']  interval_lower 127671395/1099511627776
noncomputable def e1612 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266033683857,0,true,155056234112,155056234176⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932989571695,0,false,-180569893952,-180569893888⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266147634709,0,true,155155192512,155155192576⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932875620843,0,false,-180704191232,-180704191168⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265867161800,0,true,154911605248,154911605312⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933156093752,0,false,-180373668224,-180373668160⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266001828203,0,true,155028568064,155028568128⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933021427349,0,false,-180532353280,-180532353216⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585710169,0,true,74079872,74079936⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437545383,0,false,-74084928,-74084864⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099596354004,0,true,84722944,84723008⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099426901548,0,false,-84729536,-84729472⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621247,0,false,-6592,-6528⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622785,0,false,-4992,-4928⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265950419114,0,true,154983918848,154983918912⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933072836438,0,false,-180471772352,-180471772288⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266074736344,0,true,155091886336,155091886400⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932948519208,0,false,-180618274688,-180618274624⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074279271487,0,false,-25526388288,-25526388224⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074316922634,0,false,-25487853440,-25487853376⟩
    { al := (620343/4096000), au := (248307/1638400), zl := (999/1000), zu := (7993/8000),
      A := ⟨166522056081,166636006933⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155056234112,155056234176⟩ : DyadicInterval 40),(⟨-180569893952,-180569893888⟩ : DyadicInterval 40),(⟨749464769238,749464788567⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155155192512,155155192576⟩ : DyadicInterval 40),(⟨-180704191232,-180704191168⟩ : DyadicInterval 40),(⟨749447371437,749447390766⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154911605248,154911605312⟩ : DyadicInterval 40),(⟨-180373668224,-180373668160⟩ : DyadicInterval 40),(⟨749490171811,749490191140⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155028568064,155028568128⟩ : DyadicInterval 40),(⟨-180532353280,-180532353216⟩ : DyadicInterval 40),(⟨749469630762,749469650092⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨74082393,84726228⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74079872,74079936⟩ : DyadicInterval 40),(⟨-74084928,-74084864⟩ : DyadicInterval 40),(⟨762123381088,762123400417⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨84722944,84723008⟩ : DyadicInterval 40),(⟨-84729536,-84729472⟩ : DyadicInterval 40),(⟨762123380318,762123399648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6592,-4928⟩ : DyadicInterval 40),(⟨762123386080,762123406176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166438791338,166563108568⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154983918848,154983918912⟩ : DyadicInterval 40),(⟨-180471772352,-180471772288⟩ : DyadicInterval 40),(⟨749477474316,749477493645⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155091886336,155091886400⟩ : DyadicInterval 40),(⟨-180618274688,-180618274624⟩ : DyadicInterval 40),(⟨749458502850,749458522180⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25526388288,-25487853376⟩ : DyadicInterval 40),(⟨774867310304,774886597024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155056234112,155155192576⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180704191232,-180569893888⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1612_ok : ecellOkT e1612 = true := by decide +kernel
theorem e1612_pos {a z : ℝ} (ha1 : ((620343/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((248307/1638400 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1612 e1612_ok ha1 ha2 hz1 hz2 hz

-- box ['248307/1638400', '77649/512000', '999/1000', '7993/8000']  interval_lower 32160433/274877906944
noncomputable def e1613 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266147634708,0,true,155155192512,155155192576⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932875620844,0,false,-180704191232,-180704191168⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266261585560,0,true,155254141952,155254142016⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932761669992,0,false,-180838504896,-180838504832⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265980998701,0,true,155010477696,155010477760⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933042256851,0,false,-180507807232,-180507807168⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266115679347,0,true,155127442368,155127442432⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932907576205,0,false,-180666528448,-180666528384⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585762584,0,true,74132288,74132352⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437492968,0,false,-74137344,-74137280⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099596413909,0,true,84782848,84782912⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099426841643,0,false,-84789440,-84789376⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621237,0,false,-6592,-6528⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622778,0,false,-5056,-4992⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266064312990,0,true,155082834240,155082834304⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932958942562,0,false,-180605990464,-180605990400⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266188637341,0,true,155190798208,155190798272⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932834618211,0,false,-180752519040,-180752518976⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074244750359,0,false,-25561720768,-25561720704⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074282429420,0,false,-25523156160,-25523156096⟩
    { al := (248307/1638400), au := (77649/512000), zl := (999/1000), zu := (7993/8000),
      A := ⟨166636006932,166749957784⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155155192512,155155192576⟩ : DyadicInterval 40),(⟨-180704191232,-180704191168⟩ : DyadicInterval 40),(⟨749447371437,749447390766⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155254141952,155254142016⟩ : DyadicInterval 40),(⟨-180838504896,-180838504832⟩ : DyadicInterval 40),(⟨749429961571,749429980900⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155010477696,155010477760⟩ : DyadicInterval 40),(⟨-180507807232,-180507807168⟩ : DyadicInterval 40),(⟨749472809050,749472828380⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155127442368,155127442432⟩ : DyadicInterval 40),(⟨-180666528448,-180666528384⟩ : DyadicInterval 40),(⟨749452251560,749452270889⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨74134808,84786133⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74132288,74132352⟩ : DyadicInterval 40),(⟨-74137344,-74137280⟩ : DyadicInterval 40),(⟨762123381081,762123400410⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨84782848,84782912⟩ : DyadicInterval 40),(⟨-84789440,-84789376⟩ : DyadicInterval 40),(⟨762123380309,762123399639⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6592,-4992⟩ : DyadicInterval 40),(⟨762123386112,762123406176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166552685214,166677009565⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155082834240,155082834304⟩ : DyadicInterval 40),(⟨-180605990464,-180605990400⟩ : DyadicInterval 40),(⟨749460094050,749460113379⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155190798208,155190798272⟩ : DyadicInterval 40),(⟨-180752519040,-180752518976⟩ : DyadicInterval 40),(⟨749441108295,749441127625⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25561720768,-25523156096⟩ : DyadicInterval 40),(⟨774884961664,774904263264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155155192512,155254142016⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180838504896,-180704191168⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1613_ok : ecellOkT e1613 = true := by decide +kernel
theorem e1613_pos {a z : ℝ} (ha1 : ((248307/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((77649/512000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1613 e1613_ok ha1 ha2 hz1 hz2 hz

-- box ['620343/4096000', '248307/1638400', '7993/8000', '3997/4000']  interval_lower 127531307/1099511627776
noncomputable def e1614 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266033683857,0,true,155056234112,155056234176⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932989571695,0,false,-180569893952,-180569893888⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266147634709,0,true,155155192512,155155192576⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932875620843,0,false,-180704191232,-180704191168⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265887977057,0,true,154929684928,154929684992⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933135278495,0,false,-180398194496,-180398194432⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266022657704,0,true,155046658176,155046658240⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933000597848,0,false,-180556899904,-180556899840⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575127068,0,true,63497408,63497472⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099448128484,0,false,-63501184,-63501120⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585763415,0,true,74133120,74133184⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437492137,0,false,-74138176,-74138112⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622777,0,false,-5056,-4992⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624109,0,false,-3712,-3648⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265960826585,0,true,154992957952,154992958016⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933062428967,0,false,-180484036352,-180484036288⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266085150955,0,true,155100930816,155100930880⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932938104597,0,false,-180630548736,-180630548672⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074276116005,0,false,-25529617856,-25529617792⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074313771670,0,false,-25491078336,-25491078272⟩
    { al := (620343/4096000), au := (248307/1638400), zl := (7993/8000), zu := (3997/4000),
      A := ⟨166522056081,166636006933⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155056234112,155056234176⟩ : DyadicInterval 40),(⟨-180569893952,-180569893888⟩ : DyadicInterval 40),(⟨749464769238,749464788567⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155155192512,155155192576⟩ : DyadicInterval 40),(⟨-180704191232,-180704191168⟩ : DyadicInterval 40),(⟨749447371437,749447390766⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154929684928,154929684992⟩ : DyadicInterval 40),(⟨-180398194496,-180398194432⟩ : DyadicInterval 40),(⟨749486997870,749487017200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155046658176,155046658240⟩ : DyadicInterval 40),(⟨-180556899904,-180556899840⟩ : DyadicInterval 40),(⟨749466452059,749466471388⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨63499292,74135639⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63497408,63497472⟩ : DyadicInterval 40),(⟨-63501184,-63501120⟩ : DyadicInterval 40),(⟨762123381772,762123401101⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74133120,74133184⟩ : DyadicInterval 40),(⟨-74138176,-74138112⟩ : DyadicInterval 40),(⟨762123381081,762123400410⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5056,-3648⟩ : DyadicInterval 40),(⟨762123385440,762123405408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166449198809,166573523179⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154992957952,154992958016⟩ : DyadicInterval 40),(⟨-180484036352,-180484036288⟩ : DyadicInterval 40),(⟨749475886648,749475905977⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155100930816,155100930880⟩ : DyadicInterval 40),(⟨-180630548736,-180630548672⟩ : DyadicInterval 40),(⟨749456912851,749456932180⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25529617856,-25491078272⟩ : DyadicInterval 40),(⟨774868922752,774888211808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155056234112,155155192576⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180704191232,-180569893888⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1614_ok : ecellOkT e1614 = true := by decide +kernel
theorem e1614_pos {a z : ℝ} (ha1 : ((620343/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((248307/1638400 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1614 e1614_ok ha1 ha2 hz1 hz2 hz

-- box ['248307/1638400', '77649/512000', '7993/8000', '3997/4000']  interval_lower 128501151/1099511627776
noncomputable def e1615 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1266147634708,0,true,155155192512,155155192576⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨932875620844,0,false,-180704191232,-180704191168⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266261585560,0,true,155254141952,155254142016⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932761669992,0,false,-180838504896,-180838504832⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1266001828201,0,true,155028568064,155028568128⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933021427351,0,false,-180532353280,-180532353216⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1266136523092,0,true,155145543232,155145543296⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨932886732460,0,false,-180691094848,-180691094784⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575171994,0,true,63542336,63542400⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099448083558,0,false,-63546112,-63546048⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099585815833,0,true,74185536,74185600⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099437439719,0,false,-74190592,-74190528⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622770,0,false,-5056,-4992⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624104,0,false,-3712,-3648⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1266074727577,0,true,155091878720,155091878784⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨932948527975,0,false,-180618264320,-180618264256⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1266199059074,0,true,155199848064,155199848128⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨932824196478,0,false,-180764803008,-180764802944⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074241590560,0,false,-25564954944,-25564954880⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074279274144,0,false,-25526385536,-25526385472⟩
    { al := (248307/1638400), au := (77649/512000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨166636006932,166749957784⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155155192512,155155192576⟩ : DyadicInterval 40),(⟨-180704191232,-180704191168⟩ : DyadicInterval 40),(⟨749447371437,749447390766⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155254141952,155254142016⟩ : DyadicInterval 40),(⟨-180838504896,-180838504832⟩ : DyadicInterval 40),(⟨749429961571,749429980900⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155028568064,155028568128⟩ : DyadicInterval 40),(⟨-180532353280,-180532353216⟩ : DyadicInterval 40),(⟨749469630763,749469650092⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155145543232,155145543296⟩ : DyadicInterval 40),(⟨-180691094848,-180691094784⟩ : DyadicInterval 40),(⟨749449068465,749449087794⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨63544218,74188057⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63542336,63542400⟩ : DyadicInterval 40),(⟨-63546112,-63546048⟩ : DyadicInterval 40),(⟨762123381767,762123401096⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨74185536,74185600⟩ : DyadicInterval 40),(⟨-74190592,-74190528⟩ : DyadicInterval 40),(⟨762123381074,762123400403⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5056,-3648⟩ : DyadicInterval 40),(⟨762123385440,762123405408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166563099801,166687431298⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155091878720,155091878784⟩ : DyadicInterval 40),(⟨-180618264320,-180618264256⟩ : DyadicInterval 40),(⟨749458504175,749458523504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155199848064,155199848128⟩ : DyadicInterval 40),(⟨-180764803008,-180764802944⟩ : DyadicInterval 40),(⟨749439516112,749439535441⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25564954944,-25526385472⟩ : DyadicInterval 40),(⟨774886576352,774905880352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨155155192512,155254142016⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180838504896,-180704191168⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1615_ok : ecellOkT e1615 = true := by decide +kernel
theorem e1615_pos {a z : ℝ} (ha1 : ((248307/1638400 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((77649/512000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1615 e1615_ok ha1 ha2 hz1 hz2 hz

-- box ['309747/2048000', '1239837/8192000', '3997/4000', '1599/1600']  interval_lower 62729949/549755813888
noncomputable def e1616 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265805782155,0,true,154858290624,154858290688⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933217473397,0,false,-180301348672,-180301348608⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265919733007,0,true,154957266816,154957266880⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933103522545,0,false,-180435613120,-180435613056⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265681061539,0,true,154749949696,154749949760⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933342194013,0,false,-180154413376,-180154413312⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265815727942,0,true,154866929728,154866929792⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933207527610,0,false,-180313066816,-180313066752⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564469052,0,true,52840000,52840064⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458786500,0,false,-52842560,-52842496⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575082930,0,true,63453312,63453376⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099448172622,0,false,-63457024,-63456960⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624113,0,false,-3712,-3648⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625237,0,false,-2560,-2496⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265743418088,0,true,154804118208,154804118272⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933279837464,0,false,-180227874112,-180227874048⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265867735099,0,true,154912103232,154912103296⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933155520453,0,false,-180374343680,-180374343616⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074341949034,0,false,-25462240448,-25462240384⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074379553306,0,false,-25423755840,-25423755776⟩
    { al := (309747/2048000), au := (1239837/8192000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨166294154379,166408105231⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154858290624,154858290688⟩ : DyadicInterval 40),(⟨-180301348672,-180301348608⟩ : DyadicInterval 40),(⟨749499528593,749499547922⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154957266816,154957266880⟩ : DyadicInterval 40),(⟨-180435613120,-180435613056⟩ : DyadicInterval 40),(⟨749482154965,749482174294⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154749949696,154749949760⟩ : DyadicInterval 40),(⟨-180154413376,-180154413312⟩ : DyadicInterval 40),(⟨749518530423,749518549752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154866929728,154866929792⟩ : DyadicInterval 40),(⟨-180313066816,-180313066752⟩ : DyadicInterval 40),(⟨749498012701,749498032031⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨52841276,63455154⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52840000,52840064⟩ : DyadicInterval 40),(⟨-52842560,-52842496⟩ : DyadicInterval 40),(⟨762123382292,762123401621⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63453312,63453376⟩ : DyadicInterval 40),(⟨-63457024,-63456960⟩ : DyadicInterval 40),(⟨762123381745,762123401074⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3712,-2496⟩ : DyadicInterval 40),(⟨762123384864,762123404736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166231790312,166356107323⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154804118208,154804118272⟩ : DyadicInterval 40),(⟨-180227874112,-180227874048⟩ : DyadicInterval 40),(⟨749509031890,749509051220⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154912103232,154912103296⟩ : DyadicInterval 40),(⟨-180374343680,-180374343616⟩ : DyadicInterval 40),(⟨749490084365,749490103695⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25462240448,-25423755776⟩ : DyadicInterval 40),(⟨774835261504,774854523104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154858290624,154957266880⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180435613120,-180301348608⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1616_ok : ecellOkT e1616 = true := by decide +kernel
theorem e1616_pos {a z : ℝ} (ha1 : ((309747/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1239837/8192000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1616 e1616_ok ha1 ha2 hz1 hz2 hz

-- box ['1239837/8192000', '620343/4096000', '3997/4000', '1599/1600']  interval_lower 126423973/1099511627776
noncomputable def e1617 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265919733006,0,true,154957266816,154957266880⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933103522546,0,false,-180435613120,-180435613056⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266033683858,0,true,155056234112,155056234176⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932989571694,0,false,-180569893952,-180569893888⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265794926927,0,true,154848861440,154848861504⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933228328625,0,false,-180288559168,-180288559104⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265929607574,0,true,154965843328,154965843392⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933093647978,0,false,-180447248768,-180447248704⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564506485,0,true,52877376,52877440⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458749067,0,false,-52880000,-52879936⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099575127854,0,true,63498240,63498304⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099448127698,0,false,-63501952,-63501888⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624108,0,false,-3712,-3648⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625233,0,false,-2560,-2496⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265857325952,0,true,154903061952,154903062016⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933165929600,0,false,-180362078976,-180362078912⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265981650345,0,true,155011043648,155011043712⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933041605207,0,false,-180508575104,-180508575040⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074307466479,0,false,-25497531456,-25497531392⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074345098744,0,false,-25459016960,-25459016896⟩
    { al := (1239837/8192000), au := (620343/4096000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨166408105230,166522056082⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154957266816,154957266880⟩ : DyadicInterval 40),(⟨-180435613120,-180435613056⟩ : DyadicInterval 40),(⟨749482154965,749482174294⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155056234112,155056234176⟩ : DyadicInterval 40),(⟨-180569893952,-180569893888⟩ : DyadicInterval 40),(⟨749464769237,749464788567⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154848861440,154848861504⟩ : DyadicInterval 40),(⟨-180288559168,-180288559104⟩ : DyadicInterval 40),(⟨749501183018,749501202348⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154965843328,154965843392⟩ : DyadicInterval 40),(⟨-180447248768,-180447248704⟩ : DyadicInterval 40),(⟨749480648855,749480668185⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨52878709,63500078⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52877376,52877440⟩ : DyadicInterval 40),(⟨-52880000,-52879936⟩ : DyadicInterval 40),(⟨762123382320,762123401649⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨63498240,63498304⟩ : DyadicInterval 40),(⟨-63501952,-63501888⟩ : DyadicInterval 40),(⟨762123381740,762123401069⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3712,-2496⟩ : DyadicInterval 40),(⟨762123384864,762123404736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166345698176,166470022569⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154903061952,154903062016⟩ : DyadicInterval 40),(⟨-180362078976,-180362078912⟩ : DyadicInterval 40),(⟨749491671439,749491690768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155011043648,155011043712⟩ : DyadicInterval 40),(⟨-180508575104,-180508575040⟩ : DyadicInterval 40),(⟨749472709612,749472728942⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25497531456,-25459016896⟩ : DyadicInterval 40),(⟨774852892064,774872168608⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154957266816,155056234176⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180569893952,-180435613056⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1617_ok : ecellOkT e1617 = true := by decide +kernel
theorem e1617_pos {a z : ℝ} (ha1 : ((1239837/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((620343/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1617 e1617_ok ha1 ha2 hz1 hz2 hz

-- box ['309747/2048000', '1239837/8192000', '1599/1600', '1999/2000']  interval_lower 31330021/274877906944
noncomputable def e1618 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265805782155,0,true,154858290624,154858290688⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933217473397,0,false,-180301348672,-180301348608⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1265919733007,0,true,154957266816,154957266880⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨933103522545,0,false,-180435613120,-180435613056⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265701848308,0,true,154768007296,154768007360⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933321407244,0,false,-180178901184,-180178901120⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265836528955,0,true,154884997760,154884997824⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933186726597,0,false,-180337574976,-180337574912⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099553900835,0,true,42272192,42272256⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099469354717,0,false,-42273920,-42273856⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564507225,0,true,52878144,52878208⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458748327,0,false,-52880768,-52880704⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625232,0,false,-2560,-2496⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626151,0,false,-1664,-1600⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265753811102,0,true,154813146304,154813146368⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933269444450,0,false,-180240118400,-180240118336⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265878135510,0,true,154921136832,154921136896⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933145120042,0,false,-180386598272,-180386598208⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074338801771,0,false,-25465461440,-25465461376⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074376410632,0,false,-25426972032,-25426971968⟩
    { al := (309747/2048000), au := (1239837/8192000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨166294154379,166408105231⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154858290624,154858290688⟩ : DyadicInterval 40),(⟨-180301348672,-180301348608⟩ : DyadicInterval 40),(⟨749499528593,749499547922⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154957266816,154957266880⟩ : DyadicInterval 40),(⟨-180435613120,-180435613056⟩ : DyadicInterval 40),(⟨749482154965,749482174294⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154768007296,154768007360⟩ : DyadicInterval 40),(⟨-180178901184,-180178901120⟩ : DyadicInterval 40),(⟨749515364416,749515383745⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154884997760,154884997824⟩ : DyadicInterval 40),(⟨-180337574976,-180337574912⟩ : DyadicInterval 40),(⟨749494841944,749494861274⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨42273059,52879449⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42272192,42272256⟩ : DyadicInterval 40),(⟨-42273920,-42273856⟩ : DyadicInterval 40),(⟨762123382790,762123402119⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52878144,52878208⟩ : DyadicInterval 40),(⟨-52880768,-52880704⟩ : DyadicInterval 40),(⟨762123382320,762123401649⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2560,-1600⟩ : DyadicInterval 40),(⟨762123384416,762123404160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166242183326,166366507734⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154813146304,154813146368⟩ : DyadicInterval 40),(⟨-180240118400,-180240118336⟩ : DyadicInterval 40),(⟨749507448406,749507467735⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154921136832,154921136896⟩ : DyadicInterval 40),(⟨-180386598272,-180386598208⟩ : DyadicInterval 40),(⟨749488498552,749488517881⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25465461440,-25426971968⟩ : DyadicInterval 40),(⟨774836869600,774856133600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154858290624,154957266880⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180435613120,-180301348608⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1618_ok : ecellOkT e1618 = true := by decide +kernel
theorem e1618_pos {a z : ℝ} (ha1 : ((309747/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1239837/8192000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1618 e1618_ok ha1 ha2 hz1 hz2 hz

-- box ['1239837/8192000', '620343/4096000', '1599/1600', '1999/2000']  interval_lower 126284595/1099511627776
noncomputable def e1619 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1265919733006,0,true,154957266816,154957266880⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨933103522546,0,false,-180435613120,-180435613056⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1266033683858,0,true,155056234112,155056234176⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨932989571694,0,false,-180569893952,-180569893888⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1265815727940,0,true,154866929728,154866929792⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨933207527612,0,false,-180313066816,-180313066752⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1265950422831,0,true,154983922048,154983922112⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨933072832721,0,false,-180471776704,-180471776640⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099553930782,0,true,42302144,42302208⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099469324770,0,false,-42303872,-42303808⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099564544663,0,true,52915584,52915648⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099458710889,0,false,-52918208,-52918144⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625229,0,false,-2560,-2496⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626149,0,false,-1664,-1600⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1265867726593,0,true,154912095808,154912095872⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨933155528959,0,false,-180374333696,-180374333632⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1265992057875,0,true,155020082624,155020082688⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨933031197677,0,false,-180520839616,-180520839552⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1074304314905,0,false,-25500756928,-25500756864⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1074341951609,0,false,-25462237824,-25462237760⟩
    { al := (1239837/8192000), au := (620343/4096000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨166408105230,166522056082⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154957266816,154957266880⟩ : DyadicInterval 40),(⟨-180435613120,-180435613056⟩ : DyadicInterval 40),(⟨749482154965,749482174294⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155056234112,155056234176⟩ : DyadicInterval 40),(⟨-180569893952,-180569893888⟩ : DyadicInterval 40),(⟨749464769237,749464788567⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154866929728,154866929792⟩ : DyadicInterval 40),(⟨-180313066816,-180313066752⟩ : DyadicInterval 40),(⟨749498012702,749498032031⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154983922048,154983922112⟩ : DyadicInterval 40),(⟨-180471776704,-180471776640⟩ : DyadicInterval 40),(⟨749477473753,749477493083⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨42303006,52916887⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨42302144,42302208⟩ : DyadicInterval 40),(⟨-42303872,-42303808⟩ : DyadicInterval 40),(⟨762123382788,762123402117⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨52915584,52915648⟩ : DyadicInterval 40),(⟨-52918208,-52918144⟩ : DyadicInterval 40),(⟨762123382317,762123401646⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2560,-1600⟩ : DyadicInterval 40),(⟨762123384416,762123404160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨166356098817,166480430099⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨154912095808,154912095872⟩ : DyadicInterval 40),(⟨-180374333696,-180374333632⟩ : DyadicInterval 40),(⟨749490085699,749490105028⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨155020082624,155020082688⟩ : DyadicInterval 40),(⟨-180520839616,-180520839552⟩ : DyadicInterval 40),(⟨749471121621,749471140950⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-25500756928,-25462237760⟩ : DyadicInterval 40),(⟨774854502496,774873781344⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨154957266816,155056234176⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-180569893952,-180435613056⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1619_ok : ecellOkT e1619 = true := by decide +kernel
theorem e1619_pos {a z : ℝ} (ha1 : ((1239837/8192000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((620343/4096000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1619 e1619_ok ha1 ha2 hz1 hz2 hz

end CKLaneC2R.EpCells.B026

end


