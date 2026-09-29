-- Prove2me | Definitions.Def_CK_CKLaneC2R_EpCells_B012
-- name    : CK_CKLaneC2R_EpCells_B012
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T14:16:26.81704+00:00
-- url     : https://prove2.me/theorems/8f4463df-b77f-4a1f-affc-8d6ee125218a
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EpCells.B012` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EpCells.B012` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EpCells.B012` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EpCells.B012 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EpCells/B012.lean)

import Definitions.Def_CK_CKLaneC2R_EndpointCheckT

-- ===== source module CKLaneC2R.EpCells.B012 =====
section

namespace CKLaneC2R.EpCells.B012

open GeneralCK GeneralCK.Certificates CKLaneC2R CKLaneC2R.Endpoint

-- box ['727317/4096000', '364083/2048000', '3997/4000', '1999/2000']  interval_lower 90589895/1099511627776
noncomputable def e720 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1294749298327,0,true,179716250752,179716250816⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨904273957225,0,false,-214942451648,-214942451584⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1294977200030,0,true,179909769728,179909769792⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨904046055522,0,false,-215219593536,-215219593472⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1294602870074,0,true,179591895680,179591895744⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨904420385478,0,false,-214764423168,-214764423104⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1294879467245,0,true,179826785728,179826785792⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨904143788307,0,false,-215100736128,-215100736064⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099561578213,0,true,49949248,49949312⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099461677339,0,false,-49951616,-49951552⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586646100,0,true,75015744,75015808⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436609452,0,false,-75020928,-75020864⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622657,0,false,-5120,-5056⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625507,0,false,-2304,-2240⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1294676079781,0,true,179654071232,179654071296⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨904347175771,0,false,-214853428416,-214853428352⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1294928342416,0,true,179868285952,179868286016⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨904094913136,0,false,-215160173888,-215160173824⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1064780123901,0,false,-35291887936,-35291887872⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1064869735536,0,false,-35199357184,-35199357120⟩
    { al := (727317/4096000), au := (364083/2048000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨195237670551,195465572254⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179716250752,179716250816⟩ : DyadicInterval 40),(⟨-214942451648,-214942451584⟩ : DyadicInterval 40),(⟨744697179378,744697198708⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179909769728,179909769792⟩ : DyadicInterval 40),(⟨-215219593536,-215219593472⟩ : DyadicInterval 40),(⟨744656253471,744656272801⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179591895680,179591895744⟩ : DyadicInterval 40),(⟨-214764423168,-214764423104⟩ : DyadicInterval 40),(⟨744723448783,744723468112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179826785728,179826785792⟩ : DyadicInterval 40),(⟨-215100736128,-215100736064⟩ : DyadicInterval 40),(⟨744673809986,744673829315⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨49950437,75018324⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨49949248,49949312⟩ : DyadicInterval 40),(⟨-49951616,-49951552⟩ : DyadicInterval 40),(⟨762123382466,762123401795⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75015744,75015808⟩ : DyadicInterval 40),(⟨-75020928,-75020864⟩ : DyadicInterval 40),(⟨762123381025,762123400354⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5120,-2240⟩ : DyadicInterval 40),(⟨762123384736,762123405440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨195164452005,195416714640⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179654071232,179654071296⟩ : DyadicInterval 40),(⟨-214853428416,-214853428352⟩ : DyadicInterval 40),(⟨744710317377,744710336707⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179868285952,179868286016⟩ : DyadicInterval 40),(⟨-215160173888,-215160173824⟩ : DyadicInterval 40),(⟨744665031275,744665050604⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-35291887936,-35199357120⟩ : DyadicInterval 40),(⟨779723062176,779769346848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨179716250752,179909769792⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-215219593536,-214942451584⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e720_ok : ecellOkT e720 = true := by decide +kernel
theorem e720_pos {a z : ℝ} (ha1 : ((727317/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((364083/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e720 e720_ok ha1 ha2 hz1 hz2 hz

-- box ['364083/2048000', '145803/819200', '999/1000', '3997/4000']  interval_lower 94121123/1099511627776
noncomputable def e721 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1294977200029,0,true,179909769728,179909769792⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨904046055523,0,false,-215219593536,-215219593472⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1295205101732,0,true,180103254592,180103254656⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨903818153820,0,false,-215496805248,-215496805184⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1294781734456,0,true,179743795456,179743795520⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨904241521096,0,false,-214981891648,-214981891584⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1295058331627,0,true,179978653056,179978653120⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨903964923925,0,false,-215318271168,-215318271104⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586644700,0,true,75014336,75014400⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436610852,0,false,-75019520,-75019456⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099611773661,0,true,100141312,100141376⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099411481891,0,false,-100150464,-100150400⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511618654,0,false,-9152,-9088⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622658,0,false,-5120,-5056⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1294879463312,0,true,179826782336,179826782400⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨904143792240,0,false,-215100731392,-215100731328⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1295131725809,0,true,180040963328,180040963392⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨903891529743,0,false,-215407545664,-215407545600⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1064707791429,0,false,-35366582336,-35366582272⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1064797496341,0,false,-35273948992,-35273948928⟩
    { al := (364083/2048000), au := (145803/819200), zl := (999/1000), zu := (3997/4000),
      A := ⟨195465572253,195693473956⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179909769728,179909769792⟩ : DyadicInterval 40),(⟨-215219593536,-215219593472⟩ : DyadicInterval 40),(⟨744656253472,744656272801⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180103254592,180103254656⟩ : DyadicInterval 40),(⟨-215496805248,-215496805184⟩ : DyadicInterval 40),(⟨744615278798,744615298128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179743795456,179743795520⟩ : DyadicInterval 40),(⟨-214981891648,-214981891584⟩ : DyadicInterval 40),(⟨744691357569,744691376898⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179978653056,179978653120⟩ : DyadicInterval 40),(⟨-215318271168,-215318271104⟩ : DyadicInterval 40),(⟨744641672322,744641691652⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨75016924,100145885⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75014336,75014400⟩ : DyadicInterval 40),(⟨-75019520,-75019456⟩ : DyadicInterval 40),(⟨762123381025,762123400354⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨100141312,100141376⟩ : DyadicInterval 40),(⟨-100150464,-100150400⟩ : DyadicInterval 40),(⟨762123379006,762123398335⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-9152,-5056⟩ : DyadicInterval 40),(⟨762123386144,762123407456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨195367835536,195620098033⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179826782336,179826782400⟩ : DyadicInterval 40),(⟨-215100731392,-215100731328⟩ : DyadicInterval 40),(⟨744673810742,744673830072⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180040963328,180040963392⟩ : DyadicInterval 40),(⟨-215407545664,-215407545600⟩ : DyadicInterval 40),(⟨744628476444,744628495773⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-35366582336,-35273948928⟩ : DyadicInterval 40),(⟨779760358080,779806694048⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨179909769728,180103254656⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-215496805248,-215219593472⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e721_ok : ecellOkT e721 = true := by decide +kernel
theorem e721_pos {a z : ℝ} (ha1 : ((364083/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((145803/819200 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e721 e721_ok ha1 ha2 hz1 hz2 hz

-- box ['145803/819200', '91233/512000', '999/1000', '3997/4000']  interval_lower 12136889/137438953472
noncomputable def e722 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1295205101731,0,true,180103254592,180103254656⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨903818153821,0,false,-215496805248,-215496805184⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1295433003434,0,true,180296705472,180296705536⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨903590252118,0,false,-215774086848,-215774086784⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1295009408257,0,true,179937116032,179937116096⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨904013847295,0,false,-215258766208,-215258766144⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1295286062403,0,true,180171980736,180171980800⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨903737193149,0,false,-215595299776,-215595299712⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586736294,0,true,75105920,75105984⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436519258,0,false,-75111104,-75111040⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099611895808,0,true,100263424,100263488⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099411359744,0,false,-100272640,-100272576⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511618632,0,false,-9152,-9088⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622646,0,false,-5184,-5120⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1295107251061,0,true,180020185088,180020185152⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨903916004491,0,false,-215377774528,-215377774464⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1295359542056,0,true,180234352576,180234352640⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨903663713496,0,false,-215684700800,-215684700736⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1064626680169,0,false,-35450348160,-35450348096⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1064716499756,0,false,-35357589376,-35357589312⟩
    { al := (145803/819200), au := (91233/512000), zl := (999/1000), zu := (3997/4000),
      A := ⟨195693473955,195921375658⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180103254592,180103254656⟩ : DyadicInterval 40),(⟨-215496805248,-215496805184⟩ : DyadicInterval 40),(⟨744615278798,744615298128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180296705472,180296705536⟩ : DyadicInterval 40),(⟨-215774086848,-215774086784⟩ : DyadicInterval 40),(⟨744574255298,744574274628⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179937116032,179937116096⟩ : DyadicInterval 40),(⟨-215258766208,-215258766144⟩ : DyadicInterval 40),(⟨744650465675,744650485005⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180171980736,180171980800⟩ : DyadicInterval 40),(⟨-215595299776,-215595299712⟩ : DyadicInterval 40),(⟨744600711015,744600730344⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨75108518,100268032⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75105920,75105984⟩ : DyadicInterval 40),(⟨-75111104,-75111040⟩ : DyadicInterval 40),(⟨762123381013,762123400342⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨100263424,100263488⟩ : DyadicInterval 40),(⟨-100272640,-100272576⟩ : DyadicInterval 40),(⟨762123379015,762123398345⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-9152,-5120⟩ : DyadicInterval 40),(⟨762123386176,762123407456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨195595623285,195847914280⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180020185088,180020185152⟩ : DyadicInterval 40),(⟨-215377774528,-215377774464⟩ : DyadicInterval 40),(⟨744632877464,744632896794⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180234352576,180234352640⟩ : DyadicInterval 40),(⟨-215684700800,-215684700736⟩ : DyadicInterval 40),(⟨744587484079,744587503409⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-35450348160,-35357589312⟩ : DyadicInterval 40),(⟨779802178272,779848576960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨180103254592,180296705536⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-215774086848,-215496805184⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e722_ok : ecellOkT e722 = true := by decide +kernel
theorem e722_pos {a z : ℝ} (ha1 : ((145803/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((91233/512000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e722 e722_ok ha1 ha2 hz1 hz2 hz

-- box ['364083/2048000', '145803/819200', '3997/4000', '1999/2000']  interval_lower 93546821/1099511627776
noncomputable def e723 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1294977200029,0,true,179909769728,179909769792⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨904046055523,0,false,-215219593536,-215219593472⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1295205101732,0,true,180103254592,180103254656⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨903818153820,0,false,-215496805248,-215496805184⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1294830600849,0,true,179785291328,179785291392⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨904192654703,0,false,-215041312256,-215041312192⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1295107254996,0,true,180020188480,180020188544⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨903916000556,0,false,-215377779264,-215377779200⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099561639267,0,true,50010304,50010368⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099461616285,0,false,-50012672,-50012608⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586737698,0,true,75107328,75107392⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436517854,0,false,-75112512,-75112448⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622645,0,false,-5184,-5120⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625502,0,false,-2304,-2240⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1294903896015,0,true,179847528512,179847528576⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨904119359537,0,false,-215130443904,-215130443840⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1295156187142,0,true,180061729792,180061729856⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨903867068410,0,false,-215437301312,-215437301248⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1064699086787,0,false,-35375571520,-35375571456⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1064788813098,0,false,-35282915328,-35282915264⟩
    { al := (364083/2048000), au := (145803/819200), zl := (3997/4000), zu := (1999/2000),
      A := ⟨195465572253,195693473956⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179909769728,179909769792⟩ : DyadicInterval 40),(⟨-215219593536,-215219593472⟩ : DyadicInterval 40),(⟨744656253472,744656272801⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180103254592,180103254656⟩ : DyadicInterval 40),(⟨-215496805248,-215496805184⟩ : DyadicInterval 40),(⟨744615278798,744615298128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179785291328,179785291392⟩ : DyadicInterval 40),(⟨-215041312256,-215041312192⟩ : DyadicInterval 40),(⟨744682584916,744682604246⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180020188480,180020188544⟩ : DyadicInterval 40),(⟨-215377779264,-215377779200⟩ : DyadicInterval 40),(⟨744632876706,744632896035⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨50011491,75109922⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨50010304,50010368⟩ : DyadicInterval 40),(⟨-50012672,-50012608⟩ : DyadicInterval 40),(⟨762123382461,762123401790⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75107328,75107392⟩ : DyadicInterval 40),(⟨-75112512,-75112448⟩ : DyadicInterval 40),(⟨762123381012,762123400342⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5184,-2240⟩ : DyadicInterval 40),(⟨762123384736,762123405472⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨195392268239,195644559366⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179847528512,179847528576⟩ : DyadicInterval 40),(⟨-215130443904,-215130443840⟩ : DyadicInterval 40),(⟨744669422524,744669441854⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180061729792,180061729856⟩ : DyadicInterval 40),(⟨-215437301312,-215437301248⟩ : DyadicInterval 40),(⟨744624077281,744624096611⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-35375571520,-35282915264⟩ : DyadicInterval 40),(⟨779764841248,779811188640⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨179909769728,180103254656⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-215496805248,-215219593472⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e723_ok : ecellOkT e723 = true := by decide +kernel
theorem e723_pos {a z : ℝ} (ha1 : ((364083/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((145803/819200 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e723 e723_ok ha1 ha2 hz1 hz2 hz

-- box ['145803/819200', '91233/512000', '3997/4000', '1999/2000']  interval_lower 96518625/1099511627776
noncomputable def e724 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1295205101731,0,true,180103254592,180103254656⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨903818153821,0,false,-215496805248,-215496805184⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1295433003434,0,true,180296705472,180296705536⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨903590252118,0,false,-215774086848,-215774086784⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1295058331625,0,true,179978653056,179978653120⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨903964923927,0,false,-215318271168,-215318271104⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1295335042747,0,true,180213557184,180213557248⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨903688212805,0,false,-215654892288,-215654892224⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099561700331,0,true,50071360,50071424⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099461555221,0,false,-50073728,-50073664⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586829310,0,true,75198912,75198976⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436426242,0,false,-75204160,-75204096⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622632,0,false,-5184,-5120⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625496,0,false,-2304,-2240⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1295131712252,0,true,180040951808,180040951872⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨903891543300,0,false,-215407529152,-215407529088⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1295384031868,0,true,180255139584,180255139648⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨903639223684,0,false,-215714498624,-215714498560⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1064617955243,0,false,-35459359040,-35459358976⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1064707796254,0,false,-35366577344,-35366577280⟩
    { al := (145803/819200), au := (91233/512000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨195693473955,195921375658⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180103254592,180103254656⟩ : DyadicInterval 40),(⟨-215496805248,-215496805184⟩ : DyadicInterval 40),(⟨744615278798,744615298128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180296705472,180296705536⟩ : DyadicInterval 40),(⟨-215774086848,-215774086784⟩ : DyadicInterval 40),(⟨744574255298,744574274628⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179978653056,179978653120⟩ : DyadicInterval 40),(⟨-215318271168,-215318271104⟩ : DyadicInterval 40),(⟨744641672323,744641691652⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180213557184,180213557248⟩ : DyadicInterval 40),(⟨-215654892288,-215654892224⟩ : DyadicInterval 40),(⟨744591894738,744591914068⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨50072555,75201534⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨50071360,50071424⟩ : DyadicInterval 40),(⟨-50073728,-50073664⟩ : DyadicInterval 40),(⟨762123382455,762123401784⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75198912,75198976⟩ : DyadicInterval 40),(⟨-75204160,-75204096⟩ : DyadicInterval 40),(⟨762123381032,762123400361⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5184,-2240⟩ : DyadicInterval 40),(⟨762123384736,762123405472⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨195620084476,195872404092⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180040951808,180040951872⟩ : DyadicInterval 40),(⟨-215407529152,-215407529088⟩ : DyadicInterval 40),(⟨744628478879,744628498209⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180255139584,180255139648⟩ : DyadicInterval 40),(⟨-215714498624,-215714498560⟩ : DyadicInterval 40),(⟨744583074549,744583093879⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-35459359040,-35366577280⟩ : DyadicInterval 40),(⟨779806672256,779853082400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨180103254592,180296705536⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-215774086848,-215496805184⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e724_ok : ecellOkT e724 = true := by decide +kernel
theorem e724_pos {a z : ℝ} (ha1 : ((145803/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((91233/512000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e724 e724_ok ha1 ha2 hz1 hz2 hz

-- box ['181617/1024000', '727317/4096000', '1999/2000', '3999/4000']  interval_lower 1360571/17179869184
noncomputable def e725 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1294521396625,0,true,179522697728,179522697792⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨904501858927,0,false,-214665379648,-214665379584⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1294749298328,0,true,179716250752,179716250816⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨904273957224,0,false,-214942451648,-214942451584⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1294423891740,0,true,179439878080,179439878144⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨904599363812,0,false,-214546859200,-214546859136⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1294700488911,0,true,179674800640,179674800704⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨904322766641,0,false,-214883105600,-214883105536⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536572491,0,true,24944384,24944448⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486683061,0,false,-24945024,-24944960⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099561579317,0,true,49950400,49950464⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099461676235,0,false,-49952704,-49952640⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625506,0,false,-2304,-2240⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627211,0,false,-576,-512⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1294472639412,0,true,179481284672,179481284736⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨904550616140,0,false,-214606112000,-214606111936⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1294724902187,0,true,179695533184,179695533248⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨904298353365,0,false,-214912788672,-214912788608⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1064852401312,0,false,-35217255488,-35217255424⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1064941919646,0,false,-35124827328,-35124827264⟩
    { al := (181617/1024000), au := (727317/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨195009768849,195237670552⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179522697728,179522697792⟩ : DyadicInterval 40),(⟨-214665379648,-214665379584⟩ : DyadicInterval 40),(⟨744738056519,744738075848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179716250752,179716250816⟩ : DyadicInterval 40),(⟨-214942451648,-214942451584⟩ : DyadicInterval 40),(⟨744697179378,744697198708⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179439878080,179439878144⟩ : DyadicInterval 40),(⟨-214546859200,-214546859136⟩ : DyadicInterval 40),(⟨744755530401,744755549730⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179674800640,179674800704⟩ : DyadicInterval 40),(⟨-214883105600,-214883105536⟩ : DyadicInterval 40),(⟨744705938067,744705957396⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨24944715,49951541⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24944384,24944448⟩ : DyadicInterval 40),(⟨-24945024,-24944960⟩ : DyadicInterval 40),(⟨762123383306,762123402635⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨49950400,49950464⟩ : DyadicInterval 40),(⟨-49952704,-49952640⟩ : DyadicInterval 40),(⟨762123382434,762123401763⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2304,-512⟩ : DyadicInterval 40),(⟨762123383872,762123404032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨194961011636,195213274411⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179481284672,179481284736⟩ : DyadicInterval 40),(⟨-214606112000,-214606111936⟩ : DyadicInterval 40),(⟨744746795395,744746814725⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179695533184,179695533248⟩ : DyadicInterval 40),(⟨-214912788672,-214912788608⟩ : DyadicInterval 40),(⟨744701557468,744701576797⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-35217255488,-35124827264⟩ : DyadicInterval 40),(⟨779685797248,779732030624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨179522697728,179716250816⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-214942451648,-214665379584⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e725_ok : ecellOkT e725 = true := by decide +kernel
theorem e725_pos {a z : ℝ} (ha1 : ((181617/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((727317/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e725 e725_ok ha1 ha2 hz1 hz2 hz

-- box ['727317/4096000', '364083/2048000', '1999/2000', '3999/4000']  interval_lower 22504271/274877906944
noncomputable def e726 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1294749298327,0,true,179716250752,179716250816⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨904273957225,0,false,-214942451648,-214942451584⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1294977200030,0,true,179909769728,179909769792⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨904046055522,0,false,-215219593536,-215219593472⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1294651679491,0,true,179633348928,179633348992⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨904371576061,0,false,-214823762816,-214823762752⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1294928333638,0,true,179868278464,179868278528⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨904094921914,0,false,-215160163200,-215160163136⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536603013,0,true,24974912,24974976⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486652539,0,false,-24975552,-24975488⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099561640373,0,true,50011456,50011520⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099461615179,0,false,-50013760,-50013696⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625501,0,false,-2304,-2240⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627209,0,false,-576,-512⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1294700484137,0,true,179674796544,179674796608⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨904322771415,0,false,-214883099840,-214883099776⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1294952775398,0,true,179889031552,179889031616⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨904070480154,0,false,-215189888384,-215189888320⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1064771438387,0,false,-35300856768,-35300856704⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1064861071398,0,false,-35208303232,-35208303168⟩
    { al := (727317/4096000), au := (364083/2048000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨195237670551,195465572254⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179716250752,179716250816⟩ : DyadicInterval 40),(⟨-214942451648,-214942451584⟩ : DyadicInterval 40),(⟨744697179378,744697198708⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179909769728,179909769792⟩ : DyadicInterval 40),(⟨-215219593536,-215219593472⟩ : DyadicInterval 40),(⟨744656253471,744656272801⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179633348928,179633348992⟩ : DyadicInterval 40),(⟨-214823762816,-214823762752⟩ : DyadicInterval 40),(⟨744714694565,744714713895⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179868278464,179868278528⟩ : DyadicInterval 40),(⟨-215160163200,-215160163136⟩ : DyadicInterval 40),(⟨744665032867,744665052196⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨24975237,50012597⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24974912,24974976⟩ : DyadicInterval 40),(⟨-24975552,-24975488⟩ : DyadicInterval 40),(⟨762123383304,762123402633⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨50011456,50011520⟩ : DyadicInterval 40),(⟨-50013760,-50013696⟩ : DyadicInterval 40),(⟨762123382429,762123401758⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2304,-512⟩ : DyadicInterval 40),(⟨762123383872,762123404032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨195188856361,195441147622⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179674796544,179674796608⟩ : DyadicInterval 40),(⟨-214883099840,-214883099776⟩ : DyadicInterval 40),(⟨744705938966,744705958296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179889031552,179889031616⟩ : DyadicInterval 40),(⟨-215189888384,-215189888320⟩ : DyadicInterval 40),(⟨744660641918,744660661248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-35300856768,-35208303168⟩ : DyadicInterval 40),(⟨779727535200,779773831264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨179716250752,179909769792⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-215219593536,-214942451584⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e726_ok : ecellOkT e726 = true := by decide +kernel
theorem e726_pos {a z : ℝ} (ha1 : ((727317/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((364083/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e726 e726_ok ha1 ha2 hz1 hz2 hz

-- box ['181617/1024000', '727317/4096000', '3999/4000', '1']  interval_lower 86506181/1099511627776
noncomputable def e727 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1294521396625,0,true,179522697728,179522697792⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨904501858927,0,false,-214665379648,-214665379584⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1294749298328,0,true,179716250752,179716250816⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨904273957224,0,false,-214942451648,-214942451584⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1294472644182,0,true,179481288704,179481288768⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨904550611370,0,false,-214606117824,-214606117760⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536603822,0,true,24975744,24975808⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486651730,0,false,-24976384,-24976320⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627208,0,false,-576,-512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1294497015426,0,true,179501989184,179501989248⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨904526240126,0,false,-214635742272,-214635742208⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1294749306822,0,true,179716257984,179716258048⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨904273948730,0,false,-214942462016,-214942461952⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1064843734907,0,false,-35226203968,-35226203904⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1064933274591,0,false,-35133753088,-35133753024⟩
    { al := (181617/1024000), au := (727317/4096000), zl := (3999/4000), zu := 1,
      A := ⟨195009768849,195237670552⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179522697728,179522697792⟩ : DyadicInterval 40),(⟨-214665379648,-214665379584⟩ : DyadicInterval 40),(⟨744738056519,744738075848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179716250752,179716250816⟩ : DyadicInterval 40),(⟨-214942451648,-214942451584⟩ : DyadicInterval 40),(⟨744697179378,744697198708⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179481288704,179481288768⟩ : DyadicInterval 40),(⟨-214606117824,-214606117760⟩ : DyadicInterval 40),(⟨744746794562,744746813892⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179716250752,179716250816⟩ : DyadicInterval 40),(⟨-214942451648,-214942451584⟩ : DyadicInterval 40),(⟨744697179378,744697198708⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,24976046⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24975744,24975808⟩ : DyadicInterval 40),(⟨-24976384,-24976320⟩ : DyadicInterval 40),(⟨762123383304,762123402633⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-576,0⟩ : DyadicInterval 40),(⟨762123383616,762123403168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨194985387650,195237679046⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179501989184,179501989248⟩ : DyadicInterval 40),(⟨-214635742272,-214635742208⟩ : DyadicInterval 40),(⟨744742426705,744742446035⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179716257984,179716258048⟩ : DyadicInterval 40),(⟨-214942462016,-214942461952⟩ : DyadicInterval 40),(⟨744697177860,744697197189⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-35226203968,-35133753024⟩ : DyadicInterval 40),(⟨779690260128,779736504864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨179522697728,179716250816⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-214942451648,-214665379584⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e727_ok : ecellOkT e727 = true := by decide +kernel
theorem e727_pos {a z : ℝ} (ha1 : ((181617/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((727317/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e727 e727_ok ha1 ha2 hz1 hz2 hz

-- box ['727317/4096000', '364083/2048000', '3999/4000', '1']  interval_lower 89444509/1099511627776
noncomputable def e728 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1294749298327,0,true,179716250752,179716250816⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨904273957225,0,false,-214942451648,-214942451584⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1294977200030,0,true,179909769728,179909769792⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨904046055522,0,false,-215219593536,-215219593472⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1294700488909,0,true,179674800640,179674800704⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨904322766643,0,false,-214883105600,-214883105536⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536634351,0,true,25006272,25006336⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486621201,0,false,-25006912,-25006848⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627207,0,false,-576,-512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1294724888640,0,true,179695521664,179695521728⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨904298366912,0,false,-214912772160,-214912772096⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1294977208525,0,true,179909776896,179909776960⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨904046047027,0,false,-215219603840,-215219603776⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1064762751736,0,false,-35309826880,-35309826816⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1064852406123,0,false,-35217250496,-35217250432⟩
    { al := (727317/4096000), au := (364083/2048000), zl := (3999/4000), zu := 1,
      A := ⟨195237670551,195465572254⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179716250752,179716250816⟩ : DyadicInterval 40),(⟨-214942451648,-214942451584⟩ : DyadicInterval 40),(⟨744697179378,744697198708⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179909769728,179909769792⟩ : DyadicInterval 40),(⟨-215219593536,-215219593472⟩ : DyadicInterval 40),(⟨744656253471,744656272801⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179674800640,179674800704⟩ : DyadicInterval 40),(⟨-214883105600,-214883105536⟩ : DyadicInterval 40),(⟨744705938067,744705957397⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179909769728,179909769792⟩ : DyadicInterval 40),(⟨-215219593536,-215219593472⟩ : DyadicInterval 40),(⟨744656253471,744656272801⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,25006575⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25006272,25006336⟩ : DyadicInterval 40),(⟨-25006912,-25006848⟩ : DyadicInterval 40),(⟨762123383303,762123402632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-576,0⟩ : DyadicInterval 40),(⟨762123383616,762123403168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨195213260864,195465580749⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179695521664,179695521728⟩ : DyadicInterval 40),(⟨-214912772160,-214912772096⟩ : DyadicInterval 40),(⟨744701559891,744701579221⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179909776896,179909776960⟩ : DyadicInterval 40),(⟨-215219603840,-215219603776⟩ : DyadicInterval 40),(⟨744656251960,744656271290⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-35309826880,-35217250432⟩ : DyadicInterval 40),(⟨779732008832,779778316320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨179716250752,179909769792⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-215219593536,-214942451584⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e728_ok : ecellOkT e728 = true := by decide +kernel
theorem e728_pos {a z : ℝ} (ha1 : ((727317/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((364083/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e728 e728_ok ha1 ha2 hz1 hz2 hz

-- box ['364083/2048000', '145803/819200', '1999/2000', '3999/4000']  interval_lower 92972035/1099511627776
noncomputable def e729 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1294977200029,0,true,179909769728,179909769792⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨904046055523,0,false,-215219593536,-215219593472⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1295205101732,0,true,180103254592,180103254656⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨903818153820,0,false,-215496805248,-215496805184⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1294879467242,0,true,179826785728,179826785792⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨904143788310,0,false,-215100736128,-215100736064⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1295156178364,0,true,180061722304,180061722368⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨903867077188,0,false,-215437290624,-215437290560⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536633540,0,true,25005440,25005504⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486622012,0,false,-25006080,-25006016⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099561701439,0,true,50072512,50072576⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099461554113,0,false,-50074816,-50074752⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625495,0,false,-2304,-2240⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627208,0,false,-576,-512⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1294928328864,0,true,179868274432,179868274496⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨904094926688,0,false,-215160157440,-215160157376⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1295180648613,0,true,180082495936,180082496000⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨903842606939,0,false,-215467057984,-215467057920⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1064690381007,0,false,-35384561984,-35384561920⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1064780128719,0,false,-35291882944,-35291882880⟩
    { al := (364083/2048000), au := (145803/819200), zl := (1999/2000), zu := (3999/4000),
      A := ⟨195465572253,195693473956⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179909769728,179909769792⟩ : DyadicInterval 40),(⟨-215219593536,-215219593472⟩ : DyadicInterval 40),(⟨744656253472,744656272801⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180103254592,180103254656⟩ : DyadicInterval 40),(⟨-215496805248,-215496805184⟩ : DyadicInterval 40),(⟨744615278798,744615298128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179826785728,179826785792⟩ : DyadicInterval 40),(⟨-215100736128,-215100736064⟩ : DyadicInterval 40),(⟨744673809986,744673829316⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180061722304,180061722368⟩ : DyadicInterval 40),(⟨-215437290624,-215437290560⟩ : DyadicInterval 40),(⟨744624078877,744624098206⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨25005764,50073663⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25005440,25005504⟩ : DyadicInterval 40),(⟨-25006080,-25006016⟩ : DyadicInterval 40),(⟨762123383303,762123402632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨50072512,50072576⟩ : DyadicInterval 40),(⟨-50074816,-50074752⟩ : DyadicInterval 40),(⟨762123382423,762123401752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2304,-512⟩ : DyadicInterval 40),(⟨762123383872,762123404032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨195416701088,195669020837⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179868274432,179868274496⟩ : DyadicInterval 40),(⟨-215160157440,-215160157376⟩ : DyadicInterval 40),(⟨744665033731,744665053060⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180082495936,180082496000⟩ : DyadicInterval 40),(⟨-215467057984,-215467057920⟩ : DyadicInterval 40),(⟨744619677578,744619696908⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-35384561984,-35291882880⟩ : DyadicInterval 40),(⟨779769325056,779815683872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨179909769728,180103254656⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-215496805248,-215219593472⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e729_ok : ecellOkT e729 = true := by decide +kernel
theorem e729_pos {a z : ℝ} (ha1 : ((364083/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((145803/819200 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e729 e729_ok ha1 ha2 hz1 hz2 hz

-- box ['145803/819200', '91233/512000', '1999/2000', '3999/4000']  interval_lower 95941365/1099511627776
noncomputable def e730 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1295205101731,0,true,180103254592,180103254656⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨903818153821,0,false,-215496805248,-215496805184⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1295433003434,0,true,180296705472,180296705536⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨903590252118,0,false,-215774086848,-215774086784⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1295107254994,0,true,180020188480,180020188544⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨903916000558,0,false,-215377779264,-215377779200⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1295384023091,0,true,180255132096,180255132160⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨903639232461,0,false,-215714487936,-215714487872⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536664073,0,true,25035968,25036032⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486591479,0,false,-25036608,-25036544⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099561762515,0,true,50133568,50133632⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099461493037,0,false,-50135936,-50135872⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625489,0,false,-2304,-2240⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627206,0,false,-576,-512⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1295156173585,0,true,180061718272,180061718336⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨903867081967,0,false,-215437284864,-215437284800⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1295408521830,0,true,180275926272,180275926336⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨903614733722,0,false,-215744297408,-215744297344⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1064609229174,0,false,-35468371136,-35468371072⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1064699091612,0,false,-35375566528,-35375566464⟩
    { al := (145803/819200), au := (91233/512000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨195693473955,195921375658⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180103254592,180103254656⟩ : DyadicInterval 40),(⟨-215496805248,-215496805184⟩ : DyadicInterval 40),(⟨744615278798,744615298128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180296705472,180296705536⟩ : DyadicInterval 40),(⟨-215774086848,-215774086784⟩ : DyadicInterval 40),(⟨744574255298,744574274628⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180020188480,180020188544⟩ : DyadicInterval 40),(⟨-215377779264,-215377779200⟩ : DyadicInterval 40),(⟨744632876706,744632896035⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180255132096,180255132160⟩ : DyadicInterval 40),(⟨-215714487936,-215714487872⟩ : DyadicInterval 40),(⟨744583076149,744583095478⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨25036297,50134739⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25035968,25036032⟩ : DyadicInterval 40),(⟨-25036608,-25036544⟩ : DyadicInterval 40),(⟨762123383301,762123402630⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨50133568,50133632⟩ : DyadicInterval 40),(⟨-50135936,-50135872⟩ : DyadicInterval 40),(⟨762123382449,762123401779⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2304,-512⟩ : DyadicInterval 40),(⟨762123383872,762123404032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨195644545809,195896894054⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180061718272,180061718336⟩ : DyadicInterval 40),(⟨-215437284864,-215437284800⟩ : DyadicInterval 40),(⟨744624079743,744624099073⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180275926272,180275926336⟩ : DyadicInterval 40),(⟨-215744297408,-215744297344⟩ : DyadicInterval 40),(⟨744578664449,744578683778⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-35468371136,-35375566464⟩ : DyadicInterval 40),(⟨779811166848,779857588448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨180103254592,180296705536⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-215774086848,-215496805184⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e730_ok : ecellOkT e730 = true := by decide +kernel
theorem e730_pos {a z : ℝ} (ha1 : ((145803/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((91233/512000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e730 e730_ok ha1 ha2 hz1 hz2 hz

-- box ['364083/2048000', '145803/819200', '3999/4000', '1']  interval_lower 92396943/1099511627776
noncomputable def e731 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1294977200029,0,true,179909769728,179909769792⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨904046055523,0,false,-215219593536,-215219593472⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1295205101732,0,true,180103254592,180103254656⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨903818153820,0,false,-215496805248,-215496805184⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1294928333635,0,true,179868278464,179868278528⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨904094921917,0,false,-215160163200,-215160163136⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536664884,0,true,25036800,25036864⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486590668,0,false,-25037440,-25037376⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627205,0,false,-576,-512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1294952761846,0,true,179889020032,179889020096⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨904070493706,0,false,-215189871872,-215189871808⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1295205110224,0,true,180103261824,180103261888⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨903818145328,0,false,-215496815552,-215496815488⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1064681674090,0,false,-35393553728,-35393553664⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1064771443206,0,false,-35300851776,-35300851712⟩
    { al := (364083/2048000), au := (145803/819200), zl := (3999/4000), zu := 1,
      A := ⟨195465572253,195693473956⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179909769728,179909769792⟩ : DyadicInterval 40),(⟨-215219593536,-215219593472⟩ : DyadicInterval 40),(⟨744656253472,744656272801⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180103254592,180103254656⟩ : DyadicInterval 40),(⟨-215496805248,-215496805184⟩ : DyadicInterval 40),(⟨744615278798,744615298128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179868278464,179868278528⟩ : DyadicInterval 40),(⟨-215160163200,-215160163136⟩ : DyadicInterval 40),(⟨744665032867,744665052197⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180103254592,180103254656⟩ : DyadicInterval 40),(⟨-215496805248,-215496805184⟩ : DyadicInterval 40),(⟨744615278798,744615298128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,25037108⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25036800,25036864⟩ : DyadicInterval 40),(⟨-25037440,-25037376⟩ : DyadicInterval 40),(⟨762123383301,762123402630⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-576,0⟩ : DyadicInterval 40),(⟨762123383616,762123403168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨195441134070,195693482448⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨179889020032,179889020096⟩ : DyadicInterval 40),(⟨-215189871872,-215189871808⟩ : DyadicInterval 40),(⟨744660644348,744660663678⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180103261824,180103261888⟩ : DyadicInterval 40),(⟨-215496815552,-215496815488⟩ : DyadicInterval 40),(⟨744615277246,744615296575⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-35393553728,-35300851712⟩ : DyadicInterval 40),(⟨779773809472,779820179744⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨179909769728,180103254656⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-215496805248,-215219593472⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e731_ok : ecellOkT e731 = true := by decide +kernel
theorem e731_pos {a z : ℝ} (ha1 : ((364083/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((145803/819200 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e731 e731_ok ha1 ha2 hz1 hz2 hz

-- box ['145803/819200', '91233/512000', '3999/4000', '1']  interval_lower 95363805/1099511627776
noncomputable def e732 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1295205101731,0,true,180103254592,180103254656⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨903818153821,0,false,-215496805248,-215496805184⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1295433003434,0,true,180296705472,180296705536⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨903590252118,0,false,-215774086848,-215774086784⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1295156178362,0,true,180061722304,180061722368⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨903867077190,0,false,-215437290624,-215437290560⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536695422,0,true,25067328,25067392⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486560130,0,false,-25067968,-25067904⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627204,0,false,-576,-512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1295180635054,0,true,180082484416,180082484480⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨903842620498,0,false,-215467041472,-215467041408⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1295433011934,0,true,180296712640,180296712704⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨903590243618,0,false,-215774097216,-215774097152⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1064600501962,0,false,-35477384512,-35477384448⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1064690385834,0,false,-35384556992,-35384556928⟩
    { al := (145803/819200), au := (91233/512000), zl := (3999/4000), zu := 1,
      A := ⟨195693473955,195921375658⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180103254592,180103254656⟩ : DyadicInterval 40),(⟨-215496805248,-215496805184⟩ : DyadicInterval 40),(⟨744615278798,744615298128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180296705472,180296705536⟩ : DyadicInterval 40),(⟨-215774086848,-215774086784⟩ : DyadicInterval 40),(⟨744574255298,744574274628⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180061722304,180061722368⟩ : DyadicInterval 40),(⟨-215437290624,-215437290560⟩ : DyadicInterval 40),(⟨744624078877,744624098207⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180296705472,180296705536⟩ : DyadicInterval 40),(⟨-215774086848,-215774086784⟩ : DyadicInterval 40),(⟨744574255298,744574274628⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,25067646⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25067328,25067392⟩ : DyadicInterval 40),(⟨-25067968,-25067904⟩ : DyadicInterval 40),(⟨762123383300,762123402629⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-576,0⟩ : DyadicInterval 40),(⟨762123383616,762123403168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨195669007278,195921384158⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180082484416,180082484480⟩ : DyadicInterval 40),(⟨-215467041472,-215467041408⟩ : DyadicInterval 40),(⟨744619680016,744619699345⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180296712640,180296712704⟩ : DyadicInterval 40),(⟨-215774097216,-215774097152⟩ : DyadicInterval 40),(⟨744574253805,744574273134⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-35477384512,-35384556928⟩ : DyadicInterval 40),(⟨779815662080,779862095136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨180103254592,180296705536⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-215774086848,-215496805184⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e732_ok : ecellOkT e732 = true := by decide +kernel
theorem e732_pos {a z : ℝ} (ha1 : ((145803/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((91233/512000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e732 e732_ok ha1 ha2 hz1 hz2 hz

-- box ['91233/512000', '730713/4096000', '999/1000', '3997/4000']  interval_lower 100083265/1099511627776
noncomputable def e733 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1295433003433,0,true,180296705472,180296705536⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨903590252119,0,false,-215774086848,-215774086784⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1295660905137,0,true,180490122240,180490122304⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨903362350415,0,false,-216051438400,-216051438336⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1295237082057,0,true,180130402688,180130402752⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨903786173495,0,false,-215535710592,-215535710528⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1295513793180,0,true,180365274432,180365274496⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨903509462372,0,false,-215872398272,-215872398208⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586827903,0,true,75197504,75197568⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436427649,0,false,-75202752,-75202688⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099612017976,0,true,100385600,100385664⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099411237576,0,false,-100394816,-100394752⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511618609,0,false,-9216,-9152⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622633,0,false,-5184,-5120⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1295335038815,0,true,180213553856,180213553920⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨903688216737,0,false,-215654887488,-215654887424⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1295587358294,0,true,180427707840,180427707904⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨903435897258,0,false,-215961925824,-215961925760⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1064545474506,0,false,-35534217920,-35534217856⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1064635408788,0,false,-35441333568,-35441333504⟩
    { al := (91233/512000), au := (730713/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨195921375657,196149277361⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180296705472,180296705536⟩ : DyadicInterval 40),(⟨-215774086848,-215774086784⟩ : DyadicInterval 40),(⟨744574255298,744574274628⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180490122240,180490122304⟩ : DyadicInterval 40),(⟨-216051438400,-216051438336⟩ : DyadicInterval 40),(⟨744533183062,744533202391⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180130402688,180130402752⟩ : DyadicInterval 40),(⟨-215535710592,-215535710528⟩ : DyadicInterval 40),(⟨744609525095,744609544425⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180365274432,180365274496⟩ : DyadicInterval 40),(⟨-215872398272,-215872398208⟩ : DyadicInterval 40),(⟨744559701022,744559720352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨75200127,100390200⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75197504,75197568⟩ : DyadicInterval 40),(⟨-75202752,-75202688⟩ : DyadicInterval 40),(⟨762123381032,762123400361⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨100385600,100385664⟩ : DyadicInterval 40),(⟨-100394816,-100394752⟩ : DyadicInterval 40),(⟨762123378993,762123398323⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-9216,-5120⟩ : DyadicInterval 40),(⟨762123386176,762123407488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨195823411039,196075730518⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180213553856,180213553920⟩ : DyadicInterval 40),(⟨-215654887488,-215654887424⟩ : DyadicInterval 40),(⟨744591895434,744591914764⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180427707840,180427707904⟩ : DyadicInterval 40),(⟨-215961925824,-215961925760⟩ : DyadicInterval 40),(⟨744546442955,744546462284⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-35534217920,-35441333504⟩ : DyadicInterval 40),(⟨779844050368,779890511840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨180296705472,180490122304⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-216051438400,-215774086784⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e733_ok : ecellOkT e733 = true := by decide +kernel
theorem e733_pos {a z : ℝ} (ha1 : ((91233/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((730713/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e733 e733_ok ha1 ha2 hz1 hz2 hz

-- box ['730713/4096000', '365781/2048000', '999/1000', '3997/4000']  interval_lower 103085783/1099511627776
noncomputable def e734 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1295660905136,0,true,180490122240,180490122304⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨903362350416,0,false,-216051438400,-216051438336⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1295888806839,0,true,180683505088,180683505152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨903134448713,0,false,-216328859968,-216328859904⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1295464755858,0,true,180323655296,180323655360⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨903558499694,0,false,-215812724672,-215812724608⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1295741523955,0,true,180558534144,180558534208⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨903281731597,0,false,-216149566592,-216149566528⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586919527,0,true,75289152,75289216⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436336025,0,false,-75294336,-75294272⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099612140165,0,true,100507776,100507840⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099411115387,0,false,-100516992,-100516928⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511618587,0,false,-9216,-9152⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622621,0,false,-5184,-5120⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1295562826563,0,true,180406888576,180406888640⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨903460428989,0,false,-215932070272,-215932070208⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1295815174537,0,true,180621029120,180621029184⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨903208081015,0,false,-216239220736,-216239220672⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1064464174436,0,false,-35618191616,-35618191552⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1064554223439,0,false,-35525181632,-35525181568⟩
    { al := (730713/4096000), au := (365781/2048000), zl := (999/1000), zu := (3997/4000),
      A := ⟨196149277360,196377179063⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180490122240,180490122304⟩ : DyadicInterval 40),(⟨-216051438400,-216051438336⟩ : DyadicInterval 40),(⟨744533183062,744533202392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180683505088,180683505152⟩ : DyadicInterval 40),(⟨-216328859968,-216328859904⟩ : DyadicInterval 40),(⟨744492061991,744492081321⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180323655296,180323655360⟩ : DyadicInterval 40),(⟨-215812724672,-215812724608⟩ : DyadicInterval 40),(⟨744568535841,744568555170⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180558534144,180558534208⟩ : DyadicInterval 40),(⟨-216149566592,-216149566528⟩ : DyadicInterval 40),(⟨744518642309,744518661639⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨75291751,100512389⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75289152,75289216⟩ : DyadicInterval 40),(⟨-75294336,-75294272⟩ : DyadicInterval 40),(⟨762123380988,762123400317⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨100507776,100507840⟩ : DyadicInterval 40),(⟨-100516992,-100516928⟩ : DyadicInterval 40),(⟨762123378971,762123398301⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-9216,-5120⟩ : DyadicInterval 40),(⟨762123386176,762123407488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨196051198787,196303546761⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180406888576,180406888640⟩ : DyadicInterval 40),(⟨-215932070272,-215932070208⟩ : DyadicInterval 40),(⟨744550864681,744550884011⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180621029120,180621029184⟩ : DyadicInterval 40),(⟨-216239220736,-216239220672⟩ : DyadicInterval 40),(⟨744505353058,744505372387⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-35618191616,-35525181568⟩ : DyadicInterval 40),(⟨779885974400,779932498688⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨180490122240,180683505152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-216328859968,-216051438336⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e734_ok : ecellOkT e734 = true := by decide +kernel
theorem e734_pos {a z : ℝ} (ha1 : ((730713/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((365781/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e734 e734_ok ha1 ha2 hz1 hz2 hz

-- box ['91233/512000', '730713/4096000', '3997/4000', '1999/2000']  interval_lower 49752225/549755813888
noncomputable def e735 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1295433003433,0,true,180296705472,180296705536⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨903590252119,0,false,-215774086848,-215774086784⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1295660905137,0,true,180490122240,180490122304⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨903362350415,0,false,-216051438400,-216051438336⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1295286062401,0,true,180171980736,180171980800⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨903737193151,0,false,-215595299776,-215595299712⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1295562830499,0,true,180406891968,180406892032⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨903460425053,0,false,-215932075072,-215932075008⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099561761405,0,true,50132480,50132544⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099461494147,0,false,-50134784,-50134720⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099586920938,0,true,75290560,75290624⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436334614,0,false,-75295744,-75295680⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622620,0,false,-5184,-5120⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625491,0,false,-2304,-2240⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1295359528493,0,true,180234341120,180234341184⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨903663727059,0,false,-215684684288,-215684684224⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1295611876600,0,true,180448515328,180448515392⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨903411378952,0,false,-215991765824,-215991765760⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1064536729268,0,false,-35543250432,-35543250368⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1064626685002,0,false,-35450343168,-35450343104⟩
    { al := (91233/512000), au := (730713/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨195921375657,196149277361⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180296705472,180296705536⟩ : DyadicInterval 40),(⟨-215774086848,-215774086784⟩ : DyadicInterval 40),(⟨744574255298,744574274628⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180490122240,180490122304⟩ : DyadicInterval 40),(⟨-216051438400,-216051438336⟩ : DyadicInterval 40),(⟨744533183062,744533202391⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180171980736,180171980800⟩ : DyadicInterval 40),(⟨-215595299776,-215595299712⟩ : DyadicInterval 40),(⟨744600711015,744600730345⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180406891968,180406892032⟩ : DyadicInterval 40),(⟨-215932075072,-215932075008⟩ : DyadicInterval 40),(⟨744550863945,744550883275⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨50133629,75293162⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨50132480,50132544⟩ : DyadicInterval 40),(⟨-50134784,-50134720⟩ : DyadicInterval 40),(⟨762123382418,762123401747⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75290560,75290624⟩ : DyadicInterval 40),(⟨-75295744,-75295680⟩ : DyadicInterval 40),(⟨762123380987,762123400317⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5184,-2240⟩ : DyadicInterval 40),(⟨762123384736,762123405472⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨195847900717,196100248824⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180234341120,180234341184⟩ : DyadicInterval 40),(⟨-215684684288,-215684684224⟩ : DyadicInterval 40),(⟨744587486484,744587505813⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180448515328,180448515392⟩ : DyadicInterval 40),(⟨-215991765824,-215991765760⟩ : DyadicInterval 40),(⟨744542023067,744542042397⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-35543250432,-35450343104⟩ : DyadicInterval 40),(⟨779848555168,779895028096⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨180296705472,180490122304⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-216051438400,-215774086784⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e735_ok : ecellOkT e735 = true := by decide +kernel
theorem e735_pos {a z : ℝ} (ha1 : ((91233/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((730713/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e735 e735_ok ha1 ha2 hz1 hz2 hz

-- box ['730713/4096000', '365781/2048000', '3997/4000', '1999/2000']  interval_lower 51252263/549755813888
noncomputable def e736 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1295660905136,0,true,180490122240,180490122304⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨903362350416,0,false,-216051438400,-216051438336⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1295888806839,0,true,180683505088,180683505152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨903134448713,0,false,-216328859968,-216328859904⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1295513793177,0,true,180365274432,180365274496⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨903509462375,0,false,-215872398272,-215872398208⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1295790618250,0,true,180600192704,180600192768⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨903232637302,0,false,-216209327808,-216209327744⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099561822489,0,true,50193536,50193600⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099461433063,0,false,-50195904,-50195840⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587012581,0,true,75382208,75382272⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436242971,0,false,-75387392,-75387328⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622607,0,false,-5184,-5120⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625485,0,false,-2304,-2240⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1295587344726,0,true,180427696320,180427696384⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨903435910826,0,false,-215961909312,-215961909248⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1295839721329,0,true,180641857152,180641857216⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨903183534223,0,false,-216269102976,-216269102912⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1064455408865,0,false,-35627245824,-35627245760⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1064545479346,0,false,-35534212928,-35534212864⟩
    { al := (730713/4096000), au := (365781/2048000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨196149277360,196377179063⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180490122240,180490122304⟩ : DyadicInterval 40),(⟨-216051438400,-216051438336⟩ : DyadicInterval 40),(⟨744533183062,744533202392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180683505088,180683505152⟩ : DyadicInterval 40),(⟨-216328859968,-216328859904⟩ : DyadicInterval 40),(⟨744492061991,744492081321⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180365274432,180365274496⟩ : DyadicInterval 40),(⟨-215872398272,-215872398208⟩ : DyadicInterval 40),(⟨744559701023,744559720352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180600192704,180600192768⟩ : DyadicInterval 40),(⟨-216209327808,-216209327744⟩ : DyadicInterval 40),(⟨744509784469,744509803799⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨50194713,75384805⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨50193536,50193600⟩ : DyadicInterval 40),(⟨-50195904,-50195840⟩ : DyadicInterval 40),(⟨762123382444,762123401773⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75382208,75382272⟩ : DyadicInterval 40),(⟨-75387392,-75387328⟩ : DyadicInterval 40),(⟨762123380975,762123400304⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5184,-2240⟩ : DyadicInterval 40),(⟨762123384736,762123405472⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨196075716950,196328093553⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180427696320,180427696384⟩ : DyadicInterval 40),(⟨-215961909312,-215961909248⟩ : DyadicInterval 40),(⟨744546445404,744546464733⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180641857152,180641857216⟩ : DyadicInterval 40),(⟨-216269102976,-216269102912⟩ : DyadicInterval 40),(⟨744500922777,744500942106⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-35627245824,-35534212864⟩ : DyadicInterval 40),(⟨779890490048,779937025792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨180490122240,180683505152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-216328859968,-216051438336⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e736_ok : ecellOkT e736 = true := by decide +kernel
theorem e736_pos {a z : ℝ} (ha1 : ((730713/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((365781/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e736 e736_ok ha1 ha2 hz1 hz2 hz

-- box ['365781/2048000', '732411/4096000', '999/1000', '3997/4000']  interval_lower 53051613/549755813888
noncomputable def e737 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1295888806838,0,true,180683505088,180683505152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨903134448714,0,false,-216328859968,-216328859904⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1296116708541,0,true,180876853888,180876853952⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨902906547011,0,false,-216606351552,-216606351488⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1295692429658,0,true,180516873984,180516874048⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨903330825894,0,false,-216089808640,-216089808576⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1295969254731,0,true,180751759872,180751759936⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨903054000821,0,false,-216426804800,-216426804736⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587011167,0,true,75380800,75380864⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436244385,0,false,-75385984,-75385920⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099612262373,0,true,100629952,100630016⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099410993179,0,false,-100639232,-100639168⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511618565,0,false,-9216,-9152⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622608,0,false,-5184,-5120⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1295790614313,0,true,180600189376,180600189440⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨903232641239,0,false,-216209323008,-216209322944⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1296042990775,0,true,180814316416,180814316480⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨902980264777,0,false,-216516585600,-216516585536⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1064382779961,0,false,-35702269184,-35702269120⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1064472943707,0,false,-35609133632,-35609133568⟩
    { al := (365781/2048000), au := (732411/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨196377179062,196605080765⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180683505088,180683505152⟩ : DyadicInterval 40),(⟨-216328859968,-216328859904⟩ : DyadicInterval 40),(⟨744492061992,744492081321⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180876853888,180876853952⟩ : DyadicInterval 40),(⟨-216606351552,-216606351488⟩ : DyadicInterval 40),(⟨744450892151,744450911481⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180516873984,180516874048⟩ : DyadicInterval 40),(⟨-216089808640,-216089808576⟩ : DyadicInterval 40),(⟨744527497904,744527517233⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180751759872,180751759936⟩ : DyadicInterval 40),(⟨-216426804800,-216426804736⟩ : DyadicInterval 40),(⟨744477534889,744477554218⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨75383391,100634597⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75380800,75380864⟩ : DyadicInterval 40),(⟨-75385984,-75385920⟩ : DyadicInterval 40),(⟨762123380975,762123400304⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨100629952,100630016⟩ : DyadicInterval 40),(⟨-100639232,-100639168⟩ : DyadicInterval 40),(⟨762123378980,762123398310⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-9216,-5120⟩ : DyadicInterval 40),(⟨762123386176,762123407488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨196278986537,196531362999⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180600189376,180600189440⟩ : DyadicInterval 40),(⟨-216209323008,-216209322944⟩ : DyadicInterval 40),(⟨744509785169,744509804499⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180814316416,180814316480⟩ : DyadicInterval 40),(⟨-216516585600,-216516585536⟩ : DyadicInterval 40),(⟨744464214404,744464233733⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-35702269184,-35609133568⟩ : DyadicInterval 40),(⟨779927950400,779974537472⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨180683505088,180876853952⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-216606351552,-216328859904⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e737_ok : ecellOkT e737 = true := by decide +kernel
theorem e737_pos {a z : ℝ} (ha1 : ((365781/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((732411/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e737 e737_ok ha1 ha2 hz1 hz2 hz

-- box ['732411/4096000', '36663/204800', '999/1000', '3997/4000']  interval_lower 54567337/549755813888
noncomputable def e738 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1296116708540,0,true,180876853888,180876853952⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨902906547012,0,false,-216606351552,-216606351488⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1296344610243,0,true,181070168640,181070168704⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨902678645309,0,false,-216883913152,-216883913088⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1295920103459,0,true,180710058752,180710058816⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨903103152093,0,false,-216366962368,-216366962304⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1296196985507,0,true,180944951680,180944951744⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨902826270045,0,false,-216704112896,-216704112832⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587102822,0,true,75472448,75472512⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436152730,0,false,-75477696,-75477632⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099612384601,0,true,100752192,100752256⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099410870951,0,false,-100761472,-100761408⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511618542,0,false,-9280,-9216⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622596,0,false,-5184,-5120⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1296018402067,0,true,180793456128,180793456192⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨903004853485,0,false,-216486645632,-216486645568⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1296270807016,0,true,181007569728,181007569792⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨902752448536,0,false,-216794020480,-216794020416⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1064301291079,0,false,-35786450752,-35786450688⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1064391569592,0,false,-35693189504,-35693189440⟩
    { al := (732411/4096000), au := (36663/204800), zl := (999/1000), zu := (3997/4000),
      A := ⟨196605080764,196832982467⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180876853888,180876853952⟩ : DyadicInterval 40),(⟨-216606351552,-216606351488⟩ : DyadicInterval 40),(⟨744450892151,744450911481⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181070168640,181070168704⟩ : DyadicInterval 40),(⟨-216883913152,-216883913088⟩ : DyadicInterval 40),(⟨744409673530,744409692859⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180710058752,180710058816⟩ : DyadicInterval 40),(⟨-216366962368,-216366962304⟩ : DyadicInterval 40),(⟨744486411222,744486430551⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180944951680,180944951744⟩ : DyadicInterval 40),(⟨-216704112896,-216704112832⟩ : DyadicInterval 40),(⟨744436378713,744436398042⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨75475046,100756825⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75472448,75472512⟩ : DyadicInterval 40),(⟨-75477696,-75477632⟩ : DyadicInterval 40),(⟨762123380994,762123400324⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨100752192,100752256⟩ : DyadicInterval 40),(⟨-100761472,-100761408⟩ : DyadicInterval 40),(⟨762123378958,762123398288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-9280,-5120⟩ : DyadicInterval 40),(⟨762123386176,762123407520⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨196506774291,196759179240⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180793456128,180793456192⟩ : DyadicInterval 40),(⟨-216486645632,-216486645568⟩ : DyadicInterval 40),(⟨744468656937,744468676267⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181007569728,181007569792⟩ : DyadicInterval 40),(⟨-216794020480,-216794020416⟩ : DyadicInterval 40),(⟨744423027007,744423046337⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-35786450752,-35693189440⟩ : DyadicInterval 40),(⟨779969978336,780016628256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨180876853888,181070168704⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-216883913152,-216606351488⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e738_ok : ecellOkT e738 = true := by decide +kernel
theorem e738_pos {a z : ℝ} (ha1 : ((732411/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((36663/204800 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e738 e738_ok ha1 ha2 hz1 hz2 hz

-- box ['365781/2048000', '732411/4096000', '3997/4000', '1999/2000']  interval_lower 105519421/1099511627776
noncomputable def e739 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1295888806838,0,true,180683505088,180683505152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨903134448714,0,false,-216328859968,-216328859904⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1296116708541,0,true,180876853888,180876853952⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨902906547011,0,false,-216606351552,-216606351488⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1295741523953,0,true,180558534144,180558534208⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨903281731599,0,false,-216149566592,-216149566528⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1296018406001,0,true,180793459456,180793459520⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨903004849551,0,false,-216486650432,-216486650368⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099561883583,0,true,50254656,50254720⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099461371969,0,false,-50256960,-50256896⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587104238,0,true,75473856,75473920⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436151314,0,false,-75479104,-75479040⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622594,0,false,-5184,-5120⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625479,0,false,-2304,-2240⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1295815160964,0,true,180621017600,180621017664⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨903208094588,0,false,-216239204224,-216239204160⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1296067566055,0,true,180835164928,180835164992⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨902955689497,0,false,-216546510080,-216546510016⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1064373994033,0,false,-35711345152,-35711345088⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1064464179283,0,false,-35618186560,-35618186496⟩
    { al := (365781/2048000), au := (732411/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨196377179062,196605080765⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180683505088,180683505152⟩ : DyadicInterval 40),(⟨-216328859968,-216328859904⟩ : DyadicInterval 40),(⟨744492061992,744492081321⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180876853888,180876853952⟩ : DyadicInterval 40),(⟨-216606351552,-216606351488⟩ : DyadicInterval 40),(⟨744450892151,744450911481⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180558534144,180558534208⟩ : DyadicInterval 40),(⟨-216149566592,-216149566528⟩ : DyadicInterval 40),(⟨744518642310,744518661639⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180793459456,180793459520⟩ : DyadicInterval 40),(⟨-216486650432,-216486650368⟩ : DyadicInterval 40),(⟨744468656236,744468675565⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨50255807,75476462⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨50254656,50254720⟩ : DyadicInterval 40),(⟨-50256960,-50256896⟩ : DyadicInterval 40),(⟨762123382406,762123401735⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75473856,75473920⟩ : DyadicInterval 40),(⟨-75479104,-75479040⟩ : DyadicInterval 40),(⟨762123380994,762123400324⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5184,-2240⟩ : DyadicInterval 40),(⟨762123384736,762123405472⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨196303533188,196555938279⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180621017600,180621017664⟩ : DyadicInterval 40),(⟨-216239204224,-216239204160⟩ : DyadicInterval 40),(⟨744505355513,744505374843⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180835164928,180835164992⟩ : DyadicInterval 40),(⟨-216546510080,-216546510016⟩ : DyadicInterval 40),(⟨744459773742,744459793071⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-35711345152,-35618186496⟩ : DyadicInterval 40),(⟨779932476864,779979075456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨180683505088,180876853952⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-216606351552,-216328859904⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e739_ok : ecellOkT e739 = true := by decide +kernel
theorem e739_pos {a z : ℝ} (ha1 : ((365781/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((732411/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e739 e739_ok ha1 ha2 hz1 hz2 hz

-- box ['732411/4096000', '36663/204800', '3997/4000', '1999/2000']  interval_lower 13568589/137438953472
noncomputable def e740 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1296116708540,0,true,180876853888,180876853952⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨902906547012,0,false,-216606351552,-216606351488⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1296344610243,0,true,181070168640,181070168704⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨902678645309,0,false,-216883913152,-216883913088⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1295969254729,0,true,180751759872,180751759936⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨903054000823,0,false,-216426804800,-216426804736⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1296246193752,0,true,180986692288,180986692352⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨902777061800,0,false,-216764043072,-216764043008⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099561944688,0,true,50315712,50315776⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099461310864,0,false,-50318080,-50318016⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587195911,0,true,75565504,75565568⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436059641,0,false,-75570752,-75570688⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622582,0,false,-5248,-5184⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625474,0,false,-2304,-2240⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1296042977197,0,true,180814304896,180814304960⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨902980278355,0,false,-216516569088,-216516569024⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1296295410781,0,true,181028438720,181028438784⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨902727844771,0,false,-216823987200,-216823987136⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1064292484771,0,false,-35795548416,-35795548352⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1064382784816,0,false,-35702264192,-35702264128⟩
    { al := (732411/4096000), au := (36663/204800), zl := (3997/4000), zu := (1999/2000),
      A := ⟨196605080764,196832982467⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180876853888,180876853952⟩ : DyadicInterval 40),(⟨-216606351552,-216606351488⟩ : DyadicInterval 40),(⟨744450892151,744450911481⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181070168640,181070168704⟩ : DyadicInterval 40),(⟨-216883913152,-216883913088⟩ : DyadicInterval 40),(⟨744409673530,744409692859⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180751759872,180751759936⟩ : DyadicInterval 40),(⟨-216426804800,-216426804736⟩ : DyadicInterval 40),(⟨744477534889,744477554219⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180986692288,180986692352⟩ : DyadicInterval 40),(⟨-216764043072,-216764043008⟩ : DyadicInterval 40),(⟨744427479249,744427498578⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨50316912,75568135⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨50315712,50315776⟩ : DyadicInterval 40),(⟨-50318080,-50318016⟩ : DyadicInterval 40),(⟨762123382433,762123401762⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75565504,75565568⟩ : DyadicInterval 40),(⟨-75570752,-75570688⟩ : DyadicInterval 40),(⟨762123380982,762123400311⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5248,-2240⟩ : DyadicInterval 40),(⟨762123384736,762123405504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨196531349421,196783783005⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180814304896,180814304960⟩ : DyadicInterval 40),(⟨-216516569088,-216516569024⟩ : DyadicInterval 40),(⟨744464216866,744464236196⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181028438720,181028438784⟩ : DyadicInterval 40),(⟨-216823987200,-216823987136⟩ : DyadicInterval 40),(⟨744418575939,744418595269⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-35795548416,-35702264128⟩ : DyadicInterval 40),(⟨779974515680,780021177088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨180876853888,181070168704⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-216883913152,-216606351488⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e740_ok : ecellOkT e740 = true := by decide +kernel
theorem e740_pos {a z : ℝ} (ha1 : ((732411/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((36663/204800 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e740 e740_ok ha1 ha2 hz1 hz2 hz

-- box ['91233/512000', '730713/4096000', '1999/2000', '3999/4000']  interval_lower 6182819/68719476736
noncomputable def e741 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1295433003433,0,true,180296705472,180296705536⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨903590252119,0,false,-215774086848,-215774086784⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1295660905137,0,true,180490122240,180490122304⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨903362350415,0,false,-216051438400,-216051438336⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1295335042745,0,true,180213557184,180213557248⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨903688212807,0,false,-215654892224,-215654892160⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1295611867818,0,true,180448507904,180448507968⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨903411387734,0,false,-215991755136,-215991755072⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536694610,0,true,25066496,25066560⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486560942,0,false,-25067136,-25067072⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099561823601,0,true,50194624,50194688⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099461431951,0,false,-50196992,-50196928⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625484,0,false,-2304,-2240⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627205,0,false,-576,-512⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1295384018309,0,true,180255128064,180255128128⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨903639237243,0,false,-215714482112,-215714482048⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1295636395045,0,true,180469322560,180469322624⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨903386860507,0,false,-216021606784,-216021606720⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1064527982888,0,false,-35552284224,-35552284160⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1064617960075,0,false,-35459354048,-35459353984⟩
    { al := (91233/512000), au := (730713/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨195921375657,196149277361⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180296705472,180296705536⟩ : DyadicInterval 40),(⟨-215774086848,-215774086784⟩ : DyadicInterval 40),(⟨744574255298,744574274628⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180490122240,180490122304⟩ : DyadicInterval 40),(⟨-216051438400,-216051438336⟩ : DyadicInterval 40),(⟨744533183062,744533202391⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180213557184,180213557248⟩ : DyadicInterval 40),(⟨-215654892224,-215654892160⟩ : DyadicInterval 40),(⟨744591894713,744591914042⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180448507904,180448507968⟩ : DyadicInterval 40),(⟨-215991755136,-215991755072⟩ : DyadicInterval 40),(⟨744542024634,744542043963⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨25066834,50195825⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25066496,25066560⟩ : DyadicInterval 40),(⟨-25067136,-25067072⟩ : DyadicInterval 40),(⟨762123383300,762123402629⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨50194624,50194688⟩ : DyadicInterval 40),(⟨-50196992,-50196928⟩ : DyadicInterval 40),(⟨762123382444,762123401773⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2304,-512⟩ : DyadicInterval 40),(⟨762123383872,762123404032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨195872390533,196124767269⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180255128064,180255128128⟩ : DyadicInterval 40),(⟨-215714482112,-215714482048⟩ : DyadicInterval 40),(⟨744583076992,744583096321⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180469322560,180469322624⟩ : DyadicInterval 40),(⟨-216021606784,-216021606720⟩ : DyadicInterval 40),(⟨744537602571,744537621900⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-35552284224,-35459353984⟩ : DyadicInterval 40),(⟨779853060608,779899544992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨180296705472,180490122304⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-216051438400,-215774086784⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e741_ok : ecellOkT e741 = true := by decide +kernel
theorem e741_pos {a z : ℝ} (ha1 : ((91233/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((730713/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e741 e741_ok ha1 ha2 hz1 hz2 hz

-- box ['730713/4096000', '365781/2048000', '1999/2000', '3999/4000']  interval_lower 25480723/274877906944
noncomputable def e742 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1295660905136,0,true,180490122240,180490122304⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨903362350416,0,false,-216051438400,-216051438336⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1295888806839,0,true,180683505088,180683505152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨903134448713,0,false,-216328859968,-216328859904⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1295562830497,0,true,180406891904,180406891968⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨903460425055,0,false,-215932075072,-215932075008⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1295839712545,0,true,180641849664,180641849728⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨903183543007,0,false,-216269092288,-216269092224⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536725153,0,true,25097088,25097152⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486530399,0,false,-25097664,-25097600⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099561884697,0,true,50255744,50255808⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099461370855,0,false,-50258112,-50258048⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625478,0,false,-2304,-2240⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627204,0,false,-576,-512⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1295611863027,0,true,180448503808,180448503872⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨903411392525,0,false,-215991749312,-215991749248⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1295864268259,0,true,180662684864,180662684928⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨903158987293,0,false,-216298986176,-216298986112⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1064446642149,0,false,-35636301248,-35636301184⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1064536734111,0,false,-35543245440,-35543245376⟩
    { al := (730713/4096000), au := (365781/2048000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨196149277360,196377179063⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180490122240,180490122304⟩ : DyadicInterval 40),(⟨-216051438400,-216051438336⟩ : DyadicInterval 40),(⟨744533183062,744533202392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180683505088,180683505152⟩ : DyadicInterval 40),(⟨-216328859968,-216328859904⟩ : DyadicInterval 40),(⟨744492061991,744492081321⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180406891904,180406891968⟩ : DyadicInterval 40),(⟨-215932075072,-215932075008⟩ : DyadicInterval 40),(⟨744550863983,744550883313⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180641849664,180641849728⟩ : DyadicInterval 40),(⟨-216269092288,-216269092224⟩ : DyadicInterval 40),(⟨744500924385,744500943715⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨25097377,50256921⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25097088,25097152⟩ : DyadicInterval 40),(⟨-25097664,-25097600⟩ : DyadicInterval 40),(⟨762123383267,762123402596⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨50255744,50255808⟩ : DyadicInterval 40),(⟨-50258112,-50258048⟩ : DyadicInterval 40),(⟨762123382438,762123401767⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2304,-512⟩ : DyadicInterval 40),(⟨762123383872,762123404032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨196100235251,196352640483⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180448503808,180448503872⟩ : DyadicInterval 40),(⟨-215991749312,-215991749248⟩ : DyadicInterval 40),(⟨744542025518,744542044847⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180662684864,180662684928⟩ : DyadicInterval 40),(⟨-216298986176,-216298986112⟩ : DyadicInterval 40),(⟨744496491922,744496511251⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-35636301248,-35543245376⟩ : DyadicInterval 40),(⟨779895006304,779941553504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨180490122240,180683505152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-216328859968,-216051438336⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e742_ok : ecellOkT e742 = true := by decide +kernel
theorem e742_pos {a z : ℝ} (ha1 : ((730713/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((365781/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e742 e742_ok ha1 ha2 hz1 hz2 hz

-- box ['91233/512000', '730713/4096000', '3999/4000', '1']  interval_lower 98345303/1099511627776
noncomputable def e743 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1295433003433,0,true,180296705472,180296705536⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨903590252119,0,false,-215774086848,-215774086784⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1295660905137,0,true,180490122240,180490122304⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨903362350415,0,false,-216051438400,-216051438336⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1295384023089,0,true,180255132096,180255132160⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨903639232463,0,false,-215714487936,-215714487872⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536725966,0,true,25097856,25097920⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486529586,0,false,-25098496,-25098432⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627203,0,false,-576,-512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1295408508267,0,true,180275914752,180275914816⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨903614747285,0,false,-215744280896,-215744280832⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1295660913631,0,true,180490129472,180490129536⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨903362341921,0,false,-216051448768,-216051448704⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1064519235363,0,false,-35561319232,-35561319168⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1064609234008,0,false,-35468366144,-35468366080⟩
    { al := (91233/512000), au := (730713/4096000), zl := (3999/4000), zu := 1,
      A := ⟨195921375657,196149277361⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180296705472,180296705536⟩ : DyadicInterval 40),(⟨-215774086848,-215774086784⟩ : DyadicInterval 40),(⟨744574255298,744574274628⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180490122240,180490122304⟩ : DyadicInterval 40),(⟨-216051438400,-216051438336⟩ : DyadicInterval 40),(⟨744533183062,744533202391⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180255132096,180255132160⟩ : DyadicInterval 40),(⟨-215714487936,-215714487872⟩ : DyadicInterval 40),(⟨744583076149,744583095478⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180490122240,180490122304⟩ : DyadicInterval 40),(⟨-216051438400,-216051438336⟩ : DyadicInterval 40),(⟨744533183062,744533202391⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,25098190⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25097856,25097920⟩ : DyadicInterval 40),(⟨-25098496,-25098432⟩ : DyadicInterval 40),(⟨762123383299,762123402628⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-576,0⟩ : DyadicInterval 40),(⟨762123383616,762123403168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨195896880491,196149285855⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180275914752,180275914816⟩ : DyadicInterval 40),(⟨-215744280896,-215744280832⟩ : DyadicInterval 40),(⟨744578666892,744578686222⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180490129472,180490129536⟩ : DyadicInterval 40),(⟨-216051448768,-216051448704⟩ : DyadicInterval 40),(⟨744533181528,744533200858⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-35561319232,-35468366080⟩ : DyadicInterval 40),(⟨779857566656,779904062496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨180296705472,180490122304⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-216051438400,-215774086784⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e743_ok : ecellOkT e743 = true := by decide +kernel
theorem e743_pos {a z : ℝ} (ha1 : ((91233/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((730713/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e743 e743_ok ha1 ha2 hz1 hz2 hz

-- box ['730713/4096000', '365781/2048000', '3999/4000', '1']  interval_lower 6333803/68719476736
noncomputable def e744 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1295660905136,0,true,180490122240,180490122304⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨903362350416,0,false,-216051438400,-216051438336⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1295888806839,0,true,180683505088,180683505152⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨903134448713,0,false,-216328859968,-216328859904⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1295611867816,0,true,180448507904,180448507968⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨903411387736,0,false,-215991755136,-215991755072⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536756515,0,true,25128448,25128512⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486499037,0,false,-25129088,-25129024⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627201,0,false,-576,-512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1295636381476,0,true,180469311040,180469311104⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨903386874076,0,false,-216021590272,-216021590208⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1295888815339,0,true,180683512256,180683512320⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨903134440213,0,false,-216328870336,-216328870272⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1064437874283,0,false,-35645358016,-35645357952⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1064527987729,0,false,-35552279232,-35552279168⟩
    { al := (730713/4096000), au := (365781/2048000), zl := (3999/4000), zu := 1,
      A := ⟨196149277360,196377179063⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180490122240,180490122304⟩ : DyadicInterval 40),(⟨-216051438400,-216051438336⟩ : DyadicInterval 40),(⟨744533183062,744533202392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180683505088,180683505152⟩ : DyadicInterval 40),(⟨-216328859968,-216328859904⟩ : DyadicInterval 40),(⟨744492061991,744492081321⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180448507904,180448507968⟩ : DyadicInterval 40),(⟨-215991755136,-215991755072⟩ : DyadicInterval 40),(⟨744542024634,744542043964⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180683505088,180683505152⟩ : DyadicInterval 40),(⟨-216328859968,-216328859904⟩ : DyadicInterval 40),(⟨744492061991,744492081321⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,25128739⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25128448,25128512⟩ : DyadicInterval 40),(⟨-25129088,-25129024⟩ : DyadicInterval 40),(⟨762123383297,762123402626⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-576,0⟩ : DyadicInterval 40),(⟨762123383616,762123403168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨196124753700,196377187563⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180469311040,180469311104⟩ : DyadicInterval 40),(⟨-216021590272,-216021590208⟩ : DyadicInterval 40),(⟨744537605021,744537624351⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180683512256,180683512320⟩ : DyadicInterval 40),(⟨-216328870336,-216328870272⟩ : DyadicInterval 40),(⟨744492060491,744492079820⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-35645358016,-35552279168⟩ : DyadicInterval 40),(⟨779899523200,779946081888⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨180490122240,180683505152⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-216328859968,-216051438336⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e744_ok : ecellOkT e744 = true := by decide +kernel
theorem e744_pos {a z : ℝ} (ha1 : ((730713/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((365781/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e744 e744_ok ha1 ha2 hz1 hz2 hz

-- box ['365781/2048000', '732411/4096000', '1999/2000', '3999/4000']  interval_lower 104935487/1099511627776
noncomputable def e745 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1295888806838,0,true,180683505088,180683505152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨903134448714,0,false,-216328859968,-216328859904⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1296116708541,0,true,180876853888,180876853952⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨902906547011,0,false,-216606351552,-216606351488⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1295790618248,0,true,180600192704,180600192768⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨903232637304,0,false,-216209327808,-216209327744⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1296067557271,0,true,180835157440,180835157504⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨902955698281,0,false,-216546499392,-216546499328⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536755700,0,true,25127616,25127680⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486499852,0,false,-25128256,-25128192⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099561945804,0,true,50316864,50316928⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099461309748,0,false,-50319232,-50319168⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625473,0,false,-2304,-2240⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627202,0,false,-576,-512⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1295839707755,0,true,180641845632,180641845696⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨903183547797,0,false,-216269086464,-216269086400⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1296092141473,0,true,180856013120,180856013184⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨902931114079,0,false,-216576435456,-216576435392⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1064365206956,0,false,-35720422336,-35720422272⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1064455413713,0,false,-35627240832,-35627240768⟩
    { al := (365781/2048000), au := (732411/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨196377179062,196605080765⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180683505088,180683505152⟩ : DyadicInterval 40),(⟨-216328859968,-216328859904⟩ : DyadicInterval 40),(⟨744492061992,744492081321⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180876853888,180876853952⟩ : DyadicInterval 40),(⟨-216606351552,-216606351488⟩ : DyadicInterval 40),(⟨744450892151,744450911481⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180600192704,180600192768⟩ : DyadicInterval 40),(⟨-216209327808,-216209327744⟩ : DyadicInterval 40),(⟨744509784470,744509803799⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180835157440,180835157504⟩ : DyadicInterval 40),(⟨-216546499392,-216546499328⟩ : DyadicInterval 40),(⟨744459775354,744459794683⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨25127924,50318028⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25127616,25127680⟩ : DyadicInterval 40),(⟨-25128256,-25128192⟩ : DyadicInterval 40),(⟨762123383297,762123402626⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨50316864,50316928⟩ : DyadicInterval 40),(⟨-50319232,-50319168⟩ : DyadicInterval 40),(⟨762123382433,762123401762⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2304,-512⟩ : DyadicInterval 40),(⟨762123383872,762123404032⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨196328079979,196580513697⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180641845632,180641845696⟩ : DyadicInterval 40),(⟨-216269086464,-216269086400⟩ : DyadicInterval 40),(⟨744500925233,744500944563⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180856013120,180856013184⟩ : DyadicInterval 40),(⟨-216576435456,-216576435392⟩ : DyadicInterval 40),(⟨744455332477,744455351806⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-35720422336,-35627240768⟩ : DyadicInterval 40),(⟨779937004000,779983614048⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨180683505088,180876853952⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-216606351552,-216328859904⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e745_ok : ecellOkT e745 = true := by decide +kernel
theorem e745_pos {a z : ℝ} (ha1 : ((365781/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((732411/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e745 e745_ok ha1 ha2 hz1 hz2 hz

-- box ['732411/4096000', '36663/204800', '1999/2000', '3999/4000']  interval_lower 53981133/549755813888
noncomputable def e746 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1296116708540,0,true,180876853888,180876853952⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨902906547012,0,false,-216606351552,-216606351488⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1296344610243,0,true,181070168640,181070168704⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨902678645309,0,false,-216883913152,-216883913088⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1296018405999,0,true,180793459456,180793459520⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨903004849553,0,false,-216486650432,-216486650368⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1296295401998,0,true,181028431232,181028431296⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨902727853554,0,false,-216823976512,-216823976448⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536786254,0,true,25158144,25158208⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486469298,0,false,-25158784,-25158720⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099562006920,0,true,50377984,50378048⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099461248632,0,false,-50380352,-50380288⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625467,0,false,-2368,-2304⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627201,0,false,-576,-512⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1296067552476,0,true,180835153408,180835153472⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨902955703076,0,false,-216546493504,-216546493440⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1296320014684,0,true,181049307392,181049307456⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨902703240868,0,false,-216853954816,-216853954752⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1064283677312,0,false,-35804647360,-35804647296⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1064373998889,0,false,-35711340096,-35711340032⟩
    { al := (732411/4096000), au := (36663/204800), zl := (1999/2000), zu := (3999/4000),
      A := ⟨196605080764,196832982467⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180876853888,180876853952⟩ : DyadicInterval 40),(⟨-216606351552,-216606351488⟩ : DyadicInterval 40),(⟨744450892151,744450911481⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181070168640,181070168704⟩ : DyadicInterval 40),(⟨-216883913152,-216883913088⟩ : DyadicInterval 40),(⟨744409673530,744409692859⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180793459456,180793459520⟩ : DyadicInterval 40),(⟨-216486650432,-216486650368⟩ : DyadicInterval 40),(⟨744468656236,744468675566⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181028431232,181028431296⟩ : DyadicInterval 40),(⟨-216823976512,-216823976448⟩ : DyadicInterval 40),(⟨744418577555,744418596884⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨25158478,50379144⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25158144,25158208⟩ : DyadicInterval 40),(⟨-25158784,-25158720⟩ : DyadicInterval 40),(⟨762123383296,762123402625⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨50377984,50378048⟩ : DyadicInterval 40),(⟨-50380352,-50380288⟩ : DyadicInterval 40),(⟨762123382427,762123401756⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2368,-512⟩ : DyadicInterval 40),(⟨762123383872,762123404064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨196555924700,196808386908⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180835153408,180835153472⟩ : DyadicInterval 40),(⟨-216546493504,-216546493440⟩ : DyadicInterval 40),(⟨744459776179,744459795509⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181049307392,181049307456⟩ : DyadicInterval 40),(⟨-216853954816,-216853954752⟩ : DyadicInterval 40),(⟨744414124265,744414143594⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-35804647360,-35711340032⟩ : DyadicInterval 40),(⟨779979053632,780025726560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨180876853888,181070168704⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-216883913152,-216606351488⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e746_ok : ecellOkT e746 = true := by decide +kernel
theorem e746_pos {a z : ℝ} (ha1 : ((732411/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((36663/204800 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e746 e746_ok ha1 ha2 hz1 hz2 hz

-- box ['365781/2048000', '732411/4096000', '3999/4000', '1']  interval_lower 104350777/1099511627776
noncomputable def e747 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1295888806838,0,true,180683505088,180683505152⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨903134448714,0,false,-216328859968,-216328859904⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1296116708541,0,true,180876853888,180876853952⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨902906547011,0,false,-216606351552,-216606351488⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1295839712543,0,true,180641849664,180641849728⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨903183543009,0,false,-216269092288,-216269092224⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536787069,0,true,25158976,25159040⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486468483,0,false,-25159616,-25159552⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627200,0,false,-640,-576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1295864254685,0,true,180662673344,180662673408⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨903159000867,0,false,-216298969600,-216298969536⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1296116717040,0,true,180876861056,180876861120⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨902906538512,0,false,-216606361920,-216606361856⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1064356418728,0,false,-35729500800,-35729500736⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1064446646998,0,false,-35636296256,-35636296192⟩
    { al := (365781/2048000), au := (732411/4096000), zl := (3999/4000), zu := 1,
      A := ⟨196377179062,196605080765⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180683505088,180683505152⟩ : DyadicInterval 40),(⟨-216328859968,-216328859904⟩ : DyadicInterval 40),(⟨744492061992,744492081321⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180876853888,180876853952⟩ : DyadicInterval 40),(⟨-216606351552,-216606351488⟩ : DyadicInterval 40),(⟨744450892151,744450911481⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180641849664,180641849728⟩ : DyadicInterval 40),(⟨-216269092288,-216269092224⟩ : DyadicInterval 40),(⟨744500924386,744500943715⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180876853888,180876853952⟩ : DyadicInterval 40),(⟨-216606351552,-216606351488⟩ : DyadicInterval 40),(⟨744450892151,744450911481⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,25159293⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25158976,25159040⟩ : DyadicInterval 40),(⟨-25159616,-25159552⟩ : DyadicInterval 40),(⟨762123383296,762123402625⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-640,0⟩ : DyadicInterval 40),(⟨762123383616,762123403200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨196352626909,196605089264⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180662673344,180662673408⟩ : DyadicInterval 40),(⟨-216298969600,-216298969536⟩ : DyadicInterval 40),(⟨744496494353,744496513683⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180876861056,180876861120⟩ : DyadicInterval 40),(⟨-216606361920,-216606361856⟩ : DyadicInterval 40),(⟨744450890647,744450909977⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-35729500800,-35636296192⟩ : DyadicInterval 40),(⟨779941531712,779988153280⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨180683505088,180876853952⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-216606351552,-216328859904⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e747_ok : ecellOkT e747 = true := by decide +kernel
theorem e747_pos {a z : ℝ} (ha1 : ((365781/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((732411/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e747 e747_ok ha1 ha2 hz1 hz2 hz

-- box ['732411/4096000', '36663/204800', '3999/4000', '1']  interval_lower 107375241/1099511627776
noncomputable def e748 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1296116708540,0,true,180876853888,180876853952⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨902906547012,0,false,-216606351552,-216606351488⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1296344610243,0,true,181070168640,181070168704⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨902678645309,0,false,-216883913152,-216883913088⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1296067557269,0,true,180835157440,180835157504⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨902955698283,0,false,-216546499392,-216546499328⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536817627,0,true,25189504,25189568⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486437925,0,false,-25190144,-25190080⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627198,0,false,-640,-576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1296092127894,0,true,180856001600,180856001664⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨902931127658,0,false,-216576418944,-216576418880⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1296344618737,0,true,181070175872,181070175936⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨902678636815,0,false,-216883923520,-216883923456⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1064274868698,0,false,-35813747584,-35813747520⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1064365211813,0,false,-35720417280,-35720417216⟩
    { al := (732411/4096000), au := (36663/204800), zl := (3999/4000), zu := 1,
      A := ⟨196605080764,196832982467⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180876853888,180876853952⟩ : DyadicInterval 40),(⟨-216606351552,-216606351488⟩ : DyadicInterval 40),(⟨744450892151,744450911481⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181070168640,181070168704⟩ : DyadicInterval 40),(⟨-216883913152,-216883913088⟩ : DyadicInterval 40),(⟨744409673530,744409692859⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180835157440,180835157504⟩ : DyadicInterval 40),(⟨-216546499392,-216546499328⟩ : DyadicInterval 40),(⟨744459775354,744459794683⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181070168640,181070168704⟩ : DyadicInterval 40),(⟨-216883913152,-216883913088⟩ : DyadicInterval 40),(⟨744409673530,744409692859⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,25189851⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25189504,25189568⟩ : DyadicInterval 40),(⟨-25190144,-25190080⟩ : DyadicInterval 40),(⟨762123383294,762123402623⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-640,0⟩ : DyadicInterval 40),(⟨762123383616,762123403200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨196580500118,196832990961⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180856001600,180856001664⟩ : DyadicInterval 40),(⟨-216576418944,-216576418880⟩ : DyadicInterval 40),(⟨744455334940,744455354270⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181070175872,181070175936⟩ : DyadicInterval 40),(⟨-216883923520,-216883923456⟩ : DyadicInterval 40),(⟨744409671986,744409691315⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-35813747584,-35720417216⟩ : DyadicInterval 40),(⟨779983592224,780030276672⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨180876853888,181070168704⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-216883913152,-216606351488⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e748_ok : ecellOkT e748 = true := by decide +kernel
theorem e748_pos {a z : ℝ} (ha1 : ((732411/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((36663/204800 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e748 e748_ok ha1 ha2 hz1 hz2 hz

-- box ['36663/204800', '734109/4096000', '999/1000', '3997/4000']  interval_lower 28045155/274877906944
noncomputable def e749 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1296344610242,0,true,181070168640,181070168704⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨902678645310,0,false,-216883913152,-216883913088⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1296572511945,0,true,181263449472,181263449536⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨902450743607,0,false,-217161544896,-217161544832⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1296147777259,0,true,180903209536,180903209600⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨902875478293,0,false,-216644186048,-216644185984⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1296424716283,0,true,181138109568,181138109632⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨902598539269,0,false,-216981491008,-216981490944⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587194491,0,true,75564096,75564160⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099436061061,0,false,-75569344,-75569280⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099612506850,0,true,100874432,100874496⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099410748702,0,false,-100883712,-100883648⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511618520,0,false,-9280,-9216⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622583,0,false,-5248,-5184⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1296246189811,0,true,180986688896,180986688960⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨902777065741,0,false,-216764038272,-216764038208⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1296498623257,0,true,181200789056,181200789120⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨902524632295,0,false,-217071525376,-217071525312⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1064219707792,0,false,-35870736320,-35870736256⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1064310101097,0,false,-35777349312,-35777349248⟩
    { al := (36663/204800), au := (734109/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨196832982466,197060884169⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181070168640,181070168704⟩ : DyadicInterval 40),(⟨-216883913152,-216883913088⟩ : DyadicInterval 40),(⟨744409673530,744409692860⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181263449472,181263449536⟩ : DyadicInterval 40),(⟨-217161544896,-217161544832⟩ : DyadicInterval 40),(⟨744368406094,744368425423⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180903209536,180903209600⟩ : DyadicInterval 40),(⟨-216644186048,-216644185984⟩ : DyadicInterval 40),(⟨744445275899,744445295228⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181138109568,181138109632⟩ : DyadicInterval 40),(⟨-216981491008,-216981490944⟩ : DyadicInterval 40),(⟨744395173823,744395193152⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨75566715,100879074⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75564096,75564160⟩ : DyadicInterval 40),(⟨-75569344,-75569280⟩ : DyadicInterval 40),(⟨762123380982,762123400311⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨100874432,100874496⟩ : DyadicInterval 40),(⟨-100883712,-100883648⟩ : DyadicInterval 40),(⟨762123378936,762123398265⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-9280,-5184⟩ : DyadicInterval 40),(⟨762123386208,762123407520⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨196734562035,196986995481⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180986688896,180986688960⟩ : DyadicInterval 40),(⟨-216764038272,-216764038208⟩ : DyadicInterval 40),(⟨744427479991,744427499320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181200789056,181200789120⟩ : DyadicInterval 40),(⟨-217071525376,-217071525312⟩ : DyadicInterval 40),(⟨744381790858,744381810188⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-35870736320,-35777349248⟩ : DyadicInterval 40),(⟨780012058240,780058771040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨181070168640,181263449536⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-217161544896,-216883913088⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e749_ok : ecellOkT e749 = true := by decide +kernel
theorem e749_pos {a z : ℝ} (ha1 : ((36663/204800 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((734109/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e749 e749_ok ha1 ha2 hz1 hz2 hz

-- box ['734109/4096000', '367479/2048000', '999/1000', '3997/4000']  interval_lower 115241477/1099511627776
noncomputable def e750 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1296572511944,0,true,181263449472,181263449536⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨902450743608,0,false,-217161544832,-217161544768⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1296800413647,0,true,181456696320,181456696384⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨902222841905,0,false,-217439246720,-217439246656⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1296375451059,0,true,181096326400,181096326464⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨902647804493,0,false,-216921479616,-216921479552⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1296652447058,0,true,181331233472,181331233536⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨902370808494,0,false,-217258939072,-217258939008⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587286175,0,true,75655744,75655808⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435969377,0,false,-75661056,-75660992⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099612629117,0,true,100996672,100996736⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099410626435,0,false,-101006016,-101005952⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511618497,0,false,-9280,-9216⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622570,0,false,-5248,-5184⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1296473977563,0,true,181179887744,181179887808⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨902549277989,0,false,-217041500864,-217041500800⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1296726439497,0,true,181393974464,181393974528⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨902296816055,0,false,-217349100352,-217349100288⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1064138030098,0,false,-35955125824,-35955125760⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1064228538218,0,false,-35861613056,-35861612992⟩
    { al := (734109/4096000), au := (367479/2048000), zl := (999/1000), zu := (3997/4000),
      A := ⟨197060884168,197288785871⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181263449472,181263449536⟩ : DyadicInterval 40),(⟨-217161544832,-217161544768⟩ : DyadicInterval 40),(⟨744368406068,744368425397⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181456696320,181456696384⟩ : DyadicInterval 40),(⟨-217439246720,-217439246656⟩ : DyadicInterval 40),(⟨744327089842,744327109172⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181096326400,181096326464⟩ : DyadicInterval 40),(⟨-216921479616,-216921479552⟩ : DyadicInterval 40),(⟨744404091861,744404111190⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181331233472,181331233536⟩ : DyadicInterval 40),(⟨-217258939072,-217258939008⟩ : DyadicInterval 40),(⟨744353920219,744353939548⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨75658399,101001341⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75655744,75655808⟩ : DyadicInterval 40),(⟨-75661056,-75660992⟩ : DyadicInterval 40),(⟨762123381001,762123400331⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨100996672,100996736⟩ : DyadicInterval 40),(⟨-101006016,-101005952⟩ : DyadicInterval 40),(⟨762123378945,762123398275⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-9280,-5184⟩ : DyadicInterval 40),(⟨762123386208,762123407520⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨196962349787,197214811721⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181179887744,181179887808⟩ : DyadicInterval 40),(⟨-217041500864,-217041500800⟩ : DyadicInterval 40),(⟨744386254250,744386273580⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181393974464,181393974528⟩ : DyadicInterval 40),(⟨-217349100352,-217349100288⟩ : DyadicInterval 40),(⟨744340505933,744340525263⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-35955125824,-35861612992⟩ : DyadicInterval 40),(⟨780054190112,780100965792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨181263449472,181456696384⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-217439246720,-217161544768⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e750_ok : ecellOkT e750 = true := by decide +kernel
theorem e750_pos {a z : ℝ} (ha1 : ((734109/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((367479/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e750 e750_ok ha1 ha2 hz1 hz2 hz

-- box ['36663/204800', '734109/4096000', '3997/4000', '1999/2000']  interval_lower 111592493/1099511627776
noncomputable def e751 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1296344610242,0,true,181070168640,181070168704⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨902678645310,0,false,-216883913152,-216883913088⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1296572511945,0,true,181263449472,181263449536⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨902450743607,0,false,-217161544896,-217161544832⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1296196985505,0,true,180944951680,180944951744⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨902826270047,0,false,-216704112896,-216704112832⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1296473981504,0,true,181179891136,181179891200⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨902549274048,0,false,-217041505664,-217041505600⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099562005801,0,true,50376832,50376896⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099461249751,0,false,-50379200,-50379136⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587287598,0,true,75657216,75657280⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435967954,0,false,-75662464,-75662400⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622569,0,false,-5248,-5184⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625468,0,false,-2368,-2304⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1296270793432,0,true,181007558208,181007558272⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨902752462120,0,false,-216794003968,-216794003904⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1296523255510,0,true,181221678528,181221678592⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨902500000042,0,false,-217101534336,-217101534272⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1064210881079,0,false,-35879855744,-35879855680⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1064301295942,0,false,-35786445760,-35786445696⟩
    { al := (36663/204800), au := (734109/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨196832982466,197060884169⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181070168640,181070168704⟩ : DyadicInterval 40),(⟨-216883913152,-216883913088⟩ : DyadicInterval 40),(⟨744409673530,744409692860⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181263449472,181263449536⟩ : DyadicInterval 40),(⟨-217161544896,-217161544832⟩ : DyadicInterval 40),(⟨744368406094,744368425423⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180944951680,180944951744⟩ : DyadicInterval 40),(⟨-216704112896,-216704112832⟩ : DyadicInterval 40),(⟨744436378713,744436398043⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181179891136,181179891200⟩ : DyadicInterval 40),(⟨-217041505664,-217041505600⟩ : DyadicInterval 40),(⟨744386253507,744386272836⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨50378025,75659822⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨50376832,50376896⟩ : DyadicInterval 40),(⟨-50379200,-50379136⟩ : DyadicInterval 40),(⟨762123382427,762123401756⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75657216,75657280⟩ : DyadicInterval 40),(⟨-75662464,-75662400⟩ : DyadicInterval 40),(⟨762123380969,762123400298⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5248,-2304⟩ : DyadicInterval 40),(⟨762123384768,762123405504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨196759165656,197011627734⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181007558208,181007558272⟩ : DyadicInterval 40),(⟨-216794003968,-216794003904⟩ : DyadicInterval 40),(⟨744423029477,744423048807⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181221678528,181221678592⟩ : DyadicInterval 40),(⟨-217101534336,-217101534272⟩ : DyadicInterval 40),(⟨744377329357,744377348687⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-35879855744,-35786445696⟩ : DyadicInterval 40),(⟨780016606464,780063330752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨181070168640,181263449536⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-217161544896,-216883913088⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e751_ok : ecellOkT e751 = true := by decide +kernel
theorem e751_pos {a z : ℝ} (ha1 : ((36663/204800 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((734109/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e751 e751_ok ha1 ha2 hz1 hz2 hz

-- box ['734109/4096000', '367479/2048000', '3997/4000', '1999/2000']  interval_lower 57325421/549755813888
noncomputable def e752 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1296572511944,0,true,181263449472,181263449536⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨902450743608,0,false,-217161544832,-217161544768⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1296800413647,0,true,181456696320,181456696384⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨902222841905,0,false,-217439246720,-217439246656⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1296424716280,0,true,181138109568,181138109632⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨902598539272,0,false,-216981491008,-216981490944⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1296701769255,0,true,181373056000,181373056064⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨902321486297,0,false,-217319038336,-217319038272⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099562066925,0,true,50437952,50438016⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099461188627,0,false,-50440320,-50440256⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587379302,0,true,75748864,75748928⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435876250,0,false,-75754176,-75754112⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622557,0,false,-5248,-5184⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625463,0,false,-2368,-2304⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1296498609671,0,true,181200777536,181200777600⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨902524645881,0,false,-217071508864,-217071508800⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1296751100232,0,true,181414884416,181414884480⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨902272155320,0,false,-217379151552,-217379151488⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1064129182959,0,false,-35964267136,-35964267072⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1064219712661,0,false,-35870731264,-35870731200⟩
    { al := (734109/4096000), au := (367479/2048000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨197060884168,197288785871⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181263449472,181263449536⟩ : DyadicInterval 40),(⟨-217161544832,-217161544768⟩ : DyadicInterval 40),(⟨744368406068,744368425397⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181456696320,181456696384⟩ : DyadicInterval 40),(⟨-217439246720,-217439246656⟩ : DyadicInterval 40),(⟨744327089842,744327109172⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181138109568,181138109632⟩ : DyadicInterval 40),(⟨-216981491008,-216981490944⟩ : DyadicInterval 40),(⟨744395173823,744395193153⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181373056000,181373056064⟩ : DyadicInterval 40),(⟨-217319038336,-217319038272⟩ : DyadicInterval 40),(⟨744344979053,744344998382⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨50439149,75751526⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨50437952,50438016⟩ : DyadicInterval 40),(⟨-50440320,-50440256⟩ : DyadicInterval 40),(⟨762123382422,762123401751⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75748864,75748928⟩ : DyadicInterval 40),(⟨-75754176,-75754112⟩ : DyadicInterval 40),(⟨762123380988,762123400318⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5248,-2304⟩ : DyadicInterval 40),(⟨762123384768,762123405504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨196986981895,197239472456⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181200777536,181200777600⟩ : DyadicInterval 40),(⟨-217071508864,-217071508800⟩ : DyadicInterval 40),(⟨744381793334,744381812663⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181414884416,181414884480⟩ : DyadicInterval 40),(⟨-217379151552,-217379151488⟩ : DyadicInterval 40),(⟨744336033975,744336053305⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-35964267136,-35870731200⟩ : DyadicInterval 40),(⟨780058749216,780105536448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨181263449472,181456696384⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-217439246720,-217161544768⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e752_ok : ecellOkT e752 = true := by decide +kernel
theorem e752_pos {a z : ℝ} (ha1 : ((734109/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((367479/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e752 e752_ok ha1 ha2 hz1 hz2 hz

-- box ['367479/2048000', '735807/4096000', '999/1000', '3997/4000']  interval_lower 118316533/1099511627776
noncomputable def e753 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1296800413646,0,true,181456696320,181456696384⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨902222841906,0,false,-217439246656,-217439246592⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1297028315349,0,true,181649909248,181649909312⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨901994940203,0,false,-217717018688,-217717018624⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1296603124860,0,true,181289409344,181289409408⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨902420130692,0,false,-217198843136,-217198843072⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1296880177834,0,true,181524323520,181524323584⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨902143077718,0,false,-217536457152,-217536457088⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587377875,0,true,75747456,75747520⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435877677,0,false,-75752768,-75752704⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099612751406,0,true,101118976,101119040⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099410504146,0,false,-101128320,-101128256⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511618475,0,false,-9344,-9280⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622558,0,false,-5248,-5184⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1296701765312,0,true,181373052672,181373052736⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨902321490240,0,false,-217319033536,-217319033472⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1296954255745,0,true,181587125952,181587126016⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨902068999807,0,false,-217626745344,-217626745280⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1064056257996,0,false,-36039619456,-36039619392⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1064146880957,0,false,-35945980800,-35945980736⟩
    { al := (367479/2048000), au := (735807/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨197288785870,197516687573⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181456696320,181456696384⟩ : DyadicInterval 40),(⟨-217439246656,-217439246592⟩ : DyadicInterval 40),(⟨744327089816,744327109145⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181649909248,181649909312⟩ : DyadicInterval 40),(⟨-217717018688,-217717018624⟩ : DyadicInterval 40),(⟨744285724753,744285744082⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181289409344,181289409408⟩ : DyadicInterval 40),(⟨-217198843136,-217198843072⟩ : DyadicInterval 40),(⟨744362859122,744362878452⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181524323520,181524323584⟩ : DyadicInterval 40),(⟨-217536457152,-217536457088⟩ : DyadicInterval 40),(⟨744312617840,744312637170⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨75750099,101123630⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75747456,75747520⟩ : DyadicInterval 40),(⟨-75752768,-75752704⟩ : DyadicInterval 40),(⟨762123380989,762123400318⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨101118976,101119040⟩ : DyadicInterval 40),(⟨-101128320,-101128256⟩ : DyadicInterval 40),(⟨762123378923,762123398252⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-9344,-5184⟩ : DyadicInterval 40),(⟨762123386208,762123407552⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨197190137536,197442627969⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181373052672,181373052736⟩ : DyadicInterval 40),(⟨-217319033536,-217319033472⟩ : DyadicInterval 40),(⟨744344979761,744344999090⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181587125952,181587126016⟩ : DyadicInterval 40),(⟨-217626745344,-217626745280⟩ : DyadicInterval 40),(⟨744299172193,744299191523⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-36039619456,-35945980736⟩ : DyadicInterval 40),(⟨780096373984,780143212608⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨181456696320,181649909312⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-217717018688,-217439246592⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e753_ok : ecellOkT e753 = true := by decide +kernel
theorem e753_pos {a z : ℝ} (ha1 : ((367479/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((735807/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e753 e753_ok ha1 ha2 hz1 hz2 hz

-- box ['735807/4096000', '46041/256000', '999/1000', '3997/4000']  interval_lower 60703421/549755813888
noncomputable def e754 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1297028315348,0,true,181649909248,181649909312⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨901994940204,0,false,-217717018688,-217717018624⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1297256217052,0,true,181843088192,181843088256⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨901767038500,0,false,-217994860864,-217994860800⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1296830798660,0,true,181482458432,181482458496⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨902192456892,0,false,-217476276608,-217476276544⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1297107908611,0,true,181717379648,181717379712⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨901915346941,0,false,-217814045376,-217814045312⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587469590,0,true,75839168,75839232⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435785962,0,false,-75844480,-75844416⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099612873715,0,true,101241216,101241280⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099410381837,0,false,-101250624,-101250560⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511618453,0,false,-9344,-9280⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622545,0,false,-5248,-5184⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1296929553065,0,true,181566183680,181566183744⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨902093702487,0,false,-217596636224,-217596636160⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1297182071985,0,true,181780243456,181780243520⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨901841183567,0,false,-217904460544,-217904460480⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1063974391491,0,false,-36124217024,-36124216960⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1064065129312,0,false,-36030452544,-36030452480⟩
    { al := (735807/4096000), au := (46041/256000), zl := (999/1000), zu := (3997/4000),
      A := ⟨197516687572,197744589276⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181649909248,181649909312⟩ : DyadicInterval 40),(⟨-217717018688,-217717018624⟩ : DyadicInterval 40),(⟨744285724753,744285744082⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181843088192,181843088256⟩ : DyadicInterval 40),(⟨-217994860864,-217994860800⟩ : DyadicInterval 40),(⟨744244310878,744244330208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181482458432,181482458496⟩ : DyadicInterval 40),(⟨-217476276608,-217476276544⟩ : DyadicInterval 40),(⟨744321577634,744321596964⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181717379648,181717379712⟩ : DyadicInterval 40),(⟨-217814045376,-217814045312⟩ : DyadicInterval 40),(⟨744271266767,744271286096⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨75841814,101245939⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75839168,75839232⟩ : DyadicInterval 40),(⟨-75844480,-75844416⟩ : DyadicInterval 40),(⟨762123380976,762123400305⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨101241216,101241280⟩ : DyadicInterval 40),(⟨-101250624,-101250560⟩ : DyadicInterval 40),(⟨762123378932,762123398262⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-9344,-5184⟩ : DyadicInterval 40),(⟨762123386208,762123407552⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨197417925289,197670444209⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181566183680,181566183744⟩ : DyadicInterval 40),(⟨-217596636224,-217596636160⟩ : DyadicInterval 40),(⟨744303656482,744303675812⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181780243456,181780243520⟩ : DyadicInterval 40),(⟨-217904460544,-217904460480⟩ : DyadicInterval 40),(⟨744257789747,744257809076⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-36124217024,-36030452480⟩ : DyadicInterval 40),(⟨780138609856,780185511392⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨181649909248,181843088256⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-217994860864,-217717018624⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e754_ok : ecellOkT e754 = true := by decide +kernel
theorem e754_pos {a z : ℝ} (ha1 : ((735807/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((46041/256000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e754 e754_ok ha1 ha2 hz1 hz2 hz

-- box ['367479/2048000', '735807/4096000', '3997/4000', '1999/2000']  interval_lower 29430961/274877906944
noncomputable def e755 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1296800413646,0,true,181456696320,181456696384⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨902222841906,0,false,-217439246656,-217439246592⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1297028315349,0,true,181649909248,181649909312⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨901994940203,0,false,-217717018688,-217717018624⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1296652447056,0,true,181331233472,181331233536⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨902370808496,0,false,-217258939072,-217258939008⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1296929557006,0,true,181566187008,181566187072⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨902093698546,0,false,-217596641024,-217596640960⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099562128060,0,true,50499072,50499136⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099461127492,0,false,-50501504,-50501440⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587471020,0,true,75840576,75840640⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435784532,0,false,-75845888,-75845824⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622544,0,false,-5248,-5184⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625457,0,false,-2368,-2304⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1296726425905,0,true,181393962944,181393963008⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨902296829647,0,false,-217349083776,-217349083712⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1296978944968,0,true,181608056384,181608056448⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨902044310584,0,false,-217656838912,-217656838848⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1064047390405,0,false,-36048782528,-36048782464⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1064138034975,0,false,-35955120832,-35955120768⟩
    { al := (367479/2048000), au := (735807/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨197288785870,197516687573⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181456696320,181456696384⟩ : DyadicInterval 40),(⟨-217439246656,-217439246592⟩ : DyadicInterval 40),(⟨744327089816,744327109145⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181649909248,181649909312⟩ : DyadicInterval 40),(⟨-217717018688,-217717018624⟩ : DyadicInterval 40),(⟨744285724753,744285744082⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181331233472,181331233536⟩ : DyadicInterval 40),(⟨-217258939072,-217258939008⟩ : DyadicInterval 40),(⟨744353920219,744353939549⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181566187008,181566187072⟩ : DyadicInterval 40),(⟨-217596641024,-217596640960⟩ : DyadicInterval 40),(⟨744303655773,744303675103⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨50500284,75843244⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨50499072,50499136⟩ : DyadicInterval 40),(⟨-50501504,-50501440⟩ : DyadicInterval 40),(⟨762123382448,762123401777⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75840576,75840640⟩ : DyadicInterval 40),(⟨-75845888,-75845824⟩ : DyadicInterval 40),(⟨762123380976,762123400305⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5248,-2304⟩ : DyadicInterval 40),(⟨762123384768,762123405504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨197214798129,197467317192⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181393962944,181393963008⟩ : DyadicInterval 40),(⟨-217349083776,-217349083712⟩ : DyadicInterval 40),(⟨744340508389,744340527719⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181608056384,181608056448⟩ : DyadicInterval 40),(⟨-217656838912,-217656838848⟩ : DyadicInterval 40),(⟨744294689804,744294709134⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-36048782528,-35955120768⟩ : DyadicInterval 40),(⟨780100944000,780147794144⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨181456696320,181649909312⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-217717018688,-217439246592⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e755_ok : ecellOkT e755 = true := by decide +kernel
theorem e755_pos {a z : ℝ} (ha1 : ((367479/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((735807/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e755 e755_ok ha1 ha2 hz1 hz2 hz

-- box ['735807/4096000', '46041/256000', '3997/4000', '1999/2000']  interval_lower 60405621/549755813888
noncomputable def e756 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1297028315348,0,true,181649909248,181649909312⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨901994940204,0,false,-217717018688,-217717018624⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1297256217052,0,true,181843088192,181843088256⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨901767038500,0,false,-217994860864,-217994860800⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1296880177832,0,true,181524323520,181524323584⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨902143077720,0,false,-217536457152,-217536457088⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1297157344758,0,true,181759284096,181759284160⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨901865910794,0,false,-217874313856,-217874313792⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099562189204,0,true,50560256,50560320⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099461066348,0,false,-50562624,-50562560⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587562753,0,true,75932352,75932416⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435692799,0,false,-75937600,-75937536⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622531,0,false,-5248,-5184⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625451,0,false,-2368,-2304⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1296954242145,0,true,181587114368,181587114432⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨902069013407,0,false,-217626728768,-217626728704⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1297206789697,0,true,181801194368,181801194432⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨901816465855,0,false,-217934596416,-217934596352⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1063965503424,0,false,-36133402048,-36133401984⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1064056262882,0,false,-36039614400,-36039614336⟩
    { al := (735807/4096000), au := (46041/256000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨197516687572,197744589276⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181649909248,181649909312⟩ : DyadicInterval 40),(⟨-217717018688,-217717018624⟩ : DyadicInterval 40),(⟨744285724753,744285744082⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181843088192,181843088256⟩ : DyadicInterval 40),(⟨-217994860864,-217994860800⟩ : DyadicInterval 40),(⟨744244310878,744244330208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181524323520,181524323584⟩ : DyadicInterval 40),(⟨-217536457152,-217536457088⟩ : DyadicInterval 40),(⟨744312617841,744312637170⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181759284096,181759284160⟩ : DyadicInterval 40),(⟨-217874313856,-217874313792⟩ : DyadicInterval 40),(⟨744262283747,744262303077⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨50561428,75934977⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨50560256,50560320⟩ : DyadicInterval 40),(⟨-50562624,-50562560⟩ : DyadicInterval 40),(⟨762123382410,762123401739⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75932352,75932416⟩ : DyadicInterval 40),(⟨-75937600,-75937536⟩ : DyadicInterval 40),(⟨762123380931,762123400260⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5248,-2304⟩ : DyadicInterval 40),(⟨762123384768,762123405504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨197442614369,197695161921⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181587114368,181587114432⟩ : DyadicInterval 40),(⟨-217626728768,-217626728704⟩ : DyadicInterval 40),(⟨744299174695,744299194024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181801194368,181801194432⟩ : DyadicInterval 40),(⟨-217934596416,-217934596352⟩ : DyadicInterval 40),(⟨744253296874,744253316204⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-36133402048,-36039614336⟩ : DyadicInterval 40),(⟨780143190784,780190103904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨181649909248,181843088256⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-217994860864,-217717018624⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e756_ok : ecellOkT e756 = true := by decide +kernel
theorem e756_pos {a z : ℝ} (ha1 : ((735807/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((46041/256000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e756 e756_ok ha1 ha2 hz1 hz2 hz

-- box ['36663/204800', '734109/4096000', '1999/2000', '3999/4000']  interval_lower 55501817/549755813888
noncomputable def e757 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1296344610242,0,true,181070168640,181070168704⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨902678645310,0,false,-216883913152,-216883913088⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1296572511945,0,true,181263449472,181263449536⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨902450743607,0,false,-217161544896,-217161544832⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1296246193750,0,true,180986692288,180986692352⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨902777061802,0,false,-216764043072,-216764043008⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1296523246725,0,true,181221671104,181221671168⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨902500008827,0,false,-217101523648,-217101523584⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536816810,0,true,25188736,25188800⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486438742,0,false,-25189376,-25189312⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099562068046,0,true,50439104,50439168⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099461187506,0,false,-50441472,-50441408⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625462,0,false,-2368,-2304⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627199,0,false,-640,-576⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1296295397197,0,true,181028427200,181028427264⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨902727858355,0,false,-216823970624,-216823970560⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1296547887901,0,true,181242567744,181242567808⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨902475367651,0,false,-217131544256,-217131544192⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1064202053212,0,false,-35888976512,-35888976448⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1064292489634,0,false,-35795543424,-35795543360⟩
    { al := (36663/204800), au := (734109/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨196832982466,197060884169⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181070168640,181070168704⟩ : DyadicInterval 40),(⟨-216883913152,-216883913088⟩ : DyadicInterval 40),(⟨744409673530,744409692860⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181263449472,181263449536⟩ : DyadicInterval 40),(⟨-217161544896,-217161544832⟩ : DyadicInterval 40),(⟨744368406094,744368425423⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨180986692288,180986692352⟩ : DyadicInterval 40),(⟨-216764043072,-216764043008⟩ : DyadicInterval 40),(⟨744427479249,744427498579⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181221671104,181221671168⟩ : DyadicInterval 40),(⟨-217101523648,-217101523584⟩ : DyadicInterval 40),(⟨744377330939,744377350269⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨25189034,50440270⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25188736,25188800⟩ : DyadicInterval 40),(⟨-25189376,-25189312⟩ : DyadicInterval 40),(⟨762123383294,762123402623⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨50439104,50439168⟩ : DyadicInterval 40),(⟨-50441472,-50441408⟩ : DyadicInterval 40),(⟨762123382421,762123401751⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2368,-576⟩ : DyadicInterval 40),(⟨762123383904,762123404064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨196783769421,197036260125⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181028427200,181028427264⟩ : DyadicInterval 40),(⟨-216823970624,-216823970560⟩ : DyadicInterval 40),(⟨744418578383,744418597713⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181242567744,181242567808⟩ : DyadicInterval 40),(⟨-217131544256,-217131544192⟩ : DyadicInterval 40),(⟨744372867236,744372886566⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-35888976512,-35795543360⟩ : DyadicInterval 40),(⟨780021155296,780067891136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨181070168640,181263449536⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-217161544896,-216883913088⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e757_ok : ecellOkT e757 = true := by decide +kernel
theorem e757_pos {a z : ℝ} (ha1 : ((36663/204800 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((734109/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e757 e757_ok ha1 ha2 hz1 hz2 hz

-- box ['734109/4096000', '367479/2048000', '1999/2000', '3999/4000']  interval_lower 28514901/274877906944
noncomputable def e758 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1296572511944,0,true,181263449472,181263449536⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨902450743608,0,false,-217161544832,-217161544768⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1296800413647,0,true,181456696320,181456696384⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨902222841905,0,false,-217439246720,-217439246656⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1296473981501,0,true,181179891136,181179891200⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨902549274051,0,false,-217041505664,-217041505600⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1296751091451,0,true,181414876992,181414877056⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨902272164101,0,false,-217379140864,-217379140800⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536847373,0,true,25219264,25219328⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486408179,0,false,-25219904,-25219840⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099562129183,0,true,50500224,50500288⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099461126369,0,false,-50502592,-50502528⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625456,0,false,-2368,-2304⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627198,0,false,-640,-576⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1296523241922,0,true,181221667008,181221667072⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨902500013630,0,false,-217101517760,-217101517696⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1296775761117,0,true,181435794112,181435794176⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨902247494435,0,false,-217409203776,-217409203712⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1064120334660,0,false,-35973409664,-35973409600⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1064210885949,0,false,-35879850752,-35879850688⟩
    { al := (734109/4096000), au := (367479/2048000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨197060884168,197288785871⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181263449472,181263449536⟩ : DyadicInterval 40),(⟨-217161544832,-217161544768⟩ : DyadicInterval 40),(⟨744368406068,744368425397⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181456696320,181456696384⟩ : DyadicInterval 40),(⟨-217439246720,-217439246656⟩ : DyadicInterval 40),(⟨744327089842,744327109172⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181179891136,181179891200⟩ : DyadicInterval 40),(⟨-217041505664,-217041505600⟩ : DyadicInterval 40),(⟨744386253507,744386272837⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181414876992,181414877056⟩ : DyadicInterval 40),(⟨-217379140864,-217379140800⟩ : DyadicInterval 40),(⟨744336035560,744336054890⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨25219597,50501407⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25219264,25219328⟩ : DyadicInterval 40),(⟨-25219904,-25219840⟩ : DyadicInterval 40),(⟨762123383293,762123402622⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨50500224,50500288⟩ : DyadicInterval 40),(⟨-50502592,-50502528⟩ : DyadicInterval 40),(⟨762123382416,762123401745⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2368,-576⟩ : DyadicInterval 40),(⟨762123383904,762123404064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨197011614146,197264133341⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181221667008,181221667072⟩ : DyadicInterval 40),(⟨-217101517760,-217101517696⟩ : DyadicInterval 40),(⟨744377331808,744377351137⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181435794112,181435794176⟩ : DyadicInterval 40),(⟨-217409203776,-217409203712⟩ : DyadicInterval 40),(⟨744331561418,744331580747⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-35973409664,-35879850688⟩ : DyadicInterval 40),(⟨780063308960,780110107712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨181263449472,181456696384⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-217439246720,-217161544768⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e758_ok : ecellOkT e758 = true := by decide +kernel
theorem e758_pos {a z : ℝ} (ha1 : ((734109/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((367479/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e758 e758_ok ha1 ha2 hz1 hz2 hz

-- box ['36663/204800', '734109/4096000', '3999/4000', '1']  interval_lower 110414439/1099511627776
noncomputable def e759 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1296344610242,0,true,181070168640,181070168704⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨902678645310,0,false,-216883913152,-216883913088⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1296572511945,0,true,181263449472,181263449536⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨902450743607,0,false,-217161544896,-217161544832⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1296295401996,0,true,181028431232,181028431296⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨902727853556,0,false,-216823976448,-216823976384⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536848191,0,true,25220096,25220160⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486407361,0,false,-25220736,-25220672⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627197,0,false,-640,-576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1296320001103,0,true,181049295936,181049296000⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨902703254449,0,false,-216853938304,-216853938240⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1296572520436,0,true,181263456704,181263456768⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨902450735116,0,false,-217161555200,-217161555136⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1064193224191,0,false,-35898098496,-35898098432⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1064283682175,0,false,-35804642368,-35804642304⟩
    { al := (36663/204800), au := (734109/4096000), zl := (3999/4000), zu := 1,
      A := ⟨196832982466,197060884169⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181070168640,181070168704⟩ : DyadicInterval 40),(⟨-216883913152,-216883913088⟩ : DyadicInterval 40),(⟨744409673530,744409692860⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181263449472,181263449536⟩ : DyadicInterval 40),(⟨-217161544896,-217161544832⟩ : DyadicInterval 40),(⟨744368406094,744368425423⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181028431232,181028431296⟩ : DyadicInterval 40),(⟨-216823976448,-216823976384⟩ : DyadicInterval 40),(⟨744418577529,744418596858⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181263449472,181263449536⟩ : DyadicInterval 40),(⟨-217161544896,-217161544832⟩ : DyadicInterval 40),(⟨744368406094,744368425423⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,25220415⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25220096,25220160⟩ : DyadicInterval 40),(⟨-25220736,-25220672⟩ : DyadicInterval 40),(⟨762123383293,762123402622⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-640,0⟩ : DyadicInterval 40),(⟨762123383616,762123403200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨196808373327,197060892660⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181049295936,181049296000⟩ : DyadicInterval 40),(⟨-216853938304,-216853938240⟩ : DyadicInterval 40),(⟨744414126697,744414146027⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181263456704,181263456768⟩ : DyadicInterval 40),(⟨-217161555200,-217161555136⟩ : DyadicInterval 40),(⟨744368404520,744368423849⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-35898098496,-35804642304⟩ : DyadicInterval 40),(⟨780025704768,780072452128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨181070168640,181263449536⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-217161544896,-216883913088⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e759_ok : ecellOkT e759 = true := by decide +kernel
theorem e759_pos {a z : ℝ} (ha1 : ((36663/204800 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((734109/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e759 e759_ok ha1 ha2 hz1 hz2 hz

-- box ['734109/4096000', '367479/2048000', '3999/4000', '1']  interval_lower 113467895/1099511627776
noncomputable def e760 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1296572511944,0,true,181263449472,181263449536⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨902450743608,0,false,-217161544832,-217161544768⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1296800413647,0,true,181456696320,181456696384⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨902222841905,0,false,-217439246720,-217439246656⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1296523246722,0,true,181221671104,181221671168⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨902500008830,0,false,-217101523648,-217101523584⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536878760,0,true,25250688,25250752⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486376792,0,false,-25251328,-25251264⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627196,0,false,-640,-576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1296547874314,0,true,181242556224,181242556288⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨902475381238,0,false,-217131527744,-217131527680⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1296800422139,0,true,181456703552,181456703616⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨902222833413,0,false,-217439257024,-217439256960⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1064111485205,0,false,-35982553472,-35982553408⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1064202058083,0,false,-35888971456,-35888971392⟩
    { al := (734109/4096000), au := (367479/2048000), zl := (3999/4000), zu := 1,
      A := ⟨197060884168,197288785871⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181263449472,181263449536⟩ : DyadicInterval 40),(⟨-217161544832,-217161544768⟩ : DyadicInterval 40),(⟨744368406068,744368425397⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181456696320,181456696384⟩ : DyadicInterval 40),(⟨-217439246720,-217439246656⟩ : DyadicInterval 40),(⟨744327089842,744327109172⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181221671104,181221671168⟩ : DyadicInterval 40),(⟨-217101523648,-217101523584⟩ : DyadicInterval 40),(⟨744377330940,744377350269⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181456696320,181456696384⟩ : DyadicInterval 40),(⟨-217439246720,-217439246656⟩ : DyadicInterval 40),(⟨744327089842,744327109172⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,25250984⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25250688,25250752⟩ : DyadicInterval 40),(⟨-25251328,-25251264⟩ : DyadicInterval 40),(⟨762123383292,762123402621⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-640,0⟩ : DyadicInterval 40),(⟨762123383616,762123403200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨197036246538,197288794363⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181242556224,181242556288⟩ : DyadicInterval 40),(⟨-217131527744,-217131527680⟩ : DyadicInterval 40),(⟨744372869713,744372889043⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181456703552,181456703616⟩ : DyadicInterval 40),(⟨-217439257024,-217439256960⟩ : DyadicInterval 40),(⟨744327088264,744327107594⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-35982553472,-35888971392⟩ : DyadicInterval 40),(⟨780067869312,780114679616⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨181263449472,181456696384⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-217439246720,-217161544768⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e760_ok : ecellOkT e760 = true := by decide +kernel
theorem e760_pos {a z : ℝ} (ha1 : ((734109/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((367479/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e760 e760_ok ha1 ha2 hz1 hz2 hz

-- box ['367479/2048000', '735807/4096000', '1999/2000', '3999/4000']  interval_lower 117130279/1099511627776
noncomputable def e761 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1296800413646,0,true,181456696320,181456696384⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨902222841906,0,false,-217439246656,-217439246592⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1297028315349,0,true,181649909248,181649909312⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨901994940203,0,false,-217717018688,-217717018624⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1296701769253,0,true,181373056000,181373056064⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨902321486299,0,false,-217319038336,-217319038272⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1296978936178,0,true,181608048896,181608048960⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨902044319374,0,false,-217656828224,-217656828160⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536877941,0,true,25249856,25249920⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486377611,0,false,-25250496,-25250432⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099562190329,0,true,50561344,50561408⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099461065223,0,false,-50563776,-50563712⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625450,0,false,-2368,-2304⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627197,0,false,-640,-576⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1296751086640,0,true,181414872896,181414872960⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨902272168912,0,false,-217379134976,-217379134912⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1297003634333,0,true,181628986560,181628986624⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨902019621219,0,false,-217686933504,-217686933440⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1064038521654,0,false,-36057946880,-36057946816⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1064129187837,0,false,-35964262080,-35964262016⟩
    { al := (367479/2048000), au := (735807/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨197288785870,197516687573⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181456696320,181456696384⟩ : DyadicInterval 40),(⟨-217439246656,-217439246592⟩ : DyadicInterval 40),(⟨744327089816,744327109145⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181649909248,181649909312⟩ : DyadicInterval 40),(⟨-217717018688,-217717018624⟩ : DyadicInterval 40),(⟨744285724753,744285744082⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181373056000,181373056064⟩ : DyadicInterval 40),(⟨-217319038336,-217319038272⟩ : DyadicInterval 40),(⟨744344979053,744344998383⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181608048896,181608048960⟩ : DyadicInterval 40),(⟨-217656828224,-217656828160⟩ : DyadicInterval 40),(⟨744294691432,744294710761⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨25250165,50562553⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25249856,25249920⟩ : DyadicInterval 40),(⟨-25250496,-25250432⟩ : DyadicInterval 40),(⟨762123383292,762123402621⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨50561344,50561408⟩ : DyadicInterval 40),(⟨-50563776,-50563712⟩ : DyadicInterval 40),(⟨762123382442,762123401771⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2368,-576⟩ : DyadicInterval 40),(⟨762123383904,762123404064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨197239458864,197492006557⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181414872896,181414872960⟩ : DyadicInterval 40),(⟨-217379134976,-217379134912⟩ : DyadicInterval 40),(⟨744336036432,744336055762⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181628986560,181628986624⟩ : DyadicInterval 40),(⟨-217686933504,-217686933440⟩ : DyadicInterval 40),(⟨744290206814,744290226144⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-36057946880,-35964262016⟩ : DyadicInterval 40),(⟨780105514624,780152376320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨181456696320,181649909312⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-217717018688,-217439246592⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e761_ok : ecellOkT e761 = true := by decide +kernel
theorem e761_pos {a z : ℝ} (ha1 : ((367479/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((735807/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e761 e761_ok ha1 ha2 hz1 hz2 hz

-- box ['735807/4096000', '46041/256000', '1999/2000', '3999/4000']  interval_lower 3756729/34359738368
noncomputable def e762 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1297028315348,0,true,181649909248,181649909312⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨901994940204,0,false,-217717018688,-217717018624⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1297256217052,0,true,181843088192,181843088256⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨901767038500,0,false,-217994860864,-217994860800⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1296929557004,0,true,181566187008,181566187072⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨902093698548,0,false,-217596641024,-217596640960⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1297206780905,0,true,181801186944,181801187008⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨901816474647,0,false,-217934585728,-217934585664⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536908513,0,true,25280384,25280448⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486347039,0,false,-25281088,-25281024⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099562251486,0,true,50622528,50622592⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099461004066,0,false,-50624896,-50624832⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625445,0,false,-2368,-2304⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627195,0,false,-640,-576⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1296978931367,0,true,181608044864,181608044928⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨902044324185,0,false,-217656822336,-217656822272⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1297231507551,0,true,181822145024,181822145088⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨901791748001,0,false,-217964733312,-217964733248⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1063956614194,0,false,-36142588288,-36142588224⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1064047395291,0,false,-36048777472,-36048777408⟩
    { al := (735807/4096000), au := (46041/256000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨197516687572,197744589276⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181649909248,181649909312⟩ : DyadicInterval 40),(⟨-217717018688,-217717018624⟩ : DyadicInterval 40),(⟨744285724753,744285744082⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181843088192,181843088256⟩ : DyadicInterval 40),(⟨-217994860864,-217994860800⟩ : DyadicInterval 40),(⟨744244310878,744244330208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181566187008,181566187072⟩ : DyadicInterval 40),(⟨-217596641024,-217596640960⟩ : DyadicInterval 40),(⟨744303655774,744303675103⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181801186944,181801187008⟩ : DyadicInterval 40),(⟨-217934585728,-217934585664⟩ : DyadicInterval 40),(⟨744253298469,744253317798⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨25280737,50623710⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25280384,25280448⟩ : DyadicInterval 40),(⟨-25281088,-25281024⟩ : DyadicInterval 40),(⟨762123383322,762123402651⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨50622528,50622592⟩ : DyadicInterval 40),(⟨-50624896,-50624832⟩ : DyadicInterval 40),(⟨762123382405,762123401734⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2368,-576⟩ : DyadicInterval 40),(⟨762123383904,762123404064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨197467303591,197719879775⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181608044864,181608044928⟩ : DyadicInterval 40),(⟨-217656822336,-217656822272⟩ : DyadicInterval 40),(⟨744294692269,744294711598⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181822145024,181822145088⟩ : DyadicInterval 40),(⟨-217964733312,-217964733248⟩ : DyadicInterval 40),(⟨744248803398,744248822728⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-36142588288,-36048777408⟩ : DyadicInterval 40),(⟨780147772320,780194697024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨181649909248,181843088256⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-217994860864,-217717018624⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e762_ok : ecellOkT e762 = true := by decide +kernel
theorem e762_pos {a z : ℝ} (ha1 : ((735807/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((46041/256000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e762 e762_ok ha1 ha2 hz1 hz2 hz

-- box ['367479/2048000', '735807/4096000', '3999/4000', '1']  interval_lower 116536017/1099511627776
noncomputable def e763 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1296800413646,0,true,181456696320,181456696384⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨902222841906,0,false,-217439246656,-217439246592⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1297028315349,0,true,181649909248,181649909312⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨901994940203,0,false,-217717018688,-217717018624⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1296751091449,0,true,181414876992,181414877056⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨902272164103,0,false,-217379140864,-217379140800⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536909333,0,true,25281216,25281280⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486346219,0,false,-25281856,-25281792⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627194,0,false,-640,-576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1296775747525,0,true,181435782592,181435782656⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨902247508027,0,false,-217409187264,-217409187200⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1297028323848,0,true,181649916416,181649916480⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨901994931704,0,false,-217717029056,-217717028992⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1064029651740,0,false,-36067112576,-36067112512⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1064120339538,0,false,-35973404608,-35973404544⟩
    { al := (367479/2048000), au := (735807/4096000), zl := (3999/4000), zu := 1,
      A := ⟨197288785870,197516687573⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181456696320,181456696384⟩ : DyadicInterval 40),(⟨-217439246656,-217439246592⟩ : DyadicInterval 40),(⟨744327089816,744327109145⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181649909248,181649909312⟩ : DyadicInterval 40),(⟨-217717018688,-217717018624⟩ : DyadicInterval 40),(⟨744285724753,744285744082⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181414876992,181414877056⟩ : DyadicInterval 40),(⟨-217379140864,-217379140800⟩ : DyadicInterval 40),(⟨744336035560,744336054890⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181649909248,181649909312⟩ : DyadicInterval 40),(⟨-217717018688,-217717018624⟩ : DyadicInterval 40),(⟨744285724753,744285744082⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,25281557⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25281216,25281280⟩ : DyadicInterval 40),(⟨-25281856,-25281792⟩ : DyadicInterval 40),(⟨762123383290,762123402619⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-640,0⟩ : DyadicInterval 40),(⟨762123383616,762123403200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨197264119749,197516696072⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181435782592,181435782656⟩ : DyadicInterval 40),(⟨-217409187264,-217409187200⟩ : DyadicInterval 40),(⟨744331563902,744331583231⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181649916416,181649916480⟩ : DyadicInterval 40),(⟨-217717029056,-217717028992⟩ : DyadicInterval 40),(⟨744285723234,744285742563⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-36067112576,-35973404544⟩ : DyadicInterval 40),(⟨780110085888,780156959168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨181456696320,181649909312⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-217717018688,-217439246592⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e763_ok : ecellOkT e763 = true := by decide +kernel
theorem e763_pos {a z : ℝ} (ha1 : ((367479/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((735807/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e763 e763_ok ha1 ha2 hz1 hz2 hz

-- box ['735807/4096000', '46041/256000', '3999/4000', '1']  interval_lower 119618915/1099511627776
noncomputable def e764 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1297028315348,0,true,181649909248,181649909312⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨901994940204,0,false,-217717018688,-217717018624⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1297256217052,0,true,181843088192,181843088256⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨901767038500,0,false,-217994860864,-217994860800⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1296978936176,0,true,181608048896,181608048960⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨902044319376,0,false,-217656828224,-217656828160⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536939912,0,true,25311808,25311872⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486315640,0,false,-25312448,-25312384⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627193,0,false,-640,-576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1297003620732,0,true,181628974976,181628975040⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨902019634820,0,false,-217686916864,-217686916800⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1297256225551,0,true,181843095360,181843095424⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨901767030001,0,false,-217994871232,-217994871168⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1063947723801,0,false,-36151775808,-36151775744⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1064038526541,0,false,-36057941888,-36057941824⟩
    { al := (735807/4096000), au := (46041/256000), zl := (3999/4000), zu := 1,
      A := ⟨197516687572,197744589276⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181649909248,181649909312⟩ : DyadicInterval 40),(⟨-217717018688,-217717018624⟩ : DyadicInterval 40),(⟨744285724753,744285744082⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181843088192,181843088256⟩ : DyadicInterval 40),(⟨-217994860864,-217994860800⟩ : DyadicInterval 40),(⟨744244310878,744244330208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181608048896,181608048960⟩ : DyadicInterval 40),(⟨-217656828224,-217656828160⟩ : DyadicInterval 40),(⟨744294691432,744294710762⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181843088192,181843088256⟩ : DyadicInterval 40),(⟨-217994860864,-217994860800⟩ : DyadicInterval 40),(⟨744244310878,744244330208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,25312136⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25311808,25311872⟩ : DyadicInterval 40),(⟨-25312448,-25312384⟩ : DyadicInterval 40),(⟨762123383289,762123402618⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-640,0⟩ : DyadicInterval 40),(⟨762123383616,762123403200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨197491992956,197744597775⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181628974976,181628975040⟩ : DyadicInterval 40),(⟨-217686916864,-217686916800⟩ : DyadicInterval 40),(⟨744290209291,744290228620⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181843095360,181843095424⟩ : DyadicInterval 40),(⟨-217994871232,-217994871168⟩ : DyadicInterval 40),(⟨744244309356,744244328686⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-36151775808,-36057941824⟩ : DyadicInterval 40),(⟨780152354528,780199290784⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨181649909248,181843088256⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-217994860864,-217717018624⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e764_ok : ecellOkT e764 = true := by decide +kernel
theorem e764_pos {a z : ℝ} (ha1 : ((735807/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((46041/256000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e764 e764_ok ha1 ha2 hz1 hz2 hz

-- box ['46041/256000', '147501/819200', '999/1000', '3997/4000']  interval_lower 124511197/1099511627776
noncomputable def e765 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1297256217051,0,true,181843088192,181843088256⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨901767038501,0,false,-217994860864,-217994860800⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1297484118754,0,true,182036233152,182036233216⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨901539136798,0,false,-218272773248,-218272773184⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1297058472461,0,true,181675473600,181675473664⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨901964783091,0,false,-217753780096,-217753780032⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1297335639386,0,true,181910401856,181910401920⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨901687616166,0,false,-218091703616,-218091703552⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587561319,0,true,75930880,75930944⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435694233,0,false,-75936192,-75936128⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099612996044,0,true,101363584,101363648⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099410259508,0,false,-101372992,-101372928⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511618430,0,false,-9408,-9344⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622532,0,false,-5248,-5184⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1297157340818,0,true,181759280704,181759280768⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨901865914734,0,false,-217874309056,-217874308992⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1297409888223,0,true,181973327104,181973327168⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨901613367329,0,false,-218182245888,-218182245824⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1063892430581,0,false,-36208918784,-36208918720⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1063983283285,0,false,-36115028288,-36115028224⟩
    { al := (46041/256000), au := (147501/819200), zl := (999/1000), zu := (3997/4000),
      A := ⟨197744589275,197972490978⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181843088192,181843088256⟩ : DyadicInterval 40),(⟨-217994860864,-217994860800⟩ : DyadicInterval 40),(⟨744244310878,744244330208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182036233152,182036233216⟩ : DyadicInterval 40),(⟨-218272773248,-218272773184⟩ : DyadicInterval 40),(⟨744202848208,744202867537⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181675473600,181675473664⟩ : DyadicInterval 40),(⟨-217753780096,-217753780032⟩ : DyadicInterval 40),(⟨744280247449,744280266779⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181910401856,181910401920⟩ : DyadicInterval 40),(⟨-218091703616,-218091703552⟩ : DyadicInterval 40),(⟨744229866935,744229886264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨75933543,101368268⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨75930880,75930944⟩ : DyadicInterval 40),(⟨-75936192,-75936128⟩ : DyadicInterval 40),(⟨762123380963,762123400293⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨101363584,101363648⟩ : DyadicInterval 40),(⟨-101372992,-101372928⟩ : DyadicInterval 40),(⟨762123378910,762123398239⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-9408,-5184⟩ : DyadicInterval 40),(⟨762123386208,762123407584⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨197645713042,197898260447⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181759280704,181759280768⟩ : DyadicInterval 40),(⟨-217874309056,-217874308992⟩ : DyadicInterval 40),(⟨744262284496,744262303825⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181973327104,181973327168⟩ : DyadicInterval 40),(⟨-218182245888,-218182245824⟩ : DyadicInterval 40),(⟨744216358479,744216377809⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-36208918784,-36115028224⟩ : DyadicInterval 40),(⟨780180897728,780227862272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨181843088192,182036233216⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-218272773248,-217994860800⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e765_ok : ecellOkT e765 = true := by decide +kernel
theorem e765_pos {a z : ℝ} (ha1 : ((46041/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((147501/819200 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e765 e765_ok ha1 ha2 hz1 hz2 hz

-- box ['147501/819200', '369177/2048000', '999/1000', '3997/4000']  interval_lower 127630737/1099511627776
noncomputable def e766 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1297484118753,0,true,182036233152,182036233216⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨901539136799,0,false,-218272773248,-218272773184⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1297712020456,0,true,182229344256,182229344320⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨901311235096,0,false,-218550755904,-218550755840⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1297286146261,0,true,181868454912,181868454976⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨901737109291,0,false,-218031353728,-218031353664⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1297563370162,0,true,182103390208,182103390272⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨901459885390,0,false,-218369432000,-218369431936⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587653066,0,true,76022656,76022720⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435602486,0,false,-76027968,-76027904⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099613118394,0,true,101485888,101485952⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099410137158,0,false,-101495360,-101495296⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511618407,0,false,-9408,-9344⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622520,0,false,-5312,-5248⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1297385128564,0,true,181952343872,181952343936⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨901638126988,0,false,-218152052032,-218152051968⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1297637704467,0,true,182166376768,182166376832⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨901385551085,0,false,-218460101376,-218460101312⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1063810375262,0,false,-36293724544,-36293724480⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1063901342878,0,false,-36199708096,-36199708032⟩
    { al := (147501/819200), au := (369177/2048000), zl := (999/1000), zu := (3997/4000),
      A := ⟨197972490977,198200392680⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182036233152,182036233216⟩ : DyadicInterval 40),(⟨-218272773248,-218272773184⟩ : DyadicInterval 40),(⟨744202848208,744202867537⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182229344256,182229344320⟩ : DyadicInterval 40),(⟨-218550755904,-218550755840⟩ : DyadicInterval 40),(⟨744161336680,744161356010⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181868454912,181868454976⟩ : DyadicInterval 40),(⟨-218031353728,-218031353664⟩ : DyadicInterval 40),(⟨744238868572,744238887901⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182103390208,182103390272⟩ : DyadicInterval 40),(⟨-218369432000,-218369431936⟩ : DyadicInterval 40),(⟨744188418346,744188437676⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨76025290,101490618⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76022656,76022720⟩ : DyadicInterval 40),(⟨-76027968,-76027904⟩ : DyadicInterval 40),(⟨762123380951,762123400280⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨101485888,101485952⟩ : DyadicInterval 40),(⟨-101495360,-101495296⟩ : DyadicInterval 40),(⟨762123378919,762123398249⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-9408,-5248⟩ : DyadicInterval 40),(⟨762123386240,762123407584⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨197873500788,198126076691⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181952343872,181952343936⟩ : DyadicInterval 40),(⟨-218152052032,-218152051968⟩ : DyadicInterval 40),(⟨744220863714,744220883044⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182166376768,182166376832⟩ : DyadicInterval 40),(⟨-218460101376,-218460101312⟩ : DyadicInterval 40),(⟨744174878454,744174897783⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-36293724544,-36199708032⟩ : DyadicInterval 40),(⟨780223237632,780270265152⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨182036233152,182229344320⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-218550755904,-218272773184⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e766_ok : ecellOkT e766 = true := by decide +kernel
theorem e766_pos {a z : ℝ} (ha1 : ((147501/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((369177/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e766 e766_ok ha1 ha2 hz1 hz2 hz

-- box ['46041/256000', '147501/819200', '3997/4000', '1999/2000']  interval_lower 61956723/549755813888
noncomputable def e767 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1297256217051,0,true,181843088192,181843088256⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨901767038501,0,false,-217994860864,-217994860800⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1297484118754,0,true,182036233152,182036233216⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨901539136798,0,false,-218272773248,-218272773184⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1297107908609,0,true,181717379648,181717379712⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨901915346943,0,false,-217814045376,-217814045312⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1297385132509,0,true,181952347200,181952347264⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨901638123043,0,false,-218152056832,-218152056768⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099562250359,0,true,50621376,50621440⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099461005193,0,false,-50623808,-50623744⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587654502,0,true,76024064,76024128⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435601050,0,false,-76029376,-76029312⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622519,0,false,-5312,-5248⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625446,0,false,-2368,-2304⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1297182058379,0,true,181780231936,181780232000⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨901841197173,0,false,-217904443968,-217904443904⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1297434634418,0,true,181994298432,181994298496⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨901588621134,0,false,-218212424128,-218212424064⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1063883522016,0,false,-36218125632,-36218125568⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1063974396384,0,false,-36124211968,-36124211904⟩
    { al := (46041/256000), au := (147501/819200), zl := (3997/4000), zu := (1999/2000),
      A := ⟨197744589275,197972490978⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181843088192,181843088256⟩ : DyadicInterval 40),(⟨-217994860864,-217994860800⟩ : DyadicInterval 40),(⟨744244310878,744244330208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182036233152,182036233216⟩ : DyadicInterval 40),(⟨-218272773248,-218272773184⟩ : DyadicInterval 40),(⟨744202848208,744202867537⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181717379648,181717379712⟩ : DyadicInterval 40),(⟨-217814045376,-217814045312⟩ : DyadicInterval 40),(⟨744271266767,744271286097⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181952347200,181952347264⟩ : DyadicInterval 40),(⟨-218152056832,-218152056768⟩ : DyadicInterval 40),(⟨744220863001,744220882331⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨50622583,76026726⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨50621376,50621440⟩ : DyadicInterval 40),(⟨-50623808,-50623744⟩ : DyadicInterval 40),(⟨762123382437,762123401766⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76024064,76024128⟩ : DyadicInterval 40),(⟨-76029376,-76029312⟩ : DyadicInterval 40),(⟨762123380950,762123400280⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5312,-2304⟩ : DyadicInterval 40),(⟨762123384768,762123405536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨197670430603,197923006642⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181780231936,181780232000⟩ : DyadicInterval 40),(⟨-217904443968,-217904443904⟩ : DyadicInterval 40),(⟨744257792217,744257811547⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181994298432,181994298496⟩ : DyadicInterval 40),(⟨-218212424128,-218212424064⟩ : DyadicInterval 40),(⟨744211855163,744211874493⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-36218125632,-36124211904⟩ : DyadicInterval 40),(⟨780185489568,780232465696⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨181843088192,182036233216⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-218272773248,-217994860800⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e767_ok : ecellOkT e767 = true := by decide +kernel
theorem e767_pos {a z : ℝ} (ha1 : ((46041/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((147501/819200 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e767 e767_ok ha1 ha2 hz1 hz2 hz

-- box ['147501/819200', '369177/2048000', '3997/4000', '1999/2000']  interval_lower 63515181/549755813888
noncomputable def e768 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1297484118753,0,true,182036233152,182036233216⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨901539136799,0,false,-218272773248,-218272773184⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1297712020456,0,true,182229344256,182229344320⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨901311235096,0,false,-218550755904,-218550755840⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1297335639384,0,true,181910401856,181910401920⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨901687616168,0,false,-218091703616,-218091703552⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1297612920260,0,true,182145376512,182145376576⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨901410335292,0,false,-218429870016,-218429869952⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099562311523,0,true,50682560,50682624⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099460944029,0,false,-50684928,-50684864⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587746266,0,true,76115840,76115904⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435509286,0,false,-76121152,-76121088⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622506,0,false,-5312,-5248⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625440,0,false,-2368,-2304⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1297409874612,0,true,181973315520,181973315584⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨901613380940,0,false,-218182229248,-218182229184⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1297662479149,0,true,182187368640,182187368704⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨901360776403,0,false,-218490321984,-218490321920⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1063801446175,0,false,-36302953344,-36302953280⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1063892435481,0,false,-36208913664,-36208913600⟩
    { al := (147501/819200), au := (369177/2048000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨197972490977,198200392680⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182036233152,182036233216⟩ : DyadicInterval 40),(⟨-218272773248,-218272773184⟩ : DyadicInterval 40),(⟨744202848208,744202867537⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182229344256,182229344320⟩ : DyadicInterval 40),(⟨-218550755904,-218550755840⟩ : DyadicInterval 40),(⟨744161336680,744161356010⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181910401856,181910401920⟩ : DyadicInterval 40),(⟨-218091703616,-218091703552⟩ : DyadicInterval 40),(⟨744229866935,744229886265⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182145376512,182145376576⟩ : DyadicInterval 40),(⟨-218429870016,-218429869952⟩ : DyadicInterval 40),(⟨744179393437,744179412767⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨50683747,76118490⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨50682560,50682624⟩ : DyadicInterval 40),(⟨-50684928,-50684864⟩ : DyadicInterval 40),(⟨762123382399,762123401728⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76115840,76115904⟩ : DyadicInterval 40),(⟨-76121152,-76121088⟩ : DyadicInterval 40),(⟨762123380938,762123400267⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5312,-2304⟩ : DyadicInterval 40),(⟨762123384768,762123405536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨197898246836,198150851373⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181973315520,181973315584⟩ : DyadicInterval 40),(⟨-218182229248,-218182229184⟩ : DyadicInterval 40),(⟨744216360968,744216380297⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182187368640,182187368704⟩ : DyadicInterval 40),(⟨-218490321984,-218490321920⟩ : DyadicInterval 40),(⟨744170364592,744170383922⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-36302953344,-36208913600⟩ : DyadicInterval 40),(⟨780227840416,780274879552⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨182036233152,182229344320⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-218550755904,-218272773184⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e768_ok : ecellOkT e768 = true := by decide +kernel
theorem e768_pos {a z : ℝ} (ha1 : ((147501/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((369177/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e768 e768_ok ha1 ha2 hz1 hz2 hz

-- box ['369177/2048000', '739203/4096000', '999/1000', '3997/4000']  interval_lower 130764829/1099511627776
noncomputable def e769 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1297712020455,0,true,182229344256,182229344320⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨901311235097,0,false,-218550755904,-218550755840⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1297939922158,0,true,182422421440,182422421504⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨901083333394,0,false,-218828808832,-218828808768⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1297513820062,0,true,182061402304,182061402368⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨901509435490,0,false,-218308997376,-218308997312⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1297791100938,0,true,182296344704,182296344768⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨901232154614,0,false,-218647230592,-218647230528⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587744826,0,true,76114368,76114432⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435510726,0,false,-76119744,-76119680⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099613240764,0,true,101608256,101608320⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099410014788,0,false,-101617728,-101617664⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511618385,0,false,-9408,-9344⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622507,0,false,-5312,-5248⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1297612916313,0,true,182145373120,182145373184⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨901410339239,0,false,-218429865152,-218429865088⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1297865520712,0,true,182359392640,182359392704⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨901157734840,0,false,-218738027136,-218738027072⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1063728225537,0,false,-36378634496,-36378634432⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1063819308088,0,false,-36284491968,-36284491904⟩
    { al := (369177/2048000), au := (739203/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨198200392679,198428294382⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182229344256,182229344320⟩ : DyadicInterval 40),(⟨-218550755904,-218550755840⟩ : DyadicInterval 40),(⟨744161336681,744161356010⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182422421440,182422421504⟩ : DyadicInterval 40),(⟨-218828808832,-218828808768⟩ : DyadicInterval 40),(⟨744119776323,744119795653⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182061402304,182061402368⟩ : DyadicInterval 40),(⟨-218308997376,-218308997312⟩ : DyadicInterval 40),(⟨744197440975,744197460305⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182296344704,182296344768⟩ : DyadicInterval 40),(⟨-218647230592,-218647230528⟩ : DyadicInterval 40),(⟨744146921018,744146940347⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨76117050,101612988⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76114368,76114432⟩ : DyadicInterval 40),(⟨-76119744,-76119680⟩ : DyadicInterval 40),(⟨762123380970,762123400299⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨101608256,101608320⟩ : DyadicInterval 40),(⟨-101617728,-101617664⟩ : DyadicInterval 40),(⟨762123378896,762123398226⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-9408,-5248⟩ : DyadicInterval 40),(⟨762123386240,762123407584⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨198101288537,198353892936⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182145373120,182145373184⟩ : DyadicInterval 40),(⟨-218429865152,-218429865088⟩ : DyadicInterval 40),(⟨744179394164,744179413493⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182359392640,182359392704⟩ : DyadicInterval 40),(⟨-218738027136,-218738027072⟩ : DyadicInterval 40),(⟨744133349600,744133368929⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-36378634496,-36284491904⟩ : DyadicInterval 40),(⟨780265629568,780312720128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨182229344256,182422421504⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-218828808832,-218550755840⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e769_ok : ecellOkT e769 = true := by decide +kernel
theorem e769_pos {a z : ℝ} (ha1 : ((369177/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((739203/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e769 e769_ok ha1 ha2 hz1 hz2 hz

-- box ['739203/4096000', '185013/1024000', '999/1000', '3997/4000']  interval_lower 66956853/549755813888
noncomputable def e770 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1297939922157,0,true,182422421440,182422421504⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨901083333395,0,false,-218828808832,-218828808768⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1298167823860,0,true,182615464704,182615464768⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨900855431692,0,false,-219106932160,-219106932096⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1297741493862,0,true,182254315904,182254315968⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨901281761690,0,false,-218586711168,-218586711104⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1298018831714,0,true,182489265344,182489265408⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨901004423838,0,false,-218925099392,-218925099328⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587836601,0,true,76206144,76206208⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435418951,0,false,-76211520,-76211456⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099613363154,0,true,101730624,101730688⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099409892398,0,false,-101740096,-101740032⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511618362,0,false,-9472,-9408⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622494,0,false,-5312,-5248⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1297840704068,0,true,182338368512,182338368576⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨901182551484,0,false,-218707748544,-218707748480⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1298093336951,0,true,182552374592,182552374656⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨900929918601,0,false,-219016023168,-219016023104⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1063645981408,0,false,-36463648576,-36463648512⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1063737178913,0,false,-36369379968,-36369379904⟩
    { al := (739203/4096000), au := (185013/1024000), zl := (999/1000), zu := (3997/4000),
      A := ⟨198428294381,198656196084⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182422421440,182422421504⟩ : DyadicInterval 40),(⟨-218828808832,-218828808768⟩ : DyadicInterval 40),(⟨744119776323,744119795653⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182615464704,182615464768⟩ : DyadicInterval 40),(⟨-219106932160,-219106932096⟩ : DyadicInterval 40),(⟨744078167176,744078186506⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182254315904,182254315968⟩ : DyadicInterval 40),(⟨-218586711168,-218586711104⟩ : DyadicInterval 40),(⟨744155964625,744155983955⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182489265344,182489265408⟩ : DyadicInterval 40),(⟨-218925099392,-218925099328⟩ : DyadicInterval 40),(⟨744105374937,744105394267⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨76208825,101735378⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76206144,76206208⟩ : DyadicInterval 40),(⟨-76211520,-76211456⟩ : DyadicInterval 40),(⟨762123380957,762123400287⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨101730624,101730688⟩ : DyadicInterval 40),(⟨-101740096,-101740032⟩ : DyadicInterval 40),(⟨762123378874,762123398204⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-9472,-5248⟩ : DyadicInterval 40),(⟨762123386240,762123407616⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨198329076292,198581709175⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182338368512,182338368576⟩ : DyadicInterval 40),(⟨-218707748544,-218707748480⟩ : DyadicInterval 40),(⟨744137875846,744137895176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182552374592,182552374656⟩ : DyadicInterval 40),(⟨-219016023168,-219016023104⟩ : DyadicInterval 40),(⟨744091771981,744091791311⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-36463648576,-36369379904⟩ : DyadicInterval 40),(⟨780308073568,780355227168⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨182422421440,182615464768⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-219106932160,-218828808768⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e770_ok : ecellOkT e770 = true := by decide +kernel
theorem e770_pos {a z : ℝ} (ha1 : ((739203/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((185013/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e770 e770_ok ha1 ha2 hz1 hz2 hz

-- box ['369177/2048000', '739203/4096000', '3997/4000', '1999/2000']  interval_lower 130162091/1099511627776
noncomputable def e771 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1297712020455,0,true,182229344256,182229344320⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨901311235097,0,false,-218550755904,-218550755840⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1297939922158,0,true,182422421440,182422421504⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨901083333394,0,false,-218828808832,-218828808768⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1297563370160,0,true,182103390208,182103390272⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨901459885392,0,false,-218369432000,-218369431936⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1297840708011,0,true,182338371904,182338371968⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨901182547541,0,false,-218707753344,-218707753280⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099562372698,0,true,50743744,50743808⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099460882854,0,false,-50746112,-50746048⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587838045,0,true,76207616,76207680⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435417507,0,false,-76212928,-76212864⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622493,0,false,-5312,-5248⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625435,0,false,-2368,-2304⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1297637690851,0,true,182166365248,182166365312⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨901385564701,0,false,-218460084800,-218460084736⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1297890323882,0,true,182380404928,182380404992⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨901132931670,0,false,-218768290176,-218768290112⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1063719275903,0,false,-36387885248,-36387885184⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1063810380170,0,false,-36293719488,-36293719424⟩
    { al := (369177/2048000), au := (739203/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨198200392679,198428294382⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182229344256,182229344320⟩ : DyadicInterval 40),(⟨-218550755904,-218550755840⟩ : DyadicInterval 40),(⟨744161336681,744161356010⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182422421440,182422421504⟩ : DyadicInterval 40),(⟨-218828808832,-218828808768⟩ : DyadicInterval 40),(⟨744119776323,744119795653⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182103390208,182103390272⟩ : DyadicInterval 40),(⟨-218369432000,-218369431936⟩ : DyadicInterval 40),(⟨744188418347,744188437676⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182338371904,182338371968⟩ : DyadicInterval 40),(⟨-218707753344,-218707753280⟩ : DyadicInterval 40),(⟨744137875092,744137894422⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨50744922,76210269⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨50743744,50743808⟩ : DyadicInterval 40),(⟨-50746112,-50746048⟩ : DyadicInterval 40),(⟨762123382393,762123401723⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76207616,76207680⟩ : DyadicInterval 40),(⟨-76212928,-76212864⟩ : DyadicInterval 40),(⟨762123380925,762123400254⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5312,-2304⟩ : DyadicInterval 40),(⟨762123384768,762123405536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨198126063075,198378696106⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182166365248,182166365312⟩ : DyadicInterval 40),(⟨-218460084800,-218460084736⟩ : DyadicInterval 40),(⟨744174880938,744174900267⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182380404928,182380404992⟩ : DyadicInterval 40),(⟨-218768290176,-218768290112⟩ : DyadicInterval 40),(⟨744128825268,744128844597⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-36387885248,-36293719424⟩ : DyadicInterval 40),(⟨780270243328,780317345504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨182229344256,182422421504⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-218828808832,-218550755840⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e771_ok : ecellOkT e771 = true := by decide +kernel
theorem e771_pos {a z : ℝ} (ha1 : ((369177/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((739203/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e771 e771_ok ha1 ha2 hz1 hz2 hz

-- box ['739203/4096000', '185013/1024000', '3997/4000', '1999/2000']  interval_lower 16663627/137438953472
noncomputable def e772 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1297939922157,0,true,182422421440,182422421504⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨901083333395,0,false,-218828808832,-218828808768⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1298167823860,0,true,182615464704,182615464768⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨900855431692,0,false,-219106932160,-219106932096⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1297791100936,0,true,182296344704,182296344768⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨901232154616,0,false,-218647230592,-218647230528⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1298068495763,0,true,182531333376,182531333440⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨900954759789,0,false,-218985706944,-218985706880⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099562433882,0,true,50804928,50804992⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099460821670,0,false,-50807296,-50807232⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099587929839,0,true,76299392,76299456⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099435325713,0,false,-76304768,-76304704⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511622480,0,false,-5312,-5248⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625429,0,false,-2368,-2304⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1297865507090,0,true,182359381120,182359381184⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨901157748462,0,false,-218738010560,-218738010496⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1298118168605,0,true,182573407296,182573407360⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨900905086947,0,false,-219046328640,-219046328576⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1063637011206,0,false,-36472921280,-36472921216⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1063728230453,0,false,-36378629440,-36378629376⟩
    { al := (739203/4096000), au := (185013/1024000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨198428294381,198656196084⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182422421440,182422421504⟩ : DyadicInterval 40),(⟨-218828808832,-218828808768⟩ : DyadicInterval 40),(⟨744119776323,744119795653⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182615464704,182615464768⟩ : DyadicInterval 40),(⟨-219106932160,-219106932096⟩ : DyadicInterval 40),(⟨744078167176,744078186506⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182296344704,182296344768⟩ : DyadicInterval 40),(⟨-218647230592,-218647230528⟩ : DyadicInterval 40),(⟨744146921018,744146940348⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182531333376,182531333440⟩ : DyadicInterval 40),(⟨-218985706944,-218985706880⟩ : DyadicInterval 40),(⟨744096308009,744096327338⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨50806106,76302063⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨50804928,50804992⟩ : DyadicInterval 40),(⟨-50807296,-50807232⟩ : DyadicInterval 40),(⟨762123382388,762123401717⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨76299392,76299456⟩ : DyadicInterval 40),(⟨-76304768,-76304704⟩ : DyadicInterval 40),(⟨762123380944,762123400274⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5312,-2304⟩ : DyadicInterval 40),(⟨762123384768,762123405536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨198353879314,198606540829⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182359381120,182359381184⟩ : DyadicInterval 40),(⟨-218738010560,-218738010496⟩ : DyadicInterval 40),(⟨744133352090,744133371420⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182573407296,182573407360⟩ : DyadicInterval 40),(⟨-219046328640,-219046328576⟩ : DyadicInterval 40),(⟨744087237155,744087256484⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-36472921280,-36378629376⟩ : DyadicInterval 40),(⟨780312698304,780359863520⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨182422421440,182615464768⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-219106932160,-218828808768⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e772_ok : ecellOkT e772 = true := by decide +kernel
theorem e772_pos {a z : ℝ} (ha1 : ((739203/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((185013/1024000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e772 e772_ok ha1 ha2 hz1 hz2 hz

-- box ['46041/256000', '147501/819200', '1999/2000', '3999/4000']  interval_lower 123315399/1099511627776
noncomputable def e773 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1297256217051,0,true,181843088192,181843088256⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨901767038501,0,false,-217994860864,-217994860800⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1297484118754,0,true,182036233152,182036233216⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨901539136798,0,false,-218272773248,-218272773184⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1297157344756,0,true,181759284096,181759284160⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨901865910796,0,false,-217874313856,-217874313792⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1297434625632,0,true,181994291008,181994291072⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨901588629920,0,false,-218212413376,-218212413312⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536939091,0,true,25310976,25311040⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486316461,0,false,-25311616,-25311552⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099562312652,0,true,50683648,50683712⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099460942900,0,false,-50686080,-50686016⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625439,0,false,-2368,-2304⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627194,0,false,-640,-576⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1297206776091,0,true,181801182848,181801182912⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨901816479461,0,false,-217934579840,-217934579776⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1297459380763,0,true,182015269568,182015269632⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨901563874789,0,false,-218242603328,-218242603264⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1063874612284,0,false,-36227333760,-36227333696⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1063965508318,0,false,-36133396992,-36133396928⟩
    { al := (46041/256000), au := (147501/819200), zl := (1999/2000), zu := (3999/4000),
      A := ⟨197744589275,197972490978⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181843088192,181843088256⟩ : DyadicInterval 40),(⟨-217994860864,-217994860800⟩ : DyadicInterval 40),(⟨744244310878,744244330208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182036233152,182036233216⟩ : DyadicInterval 40),(⟨-218272773248,-218272773184⟩ : DyadicInterval 40),(⟨744202848208,744202867537⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181759284096,181759284160⟩ : DyadicInterval 40),(⟨-217874313856,-217874313792⟩ : DyadicInterval 40),(⟨744262283747,744262303077⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181994291008,181994291072⟩ : DyadicInterval 40),(⟨-218212413376,-218212413312⟩ : DyadicInterval 40),(⟨744211856734,744211876063⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨25311315,50684876⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25310976,25311040⟩ : DyadicInterval 40),(⟨-25311616,-25311552⟩ : DyadicInterval 40),(⟨762123383289,762123402618⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨50683648,50683712⟩ : DyadicInterval 40),(⟨-50686080,-50686016⟩ : DyadicInterval 40),(⟨762123382431,762123401760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2368,-576⟩ : DyadicInterval 40),(⟨762123383904,762123404064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨197695148315,197947752987⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181801182848,181801182912⟩ : DyadicInterval 40),(⟨-217934579840,-217934579776⟩ : DyadicInterval 40),(⟨744253299345,744253318675⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182015269568,182015269632⟩ : DyadicInterval 40),(⟨-218242603328,-218242603264⟩ : DyadicInterval 40),(⟨744207351175,744207370504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-36227333760,-36133396928⟩ : DyadicInterval 40),(⟨780190082080,780237069760⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨181843088192,182036233216⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-218272773248,-217994860800⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e773_ok : ecellOkT e773 = true := by decide +kernel
theorem e773_pos {a z : ℝ} (ha1 : ((46041/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((147501/819200 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e773 e773_ok ha1 ha2 hz1 hz2 hz

-- box ['147501/819200', '369177/2048000', '1999/2000', '3999/4000']  interval_lower 126429913/1099511627776
noncomputable def e774 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1297484118753,0,true,182036233152,182036233216⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨901539136799,0,false,-218272773248,-218272773184⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1297712020456,0,true,182229344256,182229344320⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨901311235096,0,false,-218550755904,-218550755840⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1297385132507,0,true,181952347200,181952347264⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨901638123045,0,false,-218152056832,-218152056768⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1297662470359,0,true,182187361152,182187361216⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨901360785193,0,false,-218490311296,-218490311232⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536969674,0,true,25341568,25341632⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486285878,0,false,-25342208,-25342144⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099562373830,0,true,50744832,50744896⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099460881722,0,false,-50747264,-50747200⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625433,0,false,-2368,-2304⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627192,0,false,-640,-576⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1297434620807,0,true,181994286912,181994286976⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨901588634745,0,false,-218212407488,-218212407424⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1297687253977,0,true,182208360192,182208360256⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨901336001575,0,false,-218520543616,-218520543552⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1063792515919,0,false,-36312183424,-36312183360⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1063883526917,0,false,-36218120576,-36218120512⟩
    { al := (147501/819200), au := (369177/2048000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨197972490977,198200392680⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182036233152,182036233216⟩ : DyadicInterval 40),(⟨-218272773248,-218272773184⟩ : DyadicInterval 40),(⟨744202848208,744202867537⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182229344256,182229344320⟩ : DyadicInterval 40),(⟨-218550755904,-218550755840⟩ : DyadicInterval 40),(⟨744161336680,744161356010⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181952347200,181952347264⟩ : DyadicInterval 40),(⟨-218152056832,-218152056768⟩ : DyadicInterval 40),(⟨744220863002,744220882331⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182187361152,182187361216⟩ : DyadicInterval 40),(⟨-218490311296,-218490311232⟩ : DyadicInterval 40),(⟨744170366231,744170385561⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨25341898,50746054⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25341568,25341632⟩ : DyadicInterval 40),(⟨-25342208,-25342144⟩ : DyadicInterval 40),(⟨762123383287,762123402616⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨50744832,50744896⟩ : DyadicInterval 40),(⟨-50747264,-50747200⟩ : DyadicInterval 40),(⟨762123382425,762123401754⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2368,-576⟩ : DyadicInterval 40),(⟨762123383904,762123404064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨197922993031,198175626201⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181994286912,181994286976⟩ : DyadicInterval 40),(⟨-218212407488,-218212407424⟩ : DyadicInterval 40),(⟨744211857615,744211876944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182208360192,182208360256⟩ : DyadicInterval 40),(⟨-218520543616,-218520543552⟩ : DyadicInterval 40),(⟨744165850158,744165869488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-36312183424,-36218120512⟩ : DyadicInterval 40),(⟨780232443872,780279494592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨182036233152,182229344320⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-218550755904,-218272773184⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e774_ok : ecellOkT e774 = true := by decide +kernel
theorem e774_pos {a z : ℝ} (ha1 : ((147501/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((369177/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e774 e774_ok ha1 ha2 hz1 hz2 hz

-- box ['46041/256000', '147501/819200', '3999/4000', '1']  interval_lower 122716537/1099511627776
noncomputable def e775 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1297256217051,0,true,181843088192,181843088256⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨901767038501,0,false,-217994860864,-217994860800⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1297484118754,0,true,182036233152,182036233216⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨901539136798,0,false,-218272773248,-218272773184⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1297206780903,0,true,181801186944,181801187008⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨901816474649,0,false,-217934585728,-217934585664⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099536970496,0,true,25342400,25342464⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486285056,0,false,-25343040,-25342976⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627191,0,false,-640,-576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1297231493944,0,true,181822133504,181822133568⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨901791761608,0,false,-217964716736,-217964716672⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1297484127248,0,true,182036240384,182036240448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨901539128304,0,false,-218272783616,-218272783552⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1063865701387,0,false,-36236543168,-36236543104⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1063956619089,0,false,-36142583232,-36142583168⟩
    { al := (46041/256000), au := (147501/819200), zl := (3999/4000), zu := 1,
      A := ⟨197744589275,197972490978⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181843088192,181843088256⟩ : DyadicInterval 40),(⟨-217994860864,-217994860800⟩ : DyadicInterval 40),(⟨744244310878,744244330208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182036233152,182036233216⟩ : DyadicInterval 40),(⟨-218272773248,-218272773184⟩ : DyadicInterval 40),(⟨744202848208,744202867537⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181801186944,181801187008⟩ : DyadicInterval 40),(⟨-217934585728,-217934585664⟩ : DyadicInterval 40),(⟨744253298469,744253317799⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182036233152,182036233216⟩ : DyadicInterval 40),(⟨-218272773248,-218272773184⟩ : DyadicInterval 40),(⟨744202848208,744202867537⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,25342720⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25342400,25342464⟩ : DyadicInterval 40),(⟨-25343040,-25342976⟩ : DyadicInterval 40),(⟨762123383287,762123402616⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-640,0⟩ : DyadicInterval 40),(⟨762123383616,762123403200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨197719866168,197972499472⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181822133504,181822133568⟩ : DyadicInterval 40),(⟨-217964716736,-217964716672⟩ : DyadicInterval 40),(⟨744248805870,744248825200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182036240384,182036240448⟩ : DyadicInterval 40),(⟨-218272783616,-218272783552⟩ : DyadicInterval 40),(⟨744202846645,744202865975⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-36236543168,-36142583168⟩ : DyadicInterval 40),(⟨780194675200,780241674464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨181843088192,182036233216⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-218272773248,-217994860800⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e775_ok : ecellOkT e775 = true := by decide +kernel
theorem e775_pos {a z : ℝ} (ha1 : ((46041/256000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((147501/819200 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e775 e775_ok ha1 ha2 hz1 hz2 hz

-- box ['147501/819200', '369177/2048000', '3999/4000', '1']  interval_lower 62914321/549755813888
noncomputable def e776 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1297484118753,0,true,182036233152,182036233216⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨901539136799,0,false,-218272773248,-218272773184⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1297712020456,0,true,182229344256,182229344320⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨901311235096,0,false,-218550755904,-218550755840⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1297434625630,0,true,181994291008,181994291072⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨901588629922,0,false,-218212413376,-218212413312⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537001086,0,true,25372992,25373056⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486254466,0,false,-25373632,-25373568⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627190,0,false,-640,-576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1297459367151,0,true,182015258048,182015258112⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨901563888401,0,false,-218242586752,-218242586688⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1297712028954,0,true,182229351488,182229351552⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨901311226598,0,false,-218550766272,-218550766208⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1063783584493,0,false,-36321414784,-36321414720⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1063874617186,0,false,-36227328704,-36227328640⟩
    { al := (147501/819200), au := (369177/2048000), zl := (3999/4000), zu := 1,
      A := ⟨197972490977,198200392680⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182036233152,182036233216⟩ : DyadicInterval 40),(⟨-218272773248,-218272773184⟩ : DyadicInterval 40),(⟨744202848208,744202867537⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182229344256,182229344320⟩ : DyadicInterval 40),(⟨-218550755904,-218550755840⟩ : DyadicInterval 40),(⟨744161336680,744161356010⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨181994291008,181994291072⟩ : DyadicInterval 40),(⟨-218212413376,-218212413312⟩ : DyadicInterval 40),(⟨744211856734,744211876064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182229344256,182229344320⟩ : DyadicInterval 40),(⟨-218550755904,-218550755840⟩ : DyadicInterval 40),(⟨744161336680,744161356010⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,25373310⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25372992,25373056⟩ : DyadicInterval 40),(⟨-25373632,-25373568⟩ : DyadicInterval 40),(⟨762123383286,762123402615⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-640,0⟩ : DyadicInterval 40),(⟨762123383616,762123403200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨197947739375,198200401178⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182015258048,182015258112⟩ : DyadicInterval 40),(⟨-218242586752,-218242586688⟩ : DyadicInterval 40),(⟨744207353654,744207372983⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182229351488,182229351552⟩ : DyadicInterval 40),(⟨-218550766272,-218550766208⟩ : DyadicInterval 40),(⟨744161335113,744161354443⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-36321414784,-36227328640⟩ : DyadicInterval 40),(⟨780237047936,780284110272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨182036233152,182229344320⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-218550755904,-218272773184⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e776_ok : ecellOkT e776 = true := by decide +kernel
theorem e776_pos {a z : ℝ} (ha1 : ((147501/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((369177/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e776 e776_ok ha1 ha2 hz1 hz2 hz

-- box ['369177/2048000', '739203/4096000', '1999/2000', '3999/4000']  interval_lower 129559257/1099511627776
noncomputable def e777 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1297712020455,0,true,182229344256,182229344320⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨901311235097,0,false,-218550755904,-218550755840⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1297939922158,0,true,182422421440,182422421504⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨901083333394,0,false,-218828808832,-218828808768⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1297612920258,0,true,182145376512,182145376576⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨901410335294,0,false,-218429870016,-218429869952⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1297890315085,0,true,182380397440,182380397504⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨901132940467,0,false,-218768279424,-218768279360⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537000261,0,true,25372160,25372224⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486255291,0,false,-25372800,-25372736⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099562435017,0,true,50806016,50806080⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099460820535,0,false,-50808448,-50808384⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625428,0,false,-2368,-2304⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627191,0,false,-640,-576⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1297662465532,0,true,182187357120,182187357184⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨901360790020,0,false,-218490305408,-218490305344⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1297915127196,0,true,182401416896,182401416960⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨901108128356,0,false,-218798554176,-218798554112⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1063710325099,0,false,-36397137280,-36397137216⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1063801451084,0,false,-36302948288,-36302948224⟩
    { al := (369177/2048000), au := (739203/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨198200392679,198428294382⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182229344256,182229344320⟩ : DyadicInterval 40),(⟨-218550755904,-218550755840⟩ : DyadicInterval 40),(⟨744161336681,744161356010⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182422421440,182422421504⟩ : DyadicInterval 40),(⟨-218828808832,-218828808768⟩ : DyadicInterval 40),(⟨744119776323,744119795653⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182145376512,182145376576⟩ : DyadicInterval 40),(⟨-218429870016,-218429869952⟩ : DyadicInterval 40),(⟨744179393437,744179412767⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182380397440,182380397504⟩ : DyadicInterval 40),(⟨-218768279424,-218768279360⟩ : DyadicInterval 40),(⟨744128826886,744128846215⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨25372485,50807241⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25372160,25372224⟩ : DyadicInterval 40),(⟨-25372800,-25372736⟩ : DyadicInterval 40),(⟨762123383286,762123402615⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨50806016,50806080⟩ : DyadicInterval 40),(⟨-50808448,-50808384⟩ : DyadicInterval 40),(⟨762123382420,762123401749⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2368,-576⟩ : DyadicInterval 40),(⟨762123383904,762123404064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨198150837756,198403499420⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182187357120,182187357184⟩ : DyadicInterval 40),(⟨-218490305408,-218490305344⟩ : DyadicInterval 40),(⟨744170367077,744170386406⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182401416896,182401416960⟩ : DyadicInterval 40),(⟨-218798554176,-218798554112⟩ : DyadicInterval 40),(⟨744124300335,744124319665⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-36397137280,-36302948224⟩ : DyadicInterval 40),(⟨780274857728,780321971520⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨182229344256,182422421504⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-218828808832,-218550755840⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e777_ok : ecellOkT e777 = true := by decide +kernel
theorem e777_pos {a z : ℝ} (ha1 : ((369177/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((739203/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e777 e777_ok ha1 ha2 hz1 hz2 hz

-- box ['739203/4096000', '185013/1024000', '1999/2000', '3999/4000']  interval_lower 33175825/274877906944
noncomputable def e778 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1297939922157,0,true,182422421440,182422421504⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨901083333395,0,false,-218828808832,-218828808768⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1298167823860,0,true,182615464704,182615464768⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨900855431692,0,false,-219106932160,-219106932096⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1297840708009,0,true,182338371904,182338371968⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨901182547543,0,false,-218707753344,-218707753280⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1298118159812,0,true,182573399872,182573399936⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨900905095740,0,false,-219046317888,-219046317824⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537030855,0,true,25402752,25402816⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486224697,0,false,-25403392,-25403328⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099562496214,0,true,50867200,50867264⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099460759338,0,false,-50869632,-50869568⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625422,0,false,-2368,-2304⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627190,0,false,-640,-576⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1297890310260,0,true,182380393344,182380393408⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨901132945292,0,false,-218768273536,-218768273472⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1298143000409,0,true,182594439744,182594439808⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨900880255143,0,false,-219076635072,-219076635008⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1063628039828,0,false,-36482195264,-36482195200⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1063719280820,0,false,-36387880128,-36387880064⟩
    { al := (739203/4096000), au := (185013/1024000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨198428294381,198656196084⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182422421440,182422421504⟩ : DyadicInterval 40),(⟨-218828808832,-218828808768⟩ : DyadicInterval 40),(⟨744119776323,744119795653⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182615464704,182615464768⟩ : DyadicInterval 40),(⟨-219106932160,-219106932096⟩ : DyadicInterval 40),(⟨744078167176,744078186506⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182338371904,182338371968⟩ : DyadicInterval 40),(⟨-218707753344,-218707753280⟩ : DyadicInterval 40),(⟨744137875093,744137894422⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182573399872,182573399936⟩ : DyadicInterval 40),(⟨-219046317888,-219046317824⟩ : DyadicInterval 40),(⟨744087238739,744087258068⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨25403079,50868438⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25402752,25402816⟩ : DyadicInterval 40),(⟨-25403392,-25403328⟩ : DyadicInterval 40),(⟨762123383285,762123402614⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨50867200,50867264⟩ : DyadicInterval 40),(⟨-50869632,-50869568⟩ : DyadicInterval 40),(⟨762123382414,762123401743⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2368,-576⟩ : DyadicInterval 40),(⟨762123383904,762123404064⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨198378682484,198631372633⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182380393344,182380393408⟩ : DyadicInterval 40),(⟨-218768273536,-218768273472⟩ : DyadicInterval 40),(⟨744128827771,744128847100⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182594439744,182594439808⟩ : DyadicInterval 40),(⟨-219076635072,-219076635008⟩ : DyadicInterval 40),(⟨744082701686,744082721016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-36482195264,-36387880064⟩ : DyadicInterval 40),(⟨780317323648,780364500512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨182422421440,182615464768⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-219106932160,-218828808768⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e778_ok : ecellOkT e778 = true := by decide +kernel
theorem e778_pos {a z : ℝ} (ha1 : ((739203/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((185013/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e778 e778_ok ha1 ha2 hz1 hz2 hz

-- box ['369177/2048000', '739203/4096000', '3999/4000', '1']  interval_lower 64477765/549755813888
noncomputable def e779 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1297712020455,0,true,182229344256,182229344320⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨901311235097,0,false,-218550755904,-218550755840⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1297939922158,0,true,182422421440,182422421504⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨901083333394,0,false,-218828808832,-218828808768⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1297662470356,0,true,182187361152,182187361216⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨901360785196,0,false,-218490311296,-218490311232⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099537031679,0,true,25403584,25403648⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099486223873,0,false,-25404224,-25404160⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627189,0,false,-640,-576⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1297687240358,0,true,182208348672,182208348736⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨901336015194,0,false,-218520527040,-218520526976⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1297939930660,0,true,182422428608,182422428672⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨901083324892,0,false,-218828819264,-218828819200⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1063701373122,0,false,-36406390592,-36406390528⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1063792520829,0,false,-36312178368,-36312178304⟩
    { al := (369177/2048000), au := (739203/4096000), zl := (3999/4000), zu := 1,
      A := ⟨198200392679,198428294382⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182229344256,182229344320⟩ : DyadicInterval 40),(⟨-218550755904,-218550755840⟩ : DyadicInterval 40),(⟨744161336681,744161356010⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182422421440,182422421504⟩ : DyadicInterval 40),(⟨-218828808832,-218828808768⟩ : DyadicInterval 40),(⟨744119776323,744119795653⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182187361152,182187361216⟩ : DyadicInterval 40),(⟨-218490311296,-218490311232⟩ : DyadicInterval 40),(⟨744170366232,744170385561⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182422421440,182422421504⟩ : DyadicInterval 40),(⟨-218828808832,-218828808768⟩ : DyadicInterval 40),(⟨744119776323,744119795653⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,25403903⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨25403584,25403648⟩ : DyadicInterval 40),(⟨-25404224,-25404160⟩ : DyadicInterval 40),(⟨762123383285,762123402614⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-640,0⟩ : DyadicInterval 40),(⟨762123383616,762123403200⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨198175612582,198428302884⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182208348672,182208348736⟩ : DyadicInterval 40),(⟨-218520527040,-218520526976⟩ : DyadicInterval 40),(⟨744165852644,744165871973⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨182422428608,182422428672⟩ : DyadicInterval 40),(⟨-218828819264,-218828819200⟩ : DyadicInterval 40),(⟨744119774815,744119794145⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-36406390592,-36312178304⟩ : DyadicInterval 40),(⟨780279472768,780326598176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨182229344256,182422421504⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-218828808832,-218550755840⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e779_ok : ecellOkT e779 = true := by decide +kernel
theorem e779_pos {a z : ℝ} (ha1 : ((369177/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((739203/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e779 e779_ok ha1 ha2 hz1 hz2 hz

end CKLaneC2R.EpCells.B012

end


