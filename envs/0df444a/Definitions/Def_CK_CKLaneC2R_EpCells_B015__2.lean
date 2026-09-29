-- Prove2me | Definitions.Def_CK_CKLaneC2R_EpCells_B015__2
-- name    : CK_CKLaneC2R_EpCells_B015__2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T18:48:09.354251+00:00
-- url     : https://prove2.me/theorems/887ca59f-3f10-424f-bdf3-9ed8c1f3324b
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EpCells.B015 (+1 modules: CKLaneC2R.EpCells.B016)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EpCells.B015 (+1 modules: CKLaneC2R.EpCells.B016)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EpCells.B015 (+1 modules: CKLaneC2R.EpCells.B016)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EpCells.B015 (+1 modules: CKLaneC2R.EpCells.B016) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EpCells/B015 (+1 modules: CKLaneC2R/EpCells/B016).lean)

import Definitions.Def_CK_CKLaneC2R_EpCells_B015__2_q00

-- ===== source module CKLaneC2R.EpCells.B016 =====
section

namespace CKLaneC2R.EpCells.B016

open GeneralCK GeneralCK.Certificates CKLaneC2R CKLaneC2R.Endpoint

-- box ['778257/4096000', '389553/2048000', '3997/4000', '1999/2000']  interval_lower 73692293/274877906944
noncomputable def e960 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1308423400456,0,true,191267518656,191267518720⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨890599855096,0,false,-231695858048,-231695857984⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1308651302159,0,true,191459015296,191459015360⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨890371953393,0,false,-231977255616,-231977255552⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1308266716626,0,true,191135844096,191135844160⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨890756538926,0,false,-231502437248,-231502437184⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1308546732322,0,true,191371153600,191371153664⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨890476523230,0,false,-231848130944,-231848130880⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565259604,0,true,53630464,53630528⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457995948,0,false,-53633152,-53633088⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592169224,0,true,80538496,80538560⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431086328,0,false,-80544448,-80544384⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621876,0,false,-5952,-5888⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625160,0,false,-2624,-2560⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1308345053960,0,true,191201679488,191201679552⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨890678201592,0,false,-231599137728,-231599137664⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1308599026095,0,true,191415092800,191415092864⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨890424229457,0,false,-231912702272,-231912702208⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1059750756647,0,false,-40497609472,-40497609408⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1059847290638,0,false,-40397458176,-40397458112⟩
    { al := (778257/4096000), au := (389553/2048000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨208911772680,209139674383⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191267518656,191267518720⟩ : DyadicInterval 40),(⟨-231695858048,-231695857984⟩ : DyadicInterval 40),(⟨742155154729,742155174058⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191459015296,191459015360⟩ : DyadicInterval 40),(⟨-231977255616,-231977255552⟩ : DyadicInterval 40),(⟨742111295302,742111314632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191135844096,191135844160⟩ : DyadicInterval 40),(⟨-231502437248,-231502437184⟩ : DyadicInterval 40),(⟨742185279978,742185299308⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191371153600,191371153664⟩ : DyadicInterval 40),(⟨-231848130944,-231848130880⟩ : DyadicInterval 40),(⟨742131425744,742131445073⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨53631828,80541448⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53630464,53630528⟩ : DyadicInterval 40),(⟨-53633152,-53633088⟩ : DyadicInterval 40),(⟨762123382279,762123401609⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80538496,80538560⟩ : DyadicInterval 40),(⟨-80544448,-80544384⟩ : DyadicInterval 40),(⟨762123380627,762123399957⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5952,-2560⟩ : DyadicInterval 40),(⟨762123384896,762123405856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨208833426184,209087398319⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191201679488,191201679552⟩ : DyadicInterval 40),(⟨-231599137728,-231599137664⟩ : DyadicInterval 40),(⟨742170221130,742170240460⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191415092800,191415092864⟩ : DyadicInterval 40),(⟨-231912702272,-231912702208⟩ : DyadicInterval 40),(⟨742121360069,742121379398⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-40497609472,-40397458112⟩ : DyadicInterval 40),(⟨782322112672,782372207616⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨191267518656,191459015360⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-231977255616,-231695857984⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e960_ok : ecellOkT e960 = true := by decide +kernel
theorem e960_pos {a z : ℝ} (ha1 : ((778257/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((389553/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e960 e960_ok ha1 ha2 hz1 hz2 hz

-- box ['389553/2048000', '155991/819200', '999/1000', '3997/4000']  interval_lower 74846753/274877906944
noncomputable def e961 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1308651302158,0,true,191459015296,191459015360⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨890371953394,0,false,-231977255616,-231977255552⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1308879203861,0,true,191650478656,191650478720⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨890144051691,0,false,-232258725184,-232258725120⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1308442162483,0,true,191283284864,191283284928⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨890581093069,0,false,-231719021376,-231719021312⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1308722178180,0,true,191518562816,191518562880⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨890301077372,0,false,-232064783168,-232064783104⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592167616,0,true,80536832,80536896⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099431087936,0,false,-80542848,-80542784⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099619138938,0,true,107505856,107505920⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099404116614,0,false,-107516480,-107516416⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511617263,0,false,-10560,-10496⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621877,0,false,-5952,-5888⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1308546728340,0,true,191371150272,191371150336⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨890476527212,0,false,-231848126016,-231848125952⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1308800700317,0,true,191584530496,191584530560⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨890222555235,0,false,-232161761408,-232161761344⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1059674017351,0,false,-40577230848,-40577230784⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1059770644449,0,false,-40476975680,-40476975616⟩
    { al := (389553/2048000), au := (155991/819200), zl := (999/1000), zu := (3997/4000),
      A := ⟨209139674382,209367576085⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191459015296,191459015360⟩ : DyadicInterval 40),(⟨-231977255616,-231977255552⟩ : DyadicInterval 40),(⟨742111295302,742111314632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191650478656,191650478720⟩ : DyadicInterval 40),(⟨-232258725184,-232258725120⟩ : DyadicInterval 40),(⟨742067386810,742067406140⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191283284864,191283284928⟩ : DyadicInterval 40),(⟨-231719021376,-231719021312⟩ : DyadicInterval 40),(⟨742151545854,742151565184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191518562816,191518562880⟩ : DyadicInterval 40),(⟨-232064783168,-232064783104⟩ : DyadicInterval 40),(⟨742097645258,742097664588⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨80539840,107511162⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80536832,80536896⟩ : DyadicInterval 40),(⟨-80542848,-80542784⟩ : DyadicInterval 40),(⟨762123380660,762123399989⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨107505856,107505920⟩ : DyadicInterval 40),(⟨-107516480,-107516416⟩ : DyadicInterval 40),(⟨762123378350,762123397680⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-10560,-5888⟩ : DyadicInterval 40),(⟨762123386560,762123408160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨209035100564,209289072541⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191371150272,191371150336⟩ : DyadicInterval 40),(⟨-231848126016,-231848125952⟩ : DyadicInterval 40),(⟨742131426494,742131445824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191584530496,191584530560⟩ : DyadicInterval 40),(⟨-232161761408,-232161761344⟩ : DyadicInterval 40),(⟨742082517179,742082536508⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-40577230848,-40476975616⟩ : DyadicInterval 40),(⟨782361871424,782412018304⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨191459015296,191650478720⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-232258725184,-231977255552⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e961_ok : ecellOkT e961 = true := by decide +kernel
theorem e961_pos {a z : ℝ} (ha1 : ((389553/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((155991/819200 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e961 e961_ok ha1 ha2 hz1 hz2 hz

-- box ['155991/819200', '195201/1024000', '999/1000', '3997/4000']  interval_lower 303296239/1099511627776
noncomputable def e962 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1308879203860,0,true,191650478656,191650478720⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨890144051692,0,false,-232258725184,-232258725120⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1309107105563,0,true,191841908672,191841908736⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨889916149989,0,false,-232540266880,-232540266816⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1308669836283,0,true,191474587328,191474587392⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨890353419269,0,false,-232000143424,-232000143360⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1308949908955,0,true,191709872192,191709872256⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨890073346597,0,false,-232346064064,-232346064000⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592260147,0,true,80629376,80629440⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430995405,0,false,-80635328,-80635264⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099619262336,0,true,107629248,107629312⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099403993216,0,false,-107639872,-107639808⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511617239,0,false,-10560,-10496⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621863,0,false,-5952,-5888⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1308774516094,0,true,191562533184,191562533248⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨890248739458,0,false,-232129421824,-232129421760⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1309028516555,0,true,191775900224,191775900288⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨889994738997,0,false,-232443172672,-232443172608⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1059587241735,0,false,-40667272384,-40667272320⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1059683984920,0,false,-40566888640,-40566888576⟩
    { al := (155991/819200), au := (195201/1024000), zl := (999/1000), zu := (3997/4000),
      A := ⟨209367576084,209595477787⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191650478656,191650478720⟩ : DyadicInterval 40),(⟨-232258725184,-232258725120⟩ : DyadicInterval 40),(⟨742067386810,742067406140⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191841908672,191841908736⟩ : DyadicInterval 40),(⟨-232540266880,-232540266816⟩ : DyadicInterval 40),(⟨742023429330,742023448659⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191474587328,191474587392⟩ : DyadicInterval 40),(⟨-232000143424,-232000143360⟩ : DyadicInterval 40),(⟨742107726249,742107745579⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191709872192,191709872256⟩ : DyadicInterval 40),(⟨-232346064064,-232346064000⟩ : DyadicInterval 40),(⟨742053754533,742053773862⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨80632371,107634560⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80629376,80629440⟩ : DyadicInterval 40),(⟨-80635328,-80635264⟩ : DyadicInterval 40),(⟨762123380614,762123399944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨107629248,107629312⟩ : DyadicInterval 40),(⟨-107639872,-107639808⟩ : DyadicInterval 40),(⟨762123378326,762123397656⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-10560,-5888⟩ : DyadicInterval 40),(⟨762123386560,762123408160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨209262888318,209516888779⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191562533184,191562533248⟩ : DyadicInterval 40),(⟨-232129421824,-232129421760⟩ : DyadicInterval 40),(⟨742087562471,742087581800⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191775900224,191775900288⟩ : DyadicInterval 40),(⟨-232443172672,-232443172608⟩ : DyadicInterval 40),(⟨742038593054,742038612383⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-40667272384,-40566888576⟩ : DyadicInterval 40),(⟨782406827904,782457039072⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨191650478656,191841908736⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-232540266880,-232258725120⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e962_ok : ecellOkT e962 = true := by decide +kernel
theorem e962_pos {a z : ℝ} (ha1 : ((155991/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((195201/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e962 e962_ok ha1 ha2 hz1 hz2 hz

-- box ['389553/2048000', '155991/819200', '3997/4000', '1999/2000']  interval_lower 149329357/549755813888
noncomputable def e963 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1308651302158,0,true,191459015296,191459015360⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨890371953394,0,false,-231977255616,-231977255552⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1308879203861,0,true,191650478656,191650478720⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨890144051691,0,false,-232258725184,-232258725120⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1308494447402,0,true,191327220096,191327220160⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨890528808150,0,false,-231783574272,-231783574208⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1308774520074,0,true,191562536512,191562536576⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨890248735478,0,false,-232129426752,-232129426688⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565321281,0,true,53692160,53692224⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457934271,0,false,-53694848,-53694784⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592261760,0,true,80630976,80631040⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430993792,0,false,-80636992,-80636928⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621862,0,false,-5952,-5888⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625154,0,false,-2624,-2560⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1308572870194,0,true,191393115840,191393115904⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨890450385358,0,false,-231880404992,-231880404928⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1308826870828,0,true,191606515904,191606515968⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨890196384724,0,false,-232194084992,-232194084928⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1059664053755,0,false,-40587569088,-40587569024⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1059760703842,0,false,-40487289152,-40487289088⟩
    { al := (389553/2048000), au := (155991/819200), zl := (3997/4000), zu := (1999/2000),
      A := ⟨209139674382,209367576085⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191459015296,191459015360⟩ : DyadicInterval 40),(⟨-231977255616,-231977255552⟩ : DyadicInterval 40),(⟨742111295302,742111314632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191650478656,191650478720⟩ : DyadicInterval 40),(⟨-232258725184,-232258725120⟩ : DyadicInterval 40),(⟨742067386810,742067406140⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191327220096,191327220160⟩ : DyadicInterval 40),(⟨-231783574272,-231783574208⟩ : DyadicInterval 40),(⟨742141487100,742141506429⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191562536512,191562536576⟩ : DyadicInterval 40),(⟨-232129426752,-232129426688⟩ : DyadicInterval 40),(⟨742087561718,742087581048⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨53693505,80633984⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53692160,53692224⟩ : DyadicInterval 40),(⟨-53694848,-53694784⟩ : DyadicInterval 40),(⟨762123382273,762123401602⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80630976,80631040⟩ : DyadicInterval 40),(⟨-80636992,-80636928⟩ : DyadicInterval 40),(⟨762123380646,762123399975⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5952,-2560⟩ : DyadicInterval 40),(⟨762123384896,762123405856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨209061242418,209315243052⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191393115840,191393115904⟩ : DyadicInterval 40),(⟨-231880404992,-231880404928⟩ : DyadicInterval 40),(⟨742126394962,742126414292⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191606515904,191606515968⟩ : DyadicInterval 40),(⟨-232194084992,-232194084928⟩ : DyadicInterval 40),(⟨742077473843,742077493173⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-40587569088,-40487289088⟩ : DyadicInterval 40),(⟨782367028160,782417187424⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨191459015296,191650478720⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-232258725184,-231977255552⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e963_ok : ecellOkT e963 = true := by decide +kernel
theorem e963_pos {a z : ℝ} (ha1 : ((389553/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((155991/819200 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e963 e963_ok ha1 ha2 hz1 hz2 hz

-- box ['155991/819200', '195201/1024000', '3997/4000', '1999/2000']  interval_lower 151282425/549755813888
noncomputable def e964 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1308879203860,0,true,191650478656,191650478720⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨890144051692,0,false,-232258725184,-232258725120⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1309107105563,0,true,191841908672,191841908736⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨889916149989,0,false,-232540266880,-232540266816⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1308722178177,0,true,191518562816,191518562880⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨890301077375,0,false,-232064783168,-232064783104⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1309002307825,0,true,191753886144,191753886208⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨890020947727,0,false,-232410794560,-232410794496⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565382969,0,true,53753856,53753920⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457872583,0,false,-53756544,-53756480⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592354311,0,true,80723520,80723584⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430901241,0,false,-80729536,-80729472⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621849,0,false,-5952,-5888⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625148,0,false,-2688,-2624⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1308800686438,0,true,191584518848,191584518912⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨890222569114,0,false,-232161744256,-232161744192⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1309054715557,0,true,191797905728,191797905792⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨889968539995,0,false,-232475539776,-232475539712⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1059577256435,0,false,-40677633984,-40677633920⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1059674022635,0,false,-40577225344,-40577225280⟩
    { al := (155991/819200), au := (195201/1024000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨209367576084,209595477787⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191650478656,191650478720⟩ : DyadicInterval 40),(⟨-232258725184,-232258725120⟩ : DyadicInterval 40),(⟨742067386810,742067406140⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191841908672,191841908736⟩ : DyadicInterval 40),(⟨-232540266880,-232540266816⟩ : DyadicInterval 40),(⟨742023429330,742023448659⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191518562816,191518562880⟩ : DyadicInterval 40),(⟨-232064783168,-232064783104⟩ : DyadicInterval 40),(⟨742097645259,742097664588⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191753886144,191753886208⟩ : DyadicInterval 40),(⟨-232410794560,-232410794496⟩ : DyadicInterval 40),(⟨742043648719,742043668049⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨53755193,80726535⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53753856,53753920⟩ : DyadicInterval 40),(⟨-53756544,-53756480⟩ : DyadicInterval 40),(⟨762123382267,762123401596⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80723520,80723584⟩ : DyadicInterval 40),(⟨-80729536,-80729472⟩ : DyadicInterval 40),(⟨762123380632,762123399962⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5952,-2624⟩ : DyadicInterval 40),(⟨762123384928,762123405856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨209289058662,209543087781⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191584518848,191584518912⟩ : DyadicInterval 40),(⟨-232161744256,-232161744192⟩ : DyadicInterval 40),(⟨742082519842,742082539172⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191797905728,191797905792⟩ : DyadicInterval 40),(⟨-232475539776,-232475539712⟩ : DyadicInterval 40),(⟨742033538618,742033557948⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-40677633984,-40577225280⟩ : DyadicInterval 40),(⟨782411996256,782462219872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨191650478656,191841908736⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-232540266880,-232258725120⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e964_ok : ecellOkT e964 = true := by decide +kernel
theorem e964_pos {a z : ℝ} (ha1 : ((155991/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((195201/1024000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e964 e964_ok ha1 ha2 hz1 hz2 hz

-- box ['12147/64000', '778257/4096000', '1999/2000', '3999/4000']  interval_lower 290173477/1099511627776
noncomputable def e965 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1308195498754,0,true,191075988608,191075988672⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨890827756798,0,false,-231414532480,-231414532416⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1308423400457,0,true,191267518656,191267518720⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨890599855095,0,false,-231695858048,-231695857984⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1308091156818,0,true,190988287808,190988287872⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨890932098734,0,false,-231285755072,-231285755008⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1308371172515,0,true,191223628864,191223628928⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨890652083037,0,false,-231631380672,-231631380608⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538412908,0,true,26784768,26784832⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484842644,0,false,-26785472,-26785408⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565260845,0,true,53631744,53631808⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457994707,0,false,-53634432,-53634368⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625159,0,false,-2624,-2560⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627124,0,false,-704,-640⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1308143322782,0,true,191032134848,191032134912⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨890879932770,0,false,-231350135680,-231350135616⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1308397295085,0,true,191245581184,191245581248⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨890625960467,0,false,-231663629504,-231663629440⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1059827443539,0,false,-40418048256,-40418048192⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1059923884399,0,false,-40318000832,-40318000768⟩
    { al := (12147/64000), au := (778257/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨208683870978,208911772681⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191075988608,191075988672⟩ : DyadicInterval 40),(⟨-231414532480,-231414532416⟩ : DyadicInterval 40),(⟨742198965177,742198984507⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191267518656,191267518720⟩ : DyadicInterval 40),(⟨-231695858048,-231695857984⟩ : DyadicInterval 40),(⟨742155154729,742155174058⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨190988287808,190988287872⟩ : DyadicInterval 40),(⟨-231285755072,-231285755008⟩ : DyadicInterval 40),(⟨742219006891,742219026220⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191223628864,191223628928⟩ : DyadicInterval 40),(⟨-231631380672,-231631380608⟩ : DyadicInterval 40),(⟨742165199068,742165218398⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨26785132,53633069⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26784768,26784832⟩ : DyadicInterval 40),(⟨-26785472,-26785408⟩ : DyadicInterval 40),(⟨762123383251,762123402580⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53631744,53631808⟩ : DyadicInterval 40),(⟨-53634432,-53634368⟩ : DyadicInterval 40),(⟨762123382279,762123401608⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2624,-640⟩ : DyadicInterval 40),(⟨762123383936,762123404192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨208631695006,208885667309⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191032134848,191032134912⟩ : DyadicInterval 40),(⟨-231350135680,-231350135616⟩ : DyadicInterval 40),(⟨742208988282,742209007612⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191245581184,191245581248⟩ : DyadicInterval 40),(⟨-231663629504,-231663629440⟩ : DyadicInterval 40),(⟨742160175579,742160194909⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-40418048256,-40318000768⟩ : DyadicInterval 40),(⟨782282384000,782332427008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨191075988608,191267518720⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-231695858048,-231414532416⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e965_ok : ecellOkT e965 = true := by decide +kernel
theorem e965_pos {a z : ℝ} (ha1 : ((12147/64000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((778257/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e965 e965_ok ha1 ha2 hz1 hz2 hz

-- box ['778257/4096000', '389553/2048000', '1999/2000', '3999/4000']  interval_lower 147021551/549755813888
noncomputable def e966 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1308423400456,0,true,191267518656,191267518720⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨890599855096,0,false,-231695858048,-231695857984⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1308651302159,0,true,191459015296,191459015360⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨890371953393,0,false,-231977255616,-231977255552⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1308318944569,0,true,191179737344,191179737408⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨890704310983,0,false,-231566907072,-231566907008⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1308599017241,0,true,191415085312,191415085376⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨890424238311,0,false,-231912691392,-231912691328⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538443742,0,true,26815616,26815680⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484811810,0,false,-26816320,-26816256⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565322525,0,true,53693376,53693440⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457933027,0,false,-53696064,-53696000⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625153,0,false,-2624,-2560⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627122,0,false,-704,-640⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1308371167501,0,true,191223624640,191223624704⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨890652088051,0,false,-231631374464,-231631374400⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1308625168294,0,true,191437057792,191437057856⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨890398087258,0,false,-231944983616,-231944983552⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1059740813422,0,false,-40507925824,-40507925760⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1059837370377,0,false,-40407749760,-40407749696⟩
    { al := (778257/4096000), au := (389553/2048000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨208911772680,209139674383⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191267518656,191267518720⟩ : DyadicInterval 40),(⟨-231695858048,-231695857984⟩ : DyadicInterval 40),(⟨742155154729,742155174058⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191459015296,191459015360⟩ : DyadicInterval 40),(⟨-231977255616,-231977255552⟩ : DyadicInterval 40),(⟨742111295302,742111314632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191179737344,191179737408⟩ : DyadicInterval 40),(⟨-231566907072,-231566907008⟩ : DyadicInterval 40),(⟨742175240818,742175260148⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191415085312,191415085376⟩ : DyadicInterval 40),(⟨-231912691392,-231912691328⟩ : DyadicInterval 40),(⟨742121361824,742121381153⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨26815966,53694749⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26815616,26815680⟩ : DyadicInterval 40),(⟨-26816320,-26816256⟩ : DyadicInterval 40),(⟨762123383249,762123402578⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53693376,53693440⟩ : DyadicInterval 40),(⟨-53696064,-53696000⟩ : DyadicInterval 40),(⟨762123382273,762123401602⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2624,-640⟩ : DyadicInterval 40),(⟨762123383936,762123404192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨208859539725,209113540518⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191223624640,191223624704⟩ : DyadicInterval 40),(⟨-231631374464,-231631374400⟩ : DyadicInterval 40),(⟨742165200031,742165219360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191437057792,191437057856⟩ : DyadicInterval 40),(⟨-231944983616,-231944983552⟩ : DyadicInterval 40),(⟨742116327191,742116346521⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-40507925824,-40407749696⟩ : DyadicInterval 40),(⟨782327258464,782377365792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨191267518656,191459015360⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-231977255616,-231695857984⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e966_ok : ecellOkT e966 = true := by decide +kernel
theorem e966_pos {a z : ℝ} (ha1 : ((778257/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((389553/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e966 e966_ok ha1 ha2 hz1 hz2 hz

-- box ['12147/64000', '778257/4096000', '3999/4000', '1']  interval_lower 144724703/549755813888
noncomputable def e967 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1308195498754,0,true,191075988608,191075988672⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨890827756798,0,false,-231414532480,-231414532416⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1308423400457,0,true,191267518656,191267518720⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨890599855095,0,false,-231695858048,-231695857984⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1308143327786,0,true,191032139072,191032139136⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨890879927766,0,false,-231350141888,-231350141824⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538444620,0,true,26816512,26816576⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484810932,0,false,-26817216,-26817152⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627121,0,false,-704,-640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1308169408009,0,true,191054059648,191054059712⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨890853847543,0,false,-231382330176,-231382330112⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1308423408973,0,true,191267525760,191267525824⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨890599846579,0,false,-231695868544,-231695868480⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1059817520664,0,false,-40428342720,-40428342656⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1059913984467,0,false,-40328270528,-40328270464⟩
    { al := (12147/64000), au := (778257/4096000), zl := (3999/4000), zu := 1,
      A := ⟨208683870978,208911772681⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191075988608,191075988672⟩ : DyadicInterval 40),(⟨-231414532480,-231414532416⟩ : DyadicInterval 40),(⟨742198965177,742198984507⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191267518656,191267518720⟩ : DyadicInterval 40),(⟨-231695858048,-231695857984⟩ : DyadicInterval 40),(⟨742155154729,742155174058⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191032139072,191032139136⟩ : DyadicInterval 40),(⟨-231350141888,-231350141824⟩ : DyadicInterval 40),(⟨742208987323,742209006653⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191267518656,191267518720⟩ : DyadicInterval 40),(⟨-231695858048,-231695857984⟩ : DyadicInterval 40),(⟨742155154729,742155174058⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,26816844⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26816512,26816576⟩ : DyadicInterval 40),(⟨-26817216,-26817152⟩ : DyadicInterval 40),(⟨762123383249,762123402578⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-704,0⟩ : DyadicInterval 40),(⟨762123383616,762123403232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨208657780233,208911781197⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191054059648,191054059712⟩ : DyadicInterval 40),(⟨-231382330176,-231382330112⟩ : DyadicInterval 40),(⟨742203977558,742203996887⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191267525760,191267525824⟩ : DyadicInterval 40),(⟨-231695868544,-231695868480⟩ : DyadicInterval 40),(⟨742155153114,742155172444⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-40428342720,-40328270464⟩ : DyadicInterval 40),(⟨782287518848,782337574240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨191075988608,191267518720⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-231695858048,-231414532416⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e967_ok : ecellOkT e967 = true := by decide +kernel
theorem e967_pos {a z : ℝ} (ha1 : ((12147/64000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((778257/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e967 e967_ok ha1 ha2 hz1 hz2 hz

-- box ['778257/4096000', '389553/2048000', '3999/4000', '1']  interval_lower 36664545/137438953472
noncomputable def e968 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1308423400456,0,true,191267518656,191267518720⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨890599855096,0,false,-231695858048,-231695857984⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1308651302159,0,true,191459015296,191459015360⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨890371953393,0,false,-231977255616,-231977255552⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1308371172512,0,true,191223628864,191223628928⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨890652083040,0,false,-231631380672,-231631380608⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538475462,0,true,26847296,26847360⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484780090,0,false,-26848064,-26848000⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627120,0,false,-704,-640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1308397281216,0,true,191245569536,191245569600⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨890625974336,0,false,-231663612352,-231663612288⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1308651310668,0,true,191459022464,191459022528⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨890371944884,0,false,-231977266112,-231977266048⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1059730868887,0,false,-40518243584,-40518243520⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1059827448809,0,false,-40418042752,-40418042688⟩
    { al := (778257/4096000), au := (389553/2048000), zl := (3999/4000), zu := 1,
      A := ⟨208911772680,209139674383⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191267518656,191267518720⟩ : DyadicInterval 40),(⟨-231695858048,-231695857984⟩ : DyadicInterval 40),(⟨742155154729,742155174058⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191459015296,191459015360⟩ : DyadicInterval 40),(⟨-231977255616,-231977255552⟩ : DyadicInterval 40),(⟨742111295302,742111314632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191223628864,191223628928⟩ : DyadicInterval 40),(⟨-231631380672,-231631380608⟩ : DyadicInterval 40),(⟨742165199068,742165218398⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191459015296,191459015360⟩ : DyadicInterval 40),(⟨-231977255616,-231977255552⟩ : DyadicInterval 40),(⟨742111295302,742111314632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,26847686⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26847296,26847360⟩ : DyadicInterval 40),(⟨-26848064,-26848000⟩ : DyadicInterval 40),(⟨762123383280,762123402609⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-704,0⟩ : DyadicInterval 40),(⟨762123383616,762123403232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨208885653440,209139682892⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191245569536,191245569600⟩ : DyadicInterval 40),(⟨-231663612352,-231663612288⟩ : DyadicInterval 40),(⟨742160178230,742160197560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191459022464,191459022528⟩ : DyadicInterval 40),(⟨-231977266112,-231977266048⟩ : DyadicInterval 40),(⟨742111293648,742111312977⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-40518243584,-40418042688⟩ : DyadicInterval 40),(⟨782332404960,782382524672⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨191267518656,191459015360⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-231977255616,-231695857984⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e968_ok : ecellOkT e968 = true := by decide +kernel
theorem e968_pos {a z : ℝ} (ha1 : ((778257/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((389553/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e968 e968_ok ha1 ha2 hz1 hz2 hz

-- box ['389553/2048000', '155991/819200', '1999/2000', '3999/4000']  interval_lower 297929577/1099511627776
noncomputable def e969 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1308651302158,0,true,191459015296,191459015360⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨890371953394,0,false,-231977255616,-231977255552⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1308879203861,0,true,191650478656,191650478720⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨890144051691,0,false,-232258725184,-232258725120⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1308546732320,0,true,191371153600,191371153664⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨890476523232,0,false,-231848130880,-231848130816⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1308826861968,0,true,191606508480,191606508544⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨890196393584,0,false,-232194074048,-232194073984⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538474582,0,true,26846464,26846528⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484780970,0,false,-26847168,-26847104⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565384217,0,true,53755072,53755136⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457871335,0,false,-53757760,-53757696⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625147,0,false,-2688,-2624⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627121,0,false,-704,-640⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1308599012225,0,true,191415081152,191415081216⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨890424243327,0,false,-231912685184,-231912685120⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1308853041519,0,true,191628500992,191628501056⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨890170214033,0,false,-232226409792,-232226409728⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1059654088846,0,false,-40597908736,-40597908672⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1059750761924,0,false,-40497604032,-40497603968⟩
    { al := (389553/2048000), au := (155991/819200), zl := (1999/2000), zu := (3999/4000),
      A := ⟨209139674382,209367576085⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191459015296,191459015360⟩ : DyadicInterval 40),(⟨-231977255616,-231977255552⟩ : DyadicInterval 40),(⟨742111295302,742111314632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191650478656,191650478720⟩ : DyadicInterval 40),(⟨-232258725184,-232258725120⟩ : DyadicInterval 40),(⟨742067386810,742067406140⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191371153600,191371153664⟩ : DyadicInterval 40),(⟨-231848130880,-231848130816⟩ : DyadicInterval 40),(⟨742131425718,742131445047⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191606508480,191606508544⟩ : DyadicInterval 40),(⟨-232194074048,-232194073984⟩ : DyadicInterval 40),(⟨742077475539,742077494869⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨26846806,53756441⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26846464,26846528⟩ : DyadicInterval 40),(⟨-26847168,-26847104⟩ : DyadicInterval 40),(⟨762123383248,762123402577⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53755072,53755136⟩ : DyadicInterval 40),(⟨-53757760,-53757696⟩ : DyadicInterval 40),(⟨762123382267,762123401596⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2688,-640⟩ : DyadicInterval 40),(⟨762123383936,762123404224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨209087384449,209341413743⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191415081152,191415081216⟩ : DyadicInterval 40),(⟨-231912685184,-231912685120⟩ : DyadicInterval 40),(⟨742121362751,742121382080⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191628500992,191628501056⟩ : DyadicInterval 40),(⟨-232226409792,-232226409728⟩ : DyadicInterval 40),(⟨742072429863,742072449193⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-40597908736,-40497603968⟩ : DyadicInterval 40),(⟨782372185600,782422357248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨191459015296,191650478720⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-232258725184,-231977255552⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e969_ok : ecellOkT e969 = true := by decide +kernel
theorem e969_pos {a z : ℝ} (ha1 : ((389553/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((155991/819200 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e969 e969_ok ha1 ha2 hz1 hz2 hz

-- box ['155991/819200', '195201/1024000', '1999/2000', '3999/4000']  interval_lower 150916503/549755813888
noncomputable def e970 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1308879203860,0,true,191650478656,191650478720⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨890144051692,0,false,-232258725184,-232258725120⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1309107105563,0,true,191841908672,191841908736⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨889916149989,0,false,-232540266880,-232540266816⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1308774520071,0,true,191562536512,191562536576⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨890248735481,0,false,-232129426752,-232129426688⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1309054706694,0,true,191797898304,191797898368⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨889968548858,0,false,-232475528832,-232475528768⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538505426,0,true,26877312,26877376⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484750126,0,false,-26878016,-26877952⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565445918,0,true,53816768,53816832⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457809634,0,false,-53819520,-53819456⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625141,0,false,-2688,-2624⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627119,0,false,-704,-640⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1308826856948,0,true,191606504256,191606504320⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨890196398604,0,false,-232194067840,-232194067776⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1309080914732,0,true,191819910912,191819910976⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨889942340820,0,false,-232507908032,-232507907968⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1059567269821,0,false,-40687997056,-40687996992⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1059664059041,0,false,-40587563584,-40587563520⟩
    { al := (155991/819200), au := (195201/1024000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨209367576084,209595477787⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191650478656,191650478720⟩ : DyadicInterval 40),(⟨-232258725184,-232258725120⟩ : DyadicInterval 40),(⟨742067386810,742067406140⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191841908672,191841908736⟩ : DyadicInterval 40),(⟨-232540266880,-232540266816⟩ : DyadicInterval 40),(⟨742023429330,742023448659⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191562536512,191562536576⟩ : DyadicInterval 40),(⟨-232129426752,-232129426688⟩ : DyadicInterval 40),(⟨742087561719,742087581049⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191797898304,191797898368⟩ : DyadicInterval 40),(⟨-232475528832,-232475528768⟩ : DyadicInterval 40),(⟨742033540319,742033559648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨26877650,53818142⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26877312,26877376⟩ : DyadicInterval 40),(⟨-26878016,-26877952⟩ : DyadicInterval 40),(⟨762123383246,762123402575⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53816768,53816832⟩ : DyadicInterval 40),(⟨-53819520,-53819456⟩ : DyadicInterval 40),(⟨762123382293,762123401622⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2688,-640⟩ : DyadicInterval 40),(⟨762123383936,762123404224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨209315229172,209569286956⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191606504256,191606504320⟩ : DyadicInterval 40),(⟨-232194067840,-232194067776⟩ : DyadicInterval 40),(⟨742077476508,742077495837⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191819910912,191819910976⟩ : DyadicInterval 40),(⟨-232507908032,-232507907968⟩ : DyadicInterval 40),(⟨742028483511,742028502840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-40687997056,-40587563520⟩ : DyadicInterval 40),(⟨782417165376,782467401408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨191650478656,191841908736⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-232540266880,-232258725120⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e970_ok : ecellOkT e970 = true := by decide +kernel
theorem e970_pos {a z : ℝ} (ha1 : ((155991/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((195201/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e970 e970_ok ha1 ha2 hz1 hz2 hz

-- box ['389553/2048000', '155991/819200', '3999/4000', '1']  interval_lower 74300025/274877906944
noncomputable def e971 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1308651302158,0,true,191459015296,191459015360⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨890371953394,0,false,-231977255616,-231977255552⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1308879203861,0,true,191650478656,191650478720⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨890144051691,0,false,-232258725184,-232258725120⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1308599017239,0,true,191415085312,191415085376⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨890424238313,0,false,-231912691328,-231912691264⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538506308,0,true,26878144,26878208⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484749244,0,false,-26878912,-26878848⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627118,0,false,-704,-640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1308625154423,0,true,191437046144,191437046208⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨890398101129,0,false,-231944966464,-231944966400⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1308879212378,0,true,191650485824,191650485888⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨890144043174,0,false,-232258735744,-232258735680⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1059644122626,0,false,-40608249856,-40608249792⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1059740818699,0,false,-40507920320,-40507920256⟩
    { al := (389553/2048000), au := (155991/819200), zl := (3999/4000), zu := 1,
      A := ⟨209139674382,209367576085⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191459015296,191459015360⟩ : DyadicInterval 40),(⟨-231977255616,-231977255552⟩ : DyadicInterval 40),(⟨742111295302,742111314632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191650478656,191650478720⟩ : DyadicInterval 40),(⟨-232258725184,-232258725120⟩ : DyadicInterval 40),(⟨742067386810,742067406140⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191415085312,191415085376⟩ : DyadicInterval 40),(⟨-231912691328,-231912691264⟩ : DyadicInterval 40),(⟨742121361798,742121381127⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191650478656,191650478720⟩ : DyadicInterval 40),(⟨-232258725184,-232258725120⟩ : DyadicInterval 40),(⟨742067386810,742067406140⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,26878532⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26878144,26878208⟩ : DyadicInterval 40),(⟨-26878912,-26878848⟩ : DyadicInterval 40),(⟨762123383278,762123402607⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-704,0⟩ : DyadicInterval 40),(⟨762123383616,762123403232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨209113526647,209367584602⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191437046144,191437046208⟩ : DyadicInterval 40),(⟨-231944966464,-231944966400⟩ : DyadicInterval 40),(⟨742116329849,742116349178⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191650485824,191650485888⟩ : DyadicInterval 40),(⟨-232258735744,-232258735680⟩ : DyadicInterval 40),(⟨742067385176,742067404506⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-40608249856,-40507920256⟩ : DyadicInterval 40),(⟨782377343744,782427527808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨191459015296,191650478720⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-232258725184,-231977255552⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e971_ok : ecellOkT e971 = true := by decide +kernel
theorem e971_pos {a z : ℝ} (ha1 : ((389553/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((155991/819200 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e971 e971_ok ha1 ha2 hz1 hz2 hz

-- box ['155991/819200', '195201/1024000', '3999/4000', '1']  interval_lower 150550231/549755813888
noncomputable def e972 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1308879203860,0,true,191650478656,191650478720⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨890144051692,0,false,-232258725184,-232258725120⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1309107105563,0,true,191841908672,191841908736⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨889916149989,0,false,-232540266880,-232540266816⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1308826861965,0,true,191606508480,191606508544⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨890196393587,0,false,-232194074048,-232194073984⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538537159,0,true,26908992,26909056⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484718393,0,false,-26909760,-26909696⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627117,0,false,-704,-640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1308853027639,0,true,191628489344,191628489408⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨890170227913,0,false,-232226392640,-232226392576⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1309107114080,0,true,191841915840,191841915904⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨889916141472,0,false,-232540277440,-232540277376⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1059557281892,0,false,-40698361536,-40698361472⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1059654094132,0,false,-40597903232,-40597903168⟩
    { al := (155991/819200), au := (195201/1024000), zl := (3999/4000), zu := 1,
      A := ⟨209367576084,209595477787⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191650478656,191650478720⟩ : DyadicInterval 40),(⟨-232258725184,-232258725120⟩ : DyadicInterval 40),(⟨742067386810,742067406140⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191841908672,191841908736⟩ : DyadicInterval 40),(⟨-232540266880,-232540266816⟩ : DyadicInterval 40),(⟨742023429330,742023448659⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191606508480,191606508544⟩ : DyadicInterval 40),(⟨-232194074048,-232194073984⟩ : DyadicInterval 40),(⟨742077475539,742077494869⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191841908672,191841908736⟩ : DyadicInterval 40),(⟨-232540266880,-232540266816⟩ : DyadicInterval 40),(⟨742023429330,742023448659⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,26909383⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26908992,26909056⟩ : DyadicInterval 40),(⟨-26909760,-26909696⟩ : DyadicInterval 40),(⟨762123383277,762123402606⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-704,0⟩ : DyadicInterval 40),(⟨762123383616,762123403232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨209341399863,209595486304⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191628489344,191628489408⟩ : DyadicInterval 40),(⟨-232226392640,-232226392576⟩ : DyadicInterval 40),(⟨742072432528,742072451857⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191841915840,191841915904⟩ : DyadicInterval 40),(⟨-232540277440,-232540277376⟩ : DyadicInterval 40),(⟨742023427693,742023447022⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-40698361536,-40597903168⟩ : DyadicInterval 40),(⟨782422335200,782472583648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨191650478656,191841908736⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-232540266880,-232258725120⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e972_ok : ecellOkT e972 = true := by decide +kernel
theorem e972_pos {a z : ℝ} (ha1 : ((155991/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((195201/1024000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e972 e972_ok ha1 ha2 hz1 hz2 hz

-- box ['195201/1024000', '781653/4096000', '999/1000', '3997/4000']  interval_lower 307221785/1099511627776
noncomputable def e973 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1309107105562,0,true,191841908672,191841908736⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨889916149990,0,false,-232540266880,-232540266816⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1309335007265,0,true,192033305344,192033305408⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨889688248287,0,false,-232821880704,-232821880640⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1308897510084,0,true,191665856512,191665856576⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨890125745468,0,false,-232281337408,-232281337344⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1309177639731,0,true,191901148352,191901148416⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨889845615821,0,false,-232627416896,-232627416832⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592352695,0,true,80721920,80721984⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430902857,0,false,-80727936,-80727872⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099619385757,0,true,107752640,107752704⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099403869795,0,false,-107763264,-107763200⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511617215,0,false,-10624,-10560⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621850,0,false,-5952,-5888⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1309002303844,0,true,191753882752,191753882816⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨890020951708,0,false,-232410789632,-232410789568⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1309256332798,0,true,191967236608,191967236672⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨889766922754,0,false,-232724656000,-232724655936⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1059500371711,0,false,-40757419328,-40757419264⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1059597231011,0,false,-40656906816,-40656906752⟩
    { al := (195201/1024000), au := (781653/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨209595477786,209823379489⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191841908672,191841908736⟩ : DyadicInterval 40),(⟨-232540266880,-232540266816⟩ : DyadicInterval 40),(⟨742023429330,742023448660⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192033305344,192033305408⟩ : DyadicInterval 40),(⟨-232821880704,-232821880640⟩ : DyadicInterval 40),(⟨741979422850,741979442179⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191665856512,191665856576⟩ : DyadicInterval 40),(⟨-232281337408,-232281337344⟩ : DyadicInterval 40),(⟨742063857747,742063877077⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191901148352,191901148416⟩ : DyadicInterval 40),(⟨-232627416896,-232627416832⟩ : DyadicInterval 40),(⟨742009814809,742009834138⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨80724919,107757981⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80721920,80721984⟩ : DyadicInterval 40),(⟨-80727936,-80727872⟩ : DyadicInterval 40),(⟨762123380633,762123399962⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨107752640,107752704⟩ : DyadicInterval 40),(⟨-107763264,-107763200⟩ : DyadicInterval 40),(⟨762123378302,762123397632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-10624,-5888⟩ : DyadicInterval 40),(⟨762123386560,762123408192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨209490676068,209744705022⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191753882752,191753882816⟩ : DyadicInterval 40),(⟨-232410789632,-232410789568⟩ : DyadicInterval 40),(⟨742043649512,742043668841⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191967236608,191967236672⟩ : DyadicInterval 40),(⟨-232724656000,-232724655936⟩ : DyadicInterval 40),(⟨741994619979,741994639309⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-40757419328,-40656906752⟩ : DyadicInterval 40),(⟨782451836992,782502112544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨191841908672,192033305408⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-232821880704,-232540266816⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e973_ok : ecellOkT e973 = true := by decide +kernel
theorem e973_pos {a z : ℝ} (ha1 : ((195201/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((781653/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e973 e973_ok ha1 ha2 hz1 hz2 hz

-- box ['781653/4096000', '391251/2048000', '999/1000', '3997/4000']  interval_lower 311164739/1099511627776
noncomputable def e974 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1309335007264,0,true,192033305344,192033305408⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨889688248288,0,false,-232821880704,-232821880640⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1309562908967,0,true,192224668736,192224668800⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨889460346585,0,false,-233103566656,-233103566592⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1309125183884,0,true,191857092416,191857092480⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨889898071668,0,false,-232562603328,-232562603264⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1309405370507,0,true,192092391168,192092391232⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨889617885045,0,false,-232908841792,-232908841728⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592445259,0,true,80814464,80814528⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430810293,0,false,-80820480,-80820416⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099619509200,0,true,107876096,107876160⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099403746352,0,false,-107886720,-107886656⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511617190,0,false,-10624,-10560⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621836,0,false,-5952,-5888⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1309230091589,0,true,191945199104,191945199168⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨889793163963,0,false,-232692229440,-232692229376⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1309484149036,0,true,192158539776,192158539840⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨889539106516,0,false,-233006211392,-233006211328⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1059413407283,0,false,-40847671616,-40847671552⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1059510382721,0,false,-40747030336,-40747030272⟩
    { al := (781653/4096000), au := (391251/2048000), zl := (999/1000), zu := (3997/4000),
      A := ⟨209823379488,210051281191⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192033305344,192033305408⟩ : DyadicInterval 40),(⟨-232821880704,-232821880640⟩ : DyadicInterval 40),(⟨741979422850,741979442180⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192224668736,192224668800⟩ : DyadicInterval 40),(⟨-233103566656,-233103566592⟩ : DyadicInterval 40),(⟨741935367319,741935386649⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191857092416,191857092480⟩ : DyadicInterval 40),(⟨-232562603328,-232562603264⟩ : DyadicInterval 40),(⟨742019940337,742019959667⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192092391168,192092391232⟩ : DyadicInterval 40),(⟨-232908841792,-232908841728⟩ : DyadicInterval 40),(⟨741965826202,741965845532⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨80817483,107881424⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80814464,80814528⟩ : DyadicInterval 40),(⟨-80820480,-80820416⟩ : DyadicInterval 40),(⟨762123380619,762123399948⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨107876096,107876160⟩ : DyadicInterval 40),(⟨-107886720,-107886656⟩ : DyadicInterval 40),(⟨762123378278,762123397608⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-10624,-5888⟩ : DyadicInterval 40),(⟨762123386560,762123408192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨209718463813,209972521260⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191945199104,191945199168⟩ : DyadicInterval 40),(⟨-232692229440,-232692229376⟩ : DyadicInterval 40),(⟨741999687529,741999706859⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192158539776,192158539840⟩ : DyadicInterval 40),(⟨-233006211392,-233006211328⟩ : DyadicInterval 40),(⟨741950597869,741950617199⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-40847671616,-40747030272⟩ : DyadicInterval 40),(⟨782496898752,782547238688⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨192033305344,192224668800⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-233103566656,-232821880640⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e974_ok : ecellOkT e974 = true := by decide +kernel
theorem e974_pos {a z : ℝ} (ha1 : ((781653/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((391251/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e974 e974_ok ha1 ha2 hz1 hz2 hz

-- box ['195201/1024000', '781653/4096000', '3997/4000', '1999/2000']  interval_lower 153243957/549755813888
noncomputable def e975 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1309107105562,0,true,191841908672,191841908736⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨889916149990,0,false,-232540266880,-232540266816⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1309335007265,0,true,192033305344,192033305408⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨889688248287,0,false,-232821880704,-232821880640⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1308949908953,0,true,191709872192,191709872256⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨890073346599,0,false,-232346064064,-232346064000⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1309230095576,0,true,191945202432,191945202496⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨889793159976,0,false,-232692234368,-232692234304⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565444669,0,true,53815552,53815616⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457810883,0,false,-53818240,-53818176⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592446879,0,true,80816128,80816192⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430808673,0,false,-80822080,-80822016⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621835,0,false,-5952,-5888⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625142,0,false,-2688,-2624⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1309028502670,0,true,191775888576,191775888640⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨889994752882,0,false,-232443155520,-232443155456⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1309282560281,0,true,191989262208,191989262272⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨889740695271,0,false,-232757066560,-232757066496⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1059490364687,0,false,-40767804288,-40767804224⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1059587247027,0,false,-40667266944,-40667266880⟩
    { al := (195201/1024000), au := (781653/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨209595477786,209823379489⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191841908672,191841908736⟩ : DyadicInterval 40),(⟨-232540266880,-232540266816⟩ : DyadicInterval 40),(⟨742023429330,742023448660⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192033305344,192033305408⟩ : DyadicInterval 40),(⟨-232821880704,-232821880640⟩ : DyadicInterval 40),(⟨741979422850,741979442179⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191709872192,191709872256⟩ : DyadicInterval 40),(⟨-232346064064,-232346064000⟩ : DyadicInterval 40),(⟨742053754533,742053773863⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191945202432,191945202496⟩ : DyadicInterval 40),(⟨-232692234368,-232692234304⟩ : DyadicInterval 40),(⟨741999686772,741999706102⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨53816893,80819103⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53815552,53815616⟩ : DyadicInterval 40),(⟨-53818240,-53818176⟩ : DyadicInterval 40),(⟨762123382261,762123401590⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80816128,80816192⟩ : DyadicInterval 40),(⟨-80822080,-80822016⟩ : DyadicInterval 40),(⟨762123380587,762123399916⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5952,-2624⟩ : DyadicInterval 40),(⟨762123384928,762123405856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨209516874894,209770932505⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191775888576,191775888640⟩ : DyadicInterval 40),(⟨-232443155520,-232443155456⟩ : DyadicInterval 40),(⟨742038595724,742038615054⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191989262208,191989262272⟩ : DyadicInterval 40),(⟨-232757066560,-232757066496⟩ : DyadicInterval 40),(⟨741989554394,741989573724⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-40767804288,-40667266880⟩ : DyadicInterval 40),(⟨782457017056,782507305024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨191841908672,192033305408⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-232821880704,-232540266816⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e975_ok : ecellOkT e975 = true := by decide +kernel
theorem e975_pos {a z : ℝ} (ha1 : ((195201/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((781653/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e975 e975_ok ha1 ha2 hz1 hz2 hz

-- box ['781653/4096000', '391251/2048000', '3997/4000', '1999/2000']  interval_lower 310427739/1099511627776
noncomputable def e976 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1309335007264,0,true,192033305344,192033305408⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨889688248288,0,false,-232821880704,-232821880640⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1309562908967,0,true,192224668736,192224668800⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨889460346585,0,false,-233103566656,-233103566592⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1309177639729,0,true,191901148352,191901148416⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨889845615823,0,false,-232627416896,-232627416832⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1309457883327,0,true,192136485440,192136485504⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨889565372225,0,false,-232973746240,-232973746176⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565506379,0,true,53877248,53877312⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457749173,0,false,-53879936,-53879872⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592539462,0,true,80908672,80908736⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430716090,0,false,-80914688,-80914624⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621821,0,false,-6016,-5952⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625136,0,false,-2688,-2624⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1309256318909,0,true,191967224960,191967225024⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨889766936643,0,false,-232724638848,-232724638784⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1309510405008,0,true,192180585408,192180585472⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨889512850544,0,false,-233038665472,-233038665408⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1059403378508,0,false,-40858080000,-40858079936⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1059500377011,0,false,-40757413824,-40757413760⟩
    { al := (781653/4096000), au := (391251/2048000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨209823379488,210051281191⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192033305344,192033305408⟩ : DyadicInterval 40),(⟨-232821880704,-232821880640⟩ : DyadicInterval 40),(⟨741979422850,741979442180⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192224668736,192224668800⟩ : DyadicInterval 40),(⟨-233103566656,-233103566592⟩ : DyadicInterval 40),(⟨741935367319,741935386649⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191901148352,191901148416⟩ : DyadicInterval 40),(⟨-232627416896,-232627416832⟩ : DyadicInterval 40),(⟨742009814809,742009834139⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192136485440,192136485504⟩ : DyadicInterval 40),(⟨-232973746240,-232973746176⟩ : DyadicInterval 40),(⟨741955675852,741955695182⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨53878603,80911686⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53877248,53877312⟩ : DyadicInterval 40),(⟨-53879936,-53879872⟩ : DyadicInterval 40),(⟨762123382255,762123401584⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80908672,80908736⟩ : DyadicInterval 40),(⟨-80914688,-80914624⟩ : DyadicInterval 40),(⟨762123380605,762123399935⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6016,-2624⟩ : DyadicInterval 40),(⟨762123384928,762123405888⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨209744691133,209998777232⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191967224960,191967225024⟩ : DyadicInterval 40),(⟨-232724638848,-232724638784⟩ : DyadicInterval 40),(⟨741994622657,741994641986⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192180585408,192180585472⟩ : DyadicInterval 40),(⟨-233038665472,-233038665408⟩ : DyadicInterval 40),(⟨741945521171,741945540500⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-40858080000,-40757413760⟩ : DyadicInterval 40),(⟨782502090496,782552442880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨192033305344,192224668800⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-233103566656,-232821880640⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e976_ok : ecellOkT e976 = true := by decide +kernel
theorem e976_pos {a z : ℝ} (ha1 : ((781653/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((391251/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e976 e976_ok ha1 ha2 hz1 hz2 hz

-- box ['391251/2048000', '783351/4096000', '999/1000', '3997/4000']  interval_lower 157562293/549755813888
noncomputable def e977 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1309562908966,0,true,192224668736,192224668800⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨889460346586,0,false,-233103566656,-233103566592⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1309790810670,0,true,192415998784,192415998848⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨889232444882,0,false,-233385324736,-233385324672⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1309352857684,0,true,192048295104,192048295168⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨889670397868,0,false,-232843941184,-232843941120⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1309633101283,0,true,192283600768,192283600832⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨889390154269,0,false,-233190338688,-233190338624⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592537839,0,true,80907072,80907136⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430717713,0,false,-80913088,-80913024⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099619632664,0,true,107999552,107999616⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099403622888,0,false,-108010240,-108010176⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511617166,0,false,-10624,-10560⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621823,0,false,-6016,-5952⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1309457879343,0,true,192136482112,192136482176⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨889565376209,0,false,-232973741312,-232973741248⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1309711965281,0,true,192349809600,192349809664⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨889311290271,0,false,-233287838912,-233287838848⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1059326348447,0,false,-40938029312,-40938029248⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1059423440045,0,false,-40837259136,-40837259072⟩
    { al := (391251/2048000), au := (783351/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨210051281190,210279182894⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192224668736,192224668800⟩ : DyadicInterval 40),(⟨-233103566656,-233103566592⟩ : DyadicInterval 40),(⟨741935367320,741935386649⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192415998784,192415998848⟩ : DyadicInterval 40),(⟨-233385324736,-233385324672⟩ : DyadicInterval 40),(⟨741891262765,741891282094⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192048295104,192048295168⟩ : DyadicInterval 40),(⟨-232843941184,-232843941120⟩ : DyadicInterval 40),(⟨741975973968,741975993297⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192283600768,192283600832⟩ : DyadicInterval 40),(⟨-233190338688,-233190338624⟩ : DyadicInterval 40),(⟨741921788598,741921807928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨80910063,108004888⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80907072,80907136⟩ : DyadicInterval 40),(⟨-80913088,-80913024⟩ : DyadicInterval 40),(⟨762123380605,762123399935⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨107999552,107999616⟩ : DyadicInterval 40),(⟨-108010240,-108010176⟩ : DyadicInterval 40),(⟨762123378286,762123397616⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-10624,-5952⟩ : DyadicInterval 40),(⟨762123386592,762123408192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨209946251567,210200337505⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192136482112,192136482176⟩ : DyadicInterval 40),(⟨-232973741312,-232973741248⟩ : DyadicInterval 40),(⟨741955676610,741955695940⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192349809600,192349809664⟩ : DyadicInterval 40),(⟨-233287838912,-233287838848⟩ : DyadicInterval 40),(⟨741906526811,741906546141⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-40938029312,-40837259072⟩ : DyadicInterval 40),(⟨782542013152,782592417536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨192224668736,192415998848⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-233385324736,-233103566592⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e977_ok : ecellOkT e977 = true := by decide +kernel
theorem e977_pos {a z : ℝ} (ha1 : ((391251/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((783351/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e977 e977_ok ha1 ha2 hz1 hz2 hz

-- box ['783351/4096000', '3921/20480', '999/1000', '3997/4000']  interval_lower 159550679/549755813888
noncomputable def e978 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1309790810669,0,true,192415998784,192415998848⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨889232444883,0,false,-233385324736,-233385324672⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1310018712372,0,true,192607295616,192607295680⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨889004543180,0,false,-233667155072,-233667155008⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1309580531486,0,true,192239464512,192239464576⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨889442724066,0,false,-233125351040,-233125350976⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1309860832059,0,true,192474777088,192474777152⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨889162423493,0,false,-233471907712,-233471907648⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592630435,0,true,80999616,80999680⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430625117,0,false,-81005696,-81005632⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099619756151,0,true,108123008,108123072⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099403499401,0,false,-108133696,-108133632⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511617142,0,false,-10688,-10624⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621809,0,false,-6016,-5952⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1309685667094,0,true,192327731840,192327731904⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨889337588458,0,false,-233255325248,-233255325184⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1309939781524,0,true,192541046144,192541046208⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨889083474028,0,false,-233569538560,-233569538496⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1059239195205,0,false,-41028492416,-41028492352⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1059336402988,0,false,-40927593408,-40927593344⟩
    { al := (783351/4096000), au := (3921/20480), zl := (999/1000), zu := (3997/4000),
      A := ⟨210279182893,210507084596⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192415998784,192415998848⟩ : DyadicInterval 40),(⟨-233385324736,-233385324672⟩ : DyadicInterval 40),(⟨741891262765,741891282094⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192607295616,192607295680⟩ : DyadicInterval 40),(⟨-233667155072,-233667155008⟩ : DyadicInterval 40),(⟨741847109150,741847128479⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192239464512,192239464576⟩ : DyadicInterval 40),(⟨-233125351040,-233125350976⟩ : DyadicInterval 40),(⟨741931958691,741931978021⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192474777088,192474777152⟩ : DyadicInterval 40),(⟨-233471907712,-233471907648⟩ : DyadicInterval 40),(⟨741877702076,741877721406⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨81002659,108128375⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨80999616,80999680⟩ : DyadicInterval 40),(⟨-81005696,-81005632⟩ : DyadicInterval 40),(⟨762123380624,762123399953⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨108123008,108123072⟩ : DyadicInterval 40),(⟨-108133696,-108133632⟩ : DyadicInterval 40),(⟨762123378261,762123397591⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-10688,-5952⟩ : DyadicInterval 40),(⟨762123386592,762123408224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨210174039318,210428153748⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192327731840,192327731904⟩ : DyadicInterval 40),(⟨-233255325248,-233255325184⟩ : DyadicInterval 40),(⟨741911616708,741911636037⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192541046144,192541046208⟩ : DyadicInterval 40),(⟨-233569538560,-233569538496⟩ : DyadicInterval 40),(⟨741862406757,741862426087⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-41028492416,-40927593344⟩ : DyadicInterval 40),(⟨782587180288,782637649088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨192415998784,192607295680⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-233667155072,-233385324672⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e978_ok : ecellOkT e978 = true := by decide +kernel
theorem e978_pos {a z : ℝ} (ha1 : ((783351/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3921/20480 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e978 e978_ok ha1 ha2 hz1 hz2 hz

-- box ['391251/2048000', '783351/4096000', '3997/4000', '1999/2000']  interval_lower 157192315/549755813888
noncomputable def e979 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1309562908966,0,true,192224668736,192224668800⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨889460346586,0,false,-233103566656,-233103566592⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1309790810670,0,true,192415998784,192415998848⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨889232444882,0,false,-233385324736,-233385324672⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1309405370505,0,true,192092391168,192092391232⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨889617885047,0,false,-232908841792,-232908841728⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1309685671079,0,true,192327735232,192327735296⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨889337584473,0,false,-233255330176,-233255330112⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565568101,0,true,53938944,53939008⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457687451,0,false,-53941696,-53941632⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592632063,0,true,81001280,81001344⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430623489,0,false,-81007296,-81007232⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621808,0,false,-6016,-5952⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625130,0,false,-2688,-2624⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1309484135142,0,true,192158528064,192158528128⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨889539120410,0,false,-233006194240,-233006194176⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1309738249744,0,true,192371875328,192371875392⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨889285005808,0,false,-233320336512,-233320336448⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1059316297897,0,false,-40948461120,-40948461056⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1059413412591,0,false,-40847666112,-40847666048⟩
    { al := (391251/2048000), au := (783351/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨210051281190,210279182894⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192224668736,192224668800⟩ : DyadicInterval 40),(⟨-233103566656,-233103566592⟩ : DyadicInterval 40),(⟨741935367320,741935386649⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192415998784,192415998848⟩ : DyadicInterval 40),(⟨-233385324736,-233385324672⟩ : DyadicInterval 40),(⟨741891262765,741891282094⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192092391168,192092391232⟩ : DyadicInterval 40),(⟨-232908841792,-232908841728⟩ : DyadicInterval 40),(⟨741965826203,741965845532⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192327735232,192327735296⟩ : DyadicInterval 40),(⟨-233255330176,-233255330112⟩ : DyadicInterval 40),(⟨741911615909,741911635239⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨53940325,81004287⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53938944,53939008⟩ : DyadicInterval 40),(⟨-53941696,-53941632⟩ : DyadicInterval 40),(⟨762123382281,762123401610⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81001280,81001344⟩ : DyadicInterval 40),(⟨-81007296,-81007232⟩ : DyadicInterval 40),(⟨762123380591,762123399921⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6016,-2624⟩ : DyadicInterval 40),(⟨762123384928,762123405888⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨209972507366,210226621968⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192158528064,192158528128⟩ : DyadicInterval 40),(⟨-233006194240,-233006194176⟩ : DyadicInterval 40),(⟨741950600591,741950619921⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192371875328,192371875392⟩ : DyadicInterval 40),(⟨-233320336512,-233320336448⟩ : DyadicInterval 40),(⟨741901438936,741901458265⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-40948461120,-40847666048⟩ : DyadicInterval 40),(⟨782547216640,782597633440⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨192224668736,192415998848⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-233385324736,-233103566592⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e979_ok : ecellOkT e979 = true := by decide +kernel
theorem e979_pos {a z : ℝ} (ha1 : ((391251/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((783351/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e979 e979_ok ha1 ha2 hz1 hz2 hz

-- box ['783351/4096000', '3921/20480', '3997/4000', '1999/2000']  interval_lower 9948705/34359738368
noncomputable def e980 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1309790810669,0,true,192415998784,192415998848⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨889232444883,0,false,-233385324736,-233385324672⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1310018712372,0,true,192607295616,192607295680⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨889004543180,0,false,-233667155072,-233667155008⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1309633101281,0,true,192283600768,192283600832⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨889390154271,0,false,-233190338688,-233190338624⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1309913458830,0,true,192518951680,192518951744⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨889109796722,0,false,-233536986304,-233536986240⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565629833,0,true,54000704,54000768⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457625719,0,false,-54003392,-54003328⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592724679,0,true,81093888,81093952⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430530873,0,false,-81099904,-81099840⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621794,0,false,-6016,-5952⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625124,0,false,-2688,-2624⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1309711951381,0,true,192349797888,192349797952⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨889311304171,0,false,-233287821696,-233287821632⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1309966094470,0,true,192563131968,192563132032⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨889057161082,0,false,-233602079744,-233602079680⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1059229122859,0,false,-41038947712,-41038947648⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1059326353763,0,false,-40938023744,-40938023680⟩
    { al := (783351/4096000), au := (3921/20480), zl := (3997/4000), zu := (1999/2000),
      A := ⟨210279182893,210507084596⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192415998784,192415998848⟩ : DyadicInterval 40),(⟨-233385324736,-233385324672⟩ : DyadicInterval 40),(⟨741891262765,741891282094⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192607295616,192607295680⟩ : DyadicInterval 40),(⟨-233667155072,-233667155008⟩ : DyadicInterval 40),(⟨741847109150,741847128479⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192283600768,192283600832⟩ : DyadicInterval 40),(⟨-233190338688,-233190338624⟩ : DyadicInterval 40),(⟨741921788599,741921807929⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192518951680,192518951744⟩ : DyadicInterval 40),(⟨-233536986304,-233536986240⟩ : DyadicInterval 40),(⟨741867507060,741867526389⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨54002057,81096903⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54000704,54000768⟩ : DyadicInterval 40),(⟨-54003392,-54003328⟩ : DyadicInterval 40),(⟨762123382243,762123401572⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81093888,81093952⟩ : DyadicInterval 40),(⟨-81099904,-81099840⟩ : DyadicInterval 40),(⟨762123380578,762123399907⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6016,-2624⟩ : DyadicInterval 40),(⟨762123384928,762123405888⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨210200323605,210454466694⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192349797888,192349797952⟩ : DyadicInterval 40),(⟨-233287821696,-233287821632⟩ : DyadicInterval 40),(⟨741906529515,741906548844⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192563131968,192563132032⟩ : DyadicInterval 40),(⟨-233602079744,-233602079680⟩ : DyadicInterval 40),(⟨741857307706,741857327036⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-41038947712,-40938023680⟩ : DyadicInterval 40),(⟨782592395456,782642876736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨192415998784,192607295680⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-233667155072,-233385324672⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e980_ok : ecellOkT e980 = true := by decide +kernel
theorem e980_pos {a z : ℝ} (ha1 : ((783351/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3921/20480 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e980 e980_ok ha1 ha2 hz1 hz2 hz

-- box ['195201/1024000', '781653/4096000', '1999/2000', '3999/4000']  interval_lower 305752985/1099511627776
noncomputable def e981 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1309107105562,0,true,191841908672,191841908736⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨889916149990,0,false,-232540266880,-232540266816⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1309335007265,0,true,192033305344,192033305408⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨889688248287,0,false,-232821880704,-232821880640⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1309002307823,0,true,191753886144,191753886208⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨890020947729,0,false,-232410794496,-232410794432⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1309282551421,0,true,191989254784,191989254848⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨889740704131,0,false,-232757055616,-232757055552⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538536277,0,true,26908160,26908224⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484719275,0,false,-26908864,-26908800⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565507631,0,true,53878528,53878592⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457747921,0,false,-53881216,-53881152⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625135,0,false,-2688,-2624⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627118,0,false,-704,-640⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1309054701676,0,true,191797894080,191797894144⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨889968553876,0,false,-232475522624,-232475522560⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1309308787944,0,true,192011287488,192011287552⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨889714467608,0,false,-232789478272,-232789478208⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1059480356343,0,false,-40778190784,-40778190720⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1059577261727,0,false,-40677628480,-40677628416⟩
    { al := (195201/1024000), au := (781653/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨209595477786,209823379489⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191841908672,191841908736⟩ : DyadicInterval 40),(⟨-232540266880,-232540266816⟩ : DyadicInterval 40),(⟨742023429330,742023448660⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192033305344,192033305408⟩ : DyadicInterval 40),(⟨-232821880704,-232821880640⟩ : DyadicInterval 40),(⟨741979422850,741979442179⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191753886144,191753886208⟩ : DyadicInterval 40),(⟨-232410794496,-232410794432⟩ : DyadicInterval 40),(⟨742043648694,742043668024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191989254784,191989254848⟩ : DyadicInterval 40),(⟨-232757055616,-232757055552⟩ : DyadicInterval 40),(⟨741989556098,741989575427⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨26908501,53879855⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26908160,26908224⟩ : DyadicInterval 40),(⟨-26908864,-26908800⟩ : DyadicInterval 40),(⟨762123383245,762123402574⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53878528,53878592⟩ : DyadicInterval 40),(⟨-53881216,-53881152⟩ : DyadicInterval 40),(⟨762123382255,762123401584⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2688,-640⟩ : DyadicInterval 40),(⟨762123383936,762123404224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨209543073900,209797160168⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191797894080,191797894144⟩ : DyadicInterval 40),(⟨-232475522624,-232475522560⟩ : DyadicInterval 40),(⟨742033541289,742033560618⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192011287488,192011287552⟩ : DyadicInterval 40),(⟨-232789478272,-232789478208⟩ : DyadicInterval 40),(⟨741984488132,741984507462⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-40778190784,-40677628416⟩ : DyadicInterval 40),(⟨782462197824,782512498272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨191841908672,192033305408⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-232821880704,-232540266816⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e981_ok : ecellOkT e981 = true := by decide +kernel
theorem e981_pos {a z : ℝ} (ha1 : ((195201/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((781653/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e981 e981_ok ha1 ha2 hz1 hz2 hz

-- box ['781653/4096000', '391251/2048000', '1999/2000', '3999/4000']  interval_lower 154845007/549755813888
noncomputable def e982 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1309335007264,0,true,192033305344,192033305408⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨889688248288,0,false,-232821880704,-232821880640⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1309562908967,0,true,192224668736,192224668800⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨889460346585,0,false,-233103566656,-233103566592⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1309230095574,0,true,191945202432,191945202496⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨889793159978,0,false,-232692234368,-232692234304⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1309510396147,0,true,192180577984,192180578048⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨889512859405,0,false,-233038654528,-233038654464⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538567133,0,true,26939008,26939072⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484688419,0,false,-26939712,-26939648⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565569355,0,true,53940224,53940288⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457686197,0,false,-53942912,-53942848⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625129,0,false,-2688,-2624⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627116,0,false,-704,-640⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1309282546392,0,true,191989250560,191989250624⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨889740709160,0,false,-232757049408,-232757049344⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1309536661158,0,true,192202630784,192202630848⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨889486594394,0,false,-233071120704,-233071120640⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1059393348411,0,false,-40868489920,-40868489856⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1059490369988,0,false,-40767798784,-40767798720⟩
    { al := (781653/4096000), au := (391251/2048000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨209823379488,210051281191⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192033305344,192033305408⟩ : DyadicInterval 40),(⟨-232821880704,-232821880640⟩ : DyadicInterval 40),(⟨741979422850,741979442180⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192224668736,192224668800⟩ : DyadicInterval 40),(⟨-233103566656,-233103566592⟩ : DyadicInterval 40),(⟨741935367319,741935386649⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191945202432,191945202496⟩ : DyadicInterval 40),(⟨-232692234368,-232692234304⟩ : DyadicInterval 40),(⟨741999686772,741999706102⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192180577984,192180578048⟩ : DyadicInterval 40),(⟨-233038654528,-233038654464⟩ : DyadicInterval 40),(⟨741945522879,741945542208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨26939357,53941579⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26939008,26939072⟩ : DyadicInterval 40),(⟨-26939712,-26939648⟩ : DyadicInterval 40),(⟨762123383243,762123402572⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53940224,53940288⟩ : DyadicInterval 40),(⟨-53942912,-53942848⟩ : DyadicInterval 40),(⟨762123382249,762123401578⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2688,-640⟩ : DyadicInterval 40),(⟨762123383936,762123404224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨209770918616,210025033382⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191989250560,191989250624⟩ : DyadicInterval 40),(⟨-232757049408,-232757049344⟩ : DyadicInterval 40),(⟨741989557072,741989576401⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192202630784,192202630848⟩ : DyadicInterval 40),(⟨-233071120704,-233071120640⟩ : DyadicInterval 40),(⟨741940443755,741940463085⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-40868489920,-40767798720⟩ : DyadicInterval 40),(⟨782507282976,782557647840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨192033305344,192224668800⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-233103566656,-232821880640⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e982_ok : ecellOkT e982 = true := by decide +kernel
theorem e982_pos {a z : ℝ} (ha1 : ((781653/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((391251/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e982 e982_ok ha1 ha2 hz1 hz2 hz

-- box ['195201/1024000', '781653/4096000', '3999/4000', '1']  interval_lower 305017669/1099511627776
noncomputable def e983 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1309107105562,0,true,191841908672,191841908736⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨889916149990,0,false,-232540266880,-232540266816⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1309335007265,0,true,192033305344,192033305408⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨889688248287,0,false,-232821880704,-232821880640⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1309054706692,0,true,191797898304,191797898368⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨889968548860,0,false,-232475528832,-232475528768⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538568016,0,true,26939904,26939968⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484687536,0,false,-26940608,-26940544⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627115,0,false,-704,-640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1309080900848,0,true,191819899264,191819899328⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨889942354704,0,false,-232507890880,-232507890816⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1309335015776,0,true,192033312512,192033312576⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨889688239776,0,false,-232821891200,-232821891136⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1059470346683,0,false,-40788578688,-40788578624⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1059567275114,0,false,-40687991552,-40687991488⟩
    { al := (195201/1024000), au := (781653/4096000), zl := (3999/4000), zu := 1,
      A := ⟨209595477786,209823379489⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191841908672,191841908736⟩ : DyadicInterval 40),(⟨-232540266880,-232540266816⟩ : DyadicInterval 40),(⟨742023429330,742023448660⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192033305344,192033305408⟩ : DyadicInterval 40),(⟨-232821880704,-232821880640⟩ : DyadicInterval 40),(⟨741979422850,741979442179⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191797898304,191797898368⟩ : DyadicInterval 40),(⟨-232475528832,-232475528768⟩ : DyadicInterval 40),(⟨742033540319,742033559648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192033305344,192033305408⟩ : DyadicInterval 40),(⟨-232821880704,-232821880640⟩ : DyadicInterval 40),(⟨741979422850,741979442179⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,26940240⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26939904,26939968⟩ : DyadicInterval 40),(⟨-26940608,-26940544⟩ : DyadicInterval 40),(⟨762123383243,762123402572⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-704,0⟩ : DyadicInterval 40),(⟨762123383616,762123403232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨209569273072,209823388000⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191819899264,191819899328⟩ : DyadicInterval 40),(⟨-232507890880,-232507890816⟩ : DyadicInterval 40),(⟨742028486182,742028505512⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192033312512,192033312576⟩ : DyadicInterval 40),(⟨-232821891200,-232821891136⟩ : DyadicInterval 40),(⟨741979421184,741979440514⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-40788578688,-40687991488⟩ : DyadicInterval 40),(⟨782467379360,782517692224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨191841908672,192033305408⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-232821880704,-232540266816⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e983_ok : ecellOkT e983 = true := by decide +kernel
theorem e983_pos {a z : ℝ} (ha1 : ((195201/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((781653/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e983 e983_ok ha1 ha2 hz1 hz2 hz

-- box ['781653/4096000', '391251/2048000', '3999/4000', '1']  interval_lower 308951975/1099511627776
noncomputable def e984 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1309335007264,0,true,192033305344,192033305408⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨889688248288,0,false,-232821880704,-232821880640⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1309562908967,0,true,192224668736,192224668800⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨889460346585,0,false,-233103566656,-233103566592⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1309282551419,0,true,191989254784,191989254848⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨889740704133,0,false,-232757055616,-232757055552⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538598879,0,true,26970752,26970816⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484656673,0,false,-26971456,-26971392⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627114,0,false,-704,-640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1309308774053,0,true,192011275840,192011275904⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨889714481499,0,false,-232789461120,-232789461056⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1309562917480,0,true,192224675904,192224675968⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨889460338072,0,false,-233103577152,-233103577088⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1059383316995,0,false,-40878901248,-40878901184⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1059480361645,0,false,-40778185280,-40778185216⟩
    { al := (781653/4096000), au := (391251/2048000), zl := (3999/4000), zu := 1,
      A := ⟨209823379488,210051281191⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192033305344,192033305408⟩ : DyadicInterval 40),(⟨-232821880704,-232821880640⟩ : DyadicInterval 40),(⟨741979422850,741979442180⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192224668736,192224668800⟩ : DyadicInterval 40),(⟨-233103566656,-233103566592⟩ : DyadicInterval 40),(⟨741935367319,741935386649⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨191989254784,191989254848⟩ : DyadicInterval 40),(⟨-232757055616,-232757055552⟩ : DyadicInterval 40),(⟨741989556098,741989575428⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192224668736,192224668800⟩ : DyadicInterval 40),(⟨-233103566656,-233103566592⟩ : DyadicInterval 40),(⟨741935367319,741935386649⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,26971103⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26970752,26970816⟩ : DyadicInterval 40),(⟨-26971456,-26971392⟩ : DyadicInterval 40),(⟨762123383242,762123402571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-704,0⟩ : DyadicInterval 40),(⟨762123383616,762123403232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨209797146277,210051289704⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192011275840,192011275904⟩ : DyadicInterval 40),(⟨-232789461120,-232789461056⟩ : DyadicInterval 40),(⟨741984490812,741984510141⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192224675904,192224675968⟩ : DyadicInterval 40),(⟨-233103577152,-233103577088⟩ : DyadicInterval 40),(⟨741935365650,741935384979⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-40878901248,-40778185216⟩ : DyadicInterval 40),(⟨782512476224,782562853504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨192033305344,192224668800⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-233103566656,-232821880640⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e984_ok : ecellOkT e984 = true := by decide +kernel
theorem e984_pos {a z : ℝ} (ha1 : ((781653/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((391251/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e984 e984_ok ha1 ha2 hz1 hz2 hz

-- box ['391251/2048000', '783351/4096000', '1999/2000', '3999/4000']  interval_lower 78411029/274877906944
noncomputable def e985 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1309562908966,0,true,192224668736,192224668800⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨889460346586,0,false,-233103566656,-233103566592⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1309790810670,0,true,192415998784,192415998848⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨889232444882,0,false,-233385324736,-233385324672⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1309457883325,0,true,192136485440,192136485504⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨889565372227,0,false,-232973746240,-232973746176⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1309738240875,0,true,192371867904,192371867968⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨889285014677,0,false,-233320325568,-233320325504⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538597995,0,true,26969856,26969920⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484657557,0,false,-26970560,-26970496⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565631090,0,true,54001984,54002048⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457624462,0,false,-54004672,-54004608⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625123,0,false,-2688,-2624⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627115,0,false,-704,-640⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1309510391114,0,true,192180573760,192180573824⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨889512864438,0,false,-233038648320,-233038648256⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1309764534375,0,true,192393940800,192393940864⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨889258721177,0,false,-233352835328,-233352835264⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1059306246025,0,false,-40958894464,-40958894400⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1059403383817,0,false,-40858074496,-40858074432⟩
    { al := (391251/2048000), au := (783351/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨210051281190,210279182894⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192224668736,192224668800⟩ : DyadicInterval 40),(⟨-233103566656,-233103566592⟩ : DyadicInterval 40),(⟨741935367320,741935386649⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192415998784,192415998848⟩ : DyadicInterval 40),(⟨-233385324736,-233385324672⟩ : DyadicInterval 40),(⟨741891262765,741891282094⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192136485440,192136485504⟩ : DyadicInterval 40),(⟨-232973746240,-232973746176⟩ : DyadicInterval 40),(⟨741955675853,741955695182⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192371867904,192371867968⟩ : DyadicInterval 40),(⟨-233320325568,-233320325504⟩ : DyadicInterval 40),(⟨741901440649,741901459978⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨26970219,54003314⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26969856,26969920⟩ : DyadicInterval 40),(⟨-26970560,-26970496⟩ : DyadicInterval 40),(⟨762123383242,762123402571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54001984,54002048⟩ : DyadicInterval 40),(⟨-54004672,-54004608⟩ : DyadicInterval 40),(⟨762123382243,762123401572⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2688,-640⟩ : DyadicInterval 40),(⟨762123383936,762123404224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨209998763338,210252906599⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192180573760,192180573824⟩ : DyadicInterval 40),(⟨-233038648320,-233038648256⟩ : DyadicInterval 40),(⟨741945523856,741945543185⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192393940800,192393940864⟩ : DyadicInterval 40),(⟨-233352835328,-233352835264⟩ : DyadicInterval 40),(⟨741896350368,741896369697⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-40958894464,-40858074432⟩ : DyadicInterval 40),(⟨782552420832,782602850112⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨192224668736,192415998848⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-233385324736,-233103566592⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e985_ok : ecellOkT e985 = true := by decide +kernel
theorem e985_pos {a z : ℝ} (ha1 : ((391251/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((783351/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e985 e985_ok ha1 ha2 hz1 hz2 hz

-- box ['783351/4096000', '3921/20480', '1999/2000', '3999/4000']  interval_lower 158807657/549755813888
noncomputable def e986 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1309790810669,0,true,192415998784,192415998848⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨889232444883,0,false,-233385324736,-233385324672⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1310018712372,0,true,192607295616,192607295680⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨889004543180,0,false,-233667155072,-233667155008⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1309685671077,0,true,192327735232,192327735296⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨889337584475,0,false,-233255330176,-233255330112⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1309966085602,0,true,192563124544,192563124608⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨889057169950,0,false,-233602068800,-233602068736⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538628861,0,true,27000704,27000768⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484626691,0,false,-27001472,-27001408⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565692836,0,true,54063680,54063744⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457562716,0,false,-54066432,-54066368⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625117,0,false,-2688,-2624⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627113,0,false,-704,-640⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1309738235843,0,true,192371863680,192371863744⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨889285019709,0,false,-233320319360,-233320319296⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1309992407593,0,true,192585217536,192585217600⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨889030847959,0,false,-233634622080,-233634622016⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1059219049186,0,false,-41049404544,-41049404480⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1059316303213,0,false,-40948455616,-40948455552⟩
    { al := (783351/4096000), au := (3921/20480), zl := (1999/2000), zu := (3999/4000),
      A := ⟨210279182893,210507084596⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192415998784,192415998848⟩ : DyadicInterval 40),(⟨-233385324736,-233385324672⟩ : DyadicInterval 40),(⟨741891262765,741891282094⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192607295616,192607295680⟩ : DyadicInterval 40),(⟨-233667155072,-233667155008⟩ : DyadicInterval 40),(⟨741847109150,741847128479⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192327735232,192327735296⟩ : DyadicInterval 40),(⟨-233255330176,-233255330112⟩ : DyadicInterval 40),(⟨741911615910,741911635239⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192563124544,192563124608⟩ : DyadicInterval 40),(⟨-233602068800,-233602068736⟩ : DyadicInterval 40),(⟨741857309422,741857328752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨27001085,54065060⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27000704,27000768⟩ : DyadicInterval 40),(⟨-27001472,-27001408⟩ : DyadicInterval 40),(⟨762123383272,762123402601⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54063680,54063744⟩ : DyadicInterval 40),(⟨-54066432,-54066368⟩ : DyadicInterval 40),(⟨762123382269,762123401598⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2688,-640⟩ : DyadicInterval 40),(⟨762123383936,762123404224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨210226608067,210480779817⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192371863680,192371863744⟩ : DyadicInterval 40),(⟨-233320319360,-233320319296⟩ : DyadicInterval 40),(⟨741901441628,741901460958⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192585217536,192585217600⟩ : DyadicInterval 40),(⟨-233634622080,-233634622016⟩ : DyadicInterval 40),(⟨741852207931,741852227260⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-41049404544,-40948455552⟩ : DyadicInterval 40),(⟨782597611392,782648105152⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨192415998784,192607295680⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-233667155072,-233385324672⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e986_ok : ecellOkT e986 = true := by decide +kernel
theorem e986_pos {a z : ℝ} (ha1 : ((783351/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3921/20480 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e986 e986_ok ha1 ha2 hz1 hz2 hz

-- box ['391251/2048000', '783351/4096000', '3999/4000', '1']  interval_lower 312903043/1099511627776
noncomputable def e987 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1309562908966,0,true,192224668736,192224668800⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨889460346586,0,false,-233103566656,-233103566592⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1309790810670,0,true,192415998784,192415998848⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨889232444882,0,false,-233385324736,-233385324672⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1309510396145,0,true,192180577984,192180578048⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨889512859407,0,false,-233038654528,-233038654464⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538629747,0,true,27001600,27001664⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484625805,0,false,-27002304,-27002240⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627112,0,false,-704,-640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1309536647263,0,true,192202619136,192202619200⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨889486608289,0,false,-233071103552,-233071103488⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1309790819184,0,true,192416005952,192416006016⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨889232436368,0,false,-233385335296,-233385335232⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1059296192829,0,false,-40969329280,-40969329216⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1059393353721,0,false,-40868484352,-40868484288⟩
    { al := (391251/2048000), au := (783351/4096000), zl := (3999/4000), zu := 1,
      A := ⟨210051281190,210279182894⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192224668736,192224668800⟩ : DyadicInterval 40),(⟨-233103566656,-233103566592⟩ : DyadicInterval 40),(⟨741935367320,741935386649⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192415998784,192415998848⟩ : DyadicInterval 40),(⟨-233385324736,-233385324672⟩ : DyadicInterval 40),(⟨741891262765,741891282094⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192180577984,192180578048⟩ : DyadicInterval 40),(⟨-233038654528,-233038654464⟩ : DyadicInterval 40),(⟨741945522879,741945542208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192415998784,192415998848⟩ : DyadicInterval 40),(⟨-233385324736,-233385324672⟩ : DyadicInterval 40),(⟨741891262765,741891282094⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,27001971⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27001600,27001664⟩ : DyadicInterval 40),(⟨-27002304,-27002240⟩ : DyadicInterval 40),(⟨762123383240,762123402569⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-704,0⟩ : DyadicInterval 40),(⟨762123383616,762123403232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨210025019487,210279191408⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192202619136,192202619200⟩ : DyadicInterval 40),(⟨-233071103552,-233071103488⟩ : DyadicInterval 40),(⟨741940446441,741940465771⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192416005952,192416006016⟩ : DyadicInterval 40),(⟨-233385335296,-233385335232⟩ : DyadicInterval 40),(⟨741891261117,741891280446⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-40969329280,-40868484288⟩ : DyadicInterval 40),(⟨782557625760,782608067520⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨192224668736,192415998848⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-233385324736,-233103566592⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e987_ok : ecellOkT e987 = true := by decide +kernel
theorem e987_pos {a z : ℝ} (ha1 : ((391251/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((783351/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e987 e987_ok ha1 ha2 hz1 hz2 hz

-- box ['783351/4096000', '3921/20480', '3999/4000', '1']  interval_lower 316871439/1099511627776
noncomputable def e988 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1309790810669,0,true,192415998784,192415998848⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨889232444883,0,false,-233385324736,-233385324672⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1310018712372,0,true,192607295616,192607295680⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨889004543180,0,false,-233667155072,-233667155008⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1309738240873,0,true,192371867904,192371867968⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨889285014679,0,false,-233320325568,-233320325504⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538660620,0,true,27032448,27032512⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484594932,0,false,-27033216,-27033152⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627111,0,false,-704,-640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1309764520475,0,true,192393929152,192393929216⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨889258735077,0,false,-233352818112,-233352818048⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1310018720894,0,true,192607302720,192607302784⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨889004534658,0,false,-233667165632,-233667165568⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1059208974185,0,false,-41059862848,-41059862784⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1059306251342,0,false,-40958888960,-40958888896⟩
    { al := (783351/4096000), au := (3921/20480), zl := (3999/4000), zu := 1,
      A := ⟨210279182893,210507084596⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192415998784,192415998848⟩ : DyadicInterval 40),(⟨-233385324736,-233385324672⟩ : DyadicInterval 40),(⟨741891262765,741891282094⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192607295616,192607295680⟩ : DyadicInterval 40),(⟨-233667155072,-233667155008⟩ : DyadicInterval 40),(⟨741847109150,741847128479⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192371867904,192371867968⟩ : DyadicInterval 40),(⟨-233320325568,-233320325504⟩ : DyadicInterval 40),(⟨741901440649,741901459978⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192607295616,192607295680⟩ : DyadicInterval 40),(⟨-233667155072,-233667155008⟩ : DyadicInterval 40),(⟨741847109150,741847128479⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,27032844⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27032448,27032512⟩ : DyadicInterval 40),(⟨-27033216,-27033152⟩ : DyadicInterval 40),(⟨762123383271,762123402600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-704,0⟩ : DyadicInterval 40),(⟨762123383616,762123403232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨210252892699,210507093118⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192393929152,192393929216⟩ : DyadicInterval 40),(⟨-233352818112,-233352818048⟩ : DyadicInterval 40),(⟨741896353035,741896372364⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192607302720,192607302784⟩ : DyadicInterval 40),(⟨-233667165632,-233667165568⟩ : DyadicInterval 40),(⟨741847107535,741847126864⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-41059862848,-40958888896⟩ : DyadicInterval 40),(⟨782602828064,782653334304⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨192415998784,192607295680⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-233667155072,-233385324672⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e988_ok : ecellOkT e988 = true := by decide +kernel
theorem e988_pos {a z : ℝ} (ha1 : ((783351/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((3921/20480 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e988 e988_ok ha1 ha2 hz1 hz2 hz

-- box ['3921/20480', '785049/4096000', '999/1000', '3997/4000']  interval_lower 323095177/1099511627776
noncomputable def e989 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1310018712371,0,true,192607295616,192607295680⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨889004543181,0,false,-233667155072,-233667155008⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1310246614074,0,true,192798559104,192798559168⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨888776641478,0,false,-233949057728,-233949057664⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1309808205286,0,true,192430600704,192430600768⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨889215050266,0,false,-233406832960,-233406832896⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1310088562835,0,true,192665920192,192665920256⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨888934692717,0,false,-233753548800,-233753548736⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592723048,0,true,81092224,81092288⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430532504,0,false,-81098304,-81098240⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099619879659,0,true,108246528,108246592⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099403375893,0,false,-108257216,-108257152⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511617118,0,false,-10688,-10624⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621795,0,false,-6016,-5952⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1309913454848,0,true,192518948352,192518948416⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨889109800704,0,false,-233536981376,-233536981312⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1310167597763,0,true,192732249472,192732249536⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨888855657789,0,false,-233851310464,-233851310400⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1059151947559,0,false,-41119060928,-41119060864⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1059249271548,0,false,-41018032960,-41018032896⟩
    { al := (3921/20480), au := (785049/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨210507084595,210734986298⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192607295616,192607295680⟩ : DyadicInterval 40),(⟨-233667155072,-233667155008⟩ : DyadicInterval 40),(⟨741847109150,741847128479⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192798559104,192798559168⟩ : DyadicInterval 40),(⟨-233949057728,-233949057664⟩ : DyadicInterval 40),(⟨741802906564,741802925893⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192430600704,192430600768⟩ : DyadicInterval 40),(⟨-233406832960,-233406832896⟩ : DyadicInterval 40),(⟨741887894484,741887913813⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192665920192,192665920256⟩ : DyadicInterval 40),(⟨-233753548800,-233753548736⟩ : DyadicInterval 40),(⟨741833566559,741833585888⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨81095272,108251883⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81092224,81092288⟩ : DyadicInterval 40),(⟨-81098304,-81098240⟩ : DyadicInterval 40),(⟨762123380610,762123399939⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨108246528,108246592⟩ : DyadicInterval 40),(⟨-108257216,-108257152⟩ : DyadicInterval 40),(⟨762123378237,762123397567⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-10688,-5952⟩ : DyadicInterval 40),(⟨762123386592,762123408224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨210401827072,210655969987⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192518948352,192518948416⟩ : DyadicInterval 40),(⟨-233536981376,-233536981312⟩ : DyadicInterval 40),(⟨741867507821,741867527151⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192732249472,192732249536⟩ : DyadicInterval 40),(⟨-233851310464,-233851310400⟩ : DyadicInterval 40),(⟨741818237709,741818257038⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-41119060928,-41018032896⟩ : DyadicInterval 40),(⟨782632400064,782682933344⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨192607295616,192798559168⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-233949057728,-233667155008⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e989_ok : ecellOkT e989 = true := by decide +kernel
theorem e989_pos {a z : ℝ} (ha1 : ((3921/20480 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((785049/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e989 e989_ok ha1 ha2 hz1 hz2 hz

-- box ['785049/4096000', '392949/2048000', '999/1000', '3997/4000']  interval_lower 327106223/1099511627776
noncomputable def e990 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1310246614073,0,true,192798559104,192798559168⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨888776641479,0,false,-233949057728,-233949057664⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1310474515776,0,true,192989789376,192989789440⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨888548739776,0,false,-234231032576,-234231032512⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1310035879086,0,true,192621703680,192621703744⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨888987376466,0,false,-233688386944,-233688386880⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1310316293611,0,true,192857030080,192857030144⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨888706961941,0,false,-234035262080,-234035262016⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592815677,0,true,81184896,81184960⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430439875,0,false,-81190912,-81190848⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099620003189,0,true,108370048,108370112⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099403252363,0,false,-108380800,-108380736⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511617093,0,false,-10688,-10624⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621782,0,false,-6016,-5952⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1310141242595,0,true,192710131584,192710131648⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨888882012957,0,false,-233818709632,-233818709568⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1310395414010,0,true,192923419520,192923419584⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨888627841542,0,false,-234133154496,-234133154432⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1059064605504,0,false,-41209734976,-41209734912⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1059162045727,0,false,-41108577984,-41108577920⟩
    { al := (785049/4096000), au := (392949/2048000), zl := (999/1000), zu := (3997/4000),
      A := ⟨210734986297,210962888000⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192798559104,192798559168⟩ : DyadicInterval 40),(⟨-233949057728,-233949057664⟩ : DyadicInterval 40),(⟨741802906564,741802925893⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192989789376,192989789440⟩ : DyadicInterval 40),(⟨-234231032576,-234231032512⟩ : DyadicInterval 40),(⟨741758654867,741758674196⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192621703680,192621703744⟩ : DyadicInterval 40),(⟨-233688386944,-233688386880⟩ : DyadicInterval 40),(⟨741843781333,741843800662⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192857030080,192857030144⟩ : DyadicInterval 40),(⟨-234035262080,-234035262016⟩ : DyadicInterval 40),(⟨741789382086,741789401415⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨81187901,108375413⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81184896,81184960⟩ : DyadicInterval 40),(⟨-81190912,-81190848⟩ : DyadicInterval 40),(⟨762123380564,762123399894⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨108370048,108370112⟩ : DyadicInterval 40),(⟨-108380800,-108380736⟩ : DyadicInterval 40),(⟨762123378245,762123397575⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-10688,-5952⟩ : DyadicInterval 40),(⟨762123386592,762123408224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨210629614819,210883786234⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192710131584,192710131648⟩ : DyadicInterval 40),(⟨-233818709632,-233818709568⟩ : DyadicInterval 40),(⟨741823349954,741823369283⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192923419520,192923419584⟩ : DyadicInterval 40),(⟨-234133154496,-234133154432⟩ : DyadicInterval 40),(⟨741774019638,741774038967⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-41209734976,-41108577920⟩ : DyadicInterval 40),(⟨782677672576,782728270368⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨192798559104,192989789440⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-234231032576,-233949057664⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e990_ok : ecellOkT e990 = true := by decide +kernel
theorem e990_pos {a z : ℝ} (ha1 : ((785049/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((392949/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e990 e990_ok ha1 ha2 hz1 hz2 hz

-- box ['3921/20480', '785049/4096000', '3997/4000', '1999/2000']  interval_lower 322349729/1099511627776
noncomputable def e991 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1310018712371,0,true,192607295616,192607295680⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨889004543181,0,false,-233667155072,-233667155008⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1310246614074,0,true,192798559104,192798559168⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨888776641478,0,false,-233949057728,-233949057664⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1309860832057,0,true,192474777088,192474777152⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨889162423495,0,false,-233471907712,-233471907648⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1310141246582,0,true,192710134976,192710135040⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨888882008970,0,false,-233818714560,-233818714496⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565691576,0,true,54062464,54062528⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457563976,0,false,-54065152,-54065088⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592817312,0,true,81186496,81186560⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430438240,0,false,-81192576,-81192512⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621780,0,false,-6016,-5952⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625118,0,false,-2688,-2624⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1309939767619,0,true,192541034496,192541034560⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨889083487933,0,false,-233569521408,-233569521344⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1310193939199,0,true,192754355392,192754355456⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨888829316353,0,false,-233883895168,-233883895104⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1059141853391,0,false,-41129539776,-41129539712⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1059239200529,0,false,-41028486848,-41028486784⟩
    { al := (3921/20480), au := (785049/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨210507084595,210734986298⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192607295616,192607295680⟩ : DyadicInterval 40),(⟨-233667155072,-233667155008⟩ : DyadicInterval 40),(⟨741847109150,741847128479⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192798559104,192798559168⟩ : DyadicInterval 40),(⟨-233949057728,-233949057664⟩ : DyadicInterval 40),(⟨741802906564,741802925893⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192474777088,192474777152⟩ : DyadicInterval 40),(⟨-233471907712,-233471907648⟩ : DyadicInterval 40),(⟨741877702077,741877721406⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192710134976,192710135040⟩ : DyadicInterval 40),(⟨-233818714560,-233818714496⟩ : DyadicInterval 40),(⟨741823349151,741823368481⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨54063800,81189536⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54062464,54062528⟩ : DyadicInterval 40),(⟨-54065152,-54065088⟩ : DyadicInterval 40),(⟨762123382237,762123401566⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81186496,81186560⟩ : DyadicInterval 40),(⟨-81192576,-81192512⟩ : DyadicInterval 40),(⟨762123380596,762123399926⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6016,-2624⟩ : DyadicInterval 40),(⟨762123384928,762123405888⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨210428139843,210682311423⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192541034496,192541034560⟩ : DyadicInterval 40),(⟨-233569521408,-233569521344⟩ : DyadicInterval 40),(⟨741862409456,741862428785⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192754355392,192754355456⟩ : DyadicInterval 40),(⟨-233883895168,-233883895104⟩ : DyadicInterval 40),(⟨741813127428,741813146758⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-41129539776,-41028486784⟩ : DyadicInterval 40),(⟨782637627008,782688172768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨192607295616,192798559168⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-233949057728,-233667155008⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e991_ok : ecellOkT e991 = true := by decide +kernel
theorem e991_pos {a z : ℝ} (ha1 : ((3921/20480 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((785049/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e991 e991_ok ha1 ha2 hz1 hz2 hz

-- box ['785049/4096000', '392949/2048000', '3997/4000', '1999/2000']  interval_lower 326357895/1099511627776
noncomputable def e992 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1310246614073,0,true,192798559104,192798559168⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨888776641479,0,false,-233949057728,-233949057664⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1310474515776,0,true,192989789376,192989789440⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨888548739776,0,false,-234231032576,-234231032512⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1310088562833,0,true,192665920192,192665920256⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨888934692719,0,false,-233753548800,-233753548736⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1310369034333,0,true,192901284992,192901285056⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨888654221219,0,false,-234100515072,-234100515008⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565753330,0,true,54124160,54124224⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457502222,0,false,-54126912,-54126848⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592909962,0,true,81279168,81279232⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430345590,0,false,-81285248,-81285184⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621767,0,false,-6016,-5952⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625112,0,false,-2688,-2624⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1310167583853,0,true,192732237824,192732237888⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨888855671699,0,false,-233851293248,-233851293184⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1310421783931,0,true,192945545472,192945545536⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨888601471621,0,false,-234165782912,-234165782848⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1059054489492,0,false,-41220237376,-41220237312⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1059151952890,0,false,-41119055424,-41119055360⟩
    { al := (785049/4096000), au := (392949/2048000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨210734986297,210962888000⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192798559104,192798559168⟩ : DyadicInterval 40),(⟨-233949057728,-233949057664⟩ : DyadicInterval 40),(⟨741802906564,741802925893⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192989789376,192989789440⟩ : DyadicInterval 40),(⟨-234231032576,-234231032512⟩ : DyadicInterval 40),(⟨741758654867,741758674196⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192665920192,192665920256⟩ : DyadicInterval 40),(⟨-233753548800,-233753548736⟩ : DyadicInterval 40),(⟨741833566559,741833585888⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192901284992,192901285056⟩ : DyadicInterval 40),(⟨-234100515072,-234100515008⟩ : DyadicInterval 40),(⟨741779142300,741779161629⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨54125554,81282186⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54124160,54124224⟩ : DyadicInterval 40),(⟨-54126912,-54126848⟩ : DyadicInterval 40),(⟨762123382263,762123401592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81279168,81279232⟩ : DyadicInterval 40),(⟨-81285248,-81285184⟩ : DyadicInterval 40),(⟨762123380582,762123399912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6016,-2624⟩ : DyadicInterval 40),(⟨762123384928,762123405888⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨210655956077,210910156155⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192732237824,192732237888⟩ : DyadicInterval 40),(⟨-233851293248,-233851293184⟩ : DyadicInterval 40),(⟨741818240388,741818259718⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192945545472,192945545536⟩ : DyadicInterval 40),(⟨-234165782912,-234165782848⟩ : DyadicInterval 40),(⟨741768898219,741768917548⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-41220237376,-41119055360⟩ : DyadicInterval 40),(⟨782682911296,782733521568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨192798559104,192989789440⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-234231032576,-233949057664⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e992_ok : ecellOkT e992 = true := by decide +kernel
theorem e992_pos {a z : ℝ} (ha1 : ((785049/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((392949/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e992 e992_ok ha1 ha2 hz1 hz2 hz

-- box ['392949/2048000', '786747/4096000', '999/1000', '3997/4000']  interval_lower 331134319/1099511627776
noncomputable def e993 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1310474515775,0,true,192989789376,192989789440⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨888548739777,0,false,-234231032576,-234231032512⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1310702417478,0,true,193180986368,193180986432⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨888320838074,0,false,-234513079808,-234513079744⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1310263552886,0,true,192812773440,192812773504⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨888759702666,0,false,-233970012992,-233970012928⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1310544024386,0,true,193048106752,193048106816⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨888479231166,0,false,-234317047616,-234317047552⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099592908322,0,true,81277504,81277568⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430347230,0,false,-81283584,-81283520⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099620126740,0,true,108493568,108493632⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099403128812,0,false,-108504320,-108504256⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511617069,0,false,-10752,-10688⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621768,0,false,-6016,-5952⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1310369030353,0,true,192901281600,192901281664⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨888654225199,0,false,-234100510144,-234100510080⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1310623230249,0,true,193114556352,193114556416⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨888400025303,0,false,-234415070848,-234415070784⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1058977169046,0,false,-41300514496,-41300514432⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1059074725521,0,false,-41199228480,-41199228416⟩
    { al := (392949/2048000), au := (786747/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨210962887999,211190789702⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192989789376,192989789440⟩ : DyadicInterval 40),(⟨-234231032576,-234231032512⟩ : DyadicInterval 40),(⟨741758654867,741758674196⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193180986368,193180986432⟩ : DyadicInterval 40),(⟨-234513079808,-234513079744⟩ : DyadicInterval 40),(⟨741714354163,741714373492⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192812773440,192812773504⟩ : DyadicInterval 40),(⟨-233970012992,-233970012928⟩ : DyadicInterval 40),(⟨741799619227,741799638556⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193048106752,193048106816⟩ : DyadicInterval 40),(⟨-234317047616,-234317047552⟩ : DyadicInterval 40),(⟨741745148671,741745168001⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨81280546,108498964⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81277504,81277568⟩ : DyadicInterval 40),(⟨-81283584,-81283520⟩ : DyadicInterval 40),(⟨762123380583,762123399912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨108493568,108493632⟩ : DyadicInterval 40),(⟨-108504320,-108504256⟩ : DyadicInterval 40),(⟨762123378220,762123397550⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-10752,-5952⟩ : DyadicInterval 40),(⟨762123386592,762123408256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨210857402577,211111602473⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192901281600,192901281664⟩ : DyadicInterval 40),(⟨-234100510144,-234100510080⟩ : DyadicInterval 40),(⟨741779143103,741779162432⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193114556352,193114556416⟩ : DyadicInterval 40),(⟨-234415070848,-234415070784⟩ : DyadicInterval 40),(⟨741729752575,741729771905⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-41300514496,-41199228416⟩ : DyadicInterval 40),(⟨782722997824,782773660128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨192989789376,193180986432⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-234513079808,-234231032512⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e993_ok : ecellOkT e993 = true := by decide +kernel
theorem e993_pos {a z : ℝ} (ha1 : ((392949/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((786747/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e993 e993_ok ha1 ha2 hz1 hz2 hz

-- box ['786747/4096000', '196899/1024000', '999/1000', '3997/4000']  interval_lower 335179879/1099511627776
noncomputable def e994 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1310702417477,0,true,193180986368,193180986432⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨888320838075,0,false,-234513079808,-234513079744⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1310930319180,0,true,193372150080,193372150144⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨888092936372,0,false,-234795199424,-234795199360⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1310491226687,0,true,193003809984,193003810048⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨888532028865,0,false,-234251711296,-234251711232⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1310771755162,0,true,193239150272,193239150336⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨888251500390,0,false,-234598905344,-234598905280⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593000985,0,true,81370176,81370240⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430254567,0,false,-81376256,-81376192⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099620250314,0,true,108617152,108617216⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099403005238,0,false,-108627904,-108627840⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511617045,0,false,-10752,-10688⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621754,0,false,-6080,-6016⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1310596818101,0,true,193092398400,193092398464⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨888426437451,0,false,-234382382848,-234382382784⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1310851046490,0,true,193305659968,193305660032⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨888172209062,0,false,-234697059520,-234697059456⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1058889638181,0,false,-41391399488,-41391399424⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1058987310935,0,false,-41289984448,-41289984384⟩
    { al := (786747/4096000), au := (196899/1024000), zl := (999/1000), zu := (3997/4000),
      A := ⟨211190789701,211418691404⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193180986368,193180986432⟩ : DyadicInterval 40),(⟨-234513079808,-234513079744⟩ : DyadicInterval 40),(⟨741714354163,741714373492⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193372150080,193372150144⟩ : DyadicInterval 40),(⟨-234795199424,-234795199360⟩ : DyadicInterval 40),(⟨741670004439,741670023769⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193003809984,193003810048⟩ : DyadicInterval 40),(⟨-234251711296,-234251711232⟩ : DyadicInterval 40),(⟨741755408231,741755427560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193239150272,193239150336⟩ : DyadicInterval 40),(⟨-234598905344,-234598905280⟩ : DyadicInterval 40),(⟨741700866239,741700885568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨81373209,108622538⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81370176,81370240⟩ : DyadicInterval 40),(⟨-81376256,-81376192⟩ : DyadicInterval 40),(⟨762123380569,762123399898⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨108617152,108617216⟩ : DyadicInterval 40),(⟨-108627904,-108627840⟩ : DyadicInterval 40),(⟨762123378196,762123397526⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-10752,-6016⟩ : DyadicInterval 40),(⟨762123386624,762123408256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨211085190325,211339418714⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193092398400,193092398464⟩ : DyadicInterval 40),(⟨-234382382848,-234382382784⟩ : DyadicInterval 40),(⟨741734887234,741734906563⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193305659968,193305660032⟩ : DyadicInterval 40),(⟨-234697059520,-234697059456⟩ : DyadicInterval 40),(⟨741685436506,741685455836⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-41391399488,-41289984384⟩ : DyadicInterval 40),(⟨782768375808,782819102624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨193180986368,193372150144⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-234795199424,-234513079744⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e994_ok : ecellOkT e994 = true := by decide +kernel
theorem e994_pos {a z : ℝ} (ha1 : ((786747/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((196899/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e994 e994_ok ha1 ha2 hz1 hz2 hz

-- box ['392949/2048000', '786747/4096000', '3997/4000', '1999/2000']  interval_lower 165191587/549755813888
noncomputable def e995 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1310474515775,0,true,192989789376,192989789440⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨888548739777,0,false,-234231032576,-234231032512⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1310702417478,0,true,193180986368,193180986432⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨888320838074,0,false,-234513079808,-234513079744⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1310316293608,0,true,192857030080,192857030144⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨888706961944,0,false,-234035262080,-234035262016⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1310596822084,0,true,193092401728,193092401792⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨888426433468,0,false,-234382387776,-234382387712⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565815095,0,true,54185920,54185984⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457440457,0,false,-54188672,-54188608⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593002627,0,true,81371776,81371840⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430252925,0,false,-81377920,-81377856⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621753,0,false,-6080,-6016⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625106,0,false,-2688,-2624⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1310395400094,0,true,192923407872,192923407936⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨888627855458,0,false,-234133137280,-234133137216⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1310649628656,0,true,193136702400,193136702464⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨888373626896,0,false,-234447742848,-234447742784⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1058967031166,0,false,-41311040448,-41311040384⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1059064610843,0,false,-41209729408,-41209729344⟩
    { al := (392949/2048000), au := (786747/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨210962887999,211190789702⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192989789376,192989789440⟩ : DyadicInterval 40),(⟨-234231032576,-234231032512⟩ : DyadicInterval 40),(⟨741758654867,741758674196⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193180986368,193180986432⟩ : DyadicInterval 40),(⟨-234513079808,-234513079744⟩ : DyadicInterval 40),(⟨741714354163,741714373492⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192857030080,192857030144⟩ : DyadicInterval 40),(⟨-234035262080,-234035262016⟩ : DyadicInterval 40),(⟨741789382086,741789401416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193092401728,193092401792⟩ : DyadicInterval 40),(⟨-234382387776,-234382387712⟩ : DyadicInterval 40),(⟨741734886467,741734905797⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨54187319,81374851⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54185920,54185984⟩ : DyadicInterval 40),(⟨-54188672,-54188608⟩ : DyadicInterval 40),(⟨762123382257,762123401586⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81371776,81371840⟩ : DyadicInterval 40),(⟨-81377920,-81377856⟩ : DyadicInterval 40),(⟨762123380601,762123399930⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6080,-2624⟩ : DyadicInterval 40),(⟨762123384928,762123405920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨210883772318,211138000880⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192923407872,192923407936⟩ : DyadicInterval 40),(⟨-234133137280,-234133137216⟩ : DyadicInterval 40),(⟨741774022325,741774041654⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193136702400,193136702464⟩ : DyadicInterval 40),(⟨-234447742848,-234447742784⟩ : DyadicInterval 40),(⟨741724619902,741724639231⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-41311040448,-41209729344⟩ : DyadicInterval 40),(⟨782728248288,782778923104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨192989789376,193180986432⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-234513079808,-234231032512⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e995_ok : ecellOkT e995 = true := by decide +kernel
theorem e995_pos {a z : ℝ} (ha1 : ((392949/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((786747/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e995 e995_ok ha1 ha2 hz1 hz2 hz

-- box ['786747/4096000', '196899/1024000', '3997/4000', '1999/2000']  interval_lower 167212751/549755813888
noncomputable def e996 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1310702417477,0,true,193180986368,193180986432⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨888320838075,0,false,-234513079808,-234513079744⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1310930319180,0,true,193372150080,193372150144⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨888092936372,0,false,-234795199424,-234795199360⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1310544024384,0,true,193048106752,193048106816⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨888479231168,0,false,-234317047616,-234317047552⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1310824609835,0,true,193283485312,193283485376⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨888198645717,0,false,-234664332800,-234664332736⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565876871,0,true,54247744,54247808⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457378681,0,false,-54250496,-54250432⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593095310,0,true,81464512,81464576⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430160242,0,false,-81470592,-81470528⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621739,0,false,-6080,-6016⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625100,0,false,-2688,-2624⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1310623216328,0,true,193114544704,193114544768⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨888400039224,0,false,-234415053632,-234415053568⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1310877473381,0,true,193327826048,193327826112⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨888145782171,0,false,-234729775168,-234729775104⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1058879478411,0,false,-41401949056,-41401948992⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1058977174393,0,false,-41300508928,-41300508864⟩
    { al := (786747/4096000), au := (196899/1024000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨211190789701,211418691404⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193180986368,193180986432⟩ : DyadicInterval 40),(⟨-234513079808,-234513079744⟩ : DyadicInterval 40),(⟨741714354163,741714373492⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193372150080,193372150144⟩ : DyadicInterval 40),(⟨-234795199424,-234795199360⟩ : DyadicInterval 40),(⟨741670004439,741670023769⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193048106752,193048106816⟩ : DyadicInterval 40),(⟨-234317047616,-234317047552⟩ : DyadicInterval 40),(⟨741745148672,741745168001⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193283485312,193283485376⟩ : DyadicInterval 40),(⟨-234664332800,-234664332736⟩ : DyadicInterval 40),(⟨741690581617,741690600946⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨54249095,81467534⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54247744,54247808⟩ : DyadicInterval 40),(⟨-54250496,-54250432⟩ : DyadicInterval 40),(⟨762123382251,762123401580⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81464512,81464576⟩ : DyadicInterval 40),(⟨-81470592,-81470528⟩ : DyadicInterval 40),(⟨762123380555,762123399884⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6080,-2624⟩ : DyadicInterval 40),(⟨762123384928,762123405920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨211111588552,211365845605⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193114544704,193114544768⟩ : DyadicInterval 40),(⟨-234415053632,-234415053568⟩ : DyadicInterval 40),(⟨741729755269,741729774598⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193327826048,193327826112⟩ : DyadicInterval 40),(⟨-234729775168,-234729775104⟩ : DyadicInterval 40),(⟨741680292617,741680311947⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-41401949056,-41300508864⟩ : DyadicInterval 40),(⟨782773638048,782824377408⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨193180986368,193372150144⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-234795199424,-234513079744⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e996_ok : ecellOkT e996 = true := by decide +kernel
theorem e996_pos {a z : ℝ} (ha1 : ((786747/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((196899/1024000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e996 e996_ok ha1 ha2 hz1 hz2 hz

-- box ['3921/20480', '785049/4096000', '1999/2000', '3999/4000']  interval_lower 321603537/1099511627776
noncomputable def e997 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1310018712371,0,true,192607295616,192607295680⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨889004543181,0,false,-233667155072,-233667155008⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1310246614074,0,true,192798559104,192798559168⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨888776641478,0,false,-233949057728,-233949057664⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1309913458828,0,true,192518951680,192518951744⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨889109796724,0,false,-233536986304,-233536986240⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1310193930328,0,true,192754347904,192754347968⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨888829325224,0,false,-233883884224,-233883884160⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538659733,0,true,27031616,27031680⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484595819,0,false,-27032320,-27032256⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565754592,0,true,54125440,54125504⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457500960,0,false,-54128192,-54128128⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625111,0,false,-2688,-2624⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627112,0,false,-704,-640⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1309966080564,0,true,192563120320,192563120384⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨889057174988,0,false,-233602062528,-233602062464⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1310220280803,0,true,192776460928,192776460992⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨888802974749,0,false,-233916481088,-233916481024⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1059131757896,0,false,-41140020160,-41140020096⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1059229128184,0,false,-41038942208,-41038942144⟩
    { al := (3921/20480), au := (785049/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨210507084595,210734986298⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192607295616,192607295680⟩ : DyadicInterval 40),(⟨-233667155072,-233667155008⟩ : DyadicInterval 40),(⟨741847109150,741847128479⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192798559104,192798559168⟩ : DyadicInterval 40),(⟨-233949057728,-233949057664⟩ : DyadicInterval 40),(⟨741802906564,741802925893⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192518951680,192518951744⟩ : DyadicInterval 40),(⟨-233536986304,-233536986240⟩ : DyadicInterval 40),(⟨741867507060,741867526390⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192754347904,192754347968⟩ : DyadicInterval 40),(⟨-233883884224,-233883884160⟩ : DyadicInterval 40),(⟨741813129187,741813148517⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨27031957,54126816⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27031616,27031680⟩ : DyadicInterval 40),(⟨-27032320,-27032256⟩ : DyadicInterval 40),(⟨762123383239,762123402568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54125440,54125504⟩ : DyadicInterval 40),(⟨-54128192,-54128128⟩ : DyadicInterval 40),(⟨762123382263,762123401592⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2688,-640⟩ : DyadicInterval 40),(⟨762123383936,762123404224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨210454452788,210708653027⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192563120320,192563120384⟩ : DyadicInterval 40),(⟨-233602062528,-233602062464⟩ : DyadicInterval 40),(⟨741857310379,741857329708⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192776460928,192776460992⟩ : DyadicInterval 40),(⟨-233916481088,-233916481024⟩ : DyadicInterval 40),(⟨741808016525,741808035855⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-41140020160,-41038942144⟩ : DyadicInterval 40),(⟨782642854688,782693412960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨192607295616,192798559168⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-233949057728,-233667155008⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e997_ok : ecellOkT e997 = true := by decide +kernel
theorem e997_pos {a z : ℝ} (ha1 : ((3921/20480 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((785049/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e997 e997_ok ha1 ha2 hz1 hz2 hz

-- box ['785049/4096000', '392949/2048000', '1999/2000', '3999/4000']  interval_lower 325608697/1099511627776
noncomputable def e998 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1310246614073,0,true,192798559104,192798559168⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨888776641479,0,false,-233949057728,-233949057664⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1310474515776,0,true,192989789376,192989789440⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨888548739776,0,false,-234231032576,-234231032512⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1310141246579,0,true,192710134976,192710135040⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨888882008973,0,false,-233818714560,-233818714496⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1310421775055,0,true,192945538048,192945538112⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨888601480497,0,false,-234165771904,-234165771840⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538690611,0,true,27062464,27062528⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484564941,0,false,-27063232,-27063168⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565816360,0,true,54187200,54187264⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457439192,0,false,-54189952,-54189888⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625105,0,false,-2688,-2624⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627110,0,false,-704,-640⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1310193925288,0,true,192754343680,192754343744⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨888829330264,0,false,-233883877952,-233883877888⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1310448154025,0,true,192967671168,192967671232⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨888575101527,0,false,-234198412416,-234198412352⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1059044372149,0,false,-41230741248,-41230741184⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1059141858723,0,false,-41129534272,-41129534208⟩
    { al := (785049/4096000), au := (392949/2048000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨210734986297,210962888000⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192798559104,192798559168⟩ : DyadicInterval 40),(⟨-233949057728,-233949057664⟩ : DyadicInterval 40),(⟨741802906564,741802925893⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192989789376,192989789440⟩ : DyadicInterval 40),(⟨-234231032576,-234231032512⟩ : DyadicInterval 40),(⟨741758654867,741758674196⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192710134976,192710135040⟩ : DyadicInterval 40),(⟨-233818714560,-233818714496⟩ : DyadicInterval 40),(⟨741823349152,741823368482⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192945538048,192945538112⟩ : DyadicInterval 40),(⟨-234165771904,-234165771840⟩ : DyadicInterval 40),(⟨741768899919,741768919248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨27062835,54188584⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27062464,27062528⟩ : DyadicInterval 40),(⟨-27063232,-27063168⟩ : DyadicInterval 40),(⟨762123383269,762123402598⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54187200,54187264⟩ : DyadicInterval 40),(⟨-54189952,-54189888⟩ : DyadicInterval 40),(⟨762123382257,762123401586⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2688,-640⟩ : DyadicInterval 40),(⟨762123383936,762123404224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨210682297512,210936526249⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192754343680,192754343744⟩ : DyadicInterval 40),(⟨-233883877952,-233883877888⟩ : DyadicInterval 40),(⟨741813130147,741813149476⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192967671168,192967671232⟩ : DyadicInterval 40),(⟨-234198412416,-234198412352⟩ : DyadicInterval 40),(⟨741763776046,741763795375⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-41230741248,-41129534208⟩ : DyadicInterval 40),(⟨782688150720,782738773504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨192798559104,192989789440⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-234231032576,-233949057664⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e998_ok : ecellOkT e998 = true := by decide +kernel
theorem e998_pos {a z : ℝ} (ha1 : ((785049/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((392949/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e998 e998_ok ha1 ha2 hz1 hz2 hz

-- box ['3921/20480', '785049/4096000', '3999/4000', '1']  interval_lower 160428213/549755813888
noncomputable def e999 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1310018712371,0,true,192607295616,192607295680⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨889004543181,0,false,-233667155072,-233667155008⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1310246614074,0,true,192798559104,192798559168⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨888776641478,0,false,-233949057728,-233949057664⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1309966085599,0,true,192563124544,192563124608⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨889057169953,0,false,-233602068800,-233602068736⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538691500,0,true,27063360,27063424⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484564052,0,false,-27064064,-27064000⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627109,0,false,-704,-640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1309992393688,0,true,192585205824,192585205888⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨889030861864,0,false,-233634604928,-233634604864⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1310246622588,0,true,192798566272,192798566336⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨888776632964,0,false,-233949068224,-233949068160⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1059121661070,0,false,-41150501952,-41150501888⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1059219054511,0,false,-41049399040,-41049398976⟩
    { al := (3921/20480), au := (785049/4096000), zl := (3999/4000), zu := 1,
      A := ⟨210507084595,210734986298⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192607295616,192607295680⟩ : DyadicInterval 40),(⟨-233667155072,-233667155008⟩ : DyadicInterval 40),(⟨741847109150,741847128479⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192798559104,192798559168⟩ : DyadicInterval 40),(⟨-233949057728,-233949057664⟩ : DyadicInterval 40),(⟨741802906564,741802925893⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192563124544,192563124608⟩ : DyadicInterval 40),(⟨-233602068800,-233602068736⟩ : DyadicInterval 40),(⟨741857309423,741857328752⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192798559104,192798559168⟩ : DyadicInterval 40),(⟨-233949057728,-233949057664⟩ : DyadicInterval 40),(⟨741802906564,741802925893⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,27063724⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27063360,27063424⟩ : DyadicInterval 40),(⟨-27064064,-27064000⟩ : DyadicInterval 40),(⟨762123383237,762123402566⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-704,0⟩ : DyadicInterval 40),(⟨762123383616,762123403232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨210480765912,210734994812⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192585205824,192585205888⟩ : DyadicInterval 40),(⟨-233634604928,-233634604864⟩ : DyadicInterval 40),(⟨741852210669,741852229998⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192798566272,192798566336⟩ : DyadicInterval 40),(⟨-233949068224,-233949068160⟩ : DyadicInterval 40),(⟨741802904882,741802924212⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-41150501952,-41049398976⟩ : DyadicInterval 40),(⟨782648083104,782698653856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨192607295616,192798559168⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-233949057728,-233667155008⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e999_ok : ecellOkT e999 = true := by decide +kernel
theorem e999_pos {a z : ℝ} (ha1 : ((3921/20480 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((785049/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e999 e999_ok ha1 ha2 hz1 hz2 hz

-- box ['785049/4096000', '392949/2048000', '3999/4000', '1']  interval_lower 40607327/137438953472
noncomputable def e1000 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1310246614073,0,true,192798559104,192798559168⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨888776641479,0,false,-233949057728,-233949057664⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1310474515776,0,true,192989789376,192989789440⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨888548739776,0,false,-234231032576,-234231032512⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1310193930326,0,true,192754347904,192754347968⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨888829325226,0,false,-233883884224,-233883884160⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538722384,0,true,27094272,27094336⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484533168,0,false,-27094976,-27094912⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627108,0,false,-704,-640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1310220266891,0,true,192776449280,192776449344⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨888802988661,0,false,-233916463936,-233916463872⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1310474524300,0,true,192989796480,192989796544⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨888548731252,0,false,-234231043136,-234231043072⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1059034253471,0,false,-41241246592,-41241246528⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1059131763229,0,false,-41140014592,-41140014528⟩
    { al := (785049/4096000), au := (392949/2048000), zl := (3999/4000), zu := 1,
      A := ⟨210734986297,210962888000⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192798559104,192798559168⟩ : DyadicInterval 40),(⟨-233949057728,-233949057664⟩ : DyadicInterval 40),(⟨741802906564,741802925893⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192989789376,192989789440⟩ : DyadicInterval 40),(⟨-234231032576,-234231032512⟩ : DyadicInterval 40),(⟨741758654867,741758674196⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192754347904,192754347968⟩ : DyadicInterval 40),(⟨-233883884224,-233883884160⟩ : DyadicInterval 40),(⟨741813129188,741813148517⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192989789376,192989789440⟩ : DyadicInterval 40),(⟨-234231032576,-234231032512⟩ : DyadicInterval 40),(⟨741758654867,741758674196⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,27094608⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27094272,27094336⟩ : DyadicInterval 40),(⟨-27094976,-27094912⟩ : DyadicInterval 40),(⟨762123383236,762123402565⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-704,0⟩ : DyadicInterval 40),(⟨762123383616,762123403232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨210708639115,210962896524⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192776449280,192776449344⟩ : DyadicInterval 40),(⟨-233916463936,-233916463872⟩ : DyadicInterval 40),(⟨741808019232,741808038561⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192989796480,192989796544⟩ : DyadicInterval 40),(⟨-234231043136,-234231043072⟩ : DyadicInterval 40),(⟨741758653244,741758672574⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-41241246592,-41140014528⟩ : DyadicInterval 40),(⟨782693390880,782744026176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨192798559104,192989789440⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-234231032576,-233949057664⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1000_ok : ecellOkT e1000 = true := by decide +kernel
theorem e1000_pos {a z : ℝ} (ha1 : ((785049/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((392949/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1000 e1000_ok ha1 ha2 hz1 hz2 hz

-- box ['392949/2048000', '786747/4096000', '1999/2000', '3999/4000']  interval_lower 329631025/1099511627776
noncomputable def e1001 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1310474515775,0,true,192989789376,192989789440⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨888548739777,0,false,-234231032576,-234231032512⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1310702417478,0,true,193180986368,193180986432⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨888320838074,0,false,-234513079808,-234513079744⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1310369034330,0,true,192901284992,192901285056⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨888654221222,0,false,-234100515072,-234100515008⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1310649619781,0,true,193136694912,193136694976⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨888373635771,0,false,-234447731840,-234447731776⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538721494,0,true,27093376,27093440⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484534058,0,false,-27094080,-27094016⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565878138,0,true,54248960,54249024⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457377414,0,false,-54251712,-54251648⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625099,0,false,-2688,-2624⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627109,0,false,-704,-640⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1310421770014,0,true,192945533824,192945533888⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨888601485538,0,false,-234165765632,-234165765568⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1310676027240,0,true,193158848064,193158848128⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨888347228312,0,false,-234480416000,-234480415936⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1058956891950,0,false,-41321567936,-41321567872⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1059054494832,0,false,-41220231808,-41220231744⟩
    { al := (392949/2048000), au := (786747/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨210962887999,211190789702⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192989789376,192989789440⟩ : DyadicInterval 40),(⟨-234231032576,-234231032512⟩ : DyadicInterval 40),(⟨741758654867,741758674196⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193180986368,193180986432⟩ : DyadicInterval 40),(⟨-234513079808,-234513079744⟩ : DyadicInterval 40),(⟨741714354163,741714373492⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192901284992,192901285056⟩ : DyadicInterval 40),(⟨-234100515072,-234100515008⟩ : DyadicInterval 40),(⟨741779142301,741779161630⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193136694912,193136694976⟩ : DyadicInterval 40),(⟨-234447731840,-234447731776⟩ : DyadicInterval 40),(⟨741724621644,741724640973⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨27093718,54250362⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27093376,27093440⟩ : DyadicInterval 40),(⟨-27094080,-27094016⟩ : DyadicInterval 40),(⟨762123383236,762123402565⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54248960,54249024⟩ : DyadicInterval 40),(⟨-54251712,-54251648⟩ : DyadicInterval 40),(⟨762123382251,762123401580⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2688,-640⟩ : DyadicInterval 40),(⟨762123383936,762123404224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨210910142238,211164399464⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192945533824,192945533888⟩ : DyadicInterval 40),(⟨-234165765632,-234165765568⟩ : DyadicInterval 40),(⟨741768900881,741768920210⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193158848064,193158848128⟩ : DyadicInterval 40),(⟨-234480416000,-234480415936⟩ : DyadicInterval 40),(⟨741719486573,741719505902⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-41321567936,-41220231744⟩ : DyadicInterval 40),(⟨782733499488,782784186848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨192989789376,193180986432⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-234513079808,-234231032512⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1001_ok : ecellOkT e1001 = true := by decide +kernel
theorem e1001_pos {a z : ℝ} (ha1 : ((392949/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((786747/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1001 e1001_ok ha1 ha2 hz1 hz2 hz

-- box ['786747/4096000', '196899/1024000', '1999/2000', '3999/4000']  interval_lower 333670409/1099511627776
noncomputable def e1002 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1310702417477,0,true,193180986368,193180986432⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨888320838075,0,false,-234513079808,-234513079744⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1310930319180,0,true,193372150080,193372150144⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨888092936372,0,false,-234795199424,-234795199360⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1310596822082,0,true,193092401728,193092401792⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨888426433470,0,false,-234382387776,-234382387712⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1310877464508,0,true,193327818624,193327818688⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨888145791044,0,false,-234729764160,-234729764096⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538752382,0,true,27124224,27124288⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484503170,0,false,-27124992,-27124928⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565939927,0,true,54310784,54310848⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457315625,0,false,-54313536,-54313472⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625093,0,false,-2688,-2624⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627107,0,false,-704,-640⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1310649614735,0,true,193136690688,193136690752⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨888373640817,0,false,-234447725632,-234447725568⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1310903900453,0,true,193349991808,193349991872⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨888119355099,0,false,-234762491968,-234762491904⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1058869317300,0,false,-41412500160,-41412500096⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1058967036513,0,false,-41311034880,-41311034816⟩
    { al := (786747/4096000), au := (196899/1024000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨211190789701,211418691404⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193180986368,193180986432⟩ : DyadicInterval 40),(⟨-234513079808,-234513079744⟩ : DyadicInterval 40),(⟨741714354163,741714373492⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193372150080,193372150144⟩ : DyadicInterval 40),(⟨-234795199424,-234795199360⟩ : DyadicInterval 40),(⟨741670004439,741670023769⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193092401728,193092401792⟩ : DyadicInterval 40),(⟨-234382387776,-234382387712⟩ : DyadicInterval 40),(⟨741734886468,741734905797⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193327818624,193327818688⟩ : DyadicInterval 40),(⟨-234729764160,-234729764096⟩ : DyadicInterval 40),(⟨741680294324,741680313654⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨27124606,54312151⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27124224,27124288⟩ : DyadicInterval 40),(⟨-27124992,-27124928⟩ : DyadicInterval 40),(⟨762123383266,762123402595⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54310784,54310848⟩ : DyadicInterval 40),(⟨-54313536,-54313472⟩ : DyadicInterval 40),(⟨762123382245,762123401574⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2688,-640⟩ : DyadicInterval 40),(⟨762123383936,762123404224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨211137986959,211392272677⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193136690688,193136690752⟩ : DyadicInterval 40),(⟨-234447725632,-234447725568⟩ : DyadicInterval 40),(⟨741724622634,741724641964⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193349991808,193349991872⟩ : DyadicInterval 40),(⟨-234762491968,-234762491904⟩ : DyadicInterval 40),(⟨741675148030,741675167360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-41412500160,-41311034816⟩ : DyadicInterval 40),(⟨782778901024,782829652960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨193180986368,193372150144⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-234795199424,-234513079744⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1002_ok : ecellOkT e1002 = true := by decide +kernel
theorem e1002_pos {a z : ℝ} (ha1 : ((786747/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((196899/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1002 e1002_ok ha1 ha2 hz1 hz2 hz

-- box ['392949/2048000', '786747/4096000', '3999/4000', '1']  interval_lower 328878195/1099511627776
noncomputable def e1003 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1310474515775,0,true,192989789376,192989789440⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨888548739777,0,false,-234231032576,-234231032512⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1310702417478,0,true,193180986368,193180986432⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨888320838074,0,false,-234513079808,-234513079744⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1310421775052,0,true,192945538048,192945538112⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨888601480500,0,false,-234165771904,-234165771840⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538753273,0,true,27125120,27125184⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484502279,0,false,-27125888,-27125824⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627106,0,false,-704,-640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1310448140107,0,true,192967659456,192967659520⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨888575115445,0,false,-234198395200,-234198395136⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1310702426002,0,true,193180993472,193180993536⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨888320829550,0,false,-234513090368,-234513090304⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1058946751399,0,false,-41332096832,-41332096768⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1059044377490,0,false,-41230735680,-41230735616⟩
    { al := (392949/2048000), au := (786747/4096000), zl := (3999/4000), zu := 1,
      A := ⟨210962887999,211190789702⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192989789376,192989789440⟩ : DyadicInterval 40),(⟨-234231032576,-234231032512⟩ : DyadicInterval 40),(⟨741758654867,741758674196⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193180986368,193180986432⟩ : DyadicInterval 40),(⟨-234513079808,-234513079744⟩ : DyadicInterval 40),(⟨741714354163,741714373492⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192945538048,192945538112⟩ : DyadicInterval 40),(⟨-234165771904,-234165771840⟩ : DyadicInterval 40),(⟨741768899919,741768919249⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193180986368,193180986432⟩ : DyadicInterval 40),(⟨-234513079808,-234513079744⟩ : DyadicInterval 40),(⟨741714354163,741714373492⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,27125497⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27125120,27125184⟩ : DyadicInterval 40),(⟨-27125888,-27125824⟩ : DyadicInterval 40),(⟨762123383266,762123402595⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-704,0⟩ : DyadicInterval 40),(⟨762123383616,762123403232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨210936512331,211190798226⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨192967659456,192967659520⟩ : DyadicInterval 40),(⟨-234198395200,-234198395136⟩ : DyadicInterval 40),(⟨741763778772,741763798101⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193180993472,193180993536⟩ : DyadicInterval 40),(⟨-234513090368,-234513090304⟩ : DyadicInterval 40),(⟨741714352536,741714371866⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-41332096832,-41230735616⟩ : DyadicInterval 40),(⟨782738751424,782789451296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨192989789376,193180986432⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-234513079808,-234231032512⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1003_ok : ecellOkT e1003 = true := by decide +kernel
theorem e1003_pos {a z : ℝ} (ha1 : ((392949/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((786747/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1003 e1003_ok ha1 ha2 hz1 hz2 hz

-- box ['786747/4096000', '196899/1024000', '3999/4000', '1']  interval_lower 20807175/68719476736
noncomputable def e1004 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1310702417477,0,true,193180986368,193180986432⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨888320838075,0,false,-234513079808,-234513079744⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1310930319180,0,true,193372150080,193372150144⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨888092936372,0,false,-234795199424,-234795199360⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1310649619779,0,true,193136694912,193136694976⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨888373635773,0,false,-234447731840,-234447731776⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538784169,0,true,27156032,27156096⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484471383,0,false,-27156736,-27156672⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627105,0,false,-704,-640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1310676013318,0,true,193158836416,193158836480⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨888347242234,0,false,-234480398784,-234480398720⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1310930327697,0,true,193372157248,193372157312⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨888092927855,0,false,-234795209984,-234795209920⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1058859154853,0,false,-41423052736,-41423052672⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1058956897299,0,false,-41321562368,-41321562304⟩
    { al := (786747/4096000), au := (196899/1024000), zl := (3999/4000), zu := 1,
      A := ⟨211190789701,211418691404⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193180986368,193180986432⟩ : DyadicInterval 40),(⟨-234513079808,-234513079744⟩ : DyadicInterval 40),(⟨741714354163,741714373492⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193372150080,193372150144⟩ : DyadicInterval 40),(⟨-234795199424,-234795199360⟩ : DyadicInterval 40),(⟨741670004439,741670023769⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193136694912,193136694976⟩ : DyadicInterval 40),(⟨-234447731840,-234447731776⟩ : DyadicInterval 40),(⟨741724621644,741724640974⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193372150080,193372150144⟩ : DyadicInterval 40),(⟨-234795199424,-234795199360⟩ : DyadicInterval 40),(⟨741670004439,741670023769⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,27156393⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27156032,27156096⟩ : DyadicInterval 40),(⟨-27156736,-27156672⟩ : DyadicInterval 40),(⟨762123383233,762123402562⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-704,0⟩ : DyadicInterval 40),(⟨762123383616,762123403232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨211164385542,211418699921⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193158836416,193158836480⟩ : DyadicInterval 40),(⟨-234480398784,-234480398720⟩ : DyadicInterval 40),(⟨741719489268,741719508597⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193372157248,193372157312⟩ : DyadicInterval 40),(⟨-234795209984,-234795209920⟩ : DyadicInterval 40),(⟨741670002772,741670022102⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-41423052736,-41321562304⟩ : DyadicInterval 40),(⟨782784164768,782834929248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨193180986368,193372150144⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-234795199424,-234513079744⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1004_ok : ecellOkT e1004 = true := by decide +kernel
theorem e1004_pos {a z : ℝ} (ha1 : ((786747/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((196899/1024000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1004 e1004_ok ha1 ha2 hz1 hz2 hz

-- box ['196899/1024000', '157689/819200', '999/1000', '3997/4000']  interval_lower 169621157/549755813888
noncomputable def e1005 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1310930319179,0,true,193372150080,193372150144⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨888092936373,0,false,-234795199424,-234795199360⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1311158220882,0,true,193563280640,193563280704⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨887865034670,0,false,-235077391424,-235077391360⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1310718900487,0,true,193194813376,193194813440⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨888304355065,0,false,-234533481728,-234533481664⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1310999485938,0,true,193430160512,193430160576⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨888023769614,0,false,-234880835328,-234880835264⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593093663,0,true,81462848,81462912⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430161889,0,false,-81468928,-81468864⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099620373910,0,true,108740736,108740800⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099402881642,0,false,-108751552,-108751488⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511617020,0,false,-10816,-10752⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621740,0,false,-6080,-6016⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1310824605849,0,true,193283481984,193283482048⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨888198649703,0,false,-234664327872,-234664327808⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1311078862732,0,true,193496730432,193496730496⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨887944392820,0,false,-234979120512,-234979120448⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1058802012910,0,false,-41482390080,-41482390016⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1058899801968,0,false,-41380845824,-41380845760⟩
    { al := (196899/1024000), au := (157689/819200), zl := (999/1000), zu := (3997/4000),
      A := ⟨211418691403,211646593106⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193372150080,193372150144⟩ : DyadicInterval 40),(⟨-234795199424,-234795199360⟩ : DyadicInterval 40),(⟨741670004439,741670023769⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193563280640,193563280704⟩ : DyadicInterval 40),(⟨-235077391424,-235077391360⟩ : DyadicInterval 40),(⟨741625605608,741625624937⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193194813376,193194813440⟩ : DyadicInterval 40),(⟨-234533481728,-234533481664⟩ : DyadicInterval 40),(⟨741711148243,741711167573⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193430160512,193430160576⟩ : DyadicInterval 40),(⟨-234880835328,-234880835264⟩ : DyadicInterval 40),(⟨741656534879,741656554208⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨81465887,108746134⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81462848,81462912⟩ : DyadicInterval 40),(⟨-81468928,-81468864⟩ : DyadicInterval 40),(⟨762123380555,762123399885⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨108740736,108740800⟩ : DyadicInterval 40),(⟨-108751552,-108751488⟩ : DyadicInterval 40),(⟨762123378204,762123397534⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-10816,-6016⟩ : DyadicInterval 40),(⟨762123386624,762123408288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨211312978073,211567234956⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193283481984,193283482048⟩ : DyadicInterval 40),(⟨-234664327872,-234664327808⟩ : DyadicInterval 40),(⟨741690582385,741690601715⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193496730432,193496730496⟩ : DyadicInterval 40),(⟨-234979120512,-234979120448⟩ : DyadicInterval 40),(⟨741641071381,741641090711⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-41482390080,-41380845760⟩ : DyadicInterval 40),(⟨782813806496,782864597920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨193372150080,193563280704⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-235077391424,-234795199360⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1005_ok : ecellOkT e1005 = true := by decide +kernel
theorem e1005_pos {a z : ℝ} (ha1 : ((196899/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((157689/819200 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1005 e1005_ok ha1 ha2 hz1 hz2 hz

-- box ['157689/819200', '394647/2048000', '999/1000', '3997/4000']  interval_lower 171661173/549755813888
noncomputable def e1006 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1311158220881,0,true,193563280640,193563280704⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨887865034671,0,false,-235077391424,-235077391360⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1311386122585,0,true,193754377920,193754377984⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨887637132967,0,false,-235359655872,-235359655808⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1310946574287,0,true,193385783616,193385783680⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨888076681265,0,false,-234815324416,-234815324352⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1311227216715,0,true,193621137664,193621137728⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨887796038837,0,false,-235162837632,-235162837568⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593186358,0,true,81555520,81555584⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430069194,0,false,-81561664,-81561600⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099620497528,0,true,108864320,108864384⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099402758024,0,false,-108875200,-108875136⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511616996,0,false,-10816,-10752⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621727,0,false,-6080,-6016⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1311052393606,0,true,193474532352,193474532416⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨887970861946,0,false,-234946345216,-234946345152⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1311306678977,0,true,193687767616,193687767680⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨887716576575,0,false,-235261253888,-235261253824⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1058714293232,0,false,-41573486272,-41573486208⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1058812198614,0,false,-41471812800,-41471812736⟩
    { al := (157689/819200), au := (394647/2048000), zl := (999/1000), zu := (3997/4000),
      A := ⟨211646593105,211874494809⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193563280640,193563280704⟩ : DyadicInterval 40),(⟨-235077391424,-235077391360⟩ : DyadicInterval 40),(⟨741625605608,741625624938⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193754377920,193754377984⟩ : DyadicInterval 40),(⟨-235359655872,-235359655808⟩ : DyadicInterval 40),(⟨741581157758,741581177087⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193385783616,193385783680⟩ : DyadicInterval 40),(⟨-234815324416,-234815324352⟩ : DyadicInterval 40),(⟨741666839303,741666858633⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193621137664,193621137728⟩ : DyadicInterval 40),(⟨-235162837632,-235162837568⟩ : DyadicInterval 40),(⟨741612154490,741612173820⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨81558582,108869752⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81555520,81555584⟩ : DyadicInterval 40),(⟨-81561664,-81561600⟩ : DyadicInterval 40),(⟨762123380573,762123399903⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨108864320,108864384⟩ : DyadicInterval 40),(⟨-108875200,-108875136⟩ : DyadicInterval 40),(⟨762123378211,762123397541⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-10816,-6016⟩ : DyadicInterval 40),(⟨762123386624,762123408288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨211540765830,211795051201⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193474532352,193474532416⟩ : DyadicInterval 40),(⟨-234946345216,-234946345152⟩ : DyadicInterval 40),(⟨741646228544,741646247873⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193687767616,193687767680⟩ : DyadicInterval 40),(⟨-235261253888,-235261253824⟩ : DyadicInterval 40),(⟨741596657290,741596676619⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-41573486272,-41471812736⟩ : DyadicInterval 40),(⟨782859289984,782910146016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨193563280640,193754377984⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-235359655872,-235077391360⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1006_ok : ecellOkT e1006 = true := by decide +kernel
theorem e1006_pos {a z : ℝ} (ha1 : ((157689/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((394647/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1006 e1006_ok ha1 ha2 hz1 hz2 hz

-- box ['196899/1024000', '157689/819200', '3997/4000', '1999/2000']  interval_lower 338484955/1099511627776
noncomputable def e1007 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1310930319179,0,true,193372150080,193372150144⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨888092936373,0,false,-234795199424,-234795199360⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1311158220882,0,true,193563280640,193563280704⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨887865034670,0,false,-235077391424,-235077391360⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1310771755160,0,true,193239150272,193239150336⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨888251500392,0,false,-234598905344,-234598905280⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1311052397586,0,true,193474535680,193474535744⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨887970857966,0,false,-234946350144,-234946350080⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099565938658,0,true,54309504,54309568⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457316894,0,false,-54312256,-54312192⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593188008,0,true,81557184,81557248⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099430067544,0,false,-81563264,-81563200⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621725,0,false,-6080,-6016⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625094,0,false,-2688,-2624⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1310851032564,0,true,193305648320,193305648384⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨888172222988,0,false,-234697042304,-234697042240⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1311105318111,0,true,193518916480,193518916544⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨887917937441,0,false,-235011879808,-235011879744⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1058791831224,0,false,-41492963328,-41492963264⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1058889643536,0,false,-41391393920,-41391393856⟩
    { al := (196899/1024000), au := (157689/819200), zl := (3997/4000), zu := (1999/2000),
      A := ⟨211418691403,211646593106⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193372150080,193372150144⟩ : DyadicInterval 40),(⟨-234795199424,-234795199360⟩ : DyadicInterval 40),(⟨741670004439,741670023769⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193563280640,193563280704⟩ : DyadicInterval 40),(⟨-235077391424,-235077391360⟩ : DyadicInterval 40),(⟨741625605608,741625624937⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193239150272,193239150336⟩ : DyadicInterval 40),(⟨-234598905344,-234598905280⟩ : DyadicInterval 40),(⟨741700866239,741700885569⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193474535680,193474535744⟩ : DyadicInterval 40),(⟨-234946350144,-234946350080⟩ : DyadicInterval 40),(⟨741646227774,741646247103⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨54310882,81560232⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54309504,54309568⟩ : DyadicInterval 40),(⟨-54312256,-54312192⟩ : DyadicInterval 40),(⟨762123382245,762123401574⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81557184,81557248⟩ : DyadicInterval 40),(⟨-81563264,-81563200⟩ : DyadicInterval 40),(⟨762123380541,762123399871⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6080,-2624⟩ : DyadicInterval 40),(⟨762123384928,762123405920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨211339404788,211593690335⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193305648320,193305648384⟩ : DyadicInterval 40),(⟨-234697042304,-234697042240⟩ : DyadicInterval 40),(⟨741685439207,741685458536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193518916480,193518916544⟩ : DyadicInterval 40),(⟨-235011879808,-235011879744⟩ : DyadicInterval 40),(⟨741635916288,741635935618⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-41492963328,-41391393856⟩ : DyadicInterval 40),(⟨782819080544,782869884544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨193372150080,193563280704⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-235077391424,-234795199360⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1007_ok : ecellOkT e1007 = true := by decide +kernel
theorem e1007_pos {a z : ℝ} (ha1 : ((196899/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((157689/819200 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1007 e1007_ok ha1 ha2 hz1 hz2 hz

-- box ['157689/819200', '394647/2048000', '3997/4000', '1999/2000']  interval_lower 342562113/1099511627776
noncomputable def e1008 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1311158220881,0,true,193563280640,193563280704⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨887865034671,0,false,-235077391424,-235077391360⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1311386122585,0,true,193754377920,193754377984⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨887637132967,0,false,-235359655872,-235359655808⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1310999485936,0,true,193430160512,193430160576⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨888023769616,0,false,-234880835328,-234880835264⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1311280185338,0,true,193665552832,193665552896⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨887743070214,0,false,-235228439808,-235228439744⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566000456,0,true,54371328,54371392⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457255096,0,false,-54374080,-54374016⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593280723,0,true,81649856,81649920⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429974829,0,false,-81656000,-81655936⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621712,0,false,-6080,-6016⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625088,0,false,-2752,-2688⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1311078848800,0,true,193496718720,193496718784⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨887944406752,0,false,-234979103296,-234979103232⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1311333162838,0,true,193709973696,193709973760⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨887690092714,0,false,-235294056896,-235294056832⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1058704089608,0,false,-41584083136,-41584083072⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1058802018273,0,false,-41482384512,-41482384448⟩
    { al := (157689/819200), au := (394647/2048000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨211646593105,211874494809⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193563280640,193563280704⟩ : DyadicInterval 40),(⟨-235077391424,-235077391360⟩ : DyadicInterval 40),(⟨741625605608,741625624938⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193754377920,193754377984⟩ : DyadicInterval 40),(⟨-235359655872,-235359655808⟩ : DyadicInterval 40),(⟨741581157758,741581177087⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193430160512,193430160576⟩ : DyadicInterval 40),(⟨-234880835328,-234880835264⟩ : DyadicInterval 40),(⟨741656534879,741656554209⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193665552832,193665552896⟩ : DyadicInterval 40),(⟨-235228439808,-235228439744⟩ : DyadicInterval 40),(⟨741601824927,741601844257⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨54372680,81652947⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54371328,54371392⟩ : DyadicInterval 40),(⟨-54374080,-54374016⟩ : DyadicInterval 40),(⟨762123382239,762123401568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81649856,81649920⟩ : DyadicInterval 40),(⟨-81656000,-81655936⟩ : DyadicInterval 40),(⟨762123380559,762123399889⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6080,-2688⟩ : DyadicInterval 40),(⟨762123384960,762123405920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨211567221024,211821535062⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193496718720,193496718784⟩ : DyadicInterval 40),(⟨-234979103296,-234979103232⟩ : DyadicInterval 40),(⟨741641074127,741641093457⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193709973696,193709973760⟩ : DyadicInterval 40),(⟨-235294056896,-235294056832⟩ : DyadicInterval 40),(⟨741591490955,741591510285⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-41584083136,-41482384448⟩ : DyadicInterval 40),(⟨782864575840,782915444448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨193563280640,193754377984⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-235359655872,-235077391360⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1008_ok : ecellOkT e1008 = true := by decide +kernel
theorem e1008_pos {a z : ℝ} (ha1 : ((157689/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((394647/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1008 e1008_ok ha1 ha2 hz1 hz2 hz

-- box ['394647/2048000', '790143/4096000', '999/1000', '3997/4000']  interval_lower 5428431/17179869184
noncomputable def e1009 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1311386122584,0,true,193754377920,193754377984⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨887637132968,0,false,-235359655872,-235359655808⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1311614024287,0,true,193945441984,193945442048⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨887409231265,0,false,-235641992832,-235641992768⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1311174248089,0,true,193576720640,193576720704⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨887849007463,0,false,-235097239360,-235097239296⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1311454947490,0,true,193812081600,193812081664⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨887568308062,0,false,-235444912256,-235444912192⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593279069,0,true,81648256,81648320⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429976483,0,false,-81654336,-81654272⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099620621168,0,true,108987968,108988032⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099402634384,0,false,-108998848,-108998784⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511616971,0,false,-10816,-10752⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621713,0,false,-6080,-6016⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1311280181356,0,true,193665549504,193665549568⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨887743074196,0,false,-235228434880,-235228434816⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1311534495216,0,true,193878771648,193878771712⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨887488760336,0,false,-235543459712,-235543459648⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1058626479150,0,false,-41664688000,-41664687936⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1058724500881,0,false,-41562885312,-41562885248⟩
    { al := (394647/2048000), au := (790143/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨211874494808,212102396511⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193754377920,193754377984⟩ : DyadicInterval 40),(⟨-235359655872,-235359655808⟩ : DyadicInterval 40),(⟨741581157758,741581177088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193945441984,193945442048⟩ : DyadicInterval 40),(⟨-235641992832,-235641992768⟩ : DyadicInterval 40),(⟨741536660866,741536680196⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193576720640,193576720704⟩ : DyadicInterval 40),(⟨-235097239360,-235097239296⟩ : DyadicInterval 40),(⟨741622481437,741622500766⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193812081600,193812081664⟩ : DyadicInterval 40),(⟨-235444912256,-235444912192⟩ : DyadicInterval 40),(⟨741567725138,741567744467⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨81651293,108993392⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81648256,81648320⟩ : DyadicInterval 40),(⟨-81654336,-81654272⟩ : DyadicInterval 40),(⟨762123380528,762123399857⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨108987968,108988032⟩ : DyadicInterval 40),(⟨-108998848,-108998784⟩ : DyadicInterval 40),(⟨762123378187,762123397517⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-10816,-6016⟩ : DyadicInterval 40),(⟨762123386624,762123408288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨211768553580,212022867440⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193665549504,193665549568⟩ : DyadicInterval 40),(⟨-235228434880,-235228434816⟩ : DyadicInterval 40),(⟨741601825699,741601845028⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193878771648,193878771712⟩ : DyadicInterval 40),(⟨-235543459712,-235543459648⟩ : DyadicInterval 40),(⟨741552194171,741552213500⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-41664688000,-41562885248⟩ : DyadicInterval 40),(⟨782904826240,782955746880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨193754377920,193945442048⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-235641992832,-235359655808⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1009_ok : ecellOkT e1009 = true := by decide +kernel
theorem e1009_pos {a z : ℝ} (ha1 : ((394647/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((790143/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1009 e1009_ok ha1 ha2 hz1 hz2 hz

-- box ['790143/4096000', '49437/256000', '999/1000', '3997/4000']  interval_lower 351533971/1099511627776
noncomputable def e1010 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1311614024286,0,true,193945441984,193945442048⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨887409231266,0,false,-235641992832,-235641992768⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1311841925989,0,true,194136472896,194136472960⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨887181329563,0,false,-235924402304,-235924402240⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1311401921889,0,true,193767624512,193767624576⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨887621333663,0,false,-235379226560,-235379226496⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1311682678266,0,true,194002992384,194002992448⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨887340577286,0,false,-235727059264,-235727059200⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593371797,0,true,81740928,81740992⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429883755,0,false,-81747072,-81747008⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099620744829,0,true,109111616,109111680⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099402510723,0,false,-109122496,-109122432⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511616947,0,false,-10880,-10816⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621699,0,false,-6080,-6016⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1311507969104,0,true,193856533504,193856533568⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨887515286448,0,false,-235510596928,-235510596864⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1311762311459,0,true,194069742464,194069742528⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨887260944093,0,false,-235825737920,-235825737856⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1058538570660,0,false,-41755995392,-41755995328⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1058636708766,0,false,-41654063360,-41654063296⟩
    { al := (790143/4096000), au := (49437/256000), zl := (999/1000), zu := (3997/4000),
      A := ⟨212102396510,212330298213⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193945441984,193945442048⟩ : DyadicInterval 40),(⟨-235641992832,-235641992768⟩ : DyadicInterval 40),(⟨741536660866,741536680196⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194136472896,194136472960⟩ : DyadicInterval 40),(⟨-235924402304,-235924402240⟩ : DyadicInterval 40),(⟨741492114882,741492134211⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193767624512,193767624576⟩ : DyadicInterval 40),(⟨-235379226560,-235379226496⟩ : DyadicInterval 40),(⟨741578074594,741578093924⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194002992384,194002992448⟩ : DyadicInterval 40),(⟨-235727059264,-235727059200⟩ : DyadicInterval 40),(⟨741523246796,741523266126⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨81744021,109117053⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81740928,81740992⟩ : DyadicInterval 40),(⟨-81747072,-81747008⟩ : DyadicInterval 40),(⟨762123380546,762123399875⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨109111616,109111680⟩ : DyadicInterval 40),(⟨-109122496,-109122432⟩ : DyadicInterval 40),(⟨762123378162,762123397492⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-10880,-6016⟩ : DyadicInterval 40),(⟨762123386624,762123408320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨211996341328,212250683683⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193856533504,193856533568⟩ : DyadicInterval 40),(⟨-235510596928,-235510596864⟩ : DyadicInterval 40),(⟨741557373826,741557393156⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194069742464,194069742528⟩ : DyadicInterval 40),(⟨-235825737920,-235825737856⟩ : DyadicInterval 40),(⟨741507682023,741507701352⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-41755995392,-41654063296⟩ : DyadicInterval 40),(⟨782950415264,783001400576⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨193945441984,194136472960⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-235924402304,-235641992768⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1010_ok : ecellOkT e1010 = true := by decide +kernel
theorem e1010_pos {a z : ℝ} (ha1 : ((790143/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((49437/256000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1010 e1010_ok ha1 ha2 hz1 hz2 hz

-- box ['394647/2048000', '790143/4096000', '3997/4000', '1999/2000']  interval_lower 173328199/549755813888
noncomputable def e1011 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1311386122584,0,true,193754377920,193754377984⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨887637132968,0,false,-235359655872,-235359655808⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1311614024287,0,true,193945441984,193945442048⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨887409231265,0,false,-235641992832,-235641992768⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1311227216712,0,true,193621137664,193621137728⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨887796038840,0,false,-235162837632,-235162837568⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1311507973089,0,true,193856536832,193856536896⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨887515282463,0,false,-235510601856,-235510601792⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566062265,0,true,54433088,54433152⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457193287,0,false,-54435840,-54435776⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593373454,0,true,81742592,81742656⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429882098,0,false,-81748736,-81748672⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621698,0,false,-6080,-6016⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625082,0,false,-2752,-2688⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1311306665040,0,true,193687755904,193687755968⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨887716590512,0,false,-235261236672,-235261236608⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1311561007563,0,true,193900997760,193900997824⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨887462247989,0,false,-235576306368,-235576306304⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1058616253564,0,false,-41675308608,-41675308544⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1058714298602,0,false,-41573480704,-41573480640⟩
    { al := (394647/2048000), au := (790143/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨211874494808,212102396511⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193754377920,193754377984⟩ : DyadicInterval 40),(⟨-235359655872,-235359655808⟩ : DyadicInterval 40),(⟨741581157758,741581177088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193945441984,193945442048⟩ : DyadicInterval 40),(⟨-235641992832,-235641992768⟩ : DyadicInterval 40),(⟨741536660866,741536680196⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193621137664,193621137728⟩ : DyadicInterval 40),(⟨-235162837632,-235162837568⟩ : DyadicInterval 40),(⟨741612154491,741612173820⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193856536832,193856536896⟩ : DyadicInterval 40),(⟨-235510601856,-235510601792⟩ : DyadicInterval 40),(⟨741557373052,741557392381⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨54434489,81745678⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54433088,54433152⟩ : DyadicInterval 40),(⟨-54435840,-54435776⟩ : DyadicInterval 40),(⟨762123382233,762123401562⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81742592,81742656⟩ : DyadicInterval 40),(⟨-81748736,-81748672⟩ : DyadicInterval 40),(⟨762123380546,762123399875⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6080,-2688⟩ : DyadicInterval 40),(⟨762123384960,762123405920⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨211795037264,212049379787⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193687755904,193687755968⟩ : DyadicInterval 40),(⟨-235261236672,-235261236608⟩ : DyadicInterval 40),(⟨741596660043,741596679372⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193900997760,193900997824⟩ : DyadicInterval 40),(⟨-235576306368,-235576306304⟩ : DyadicInterval 40),(⟨741547016543,741547035872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-41675308608,-41573480640⟩ : DyadicInterval 40),(⟨782910123936,782961057184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨193754377920,193945442048⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-235641992832,-235359655808⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1011_ok : ecellOkT e1011 = true := by decide +kernel
theorem e1011_pos {a z : ℝ} (ha1 : ((394647/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((790143/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1011 e1011_ok ha1 ha2 hz1 hz2 hz

-- box ['790143/4096000', '49437/256000', '3997/4000', '1999/2000']  interval_lower 350768015/1099511627776
noncomputable def e1012 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1311614024286,0,true,193945441984,193945442048⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨887409231266,0,false,-235641992832,-235641992768⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1311841925989,0,true,194136472896,194136472960⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨887181329563,0,false,-235924402304,-235924402240⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1311454947488,0,true,193812081600,193812081664⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨887568308064,0,false,-235444912256,-235444912192⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1311735760841,0,true,194047487680,194047487744⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨887287494711,0,false,-235792836352,-235792836288⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566124085,0,true,54494912,54494976⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457131467,0,false,-54497664,-54497600⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099593466203,0,true,81835328,81835392⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429789349,0,false,-81841536,-81841472⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621684,0,false,-6144,-6080⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625075,0,false,-2752,-2688⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1311534481274,0,true,193878759936,193878760000⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨887488774278,0,false,-235543442432,-235543442368⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1311788852293,0,true,194091988608,194091988672⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨887234403259,0,false,-235858628352,-235858628288⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1058528323088,0,false,-41766639680,-41766639616⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1058626484528,0,false,-41664682432,-41664682368⟩
    { al := (790143/4096000), au := (49437/256000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨212102396510,212330298213⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193945441984,193945442048⟩ : DyadicInterval 40),(⟨-235641992832,-235641992768⟩ : DyadicInterval 40),(⟨741536660866,741536680196⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194136472896,194136472960⟩ : DyadicInterval 40),(⟨-235924402304,-235924402240⟩ : DyadicInterval 40),(⟨741492114882,741492134211⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193812081600,193812081664⟩ : DyadicInterval 40),(⟨-235444912256,-235444912192⟩ : DyadicInterval 40),(⟨741567725138,741567744468⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194047487680,194047487744⟩ : DyadicInterval 40),(⟨-235792836352,-235792836288⟩ : DyadicInterval 40),(⟨741512872162,741512891492⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨54496309,81838427⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54494912,54494976⟩ : DyadicInterval 40),(⟨-54497664,-54497600⟩ : DyadicInterval 40),(⟨762123382226,762123401556⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨81835328,81835392⟩ : DyadicInterval 40),(⟨-81841536,-81841472⟩ : DyadicInterval 40),(⟨762123380564,762123399893⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6144,-2688⟩ : DyadicInterval 40),(⟨762123384960,762123405952⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨212022853498,212277224517⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193878759936,193878760000⟩ : DyadicInterval 40),(⟨-235543442432,-235543442368⟩ : DyadicInterval 40),(⟨741552196905,741552216234⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194091988608,194091988672⟩ : DyadicInterval 40),(⟨-235858628352,-235858628288⟩ : DyadicInterval 40),(⟨741502493126,741502512455⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-41766639680,-41664682368⟩ : DyadicInterval 40),(⟨782955724800,783006722720⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨193945441984,194136472960⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-235924402304,-235641992768⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1012_ok : ecellOkT e1012 = true := by decide +kernel
theorem e1012_pos {a z : ℝ} (ha1 : ((790143/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((49437/256000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1012 e1012_ok ha1 ha2 hz1 hz2 hz

-- box ['196899/1024000', '157689/819200', '1999/2000', '3999/4000']  interval_lower 337727207/1099511627776
noncomputable def e1013 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1310930319179,0,true,193372150080,193372150144⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨888092936373,0,false,-234795199424,-234795199360⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1311158220882,0,true,193563280640,193563280704⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨887865034670,0,false,-235077391424,-235077391360⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1310824609833,0,true,193283485312,193283485376⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨888198645719,0,false,-234664332800,-234664332736⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1311105309234,0,true,193518909056,193518909120⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨887917946318,0,false,-235011868800,-235011868736⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538783277,0,true,27155136,27155200⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484472275,0,false,-27155840,-27155776⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566001728,0,true,54372544,54372608⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457253824,0,false,-54375360,-54375296⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625087,0,false,-2752,-2688⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627106,0,false,-704,-640⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1310877459454,0,true,193327814336,193327814400⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨888145796098,0,false,-234729757888,-234729757824⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1311131773671,0,true,193541102272,193541102336⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨887891481881,0,false,-235044640320,-235044640256⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1058781648194,0,false,-41503537984,-41503537920⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1058879483766,0,false,-41401943552,-41401943488⟩
    { al := (196899/1024000), au := (157689/819200), zl := (1999/2000), zu := (3999/4000),
      A := ⟨211418691403,211646593106⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193372150080,193372150144⟩ : DyadicInterval 40),(⟨-234795199424,-234795199360⟩ : DyadicInterval 40),(⟨741670004439,741670023769⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193563280640,193563280704⟩ : DyadicInterval 40),(⟨-235077391424,-235077391360⟩ : DyadicInterval 40),(⟨741625605608,741625624937⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193283485312,193283485376⟩ : DyadicInterval 40),(⟨-234664332800,-234664332736⟩ : DyadicInterval 40),(⟨741690581617,741690600947⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193518909056,193518909120⟩ : DyadicInterval 40),(⟨-235011868800,-235011868736⟩ : DyadicInterval 40),(⟨741635918000,741635937329⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨27155501,54373952⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27155136,27155200⟩ : DyadicInterval 40),(⟨-27155840,-27155776⟩ : DyadicInterval 40),(⟨762123383233,762123402562⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54372544,54372608⟩ : DyadicInterval 40),(⟨-54375360,-54375296⟩ : DyadicInterval 40),(⟨762123382270,762123401600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2752,-640⟩ : DyadicInterval 40),(⟨762123383936,762123404256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨211365831678,211620145895⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193327814336,193327814400⟩ : DyadicInterval 40),(⟨-234729757888,-234729757824⟩ : DyadicInterval 40),(⟨741680295331,741680314661⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193541102272,193541102336⟩ : DyadicInterval 40),(⟨-235044640320,-235044640256⟩ : DyadicInterval 40),(⟨741630760481,741630779811⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-41503537984,-41401943488⟩ : DyadicInterval 40),(⟨782824355360,782875171872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨193372150080,193563280704⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-235077391424,-234795199360⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1013_ok : ecellOkT e1013 = true := by decide +kernel
theorem e1013_pos {a z : ℝ} (ha1 : ((196899/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((157689/819200 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1013 e1013_ok ha1 ha2 hz1 hz2 hz

-- box ['157689/819200', '394647/2048000', '1999/2000', '3999/4000']  interval_lower 42725145/137438953472
noncomputable def e1014 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1311158220881,0,true,193563280640,193563280704⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨887865034671,0,false,-235077391424,-235077391360⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1311386122585,0,true,193754377920,193754377984⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨887637132967,0,false,-235359655872,-235359655808⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1311052397584,0,true,193474535680,193474535744⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨887970857968,0,false,-234946350144,-234946350080⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1311333153962,0,true,193709966272,193709966336⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨887690101590,0,false,-235294045888,-235294045824⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538814176,0,true,27186048,27186112⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484441376,0,false,-27186752,-27186688⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566063539,0,true,54434368,54434432⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457192013,0,false,-54437120,-54437056⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625080,0,false,-2752,-2688⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627104,0,false,-704,-640⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1311105304178,0,true,193518904832,193518904896⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨887917951374,0,false,-235011862592,-235011862528⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1311359646883,0,true,193732179520,193732179584⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨887663608669,0,false,-235326861056,-235326860992⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1058693884638,0,false,-41594681472,-41594681408⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1058791836587,0,false,-41492957760,-41492957696⟩
    { al := (157689/819200), au := (394647/2048000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨211646593105,211874494809⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193563280640,193563280704⟩ : DyadicInterval 40),(⟨-235077391424,-235077391360⟩ : DyadicInterval 40),(⟨741625605608,741625624938⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193754377920,193754377984⟩ : DyadicInterval 40),(⟨-235359655872,-235359655808⟩ : DyadicInterval 40),(⟨741581157758,741581177087⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193474535680,193474535744⟩ : DyadicInterval 40),(⟨-234946350144,-234946350080⟩ : DyadicInterval 40),(⟨741646227774,741646247104⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193709966272,193709966336⟩ : DyadicInterval 40),(⟨-235294045888,-235294045824⟩ : DyadicInterval 40),(⟨741591492670,741591512000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨27186400,54435763⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27186048,27186112⟩ : DyadicInterval 40),(⟨-27186752,-27186688⟩ : DyadicInterval 40),(⟨762123383231,762123402560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54434368,54434432⟩ : DyadicInterval 40),(⟨-54437120,-54437056⟩ : DyadicInterval 40),(⟨762123382232,762123401562⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2752,-640⟩ : DyadicInterval 40),(⟨762123383936,762123404256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨211593676402,211848019107⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193518904832,193518904896⟩ : DyadicInterval 40),(⟨-235011862592,-235011862528⟩ : DyadicInterval 40),(⟨741635918997,741635938326⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193732179520,193732179584⟩ : DyadicInterval 40),(⟨-235326861056,-235326860992⟩ : DyadicInterval 40),(⟨741586323878,741586343207⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-41594681472,-41492957696⟩ : DyadicInterval 40),(⟨782869862464,782920743616⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨193563280640,193754377984⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-235359655872,-235077391360⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1014_ok : ecellOkT e1014 = true := by decide +kernel
theorem e1014_pos {a z : ℝ} (ha1 : ((157689/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((394647/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1014 e1014_ok ha1 ha2 hz1 hz2 hz

-- box ['196899/1024000', '157689/819200', '3999/4000', '1']  interval_lower 168484175/549755813888
noncomputable def e1015 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1310930319179,0,true,193372150080,193372150144⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨888092936373,0,false,-234795199424,-234795199360⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1311158220882,0,true,193563280640,193563280704⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨887865034670,0,false,-235077391424,-235077391360⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1310877464506,0,true,193327818624,193327818688⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨888145791046,0,false,-234729764160,-234729764096⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538815070,0,true,27186944,27187008⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484440482,0,false,-27187648,-27187584⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627103,0,false,-704,-640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1310903886526,0,true,193349980096,193349980160⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨888119369026,0,false,-234762474752,-234762474688⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1311158229407,0,true,193563287744,193563287808⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨887865026145,0,false,-235077401984,-235077401920⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1058771463824,0,false,-41514114240,-41514114176⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1058869322656,0,false,-41412494592,-41412494528⟩
    { al := (196899/1024000), au := (157689/819200), zl := (3999/4000), zu := 1,
      A := ⟨211418691403,211646593106⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193372150080,193372150144⟩ : DyadicInterval 40),(⟨-234795199424,-234795199360⟩ : DyadicInterval 40),(⟨741670004439,741670023769⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193563280640,193563280704⟩ : DyadicInterval 40),(⟨-235077391424,-235077391360⟩ : DyadicInterval 40),(⟨741625605608,741625624937⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193327818624,193327818688⟩ : DyadicInterval 40),(⟨-234729764160,-234729764096⟩ : DyadicInterval 40),(⟨741680294325,741680313654⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193563280640,193563280704⟩ : DyadicInterval 40),(⟨-235077391424,-235077391360⟩ : DyadicInterval 40),(⟨741625605608,741625624937⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,27187294⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27186944,27187008⟩ : DyadicInterval 40),(⟨-27187648,-27187584⟩ : DyadicInterval 40),(⟨762123383231,762123402560⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-704,0⟩ : DyadicInterval 40),(⟨762123383616,762123403232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨211392258750,211646601631⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193349980096,193349980160⟩ : DyadicInterval 40),(⟨-234762474752,-234762474688⟩ : DyadicInterval 40),(⟨741675150771,741675170100⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193563287744,193563287808⟩ : DyadicInterval 40),(⟨-235077401984,-235077401920⟩ : DyadicInterval 40),(⟨741625603974,741625623303⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-41514114240,-41412494528⟩ : DyadicInterval 40),(⟨782829630880,782880460000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨193372150080,193563280704⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-235077391424,-234795199360⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1015_ok : ecellOkT e1015 = true := by decide +kernel
theorem e1015_pos {a z : ℝ} (ha1 : ((196899/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((157689/819200 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1015 e1015_ok ha1 ha2 hz1 hz2 hz

-- box ['157689/819200', '394647/2048000', '3999/4000', '1']  interval_lower 170519733/549755813888
noncomputable def e1016 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1311158220881,0,true,193563280640,193563280704⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨887865034671,0,false,-235077391424,-235077391360⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1311386122585,0,true,193754377920,193754377984⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨887637132967,0,false,-235359655872,-235359655808⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1311105309232,0,true,193518909056,193518909120⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨887917946320,0,false,-235011868800,-235011868736⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538845976,0,true,27217856,27217920⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484409576,0,false,-27218560,-27218496⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627102,0,false,-704,-640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1311131759739,0,true,193541090560,193541090624⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨887891495813,0,false,-235044623040,-235044622976⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1311386131107,0,true,193754385088,193754385152⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨887637124445,0,false,-235359666432,-235359666368⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1058683678323,0,false,-41605281344,-41605281280⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1058781653558,0,false,-41503532416,-41503532352⟩
    { al := (157689/819200), au := (394647/2048000), zl := (3999/4000), zu := 1,
      A := ⟨211646593105,211874494809⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193563280640,193563280704⟩ : DyadicInterval 40),(⟨-235077391424,-235077391360⟩ : DyadicInterval 40),(⟨741625605608,741625624938⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193754377920,193754377984⟩ : DyadicInterval 40),(⟨-235359655872,-235359655808⟩ : DyadicInterval 40),(⟨741581157758,741581177087⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193518909056,193518909120⟩ : DyadicInterval 40),(⟨-235011868800,-235011868736⟩ : DyadicInterval 40),(⟨741635918000,741635937330⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193754377920,193754377984⟩ : DyadicInterval 40),(⟨-235359655872,-235359655808⟩ : DyadicInterval 40),(⟨741581157758,741581177087⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,27218200⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27217856,27217920⟩ : DyadicInterval 40),(⟨-27218560,-27218496⟩ : DyadicInterval 40),(⟨762123383230,762123402559⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-704,0⟩ : DyadicInterval 40),(⟨762123383616,762123403232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨211620131963,211874503331⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193541090560,193541090624⟩ : DyadicInterval 40),(⟨-235044623040,-235044622976⟩ : DyadicInterval 40),(⟨741630763203,741630782532⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193754385088,193754385152⟩ : DyadicInterval 40),(⟨-235359666432,-235359666368⟩ : DyadicInterval 40),(⟨741581156083,741581175412⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-41605281344,-41503532352⟩ : DyadicInterval 40),(⟨782875149792,782926043552⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨193563280640,193754377984⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-235359655872,-235077391360⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1016_ok : ecellOkT e1016 = true := by decide +kernel
theorem e1016_pos {a z : ℝ} (ha1 : ((157689/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((394647/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1016 e1016_ok ha1 ha2 hz1 hz2 hz

-- box ['394647/2048000', '790143/4096000', '1999/2000', '3999/4000']  interval_lower 172946215/549755813888
noncomputable def e1017 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1311386122584,0,true,193754377920,193754377984⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨887637132968,0,false,-235359655872,-235359655808⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1311614024287,0,true,193945441984,193945442048⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨887409231265,0,false,-235641992832,-235641992768⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1311280185336,0,true,193665552832,193665552896⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨887743070216,0,false,-235228439808,-235228439744⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1311560998689,0,true,193900990336,193900990400⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨887462256863,0,false,-235576295360,-235576295296⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538845081,0,true,27216960,27217024⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484410471,0,false,-27217664,-27217600⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566125362,0,true,54496192,54496256⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457130190,0,false,-54498944,-54498880⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625074,0,false,-2752,-2688⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627103,0,false,-704,-640⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1311333148900,0,true,193709962048,193709962112⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨887690106652,0,false,-235294039616,-235294039552⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1311587520097,0,true,193923223616,193923223680⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨887435735455,0,false,-235609154304,-235609154240⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1058606026627,0,false,-41685930624,-41685930560⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1058704094979,0,false,-41584077568,-41584077504⟩
    { al := (394647/2048000), au := (790143/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨211874494808,212102396511⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193754377920,193754377984⟩ : DyadicInterval 40),(⟨-235359655872,-235359655808⟩ : DyadicInterval 40),(⟨741581157758,741581177088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193945441984,193945442048⟩ : DyadicInterval 40),(⟨-235641992832,-235641992768⟩ : DyadicInterval 40),(⟨741536660866,741536680196⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193665552832,193665552896⟩ : DyadicInterval 40),(⟨-235228439808,-235228439744⟩ : DyadicInterval 40),(⟨741601824928,741601844257⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193900990336,193900990400⟩ : DyadicInterval 40),(⟨-235576295360,-235576295296⟩ : DyadicInterval 40),(⟨741547018261,741547037591⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨27217305,54497586⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27216960,27217024⟩ : DyadicInterval 40),(⟨-27217664,-27217600⟩ : DyadicInterval 40),(⟨762123383230,762123402559⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54496192,54496256⟩ : DyadicInterval 40),(⟨-54498944,-54498880⟩ : DyadicInterval 40),(⟨762123382226,762123401555⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2752,-640⟩ : DyadicInterval 40),(⟨762123383936,762123404256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨211821521124,212075892321⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193709962048,193709962112⟩ : DyadicInterval 40),(⟨-235294039616,-235294039552⟩ : DyadicInterval 40),(⟨741591493645,741591512974⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193923223616,193923223680⟩ : DyadicInterval 40),(⟨-235609154304,-235609154240⟩ : DyadicInterval 40),(⟨741541838219,741541857548⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-41685930624,-41584077504⟩ : DyadicInterval 40),(⟨782915422368,782966368192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨193754377920,193945442048⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-235641992832,-235359655808⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1017_ok : ecellOkT e1017 = true := by decide +kernel
theorem e1017_pos {a z : ℝ} (ha1 : ((394647/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((790143/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1017 e1017_ok ha1 ha2 hz1 hz2 hz

-- box ['790143/4096000', '49437/256000', '1999/2000', '3999/4000']  interval_lower 350001065/1099511627776
noncomputable def e1018 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1311614024286,0,true,193945441984,193945442048⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨887409231266,0,false,-235641992832,-235641992768⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1311841925989,0,true,194136472896,194136472960⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨887181329563,0,false,-235924402304,-235924402240⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1311507973087,0,true,193856536832,193856536896⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨887515282465,0,false,-235510601856,-235510601792⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1311788843415,0,true,194091981184,194091981248⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨887234412137,0,false,-235858617344,-235858617280⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538875992,0,true,27247872,27247936⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484379560,0,false,-27248576,-27248512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099566187195,0,true,54558016,54558080⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099457068357,0,false,-54560832,-54560768⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625068,0,false,-2752,-2688⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627101,0,false,-704,-640⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1311560993620,0,true,193900986048,193900986112⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨887462261932,0,false,-235576289088,-235576289024⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1311815393309,0,true,194114234496,194114234560⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨887207862243,0,false,-235891520000,-235891519936⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1058518074164,0,false,-41777285440,-41777285376⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1058616258943,0,false,-41675302976,-41675302912⟩
    { al := (790143/4096000), au := (49437/256000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨212102396510,212330298213⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193945441984,193945442048⟩ : DyadicInterval 40),(⟨-235641992832,-235641992768⟩ : DyadicInterval 40),(⟨741536660866,741536680196⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194136472896,194136472960⟩ : DyadicInterval 40),(⟨-235924402304,-235924402240⟩ : DyadicInterval 40),(⟨741492114882,741492134211⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193856536832,193856536896⟩ : DyadicInterval 40),(⟨-235510601856,-235510601792⟩ : DyadicInterval 40),(⟨741557373052,741557392382⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194091981184,194091981248⟩ : DyadicInterval 40),(⟨-235858617344,-235858617280⟩ : DyadicInterval 40),(⟨741502494849,741502514178⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨27248216,54559419⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27247872,27247936⟩ : DyadicInterval 40),(⟨-27248576,-27248512⟩ : DyadicInterval 40),(⟨762123383228,762123402557⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨54558016,54558080⟩ : DyadicInterval 40),(⟨-54560832,-54560768⟩ : DyadicInterval 40),(⟨762123382252,762123401581⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2752,-640⟩ : DyadicInterval 40),(⟨762123383936,762123404256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨212049365844,212303765533⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193900986048,193900986112⟩ : DyadicInterval 40),(⟨-235576289088,-235576289024⟩ : DyadicInterval 40),(⟨741547019277,741547038607⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨194114234496,194114234560⟩ : DyadicInterval 40),(⟨-235891520000,-235891519936⟩ : DyadicInterval 40),(⟨741497303505,741497322835⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-41777285440,-41675302912⟩ : DyadicInterval 40),(⟨782961035072,783012045600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨193945441984,194136472960⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-235924402304,-235641992768⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1018_ok : ecellOkT e1018 = true := by decide +kernel
theorem e1018_pos {a z : ℝ} (ha1 : ((790143/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((49437/256000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1018 e1018_ok ha1 ha2 hz1 hz2 hz

-- box ['394647/2048000', '790143/4096000', '3999/4000', '1']  interval_lower 86282001/274877906944
noncomputable def e1019 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1311386122584,0,true,193754377920,193754377984⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨887637132968,0,false,-235359655872,-235359655808⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1311614024287,0,true,193945441984,193945442048⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨887409231265,0,false,-235641992832,-235641992768⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1311333153960,0,true,193709966272,193709966336⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨887690101592,0,false,-235294045888,-235294045824⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099538876888,0,true,27248768,27248832⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099484378664,0,false,-27249472,-27249408⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627100,0,false,-704,-640⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1311359632945,0,true,193732167872,193732167936⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨887663622607,0,false,-235326843776,-235326843712⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1311614032802,0,true,193945449152,193945449216⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨887409222750,0,false,-235642003392,-235642003328⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1058595798346,0,false,-41696554176,-41696554112⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1058693890010,0,false,-41594675904,-41594675840⟩
    { al := (394647/2048000), au := (790143/4096000), zl := (3999/4000), zu := 1,
      A := ⟨211874494808,212102396511⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193754377920,193754377984⟩ : DyadicInterval 40),(⟨-235359655872,-235359655808⟩ : DyadicInterval 40),(⟨741581157758,741581177088⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193945441984,193945442048⟩ : DyadicInterval 40),(⟨-235641992832,-235641992768⟩ : DyadicInterval 40),(⟨741536660866,741536680196⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193709966272,193709966336⟩ : DyadicInterval 40),(⟨-235294045888,-235294045824⟩ : DyadicInterval 40),(⟨741591492671,741591512000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193945441984,193945442048⟩ : DyadicInterval 40),(⟨-235641992832,-235641992768⟩ : DyadicInterval 40),(⟨741536660866,741536680196⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,27249112⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨27248768,27248832⟩ : DyadicInterval 40),(⟨-27249472,-27249408⟩ : DyadicInterval 40),(⟨762123383228,762123402557⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-704,0⟩ : DyadicInterval 40),(⟨762123383616,762123403232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨211848005169,212102405026⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193732167872,193732167936⟩ : DyadicInterval 40),(⟨-235326843776,-235326843712⟩ : DyadicInterval 40),(⟨741586326568,741586345897⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨193945449152,193945449216⟩ : DyadicInterval 40),(⟨-235642003392,-235642003328⟩ : DyadicInterval 40),(⟨741536659189,741536678518⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-41696554176,-41594675840⟩ : DyadicInterval 40),(⟨782920721536,782971679968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨193754377920,193945442048⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-235641992832,-235359655808⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1019_ok : ecellOkT e1019 = true := by decide +kernel
theorem e1019_pos {a z : ℝ} (ha1 : ((394647/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((790143/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1019 e1019_ok ha1 ha2 hz1 hz2 hz

end CKLaneC2R.EpCells.B016

end


