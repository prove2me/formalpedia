-- Prove2me | Definitions.Def_CK_CKLaneC2R_EpCells_B023
-- name    : CK_CKLaneC2R_EpCells_B023
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T14:21:15.600481+00:00
-- url     : https://prove2.me/theorems/465bd27f-298b-46ba-98a7-ef0092bb244c
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EpCells.B023` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EpCells.B023` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EpCells.B023` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EpCells.B023 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EpCells/B023.lean)

import Definitions.Def_CK_CKLaneC2R_EndpointCheckT

-- ===== source module CKLaneC2R.EpCells.B023 =====
section

namespace CKLaneC2R.EpCells.B023

open GeneralCK GeneralCK.Certificates CKLaneC2R CKLaneC2R.Endpoint

-- box ['868251/4096000', '8691/40960', '3997/4000', '1999/2000']  interval_lower 809644901/1099511627776
noncomputable def e1380 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1332580980883,0,true,211382806272,211382806336⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨866442274669,0,false,-261932144320,-261932144256⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1332808882586,0,true,211570831744,211570831808⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨866214372966,0,false,-262221388672,-262221388608⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1332406178868,0,true,211238567808,211238567872⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨866617076684,0,false,-261710343680,-261710343616⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1332692233959,0,true,211474597312,211474597376⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨866331021593,0,false,-262073333120,-262073333056⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099571860575,0,true,60231104,60231168⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099451394977,0,false,-60234496,-60234432⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099602072753,0,true,90441216,90441280⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099421182799,0,false,-90448704,-90448640⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620336,0,false,-7488,-7424⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624477,0,false,-3328,-3264⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1332493575077,0,true,211310685440,211310685504⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨866529680475,0,false,-261821232320,-261821232256⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1332750567305,0,true,211522723008,211522723072⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨866272688247,0,false,-262147369856,-262147369792⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1050034749552,0,false,-50624646848,-50624646784⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1050143720792,0,false,-50510546880,-50510546816⟩
    { al := (868251/4096000), au := (8691/40960), zl := (3997/4000), zu := (1999/2000),
      A := ⟨233069353107,233297254810⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211382806272,211382806336⟩ : DyadicInterval 40),(⟨-261932144320,-261932144256⟩ : DyadicInterval 40),(⟨737232503361,737232522690⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211570831744,211570831808⟩ : DyadicInterval 40),(⟨-262221388672,-262221388608⟩ : DyadicInterval 40),(⟨737183425350,737183444679⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211238567808,211238567872⟩ : DyadicInterval 40),(⟨-261710343680,-261710343616⟩ : DyadicInterval 40),(⟨737270112970,737270132300⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211474597312,211474597376⟩ : DyadicInterval 40),(⟨-262073333120,-262073333056⟩ : DyadicInterval 40),(⟨737208551493,737208570823⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨60232799,90444977⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨60231104,60231168⟩ : DyadicInterval 40),(⟨-60234496,-60234432⟩ : DyadicInterval 40),(⟨762123381948,762123401277⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨90441216,90441280⟩ : DyadicInterval 40),(⟨-90448704,-90448640⟩ : DyadicInterval 40),(⟨762123379855,762123399185⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7488,-3264⟩ : DyadicInterval 40),(⟨762123385248,762123406624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨232981947301,233238939529⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211310685440,211310685504⟩ : DyadicInterval 40),(⟨-261821232320,-261821232256⟩ : DyadicInterval 40),(⟨737251312839,737251332169⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211522723008,211522723072⟩ : DyadicInterval 40),(⟨-262147369856,-262147369792⟩ : DyadicInterval 40),(⟨737195988106,737196007435⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-50624646848,-50510546816⟩ : DyadicInterval 40),(⟨787378657024,787435726304⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨211382806272,211570831808⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-262221388672,-261932144256⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1380_ok : ecellOkT e1380 = true := by decide +kernel
theorem e1380_pos {a z : ℝ} (ha1 : ((868251/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((8691/40960 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1380 e1380_ok ha1 ha2 hz1 hz2 hz

-- box ['108213/512000', '866553/4096000', '1999/2000', '3999/4000']  interval_lower 98861861/137438953472
noncomputable def e1381 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1331897275777,0,true,210818536896,210818536960⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨867125979775,0,false,-261064867584,-261064867520⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1332125177480,0,true,211006658880,211006658944⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨866898078072,0,false,-261353883840,-261353883776⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1331781082952,0,true,210722612928,210722612992⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨867242172600,0,false,-260917545472,-260917545408⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1332067024093,0,true,210958659072,210958659136⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨866956231459,0,false,-261280128704,-261280128640⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541649975,0,true,30021760,30021824⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099481605577,0,false,-30022656,-30022592⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099571736330,0,true,60106880,60106944⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099451519222,0,false,-60110208,-60110144⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624489,0,false,-3328,-3264⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626957,0,false,-832,-768⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1331839173976,0,true,210770571520,210770571584⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨867184081576,0,false,-260991197248,-260991197184⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1332096109450,0,true,210982666432,210982666496⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨866927146102,0,false,-261317016640,-261317016576⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1050312019741,0,false,-50334350208,-50334350144⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1050420661060,0,false,-50220625664,-50220625600⟩
    { al := (108213/512000), au := (866553/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨232385648001,232613549704⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210818536896,210818536960⟩ : DyadicInterval 40),(⟨-261064867584,-261064867520⟩ : DyadicInterval 40),(⟨737379440644,737379459974⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211006658880,211006658944⟩ : DyadicInterval 40),(⟨-261353883840,-261353883776⟩ : DyadicInterval 40),(⟨737330511000,737330530329⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210722612928,210722612992⟩ : DyadicInterval 40),(⟨-260917545472,-260917545408⟩ : DyadicInterval 40),(⟨737404367731,737404387060⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210958659072,210958659136⟩ : DyadicInterval 40),(⟨-261280128704,-261280128640⟩ : DyadicInterval 40),(⟨737343001023,737343020353⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨30022199,60108554⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨30021760,30021824⟩ : DyadicInterval 40),(⟨-30022656,-30022592⟩ : DyadicInterval 40),(⟨762123383180,762123402509⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨60106880,60106944⟩ : DyadicInterval 40),(⟨-60110208,-60110144⟩ : DyadicInterval 40),(⟨762123381929,762123401259⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3328,-768⟩ : DyadicInterval 40),(⟨762123384000,762123404544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨232327546200,232584481674⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210770571520,210770571584⟩ : DyadicInterval 40),(⟨-260991197248,-260991197184⟩ : DyadicInterval 40),(⟨737391906951,737391926281⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210982666432,210982666496⟩ : DyadicInterval 40),(⟨-261317016640,-261317016576⟩ : DyadicInterval 40),(⟨737336754527,737336773856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-50334350208,-50220625600⟩ : DyadicInterval 40),(⟨787233696416,787290577984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨210818536896,211006658944⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-261353883840,-261064867520⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1381_ok : ecellOkT e1381 = true := by decide +kernel
theorem e1381_pos {a z : ℝ} (ha1 : ((108213/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((866553/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1381 e1381_ok ha1 ha2 hz1 hz2 hz

-- box ['866553/4096000', '433701/2048000', '1999/2000', '3999/4000']  interval_lower 796760911/1099511627776
noncomputable def e1382 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1332125177479,0,true,211006658880,211006658944⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨866898078073,0,false,-261353883840,-261353883776⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1332353079182,0,true,211194748672,211194748736⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨866670176370,0,false,-261642976064,-261642976000⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1332008870704,0,true,210910657216,210910657280⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨867014384848,0,false,-261206378496,-261206378432⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1332294868820,0,true,211146710080,211146710144⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨866728386732,0,false,-261569129280,-261569129216⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541681412,0,true,30053184,30053248⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099481574140,0,false,-30054080,-30054016⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099571799217,0,true,60169792,60169856⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099451456335,0,false,-60173120,-60173056⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624483,0,false,-3328,-3264⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626955,0,false,-832,-768⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1332067018698,0,true,210958654656,210958654720⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨866956236854,0,false,-261280121856,-261280121792⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1332323982669,0,true,211170736768,211170736832⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨866699272883,0,false,-261606063040,-261606062976⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1050215566486,0,false,-50435326208,-50435326144⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1050324326360,0,false,-50321467200,-50321467136⟩
    { al := (866553/4096000), au := (433701/2048000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨232613549703,232841451406⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211006658880,211006658944⟩ : DyadicInterval 40),(⟨-261353883840,-261353883776⟩ : DyadicInterval 40),(⟨737330511000,737330530329⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211194748672,211194748736⟩ : DyadicInterval 40),(⟨-261642976064,-261642976000⟩ : DyadicInterval 40),(⟨737281531901,737281551231⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210910657216,210910657280⟩ : DyadicInterval 40),(⟨-261206378496,-261206378432⟩ : DyadicInterval 40),(⟨737355487791,737355507121⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211146710080,211146710144⟩ : DyadicInterval 40),(⟨-261569129280,-261569129216⟩ : DyadicInterval 40),(⟨737294046786,737294066115⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨30053636,60171441⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨30053184,30053248⟩ : DyadicInterval 40),(⟨-30054080,-30054016⟩ : DyadicInterval 40),(⟨762123383178,762123402507⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨60169792,60169856⟩ : DyadicInterval 40),(⟨-60173120,-60173056⟩ : DyadicInterval 40),(⟨762123381922,762123401252⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3328,-768⟩ : DyadicInterval 40),(⟨762123384000,762123404544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨232555390922,232812354893⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210958654656,210958654720⟩ : DyadicInterval 40),(⟨-261280121856,-261280121792⟩ : DyadicInterval 40),(⟨737343002157,737343021487⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211170736768,211170736832⟩ : DyadicInterval 40),(⟨-261606063040,-261606062976⟩ : DyadicInterval 40),(⟨737287787894,737287807224⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-50435326208,-50321467136⟩ : DyadicInterval 40),(⟨787284117184,787341065984⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨211006658880,211194748736⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-261642976064,-261353883776⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1382_ok : ecellOkT e1382 = true := by decide +kernel
theorem e1382_pos {a z : ℝ} (ha1 : ((866553/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((433701/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1382 e1382_ok ha1 ha2 hz1 hz2 hz

-- box ['108213/512000', '866553/4096000', '3999/4000', '1']  interval_lower 789819417/1099511627776
noncomputable def e1383 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1331897275777,0,true,210818536896,210818536960⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨867125979775,0,false,-261064867584,-261064867520⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1332125177480,0,true,211006658880,211006658944⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨866898078072,0,false,-261353883840,-261353883776⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1331839179364,0,true,210770575936,210770576000⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨867184076188,0,false,-260991204032,-260991203968⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541682436,0,true,30054208,30054272⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099481573116,0,false,-30055104,-30055040⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626954,0,false,-832,-768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1331868221822,0,true,210794551936,210794552000⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨867155033730,0,false,-261028027904,-261028027840⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1332125186025,0,true,211006665920,211006665984⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨866898069527,0,false,-261353894656,-261353894592⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1050299717583,0,false,-50347228672,-50347228608⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1050408384634,0,false,-50233475904,-50233475840⟩
    { al := (108213/512000), au := (866553/4096000), zl := (3999/4000), zu := 1,
      A := ⟨232385648001,232613549704⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210818536896,210818536960⟩ : DyadicInterval 40),(⟨-261064867584,-261064867520⟩ : DyadicInterval 40),(⟨737379440644,737379459974⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211006658880,211006658944⟩ : DyadicInterval 40),(⟨-261353883840,-261353883776⟩ : DyadicInterval 40),(⟨737330511000,737330530329⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210770575936,210770576000⟩ : DyadicInterval 40),(⟨-260991204032,-260991203968⟩ : DyadicInterval 40),(⟨737391905796,737391925126⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211006658880,211006658944⟩ : DyadicInterval 40),(⟨-261353883840,-261353883776⟩ : DyadicInterval 40),(⟨737330511000,737330530329⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,30054660⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨30054208,30054272⟩ : DyadicInterval 40),(⟨-30055104,-30055040⟩ : DyadicInterval 40),(⟨762123383178,762123402507⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-832,0⟩ : DyadicInterval 40),(⟨762123383616,762123403296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨232356594046,232613558249⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210794551936,210794552000⟩ : DyadicInterval 40),(⟨-261028027904,-261028027840⟩ : DyadicInterval 40),(⟨737385674854,737385694183⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211006665920,211006665984⟩ : DyadicInterval 40),(⟨-261353894656,-261353894592⟩ : DyadicInterval 40),(⟨737330509163,737330528493⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-50347228672,-50233475840⟩ : DyadicInterval 40),(⟨787240121536,787297017216⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨210818536896,211006658944⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-261353883840,-261064867520⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1383_ok : ecellOkT e1383 = true := by decide +kernel
theorem e1383_pos {a z : ℝ} (ha1 : ((108213/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((866553/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1383 e1383_ok ha1 ha2 hz1 hz2 hz

-- box ['866553/4096000', '433701/2048000', '3999/4000', '1']  interval_lower 198920359/274877906944
noncomputable def e1384 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1332125177479,0,true,211006658880,211006658944⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨866898078073,0,false,-261353883840,-261353883776⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1332353079182,0,true,211194748672,211194748736⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨866670176370,0,false,-261642976064,-261642976000⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1332067024091,0,true,210958659072,210958659136⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨866956231461,0,false,-261280128704,-261280128640⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541713881,0,true,30085632,30085696⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099481541671,0,false,-30086528,-30086464⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626952,0,false,-832,-768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1332096095031,0,true,210982654528,210982654592⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨866927160521,0,false,-261316998336,-261316998272⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1332353087732,0,true,211194755712,211194755776⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨866670167820,0,false,-261642986944,-261642986880⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1050203240211,0,false,-50448231168,-50448231104⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1050312025843,0,false,-50334343808,-50334343744⟩
    { al := (866553/4096000), au := (433701/2048000), zl := (3999/4000), zu := 1,
      A := ⟨232613549703,232841451406⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211006658880,211006658944⟩ : DyadicInterval 40),(⟨-261353883840,-261353883776⟩ : DyadicInterval 40),(⟨737330511000,737330530329⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211194748672,211194748736⟩ : DyadicInterval 40),(⟨-261642976064,-261642976000⟩ : DyadicInterval 40),(⟨737281531901,737281551231⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210958659072,210958659136⟩ : DyadicInterval 40),(⟨-261280128704,-261280128640⟩ : DyadicInterval 40),(⟨737343001024,737343020353⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211194748672,211194748736⟩ : DyadicInterval 40),(⟨-261642976064,-261642976000⟩ : DyadicInterval 40),(⟨737281531901,737281551231⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,30086105⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨30085632,30085696⟩ : DyadicInterval 40),(⟨-30086528,-30086464⟩ : DyadicInterval 40),(⟨762123383176,762123402505⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-832,0⟩ : DyadicInterval 40),(⟨762123383616,762123403296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨232584467255,232841459956⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨210982654528,210982654592⟩ : DyadicInterval 40),(⟨-261316998336,-261316998272⟩ : DyadicInterval 40),(⟨737336757619,737336776948⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211194755712,211194755776⟩ : DyadicInterval 40),(⟨-261642986944,-261642986880⟩ : DyadicInterval 40),(⟨737281530085,737281549415⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-50448231168,-50334343744⟩ : DyadicInterval 40),(⟨787290555488,787347518464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨211006658880,211194748736⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-261642976064,-261353883776⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1384_ok : ecellOkT e1384 = true := by decide +kernel
theorem e1384_pos {a z : ℝ} (ha1 : ((866553/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((433701/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1384 e1384_ok ha1 ha2 hz1 hz2 hz

-- box ['433701/2048000', '868251/4096000', '1999/2000', '3999/4000']  interval_lower 802648619/1099511627776
noncomputable def e1385 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1332353079181,0,true,211194748672,211194748736⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨866670176371,0,false,-261642976064,-261642976000⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1332580980884,0,true,211382806272,211382806336⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨866442274668,0,false,-261932144320,-261932144256⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1332236658455,0,true,211098669376,211098669440⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨866786597097,0,false,-261495287424,-261495287360⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1332522713546,0,true,211334728896,211334728960⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨866500542006,0,false,-261858205824,-261858205760⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541712854,0,true,30084608,30084672⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099481542698,0,false,-30085504,-30085440⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099571862116,0,true,60232640,60232704⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099451393436,0,false,-60236032,-60235968⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624476,0,false,-3328,-3264⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626953,0,false,-832,-768⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1332294863423,0,true,211146705600,211146705664⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨866728392129,0,false,-261569122432,-261569122368⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1332551855885,0,true,211358774976,211358775040⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨866471399667,0,false,-261895185472,-261895185408⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1050119018780,0,false,-50536410432,-50536410368⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1050227897228,0,false,-50422416768,-50422416704⟩
    { al := (433701/2048000), au := (868251/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨232841451405,233069353108⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211194748672,211194748736⟩ : DyadicInterval 40),(⟨-261642976064,-261642976000⟩ : DyadicInterval 40),(⟨737281531902,737281551231⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211382806272,211382806336⟩ : DyadicInterval 40),(⟨-261932144320,-261932144256⟩ : DyadicInterval 40),(⟨737232503360,737232522690⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211098669376,211098669440⟩ : DyadicInterval 40),(⟨-261495287424,-261495287360⟩ : DyadicInterval 40),(⟨737306558439,737306577768⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211334728896,211334728960⟩ : DyadicInterval 40),(⟨-261858205824,-261858205760⟩ : DyadicInterval 40),(⟨737245043133,737245062462⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨30085078,60234340⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨30084608,30084672⟩ : DyadicInterval 40),(⟨-30085504,-30085440⟩ : DyadicInterval 40),(⟨762123383176,762123402505⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨60232640,60232704⟩ : DyadicInterval 40),(⟨-60236032,-60235968⟩ : DyadicInterval 40),(⟨762123381948,762123401277⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3328,-768⟩ : DyadicInterval 40),(⟨762123384000,762123404544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨232783235647,233040228109⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211146705600,211146705664⟩ : DyadicInterval 40),(⟨-261569122432,-261569122368⟩ : DyadicInterval 40),(⟨737294047961,737294067290⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211358774976,211358775040⟩ : DyadicInterval 40),(⟨-261895185472,-261895185408⟩ : DyadicInterval 40),(⟨737238771808,737238791137⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-50536410432,-50422416704⟩ : DyadicInterval 40),(⟨787334591968,787391608096⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨211194748672,211382806336⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-261932144320,-261642976000⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1385_ok : ecellOkT e1385 = true := by decide +kernel
theorem e1385_pos {a z : ℝ} (ha1 : ((433701/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((868251/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1385 e1385_ok ha1 ha2 hz1 hz2 hz

-- box ['868251/4096000', '8691/40960', '1999/2000', '3999/4000']  interval_lower 808558201/1099511627776
noncomputable def e1386 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1332580980883,0,true,211382806272,211382806336⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨866442274669,0,false,-261932144320,-261932144256⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1332808882586,0,true,211570831744,211570831808⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨866214372966,0,false,-262221388672,-262221388608⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1332464446206,0,true,211286649408,211286649472⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨866558809346,0,false,-261784272256,-261784272192⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1332750558273,0,true,211522715584,211522715648⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨866272697279,0,false,-262147358400,-262147358336⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541744304,0,true,30116096,30116160⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099481511248,0,false,-30116992,-30116928⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099571925027,0,true,60295552,60295616⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099451330525,0,false,-60298944,-60298880⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624469,0,false,-3328,-3264⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626952,0,false,-832,-768⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1332522708148,0,true,211334724416,211334724480⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨866500547404,0,false,-261858198976,-261858198912⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1332779729103,0,true,211546781056,211546781120⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨866243526449,0,false,-262184383936,-262184383872⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1050022376619,0,false,-50637602816,-50637602752⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1050131373667,0,false,-50523474496,-50523474432⟩
    { al := (868251/4096000), au := (8691/40960), zl := (1999/2000), zu := (3999/4000),
      A := ⟨233069353107,233297254810⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211382806272,211382806336⟩ : DyadicInterval 40),(⟨-261932144320,-261932144256⟩ : DyadicInterval 40),(⟨737232503361,737232522690⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211570831744,211570831808⟩ : DyadicInterval 40),(⟨-262221388672,-262221388608⟩ : DyadicInterval 40),(⟨737183425350,737183444679⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211286649408,211286649472⟩ : DyadicInterval 40),(⟨-261784272256,-261784272192⟩ : DyadicInterval 40),(⟨737257579661,737257598990⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211522715584,211522715648⟩ : DyadicInterval 40),(⟨-262147358400,-262147358336⟩ : DyadicInterval 40),(⟨737195990038,737196009367⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨30116528,60297251⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨30116096,30116160⟩ : DyadicInterval 40),(⟨-30116992,-30116928⟩ : DyadicInterval 40),(⟨762123383175,762123402504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨60295552,60295616⟩ : DyadicInterval 40),(⟨-60298944,-60298880⟩ : DyadicInterval 40),(⟨762123381941,762123401270⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3328,-768⟩ : DyadicInterval 40),(⟨762123384000,762123404544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨233011080372,233268101327⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211334724416,211334724480⟩ : DyadicInterval 40),(⟨-261858198976,-261858198912⟩ : DyadicInterval 40),(⟨737245044311,737245063640⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211546781056,211546781120⟩ : DyadicInterval 40),(⟨-262184383936,-262184383872⟩ : DyadicInterval 40),(⟨737189706252,737189725581⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-50637602816,-50523474432⟩ : DyadicInterval 40),(⟨787385120832,787442204288⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨211382806272,211570831808⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-262221388672,-261932144256⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1386_ok : ecellOkT e1386 = true := by decide +kernel
theorem e1386_pos {a z : ℝ} (ha1 : ((868251/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((8691/40960 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1386 e1386_ok ha1 ha2 hz1 hz2 hz

-- box ['433701/2048000', '868251/4096000', '3999/4000', '1']  interval_lower 801565041/1099511627776
noncomputable def e1387 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1332353079181,0,true,211194748672,211194748736⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨866670176371,0,false,-261642976064,-261642976000⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1332580980884,0,true,211382806272,211382806336⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨866442274668,0,false,-261932144320,-261932144256⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1332294868818,0,true,211146710080,211146710144⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨866728386734,0,false,-261569129280,-261569129216⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541745331,0,true,30117120,30117184⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099481510221,0,false,-30118016,-30117952⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626951,0,false,-832,-768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1332323968246,0,true,211170724864,211170724928⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨866699287306,0,false,-261606044736,-261606044672⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1332580989434,0,true,211382813312,211382813376⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨866442266118,0,false,-261932155200,-261932155136⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1050106668363,0,false,-50549341824,-50549341760⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1050215572595,0,false,-50435319808,-50435319744⟩
    { al := (433701/2048000), au := (868251/4096000), zl := (3999/4000), zu := 1,
      A := ⟨232841451405,233069353108⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211194748672,211194748736⟩ : DyadicInterval 40),(⟨-261642976064,-261642976000⟩ : DyadicInterval 40),(⟨737281531902,737281551231⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211382806272,211382806336⟩ : DyadicInterval 40),(⟨-261932144320,-261932144256⟩ : DyadicInterval 40),(⟨737232503360,737232522690⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211146710080,211146710144⟩ : DyadicInterval 40),(⟨-261569129280,-261569129216⟩ : DyadicInterval 40),(⟨737294046786,737294066116⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211382806272,211382806336⟩ : DyadicInterval 40),(⟨-261932144320,-261932144256⟩ : DyadicInterval 40),(⟨737232503360,737232522690⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,30117555⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨30117120,30117184⟩ : DyadicInterval 40),(⟨-30118016,-30117952⟩ : DyadicInterval 40),(⟨762123383175,762123402504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-832,0⟩ : DyadicInterval 40),(⟨762123383616,762123403296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨232812340470,233069361658⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211170724864,211170724928⟩ : DyadicInterval 40),(⟨-261606044736,-261606044672⟩ : DyadicInterval 40),(⟨737287790993,737287810323⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211382813312,211382813376⟩ : DyadicInterval 40),(⟨-261932155200,-261932155136⟩ : DyadicInterval 40),(⟨737232501541,737232520870⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-50549341824,-50435319744⟩ : DyadicInterval 40),(⟨787341043488,787398073792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨211194748672,211382806336⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-261932144320,-261642976000⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1387_ok : ecellOkT e1387 = true := by decide +kernel
theorem e1387_pos {a z : ℝ} (ha1 : ((433701/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((868251/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1387 e1387_ok ha1 ha2 hz1 hz2 hz

-- box ['868251/4096000', '8691/40960', '3999/4000', '1']  interval_lower 807470605/1099511627776
noncomputable def e1388 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1332580980883,0,true,211382806272,211382806336⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨866442274669,0,false,-261932144320,-261932144256⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1332808882586,0,true,211570831744,211570831808⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨866214372966,0,false,-262221388672,-262221388608⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1332522713544,0,true,211334728896,211334728960⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨866500542008,0,false,-261858205824,-261858205760⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541776787,0,true,30148544,30148608⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099481478765,0,false,-30149440,-30149376⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626949,0,false,-832,-768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1332551841456,0,true,211358763072,211358763136⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨866471414096,0,false,-261895167168,-261895167104⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1332808891139,0,true,211570838784,211570838848⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨866214364413,0,false,-262221399552,-262221399488⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1050010002038,0,false,-50650560704,-50650560640⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1050119024897,0,false,-50536404032,-50536403968⟩
    { al := (868251/4096000), au := (8691/40960), zl := (3999/4000), zu := 1,
      A := ⟨233069353107,233297254810⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211382806272,211382806336⟩ : DyadicInterval 40),(⟨-261932144320,-261932144256⟩ : DyadicInterval 40),(⟨737232503361,737232522690⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211570831744,211570831808⟩ : DyadicInterval 40),(⟨-262221388672,-262221388608⟩ : DyadicInterval 40),(⟨737183425350,737183444679⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211334728896,211334728960⟩ : DyadicInterval 40),(⟨-261858205824,-261858205760⟩ : DyadicInterval 40),(⟨737245043133,737245062463⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211570831744,211570831808⟩ : DyadicInterval 40),(⟨-262221388672,-262221388608⟩ : DyadicInterval 40),(⟨737183425350,737183444679⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,30149011⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨30148544,30148608⟩ : DyadicInterval 40),(⟨-30149440,-30149376⟩ : DyadicInterval 40),(⟨762123383173,762123402502⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-832,0⟩ : DyadicInterval 40),(⟨762123383616,762123403296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨233040213680,233297263363⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211358763072,211358763136⟩ : DyadicInterval 40),(⟨-261895167168,-261895167104⟩ : DyadicInterval 40),(⟨737238774914,737238794243⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211570838784,211570838848⟩ : DyadicInterval 40),(⟨-262221399552,-262221399488⟩ : DyadicInterval 40),(⟨737183423526,737183442855⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-50650560704,-50536403968⟩ : DyadicInterval 40),(⟨787391585600,787448683232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨211382806272,211570831808⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-262221388672,-261932144256⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1388_ok : ecellOkT e1388 = true := by decide +kernel
theorem e1388_pos {a z : ℝ} (ha1 : ((868251/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((8691/40960 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1388 e1388_ok ha1 ha2 hz1 hz2 hz

-- box ['8691/40960', '869949/4096000', '999/1000', '3997/4000']  interval_lower 408335123/549755813888
noncomputable def e1389 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1332808882585,0,true,211570831744,211570831808⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨866214372967,0,false,-262221388672,-262221388608⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1333036784288,0,true,211758825024,211758825088⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨865986471264,0,false,-262510709184,-262510709120⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1332575585330,0,true,211378354432,211378354496⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨866447670222,0,false,-261925297408,-261925297344⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1332861640421,0,true,211614353856,211614353920⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨866161615131,0,false,-262288357824,-262288357760⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099602070695,0,true,90439168,90439232⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099421184857,0,false,-90446656,-90446592⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099632345808,0,true,120711360,120711424⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099390909744,0,false,-120724672,-120724608⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511614522,0,false,-13312,-13248⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620337,0,false,-7488,-7424⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1332692230000,0,true,211474594048,211474594112⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨866331025552,0,false,-262073328064,-262073328000⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1332949221981,0,true,211686599808,211686599872⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨866074033571,0,false,-262399540096,-262399540032⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1049950432594,0,false,-50712940288,-50712940224⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1050059496594,0,false,-50598734016,-50598733952⟩
    { al := (8691/40960), au := (869949/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨233297254809,233525156512⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211570831744,211570831808⟩ : DyadicInterval 40),(⟨-262221388672,-262221388608⟩ : DyadicInterval 40),(⟨737183425350,737183444680⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211758825024,211758825088⟩ : DyadicInterval 40),(⟨-262510709184,-262510709120⟩ : DyadicInterval 40),(⟨737134297920,737134317249⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211378354432,211378354496⟩ : DyadicInterval 40),(⟨-261925297408,-261925297344⟩ : DyadicInterval 40),(⟨737233664657,737233683987⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211614353856,211614353920⟩ : DyadicInterval 40),(⟨-262288357824,-262288357760⟩ : DyadicInterval 40),(⟨737172057077,737172076406⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨90442919,120718032⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨90439168,90439232⟩ : DyadicInterval 40),(⟨-90446656,-90446592⟩ : DyadicInterval 40),(⟨762123379856,762123399185⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨120711360,120711424⟩ : DyadicInterval 40),(⟨-120724672,-120724608⟩ : DyadicInterval 40),(⟨762123376953,762123396283⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-13312,-7424⟩ : DyadicInterval 40),(⟨762123387328,762123409536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨233180602224,233437594205⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211474594048,211474594112⟩ : DyadicInterval 40),(⟨-262073328064,-262073328000⟩ : DyadicInterval 40),(⟨737208552332,737208571662⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211686599808,211686599872⟩ : DyadicInterval 40),(⟨-262399540096,-262399540032⟩ : DyadicInterval 40),(⟨737153179038,737153198368⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-50712940288,-50598733952⟩ : DyadicInterval 40),(⟨787422750592,787479873024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨211570831744,211758825088⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-262510709184,-262221388608⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1389_ok : ecellOkT e1389 = true := by decide +kernel
theorem e1389_pos {a z : ℝ} (ha1 : ((8691/40960 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((869949/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1389 e1389_ok ha1 ha2 hz1 hz2 hz

-- box ['869949/4096000', '435399/2048000', '999/1000', '3997/4000']  interval_lower 822631507/1099511627776
noncomputable def e1390 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1333036784287,0,true,211758825024,211758825088⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨865986471265,0,false,-262510709184,-262510709120⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1333264685990,0,true,211946786240,211946786304⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨865758569562,0,false,-262800105792,-262800105728⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1332803259130,0,true,211566192640,211566192704⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨866219996422,0,false,-262214250688,-262214250624⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1333089371197,0,true,211802198784,211802198848⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨865933884355,0,false,-262577478848,-262577478784⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099602165074,0,true,90533568,90533632⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099421090478,0,false,-90541056,-90540992⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099632471674,0,true,120837248,120837312⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099390783878,0,false,-120850560,-120850496⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511614494,0,false,-13312,-13248⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620321,0,false,-7488,-7424⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1332920017746,0,true,211662509760,211662509824⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨866103237806,0,false,-262362464896,-262362464832⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1333177038233,0,true,211874502848,211874502912⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨865846217319,0,false,-262688798912,-262688798848⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1049853649938,0,false,-50814296064,-50814296000⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1049962832537,0,false,-50699955072,-50699955008⟩
    { al := (869949/4096000), au := (435399/2048000), zl := (999/1000), zu := (3997/4000),
      A := ⟨233525156511,233753058214⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211758825024,211758825088⟩ : DyadicInterval 40),(⟨-262510709184,-262510709120⟩ : DyadicInterval 40),(⟨737134297920,737134317249⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211946786240,211946786304⟩ : DyadicInterval 40),(⟨-262800105792,-262800105728⟩ : DyadicInterval 40),(⟨737085120953,737085140283⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211566192640,211566192704⟩ : DyadicInterval 40),(⟨-262214250688,-262214250624⟩ : DyadicInterval 40),(⟨737184636932,737184656262⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211802198784,211802198848⟩ : DyadicInterval 40),(⟨-262577478848,-262577478784⟩ : DyadicInterval 40),(⟨737122954996,737122974325⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨90537298,120843898⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨90533568,90533632⟩ : DyadicInterval 40),(⟨-90541056,-90540992⟩ : DyadicInterval 40),(⟨762123379840,762123399170⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨120837248,120837312⟩ : DyadicInterval 40),(⟨-120850560,-120850496⟩ : DyadicInterval 40),(⟨762123376926,762123396255⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-13312,-7424⟩ : DyadicInterval 40),(⟨762123387328,762123409536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨233408389970,233665410457⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211662509760,211662509824⟩ : DyadicInterval 40),(⟨-262362464896,-262362464832⟩ : DyadicInterval 40),(⟨737159474779,737159494108⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211874502848,211874502912⟩ : DyadicInterval 40),(⟨-262688798912,-262688798848⟩ : DyadicInterval 40),(⟨737104039543,737104058872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-50814296064,-50699955008⟩ : DyadicInterval 40),(⟨787473361120,787530550912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨211758825024,211946786304⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-262800105792,-262510709120⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1390_ok : ecellOkT e1390 = true := by decide +kernel
theorem e1390_pos {a z : ℝ} (ha1 : ((869949/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((435399/2048000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1390 e1390_ok ha1 ha2 hz1 hz2 hz

-- box ['8691/40960', '869949/4096000', '3997/4000', '1999/2000']  interval_lower 50973783/68719476736
noncomputable def e1391 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1332808882585,0,true,211570831744,211570831808⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨866214372967,0,false,-262221388672,-262221388608⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1333036784288,0,true,211758825024,211758825088⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨865986471264,0,false,-262510709184,-262510709120⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1332633909643,0,true,211426476928,211426476992⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨866389345909,0,false,-261999312768,-261999312704⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1332920021710,0,true,211662513024,211662513088⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨866103233842,0,false,-262362469952,-262362469888⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099571923483,0,true,60294016,60294080⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099451332069,0,false,-60297408,-60297344⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099602167137,0,true,90535616,90535680⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099421088415,0,false,-90543104,-90543040⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620320,0,false,-7488,-7424⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624470,0,false,-3328,-3264⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1332721391317,0,true,211498652736,211498652800⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨866301864235,0,false,-262110339008,-262110338944⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1332978412023,0,true,211710677568,211710677632⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨866044843529,0,false,-262436598528,-262436598464⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1049938037129,0,false,-50725920960,-50725920896⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1050047126959,0,false,-50611686272,-50611686208⟩
    { al := (8691/40960), au := (869949/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨233297254809,233525156512⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211570831744,211570831808⟩ : DyadicInterval 40),(⟨-262221388672,-262221388608⟩ : DyadicInterval 40),(⟨737183425350,737183444680⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211758825024,211758825088⟩ : DyadicInterval 40),(⟨-262510709184,-262510709120⟩ : DyadicInterval 40),(⟨737134297920,737134317249⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211426476928,211426476992⟩ : DyadicInterval 40),(⟨-261999312768,-261999312704⟩ : DyadicInterval 40),(⟨737221109692,737221129021⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211662513024,211662513088⟩ : DyadicInterval 40),(⟨-262362469952,-262362469888⟩ : DyadicInterval 40),(⟨737159473937,737159493267⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨60295707,90539361⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨60294016,60294080⟩ : DyadicInterval 40),(⟨-60297408,-60297344⟩ : DyadicInterval 40),(⟨762123381941,762123401270⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨90535616,90535680⟩ : DyadicInterval 40),(⟨-90543104,-90543040⟩ : DyadicInterval 40),(⟨762123379840,762123399169⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7488,-3264⟩ : DyadicInterval 40),(⟨762123385248,762123406624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨233209763541,233466784247⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211498652736,211498652800⟩ : DyadicInterval 40),(⟨-262110339008,-262110338944⟩ : DyadicInterval 40),(⟨737202272199,737202291528⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211710677568,211710677632⟩ : DyadicInterval 40),(⟨-262436598528,-262436598464⟩ : DyadicInterval 40),(⟨737146885578,737146904908⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-50725920960,-50611686208⟩ : DyadicInterval 40),(⟨787429226720,787486363360⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨211570831744,211758825088⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-262510709184,-262221388608⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1391_ok : ecellOkT e1391 = true := by decide +kernel
theorem e1391_pos {a z : ℝ} (ha1 : ((8691/40960 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((869949/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1391 e1391_ok ha1 ha2 hz1 hz2 hz

-- box ['869949/4096000', '435399/2048000', '3997/4000', '1999/2000']  interval_lower 821537769/1099511627776
noncomputable def e1392 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1333036784287,0,true,211758825024,211758825088⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨865986471265,0,false,-262510709184,-262510709120⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1333264685990,0,true,211946786240,211946786304⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨865758569562,0,false,-262800105792,-262800105728⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1332861640419,0,true,211614353856,211614353920⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨866161615133,0,false,-262288357824,-262288357760⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1333147809462,0,true,211850396672,211850396736⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨865875446090,0,false,-262651682816,-262651682752⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099571986405,0,true,60356928,60356992⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099451269147,0,false,-60360320,-60360256⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099602261539,0,true,90630016,90630080⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099420994013,0,false,-90637504,-90637440⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620304,0,false,-7488,-7424⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624463,0,false,-3328,-3264⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1332949207543,0,true,211686587840,211686587904⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨866074048009,0,false,-262399521792,-262399521728⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1333206256758,0,true,211898599936,211898600000⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨865816998794,0,false,-262725903296,-262725903232⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1049841230269,0,false,-50827303296,-50827303232⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1049950438726,0,false,-50712933888,-50712933824⟩
    { al := (869949/4096000), au := (435399/2048000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨233525156511,233753058214⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211758825024,211758825088⟩ : DyadicInterval 40),(⟨-262510709184,-262510709120⟩ : DyadicInterval 40),(⟨737134297920,737134317249⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211946786240,211946786304⟩ : DyadicInterval 40),(⟨-262800105792,-262800105728⟩ : DyadicInterval 40),(⟨737085120953,737085140283⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211614353856,211614353920⟩ : DyadicInterval 40),(⟨-262288357824,-262288357760⟩ : DyadicInterval 40),(⟨737172057077,737172076407⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211850396672,211850396736⟩ : DyadicInterval 40),(⟨-262651682816,-262651682752⟩ : DyadicInterval 40),(⟨737110346925,737110366255⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨60358629,90633763⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨60356928,60356992⟩ : DyadicInterval 40),(⟨-60360320,-60360256⟩ : DyadicInterval 40),(⟨762123381934,762123401263⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨90630016,90630080⟩ : DyadicInterval 40),(⟨-90637504,-90637440⟩ : DyadicInterval 40),(⟨762123379824,762123399154⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7488,-3264⟩ : DyadicInterval 40),(⟨762123385248,762123406624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨233437579767,233694628982⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211686587840,211686587904⟩ : DyadicInterval 40),(⟨-262399521792,-262399521728⟩ : DyadicInterval 40),(⟨737153182197,737153201526⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211898599936,211898600000⟩ : DyadicInterval 40),(⟨-262725903296,-262725903232⟩ : DyadicInterval 40),(⟨737097733642,737097752971⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-50827303296,-50712933824⟩ : DyadicInterval 40),(⟨787479850528,787537054528⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨211758825024,211946786304⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-262800105792,-262510709120⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1392_ok : ecellOkT e1392 = true := by decide +kernel
theorem e1392_pos {a z : ℝ} (ha1 : ((869949/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((435399/2048000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1392 e1392_ok ha1 ha2 hz1 hz2 hz

-- box ['435399/2048000', '871647/4096000', '999/1000', '3997/4000']  interval_lower 414307649/549755813888
noncomputable def e1393 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1333264685989,0,true,211946786240,211946786304⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨865758569563,0,false,-262800105792,-262800105728⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1333492587693,0,true,212134715264,212134715328⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨865530667859,0,false,-263089578560,-263089578496⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1333030932930,0,true,211753998720,211753998784⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨865992322622,0,false,-262503279936,-262503279872⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1333317101974,0,true,211990011584,211990011648⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨865706153578,0,false,-262866675968,-262866675904⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099602259471,0,true,90627904,90627968⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099420996081,0,false,-90635456,-90635392⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099632597564,0,true,120963072,120963136⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099390657988,0,false,-120976448,-120976384⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511614466,0,false,-13312,-13248⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620306,0,false,-7488,-7424⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1333147805497,0,true,211850393408,211850393472⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨865875450055,0,false,-262651677824,-262651677760⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1333404854475,0,true,212062373760,212062373824⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨865618401077,0,false,-262978133888,-262978133824⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1049756772880,0,false,-50915760064,-50915760000⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1049866074095,0,false,-50801284352,-50801284288⟩
    { al := (435399/2048000), au := (871647/4096000), zl := (999/1000), zu := (3997/4000),
      A := ⟨233753058213,233980959917⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211946786240,211946786304⟩ : DyadicInterval 40),(⟨-262800105792,-262800105728⟩ : DyadicInterval 40),(⟨737085120953,737085140283⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212134715264,212134715328⟩ : DyadicInterval 40),(⟨-263089578560,-263089578496⟩ : DyadicInterval 40),(⟨737035894540,737035913869⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211753998720,211753998784⟩ : DyadicInterval 40),(⟨-262503279936,-262503279872⟩ : DyadicInterval 40),(⟨737135559871,737135579201⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211990011584,211990011648⟩ : DyadicInterval 40),(⟨-262866675968,-262866675904⟩ : DyadicInterval 40),(⟨737073803563,737073822892⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨90631695,120969788⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨90627904,90627968⟩ : DyadicInterval 40),(⟨-90635456,-90635392⟩ : DyadicInterval 40),(⟨762123379857,762123399186⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨120963072,120963136⟩ : DyadicInterval 40),(⟨-120976448,-120976384⟩ : DyadicInterval 40),(⟨762123376930,762123396260⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-13312,-7424⟩ : DyadicInterval 40),(⟨762123387328,762123409536⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨233636177721,233893226699⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211850393408,211850393472⟩ : DyadicInterval 40),(⟨-262651677824,-262651677760⟩ : DyadicInterval 40),(⟨737110347794,737110367123⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212062373760,212062373824⟩ : DyadicInterval 40),(⟨-262978133888,-262978133824⟩ : DyadicInterval 40),(⟨737054850642,737054869972⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-50915760064,-50801284288⟩ : DyadicInterval 40),(⟨787524025760,787581282912⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨211946786240,212134715328⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-263089578560,-262800105728⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1393_ok : ecellOkT e1393 = true := by decide +kernel
theorem e1393_pos {a z : ℝ} (ha1 : ((435399/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((871647/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1393 e1393_ok ha1 ha2 hz1 hz2 hz

-- box ['871647/4096000', '54531/256000', '999/1000', '3997/4000']  interval_lower 417310535/549755813888
noncomputable def e1394 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1333492587692,0,true,212134715264,212134715328⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨865530667860,0,false,-263089578560,-263089578496⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1333720489395,0,true,212322612160,212322612224⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨865302766157,0,false,-263379127616,-263379127552⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1333258606732,0,true,211941772800,211941772864⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨865764648820,0,false,-262792385152,-262792385088⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1333544832749,0,true,212177792320,212177792384⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨865478422803,0,false,-263155949184,-263155949120⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099602353888,0,true,90722368,90722432⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099420901664,0,false,-90729856,-90729792⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099632723481,0,true,121089024,121089088⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099390532071,0,false,-121102400,-121102336⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511614439,0,false,-13376,-13312⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620290,0,false,-7488,-7424⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1333375593255,0,true,212038244992,212038245056⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨865647662297,0,false,-262940966784,-262940966720⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1333632670711,0,true,212250212608,212250212672⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨865390584841,0,false,-263267544960,-263267544896⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1049659801419,0,false,-51017332352,-51017332288⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1049769221268,0,false,-50902721792,-50902721728⟩
    { al := (871647/4096000), au := (54531/256000), zl := (999/1000), zu := (3997/4000),
      A := ⟨233980959916,234208861619⟩, Z := ⟨1098412116148,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212134715264,212134715328⟩ : DyadicInterval 40),(⟨-263089578560,-263089578496⟩ : DyadicInterval 40),(⟨737035894540,737035913870⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212322612160,212322612224⟩ : DyadicInterval 40),(⟨-263379127616,-263379127552⟩ : DyadicInterval 40),(⟨736986618678,736986638008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211941772800,211941772864⟩ : DyadicInterval 40),(⟨-262792385152,-262792385088⟩ : DyadicInterval 40),(⟨737086433383,737086452712⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212177792320,212177792384⟩ : DyadicInterval 40),(⟨-263155949184,-263155949120⟩ : DyadicInterval 40),(⟨737024602726,737024622055⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨90726112,121095705⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨90722368,90722432⟩ : DyadicInterval 40),(⟨-90729856,-90729792⟩ : DyadicInterval 40),(⟨762123379809,762123399139⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨121089024,121089088⟩ : DyadicInterval 40),(⟨-121102400,-121102336⟩ : DyadicInterval 40),(⟨762123376902,762123396232⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-13376,-7424⟩ : DyadicInterval 40),(⟨762123387328,762123409568⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨233863965479,234121042935⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212038244992,212038245056⟩ : DyadicInterval 40),(⟨-262940966784,-262940966720⟩ : DyadicInterval 40),(⟨737061171339,737061190669⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212250212608,212250212672⟩ : DyadicInterval 40),(⟨-263267544960,-263267544896⟩ : DyadicInterval 40),(⟨737005612260,737005631589⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-51017332352,-50902721728⟩ : DyadicInterval 40),(⟨787574744480,787632069056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨212134715264,212322612224⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-263379127616,-263089578496⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1394_ok : ecellOkT e1394 = true := by decide +kernel
theorem e1394_pos {a z : ℝ} (ha1 : ((871647/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((54531/256000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1394 e1394_ok ha1 ha2 hz1 hz2 hz

-- box ['435399/2048000', '871647/4096000', '3997/4000', '1999/2000']  interval_lower 827517571/1099511627776
noncomputable def e1395 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1333264685989,0,true,211946786240,211946786304⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨865758569563,0,false,-262800105792,-262800105728⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1333492587693,0,true,212134715264,212134715328⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨865530667859,0,false,-263089578560,-263089578496⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1333089371195,0,true,211802198784,211802198848⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨865933884357,0,false,-262577478848,-262577478784⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1333375597214,0,true,212038248256,212038248320⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨865647658338,0,false,-262940971840,-262940971776⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099572049337,0,true,60419840,60419904⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099451206215,0,false,-60423232,-60423168⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099602355960,0,true,90724416,90724480⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099420899592,0,false,-90731968,-90731904⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620289,0,false,-7488,-7424⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624456,0,false,-3328,-3264⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1333177023790,0,true,211874490880,211874490944⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨865846231762,0,false,-262688780608,-262688780544⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1333434101488,0,true,212086490240,212086490304⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨865589154064,0,false,-263015284160,-263015284096⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1049744328981,0,false,-50928793856,-50928793792⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1049853656078,0,false,-50814289664,-50814289600⟩
    { al := (435399/2048000), au := (871647/4096000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨233753058213,233980959917⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211946786240,211946786304⟩ : DyadicInterval 40),(⟨-262800105792,-262800105728⟩ : DyadicInterval 40),(⟨737085120953,737085140283⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212134715264,212134715328⟩ : DyadicInterval 40),(⟨-263089578560,-263089578496⟩ : DyadicInterval 40),(⟨737035894540,737035913869⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211802198784,211802198848⟩ : DyadicInterval 40),(⟨-262577478848,-262577478784⟩ : DyadicInterval 40),(⟨737122954996,737122974326⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212038248256,212038248320⟩ : DyadicInterval 40),(⟨-262940971840,-262940971776⟩ : DyadicInterval 40),(⟨737061170495,737061189825⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨60421561,90728184⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨60419840,60419904⟩ : DyadicInterval 40),(⟨-60423232,-60423168⟩ : DyadicInterval 40),(⟨762123381927,762123401256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨90724416,90724480⟩ : DyadicInterval 40),(⟨-90731968,-90731904⟩ : DyadicInterval 40),(⟨762123379841,762123399170⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7488,-3264⟩ : DyadicInterval 40),(⟨762123385248,762123406624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨233665396014,233922473712⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211874490880,211874490944⟩ : DyadicInterval 40),(⟨-262688780608,-262688780544⟩ : DyadicInterval 40),(⟨737104042708,737104062038⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212086490240,212086490304⟩ : DyadicInterval 40),(⟨-263015284160,-263015284096⟩ : DyadicInterval 40),(⟨737048532210,737048551540⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-50928793856,-50814289600⟩ : DyadicInterval 40),(⟨787530528416,787587799808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨211946786240,212134715328⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-263089578560,-262800105728⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1395_ok : ecellOkT e1395 = true := by decide +kernel
theorem e1395_pos {a z : ℝ} (ha1 : ((435399/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((871647/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1395 e1395_ok ha1 ha2 hz1 hz2 hz

-- box ['871647/4096000', '54531/256000', '3997/4000', '1999/2000']  interval_lower 833519401/1099511627776
noncomputable def e1396 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1333492587692,0,true,212134715264,212134715328⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨865530667860,0,false,-263089578560,-263089578496⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1333720489395,0,true,212322612160,212322612224⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨865302766157,0,false,-263379127616,-263379127552⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1333317101972,0,true,211990011584,211990011648⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨865706153580,0,false,-262866675968,-262866675904⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1333603384965,0,true,212226067712,212226067776⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨865419870587,0,false,-263230336960,-263230336896⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099572112283,0,true,60482816,60482880⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099451143269,0,false,-60486208,-60486144⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099602450400,0,true,90818816,90818880⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099420805152,0,false,-90826432,-90826368⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511620273,0,false,-7552,-7488⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624449,0,false,-3328,-3264⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1333404840027,0,true,212062361856,212062361920⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨865618415525,0,false,-262978115520,-262978115456⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1333661946211,0,true,212274348480,212274348544⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨865361309341,0,false,-263304741248,-263304741184⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1049647333267,0,false,-51030392768,-51030392704⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1049756779028,0,false,-50915753664,-50915753600⟩
    { al := (871647/4096000), au := (54531/256000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨233980959916,234208861619⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212134715264,212134715328⟩ : DyadicInterval 40),(⟨-263089578560,-263089578496⟩ : DyadicInterval 40),(⟨737035894540,737035913870⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212322612160,212322612224⟩ : DyadicInterval 40),(⟨-263379127616,-263379127552⟩ : DyadicInterval 40),(⟨736986618678,736986638008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211990011584,211990011648⟩ : DyadicInterval 40),(⟨-262866675968,-262866675904⟩ : DyadicInterval 40),(⟨737073803563,737073822893⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212226067712,212226067776⟩ : DyadicInterval 40),(⟨-263230336960,-263230336896⟩ : DyadicInterval 40),(⟨737011944646,737011963976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨60484507,90822624⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨60482816,60482880⟩ : DyadicInterval 40),(⟨-60486208,-60486144⟩ : DyadicInterval 40),(⟨762123381920,762123401249⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨90818816,90818880⟩ : DyadicInterval 40),(⟨-90826432,-90826368⟩ : DyadicInterval 40),(⟨762123379857,762123399187⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-7552,-3264⟩ : DyadicInterval 40),(⟨762123385248,762123406656⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨233893212251,234150318435⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212062361856,212062361920⟩ : DyadicInterval 40),(⟨-262978115520,-262978115456⟩ : DyadicInterval 40),(⟨737054853751,737054873081⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212274348480,212274348544⟩ : DyadicInterval 40),(⟨-263304741248,-263304741184⟩ : DyadicInterval 40),(⟨736999281320,736999300649⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-51030392768,-50915753600⟩ : DyadicInterval 40),(⟨787581260416,787638599264⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨212134715264,212322612224⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-263379127616,-263089578496⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1396_ok : ecellOkT e1396 = true := by decide +kernel
theorem e1396_pos {a z : ℝ} (ha1 : ((871647/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((54531/256000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1396 e1396_ok ha1 ha2 hz1 hz2 hz

-- box ['8691/40960', '869949/4096000', '1999/2000', '3999/4000']  interval_lower 203622441/274877906944
noncomputable def e1397 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1332808882585,0,true,211570831744,211570831808⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨866214372967,0,false,-262221388672,-262221388608⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1333036784288,0,true,211758825024,211758825088⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨865986471264,0,false,-262510709184,-262510709120⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1332692233957,0,true,211474597312,211474597376⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨866331021595,0,false,-262073333120,-262073333056⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1332978403000,0,true,211710670080,211710670144⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨866044852552,0,false,-262436587072,-262436587008⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541775758,0,true,30147520,30147584⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099481479794,0,false,-30148416,-30148352⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099571987952,0,true,60358464,60358528⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099451267600,0,false,-60361856,-60361792⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624462,0,false,-3328,-3264⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626950,0,false,-832,-768⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1332750552872,0,true,211522711104,211522711168⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨866272702680,0,false,-262147351552,-262147351488⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1333007602307,0,true,211734755008,211734755072⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨866015653245,0,false,-262473658496,-262473658432⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1049925640011,0,false,-50738903488,-50738903424⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1050034755676,0,false,-50624640384,-50624640320⟩
    { al := (8691/40960), au := (869949/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨233297254809,233525156512⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211570831744,211570831808⟩ : DyadicInterval 40),(⟨-262221388672,-262221388608⟩ : DyadicInterval 40),(⟨737183425350,737183444680⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211758825024,211758825088⟩ : DyadicInterval 40),(⟨-262510709184,-262510709120⟩ : DyadicInterval 40),(⟨737134297920,737134317249⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211474597312,211474597376⟩ : DyadicInterval 40),(⟨-262073333120,-262073333056⟩ : DyadicInterval 40),(⟨737208551494,737208570823⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211710670080,211710670144⟩ : DyadicInterval 40),(⟨-262436587072,-262436587008⟩ : DyadicInterval 40),(⟨737146887551,737146906881⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨30147982,60360176⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨30147520,30147584⟩ : DyadicInterval 40),(⟨-30148416,-30148352⟩ : DyadicInterval 40),(⟨762123383173,762123402502⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨60358464,60358528⟩ : DyadicInterval 40),(⟨-60361856,-60361792⟩ : DyadicInterval 40),(⟨762123381934,762123401263⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3328,-768⟩ : DyadicInterval 40),(⟨762123384000,762123404544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨233238925096,233495974531⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211522711104,211522711168⟩ : DyadicInterval 40),(⟨-262147351552,-262147351488⟩ : DyadicInterval 40),(⟨737195991219,737196010548⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211734755008,211734755072⟩ : DyadicInterval 40),(⟨-262473658496,-262473658432⟩ : DyadicInterval 40),(⟨737140591242,737140610572⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-50738903488,-50624640320⟩ : DyadicInterval 40),(⟨787435703776,787492854624⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨211570831744,211758825088⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-262510709184,-262221388608⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1397_ok : ecellOkT e1397 = true := by decide +kernel
theorem e1397_pos {a z : ℝ} (ha1 : ((8691/40960 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((869949/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1397 e1397_ok ha1 ha2 hz1 hz2 hz

-- box ['869949/4096000', '435399/2048000', '1999/2000', '3999/4000']  interval_lower 820443243/1099511627776
noncomputable def e1398 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1333036784287,0,true,211758825024,211758825088⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨865986471265,0,false,-262510709184,-262510709120⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1333264685990,0,true,211946786240,211946786304⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨865758569562,0,false,-262800105792,-262800105728⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1332920021708,0,true,211662513024,211662513088⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨866103233844,0,false,-262362469952,-262362469888⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1333206247726,0,true,211898592512,211898592576⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨865817007826,0,false,-262725891776,-262725891712⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541807219,0,true,30179008,30179072⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099481448333,0,false,-30179904,-30179840⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099572050887,0,true,60421440,60421504⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099451204665,0,false,-60424832,-60424768⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624455,0,false,-3328,-3264⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626948,0,false,-832,-768⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1332978397585,0,true,211710665664,211710665728⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨866044857967,0,false,-262436580160,-262436580096⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1333235475530,0,true,211922696768,211922696832⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨865787780022,0,false,-262763009152,-262763009088⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1049828808941,0,false,-50840312384,-50840312320⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1049938043261,0,false,-50725914496,-50725914432⟩
    { al := (869949/4096000), au := (435399/2048000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨233525156511,233753058214⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211758825024,211758825088⟩ : DyadicInterval 40),(⟨-262510709184,-262510709120⟩ : DyadicInterval 40),(⟨737134297920,737134317249⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211946786240,211946786304⟩ : DyadicInterval 40),(⟨-262800105792,-262800105728⟩ : DyadicInterval 40),(⟨737085120953,737085140283⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211662513024,211662513088⟩ : DyadicInterval 40),(⟨-262362469952,-262362469888⟩ : DyadicInterval 40),(⟨737159473937,737159493267⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211898592512,211898592576⟩ : DyadicInterval 40),(⟨-262725891776,-262725891712⟩ : DyadicInterval 40),(⟨737097735556,737097754886⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨30179443,60423111⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨30179008,30179072⟩ : DyadicInterval 40),(⟨-30179904,-30179840⟩ : DyadicInterval 40),(⟨762123383171,762123402500⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨60421440,60421504⟩ : DyadicInterval 40),(⟨-60424832,-60424768⟩ : DyadicInterval 40),(⟨762123381927,762123401256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3328,-768⟩ : DyadicInterval 40),(⟨762123384000,762123404544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨233466769809,233723847754⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211710665664,211710665728⟩ : DyadicInterval 40),(⟨-262436580160,-262436580096⟩ : DyadicInterval 40),(⟨737146888674,737146908003⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211922696768,211922696832⟩ : DyadicInterval 40),(⟨-262763009152,-262763009088⟩ : DyadicInterval 40),(⟨737091426797,737091446126⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-50840312384,-50725914432⟩ : DyadicInterval 40),(⟨787486340832,787543559072⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨211758825024,211946786304⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-262800105792,-262510709120⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1398_ok : ecellOkT e1398 = true := by decide +kernel
theorem e1398_pos {a z : ℝ} (ha1 : ((869949/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((435399/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1398 e1398_ok ha1 ha2 hz1 hz2 hz

-- box ['8691/40960', '869949/4096000', '3999/4000', '1']  interval_lower 813398181/1099511627776
noncomputable def e1399 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1332808882585,0,true,211570831744,211570831808⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨866214372967,0,false,-262221388672,-262221388608⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1333036784288,0,true,211758825024,211758825088⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨865986471264,0,false,-262510709184,-262510709120⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1332750558271,0,true,211522715584,211522715648⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨866272697281,0,false,-262147358400,-262147358336⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541808250,0,true,30180032,30180096⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099481447302,0,false,-30180928,-30180864⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626947,0,false,-832,-768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1332779714669,0,true,211546769152,211546769216⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨866243540883,0,false,-262184365632,-262184365568⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1333036792830,0,true,211758832064,211758832128⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨865986462722,0,false,-262510720000,-262510719936⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1049913241241,0,false,-50751887872,-50751887808⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1050022382744,0,false,-50637596416,-50637596352⟩
    { al := (8691/40960), au := (869949/4096000), zl := (3999/4000), zu := 1,
      A := ⟨233297254809,233525156512⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211570831744,211570831808⟩ : DyadicInterval 40),(⟨-262221388672,-262221388608⟩ : DyadicInterval 40),(⟨737183425350,737183444680⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211758825024,211758825088⟩ : DyadicInterval 40),(⟨-262510709184,-262510709120⟩ : DyadicInterval 40),(⟨737134297920,737134317249⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211522715584,211522715648⟩ : DyadicInterval 40),(⟨-262147358400,-262147358336⟩ : DyadicInterval 40),(⟨737195990038,737196009368⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211758825024,211758825088⟩ : DyadicInterval 40),(⟨-262510709184,-262510709120⟩ : DyadicInterval 40),(⟨737134297920,737134317249⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,30180474⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨30180032,30180096⟩ : DyadicInterval 40),(⟨-30180928,-30180864⟩ : DyadicInterval 40),(⟨762123383171,762123402500⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-832,0⟩ : DyadicInterval 40),(⟨762123383616,762123403296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨233268086893,233525165054⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211546769152,211546769216⟩ : DyadicInterval 40),(⟨-262184365632,-262184365568⟩ : DyadicInterval 40),(⟨737189709366,737189728695⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211758832064,211758832128⟩ : DyadicInterval 40),(⟨-262510720000,-262510719936⟩ : DyadicInterval 40),(⟨737134296069,737134315399⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-50751887872,-50637596352⟩ : DyadicInterval 40),(⟨787442181792,787499346816⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨211570831744,211758825088⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-262510709184,-262221388608⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1399_ok : ecellOkT e1399 = true := by decide +kernel
theorem e1399_pos {a z : ℝ} (ha1 : ((8691/40960 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((869949/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1399 e1399_ok ha1 ha2 hz1 hz2 hz

-- box ['869949/4096000', '435399/2048000', '3999/4000', '1']  interval_lower 409673797/549755813888
noncomputable def e1400 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1333036784287,0,true,211758825024,211758825088⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨865986471265,0,false,-262510709184,-262510709120⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1333264685990,0,true,211946786240,211946786304⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨865758569562,0,false,-262800105792,-262800105728⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1332978402997,0,true,211710670080,211710670144⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨866044852555,0,false,-262436587072,-262436587008⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541839719,0,true,30211520,30211584⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099481415833,0,false,-30212416,-30212352⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626945,0,false,-832,-768⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1333007587868,0,true,211734743104,211734743168⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨866015667684,0,false,-262473640128,-262473640064⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1333264694542,0,true,211946793280,211946793344⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨865758561010,0,false,-262800116608,-262800116544⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1049816385959,0,false,-50853323328,-50853323264⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1049925646144,0,false,-50738897024,-50738896960⟩
    { al := (869949/4096000), au := (435399/2048000), zl := (3999/4000), zu := 1,
      A := ⟨233525156511,233753058214⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211758825024,211758825088⟩ : DyadicInterval 40),(⟨-262510709184,-262510709120⟩ : DyadicInterval 40),(⟨737134297920,737134317249⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211946786240,211946786304⟩ : DyadicInterval 40),(⟨-262800105792,-262800105728⟩ : DyadicInterval 40),(⟨737085120953,737085140283⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211710670080,211710670144⟩ : DyadicInterval 40),(⟨-262436587072,-262436587008⟩ : DyadicInterval 40),(⟨737146887552,737146906881⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211946786240,211946786304⟩ : DyadicInterval 40),(⟨-262800105792,-262800105728⟩ : DyadicInterval 40),(⟨737085120953,737085140283⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,30211943⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨30211520,30211584⟩ : DyadicInterval 40),(⟨-30212416,-30212352⟩ : DyadicInterval 40),(⟨762123383169,762123402498⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-832,0⟩ : DyadicInterval 40),(⟨762123383616,762123403296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨233495960092,233753066766⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211734743104,211734743168⟩ : DyadicInterval 40),(⟨-262473640128,-262473640064⟩ : DyadicInterval 40),(⟨737140594338,737140613668⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211946793280,211946793344⟩ : DyadicInterval 40),(⟨-262800116608,-262800116544⟩ : DyadicInterval 40),(⟨737085119097,737085138427⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-50853323328,-50738896960⟩ : DyadicInterval 40),(⟨787492832096,787550064544⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨211758825024,211946786304⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-262800105792,-262510709120⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1400_ok : ecellOkT e1400 = true := by decide +kernel
theorem e1400_pos {a z : ℝ} (ha1 : ((869949/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((435399/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1400 e1400_ok ha1 ha2 hz1 hz2 hz

-- box ['435399/2048000', '871647/4096000', '1999/2000', '3999/4000']  interval_lower 826418559/1099511627776
noncomputable def e1401 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1333264685989,0,true,211946786240,211946786304⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨865758569563,0,false,-262800105792,-262800105728⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1333492587693,0,true,212134715264,212134715328⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨865530667859,0,false,-263089578560,-263089578496⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1333147809459,0,true,211850396672,211850396736⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨865875446093,0,false,-262651682816,-262651682752⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1333434092454,0,true,212086482816,212086482880⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨865589163098,0,false,-263015272704,-263015272640⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541838687,0,true,30210432,30210496⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099481416865,0,false,-30211328,-30211264⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099572113836,0,true,60484352,60484416⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099451141716,0,false,-60487744,-60487680⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624448,0,false,-3392,-3328⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626946,0,false,-832,-768⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1333206242313,0,true,211898588032,211898588096⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨865817013239,0,false,-262725884928,-262725884864⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1333463348745,0,true,212110606464,212110606528⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨865559906807,0,false,-263052436032,-263052435968⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1049731883422,0,false,-50941829504,-50941829440⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1049841236410,0,false,-50827296832,-50827296768⟩
    { al := (435399/2048000), au := (871647/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨233753058213,233980959917⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211946786240,211946786304⟩ : DyadicInterval 40),(⟨-262800105792,-262800105728⟩ : DyadicInterval 40),(⟨737085120953,737085140283⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212134715264,212134715328⟩ : DyadicInterval 40),(⟨-263089578560,-263089578496⟩ : DyadicInterval 40),(⟨737035894540,737035913869⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211850396672,211850396736⟩ : DyadicInterval 40),(⟨-262651682816,-262651682752⟩ : DyadicInterval 40),(⟨737110346926,737110366256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212086482816,212086482880⟩ : DyadicInterval 40),(⟨-263015272704,-263015272640⟩ : DyadicInterval 40),(⟨737048534154,737048553484⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨30210911,60486060⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨30210432,30210496⟩ : DyadicInterval 40),(⟨-30211328,-30211264⟩ : DyadicInterval 40),(⟨762123383169,762123402498⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨60484352,60484416⟩ : DyadicInterval 40),(⟨-60487744,-60487680⟩ : DyadicInterval 40),(⟨762123381920,762123401249⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3392,-768⟩ : DyadicInterval 40),(⟨762123384000,762123404576⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨233694614537,233951720969⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211898588032,211898588096⟩ : DyadicInterval 40),(⟨-262725884928,-262725884864⟩ : DyadicInterval 40),(⟨737097736745,737097756074⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212110606464,212110606528⟩ : DyadicInterval 40),(⟨-263052436032,-263052435968⟩ : DyadicInterval 40),(⟨737042212880,737042232209⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-50941829504,-50827296768⟩ : DyadicInterval 40),(⟨787537032000,787594317632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨211946786240,212134715328⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-263089578560,-262800105728⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1401_ok : ecellOkT e1401 = true := by decide +kernel
theorem e1401_pos {a z : ℝ} (ha1 : ((435399/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((871647/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1401 e1401_ok ha1 ha2 hz1 hz2 hz

-- box ['871647/4096000', '54531/256000', '1999/2000', '3999/4000']  interval_lower 26013009/34359738368
noncomputable def e1402 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1333492587692,0,true,212134715264,212134715328⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨865530667860,0,false,-263089578560,-263089578496⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1333720489395,0,true,212322612160,212322612224⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨865302766157,0,false,-263379127616,-263379127552⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1333375597212,0,true,212038248256,212038248320⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨865647658340,0,false,-262940971840,-262940971776⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1333661937180,0,true,212274340992,212274341056⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨865361318372,0,false,-263304729728,-263304729664⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541870160,0,true,30241920,30241984⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099481385392,0,false,-30242816,-30242752⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099572176798,0,true,60547328,60547392⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099451078754,0,false,-60550720,-60550656⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624441,0,false,-3392,-3328⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626945,0,false,-832,-768⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1333434087039,0,true,212086478336,212086478400⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨865589168513,0,false,-263015265792,-263015265728⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1333691221956,0,true,212298484032,212298484096⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨865332033596,0,false,-263341939072,-263341939008⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1049634863451,0,false,-51043455040,-51043454976⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1049744335130,0,false,-50928787456,-50928787392⟩
    { al := (871647/4096000), au := (54531/256000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨233980959916,234208861619⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212134715264,212134715328⟩ : DyadicInterval 40),(⟨-263089578560,-263089578496⟩ : DyadicInterval 40),(⟨737035894540,737035913870⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212322612160,212322612224⟩ : DyadicInterval 40),(⟨-263379127616,-263379127552⟩ : DyadicInterval 40),(⟨736986618678,736986638008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212038248256,212038248320⟩ : DyadicInterval 40),(⟨-262940971840,-262940971776⟩ : DyadicInterval 40),(⟨737061170496,737061189825⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212274340992,212274341056⟩ : DyadicInterval 40),(⟨-263304729728,-263304729664⟩ : DyadicInterval 40),(⟨736999283281,736999302610⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨30242384,60549022⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨30241920,30241984⟩ : DyadicInterval 40),(⟨-30242816,-30242752⟩ : DyadicInterval 40),(⟨762123383168,762123402497⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨60547328,60547392⟩ : DyadicInterval 40),(⟨-60550720,-60550656⟩ : DyadicInterval 40),(⟨762123381913,762123401242⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3392,-768⟩ : DyadicInterval 40),(⟨762123384000,762123404576⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨233922459263,234179594180⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212086478336,212086478400⟩ : DyadicInterval 40),(⟨-263015265792,-263015265728⟩ : DyadicInterval 40),(⟨737048535320,737048554650⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212298484032,212298484096⟩ : DyadicInterval 40),(⟨-263341939072,-263341939008⟩ : DyadicInterval 40),(⟨736992949491,736992968821⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-51043455040,-50928787392⟩ : DyadicInterval 40),(⟨787587777312,787645130400⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨212134715264,212322612224⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-263379127616,-263089578496⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1402_ok : ecellOkT e1402 = true := by decide +kernel
theorem e1402_pos {a z : ℝ} (ha1 : ((871647/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((54531/256000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1402 e1402_ok ha1 ha2 hz1 hz2 hz

-- box ['435399/2048000', '871647/4096000', '3999/4000', '1']  interval_lower 825318849/1099511627776
noncomputable def e1403 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1333264685989,0,true,211946786240,211946786304⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨865758569563,0,false,-262800105792,-262800105728⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1333492587693,0,true,212134715264,212134715328⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨865530667859,0,false,-263089578560,-263089578496⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1333206247724,0,true,211898592512,211898592576⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨865817007828,0,false,-262725891776,-262725891712⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541871194,0,true,30242944,30243008⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099481384358,0,false,-30243840,-30243776⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626944,0,false,-896,-832⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1333235461086,0,true,211922684864,211922684928⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨865787794466,0,false,-262762990848,-262762990784⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1333492596245,0,true,212134722304,212134722368⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨865530659307,0,false,-263089589440,-263089589376⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1049719436204,0,false,-50954867072,-50954867008⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1049828815083,0,false,-50840305920,-50840305856⟩
    { al := (435399/2048000), au := (871647/4096000), zl := (3999/4000), zu := 1,
      A := ⟨233753058213,233980959917⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211946786240,211946786304⟩ : DyadicInterval 40),(⟨-262800105792,-262800105728⟩ : DyadicInterval 40),(⟨737085120953,737085140283⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212134715264,212134715328⟩ : DyadicInterval 40),(⟨-263089578560,-263089578496⟩ : DyadicInterval 40),(⟨737035894540,737035913869⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211898592512,211898592576⟩ : DyadicInterval 40),(⟨-262725891776,-262725891712⟩ : DyadicInterval 40),(⟨737097735557,737097754886⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212134715264,212134715328⟩ : DyadicInterval 40),(⟨-263089578560,-263089578496⟩ : DyadicInterval 40),(⟨737035894540,737035913869⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,30243418⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨30242944,30243008⟩ : DyadicInterval 40),(⟨-30243840,-30243776⟩ : DyadicInterval 40),(⟨762123383168,762123402497⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-896,0⟩ : DyadicInterval 40),(⟨762123383616,762123403328⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨233723833310,233980968469⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨211922684864,211922684928⟩ : DyadicInterval 40),(⟨-262762990848,-262762990784⟩ : DyadicInterval 40),(⟨737091429925,737091449255⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212134722304,212134722368⟩ : DyadicInterval 40),(⟨-263089589440,-263089589376⟩ : DyadicInterval 40),(⟨737035892705,737035912035⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-50954867072,-50840305856⟩ : DyadicInterval 40),(⟨787543536544,787600836416⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨211946786240,212134715328⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-263089578560,-262800105728⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1403_ok : ecellOkT e1403 = true := by decide +kernel
theorem e1403_pos {a z : ℝ} (ha1 : ((435399/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((871647/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1403 e1403_ok ha1 ha2 hz1 hz2 hz

-- box ['871647/4096000', '54531/256000', '3999/4000', '1']  interval_lower 831312591/1099511627776
noncomputable def e1404 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1333492587692,0,true,212134715264,212134715328⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨865530667860,0,false,-263089578560,-263089578496⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1333720489395,0,true,212322612160,212322612224⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨865302766157,0,false,-263379127616,-263379127552⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1333434092452,0,true,212086482816,212086482880⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨865589163100,0,false,-263015272704,-263015272640⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099541902675,0,true,30274432,30274496⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099481352877,0,false,-30275328,-30275264⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626942,0,false,-896,-832⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1333463334296,0,true,212110594560,212110594624⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨865559921256,0,false,-263052417664,-263052417600⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1333720497939,0,true,212322619200,212322619264⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨865302757613,0,false,-263379138432,-263379138368⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1049622391975,0,false,-51056519168,-51056519104⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1049731889572,0,false,-50941823104,-50941823040⟩
    { al := (871647/4096000), au := (54531/256000), zl := (3999/4000), zu := 1,
      A := ⟨233980959916,234208861619⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212134715264,212134715328⟩ : DyadicInterval 40),(⟨-263089578560,-263089578496⟩ : DyadicInterval 40),(⟨737035894540,737035913870⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212322612160,212322612224⟩ : DyadicInterval 40),(⟨-263379127616,-263379127552⟩ : DyadicInterval 40),(⟨736986618678,736986638008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212086482816,212086482880⟩ : DyadicInterval 40),(⟨-263015272704,-263015272640⟩ : DyadicInterval 40),(⟨737048534155,737048553484⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212322612160,212322612224⟩ : DyadicInterval 40),(⟨-263379127616,-263379127552⟩ : DyadicInterval 40),(⟨736986618678,736986638008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,30274899⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨30274432,30274496⟩ : DyadicInterval 40),(⟨-30275328,-30275264⟩ : DyadicInterval 40),(⟨762123383166,762123402495⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-896,0⟩ : DyadicInterval 40),(⟨762123383616,762123403328⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨233951706520,234208870163⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212110594560,212110594624⟩ : DyadicInterval 40),(⟨-263052417664,-263052417600⟩ : DyadicInterval 40),(⟨737042215991,737042235320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨212322619200,212322619264⟩ : DyadicInterval 40),(⟨-263379138432,-263379138368⟩ : DyadicInterval 40),(⟨736986616816,736986636145⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-51056519168,-50941823040⟩ : DyadicInterval 40),(⟨787594295136,787651662464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨212134715264,212322612224⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-263379127616,-263089578496⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1404_ok : ecellOkT e1404 = true := by decide +kernel
theorem e1404_pos {a z : ℝ} (ha1 : ((871647/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((54531/256000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1404 e1404_ok ha1 ha2 hz1 hz2 hz

-- box ['510639/512000', '4085961/4096000', '3999/4000', '1']  interval_lower 17548605707365723/1099511627776
noncomputable def e1405 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨2196100530307,0,true,760661049024,760661067712⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨2922725245,8,false,-6520219437760,-6520219283584⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨2196328432010,0,true,760775145600,760775164288⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨2694823542,8,false,-6609481923648,-6609481769408⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨2195826383081,0,true,760523784448,760523803008⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨3196872471,8,false,-6421641079040,-6421640924864⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1109577173150,0,true,10019751808,10019751872⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1089446082402,0,false,-10111901376,-10111901312⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099419482135,0,false,-92149504,-92149440⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨2195963908818,0,true,760592645248,760592663872⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨3059346734,8,false,-6469988333184,-6469988179008⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨2196328445769,0,true,760775152512,760775171200⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨2694809783,8,false,-6609487537472,-6609487383232⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨5383014815,7,false,-5848712365888,-5848712230912⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨6110180960,7,false,-5709395668608,-5709395533696⟩
    { al := (510639/512000), au := (4085961/4096000), zl := (3999/4000), zu := 1,
      A := ⟨1096588902531,1096816804234⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760661049024,760661067712⟩ : DyadicInterval 40),(⟨-6520219437760,-6520219283584⟩ : DyadicInterval 40),(⟨11139345355,11139383488⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760775145600,760775164288⟩ : DyadicInterval 40),(⟨-6609481923648,-6609481769408⟩ : DyadicInterval 40),(⟨10380202889,10380241008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760523784448,760523803008⟩ : DyadicInterval 40),(⟨-6421641079040,-6421640924864⟩ : DyadicInterval 40),(⟨12040791105,12040829128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760775145600,760775164288⟩ : DyadicInterval 40),(⟨-6609481923648,-6609481769408⟩ : DyadicInterval 40),(⟨10380202889,10380241008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10065545374⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10019751808,10019751872⟩ : DyadicInterval 40),(⟨-10111901376,-10111901312⟩ : DyadicInterval 40),(⟨762077310120,762077329450⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-92149504,0⟩ : DyadicInterval 40),(⟨762123383616,762169477632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨1096452281042,1096816817993⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760592645248,760592663872⟩ : DyadicInterval 40),(⟨-6469988333184,-6469988179008⟩ : DyadicInterval 40),(⟨11590119447,11590157526⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760775152512,760775171200⟩ : DyadicInterval 40),(⟨-6609487537472,-6609487383232⟩ : DyadicInterval 40),(⟨10380156750,10380194870⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5848712365888,-5709395533696⟩ : DyadicInterval 40),(⟨3616821150464,3686479585824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨760661049024,760775164288⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-6609481923648,-6520219283584⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1405_ok : ecellOkT e1405 = true := by decide +kernel
theorem e1405_pos {a z : ℝ} (ha1 : ((510639/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((4085961/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1405 e1405_ok ha1 ha2 hz1 hz2 hz

-- box ['4085961/4096000', '408681/409600', '3999/4000', '1']  interval_lower 4734543527238383/274877906944
noncomputable def e1406 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨2196328432009,0,true,760775145600,760775164288⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨2694823543,8,false,-6609481923200,-6609481769024⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨2196556333712,0,true,760889230336,760889249088⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨2466921840,8,false,-6706636499200,-6706636344512⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨2196054227807,0,true,760637866752,760637885376⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨2969027745,8,false,-6502937251840,-6502937097664⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1110384451661,0,true,10819416192,10819416256⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1088638803891,0,false,-10926940416,-10926940352⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099404108859,0,false,-107524224,-107524160⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨2196191814053,0,true,760706750720,760706769344⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨2831441499,8,false,-6555107533824,-6555107379648⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨2196556347416,0,true,760889237248,760889255936⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨2466908136,8,false,-6706642607104,-6706642452416⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨4928281418,7,false,-5945753350784,-5945753215360⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨5655591524,7,false,-5794400763840,-5794400628928⟩
    { al := (4085961/4096000), au := (408681/409600), zl := (3999/4000), zu := 1,
      A := ⟨1096816804233,1097044705936⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760775145600,760775164288⟩ : DyadicInterval 40),(⟨-6609481923200,-6609481769024⟩ : DyadicInterval 40),(⟨10380202891,10380241011⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760889230336,760889249088⟩ : DyadicInterval 40),(⟨-6706636499200,-6706636344512⟩ : DyadicInterval 40),(⟨9611400175,9611438345⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760637866752,760637885376⟩ : DyadicInterval 40),(⟨-6502937251840,-6502937097664⟩ : DyadicInterval 40),(⟨11292468492,11292506564⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760889230336,760889249088⟩ : DyadicInterval 40),(⟨-6706636499200,-6706636344512⟩ : DyadicInterval 40),(⟨9611400175,9611438345⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,10872823885⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10819416192,10819416256⟩ : DyadicInterval 40),(⟨-10926940416,-10926940352⟩ : DyadicInterval 40),(⟨762069623242,762069642571⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-107524224,0⟩ : DyadicInterval 40),(⟨762123383616,762177164992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨1096680186277,1097044719640⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760706750720,760706769344⟩ : DyadicInterval 40),(⟨-6555107533824,-6555107379648⟩ : DyadicInterval 40),(⟨10836387222,10836425286⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760889237248,760889255936⟩ : DyadicInterval 40),(⟨-6706642607104,-6706642452416⟩ : DyadicInterval 40),(⟨9611353650,9611391756⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5945753350784,-5794400628928⟩ : DyadicInterval 40),(⟨3659323698080,3735000078272⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨760775145600,760889249088⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-6706636499200,-6609481769024⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1406_ok : ecellOkT e1406 = true := by decide +kernel
theorem e1406_pos {a z : ℝ} (ha1 : ((4085961/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((408681/409600 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1406 e1406_ok ha1 ha2 hz1 hz2 hz

-- box ['408681/409600', '4087659/4096000', '1999/2000', '3999/4000']  interval_lower 14234078118365607/549755813888
noncomputable def e1407 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨2196556333711,0,true,760889230336,760889249088⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨2466921841,8,false,-6706636498752,-6706636344064⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨2196784235414,0,true,761003303296,761003322048⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨2239020138,8,false,-6813215271488,-6813215110208⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨2196007811357,0,true,760614626880,760614645504⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨3015444195,8,false,-6485880960000,-6485880805824⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨2196509917264,0,true,760865995840,760866014528⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨2513338288,8,false,-6686140821760,-6686140667264⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1109437436161,0,true,9881273728,9881273792⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1089585819391,0,false,-9970882368,-9970882304⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1121983858483,0,true,22245664640,22245664704⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1077039397069,0,false,-22705056512,-22705056448⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099052331903,0,false,-459391872,-459391808⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099422022838,0,false,-89608640,-89608576⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨2196284110584,0,true,760752957504,760752976192⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨2739144968,8,false,-6591545491392,-6591545337216⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨2196647669175,0,true,760934948416,760934967168⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨2375586377,8,false,-6748117612864,-6748117457152⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨4746040101,7,false,-5987182645504,-5987182508992⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨5471466075,7,false,-5830792514560,-5830792379648⟩
    { al := (408681/409600), au := (4087659/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨1097044705935,1097272607638⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760889230336,760889249088⟩ : DyadicInterval 40),(⟨-6706636498752,-6706636344064⟩ : DyadicInterval 40),(⟨9611400178,9611438348⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761003303296,761003322048⟩ : DyadicInterval 40),(⟨-6813215271488,-6813215110208⟩ : DyadicInterval 40),(⟨8832043492,8832081655⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760614626880,760614645504⟩ : DyadicInterval 40),(⟨-6485880960000,-6485880805824⟩ : DyadicInterval 40),(⟨11445605576,11445643652⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760865995840,760866014528⟩ : DyadicInterval 40),(⟨-6686140821760,-6686140667264⟩ : DyadicInterval 40),(⟨9768805688,9768843797⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨9925808385,22472230707⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨9881273728,9881273792⟩ : DyadicInterval 40),(⟨-9970882368,-9970882304⟩ : DyadicInterval 40),(⟨762078580498,762078599828⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨22245664640,22245664704⟩ : DyadicInterval 40),(⟨-22705056512,-22705056448⟩ : DyadicInterval 40),(⟨761893719645,761893738974⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-459391872,-89608576⟩ : DyadicInterval 40),(⟨762168187904,762353098816⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨1096772482808,1097136041399⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760752957504,760752976192⟩ : DyadicInterval 40),(⟨-6591545491392,-6591545337216⟩ : DyadicInterval 40),(⟨10528569292,10528607415⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760934948416,760934967168⟩ : DyadicInterval 40),(⟨-6748117612864,-6748117457152⟩ : DyadicInterval 40),(⟨9300382794,9300420959⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-5987182645504,-5830792379648⟩ : DyadicInterval 40),(⟨3677519573440,3755714725632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨760889230336,761003322048⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-6813215271488,-6706636344064⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1407_ok : ecellOkT e1407 = true := by decide +kernel
theorem e1407_pos {a z : ℝ} (ha1 : ((408681/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((4087659/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1407 e1407_ok ha1 ha2 hz1 hz2 hz

-- box ['4087659/4096000', '1022127/1024000', '1999/2000', '3999/4000']  interval_lower 32302844024728583/1099511627776
noncomputable def e1408 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨2196784235413,0,true,761003303296,761003322048⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨2239020139,8,false,-6813215270976,-6813215109696⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨2197012137116,0,true,761117364352,761117383168⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨2011118436,9,false,-6931244918912,-6931244745472⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨2196235599109,0,true,760728671232,760728689920⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨2787656443,8,false,-6572243078720,-6572242924544⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨2196737761990,0,true,760980042624,760980061376⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨2285493562,8,false,-6790627264576,-6790627106176⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1110219689928,0,true,10656255680,10656255744⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1088803565624,0,false,-10760545728,-10760545664⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1124056145340,0,true,24274572544,24274572608⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1074967110212,0,false,-24822619072,-24822619008⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1098963717842,0,false,-548046528,-548046464⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099407342754,0,false,-104289984,-104289920⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨2196512114623,0,true,760867095744,760867114496⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨2511140929,8,false,-6687102522176,-6687102367680⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨2196875594853,0,true,761049028608,761049047424⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨2147660699,8,false,-6859019979520,-6859019806208⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨4291126402,8,false,-6097970931840,-6097970777664⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨5016546741,7,false,-5926235407040,-5926235271808⟩
    { al := (4087659/4096000), au := (1022127/1024000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨1097272607637,1097500509340⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761003303296,761003322048⟩ : DyadicInterval 40),(⟨-6813215270976,-6813215109696⟩ : DyadicInterval 40),(⟨8832043495,8832081658⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761117364352,761117383168⟩ : DyadicInterval 40),(⟨-6931244918912,-6931244745472⟩ : DyadicInterval 40),(⟨8041056240,8041094464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760728671232,760728689920⟩ : DyadicInterval 40),(⟨-6572243078720,-6572242924544⟩ : DyadicInterval 40),(⟨10690550624,10690588750⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760980042624,760980061376⟩ : DyadicInterval 40),(⟨-6790627264576,-6790627106176⟩ : DyadicInterval 40),(⟨8991874782,8991912945⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨10708062152,24544517564⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨10656255680,10656255744⟩ : DyadicInterval 40),(⟨-10760545728,-10760545664⟩ : DyadicInterval 40),(⟨762071240256,762071259585⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨24274572544,24274572608⟩ : DyadicInterval 40),(⟨-24822619072,-24822619008⟩ : DyadicInterval 40),(⟨761849405843,761849425172⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-548046528,-104289920⟩ : DyadicInterval 40),(⟨762175528576,762397426144⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨1097000486847,1097363967077⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760867095744,760867114496⟩ : DyadicInterval 40),(⟨-6687102522176,-6687102367680⟩ : DyadicInterval 40),(⟨9761363805,9761401977⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761049028608,761049047424⟩ : DyadicInterval 40),(⟨-6859019979520,-6859019806208⟩ : DyadicInterval 40),(⟨8516423200,8516461432⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6097970931840,-5926235271808⟩ : DyadicInterval 40),(⟨3725241019520,3811108868800⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨761003303296,761117383168⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-6931244918912,-6813215109696⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1408_ok : ecellOkT e1408 = true := by decide +kernel
theorem e1408_pos {a z : ℝ} (ha1 : ((4087659/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1022127/1024000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1408 e1408_ok ha1 ha2 hz1 hz2 hz

-- box ['408681/409600', '4087659/4096000', '3999/4000', '1']  interval_lower 20084127133819139/1099511627776
noncomputable def e1409 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨2196556333711,0,true,760889230336,760889249088⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨2466921841,8,false,-6706636498752,-6706636344064⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨2196784235414,0,true,761003303296,761003322048⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨2239020138,8,false,-6813215271488,-6813215110208⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨2196282072534,0,true,760751937216,760751955904⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨2741183018,8,false,-6590727708288,-6590727554112⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1111346194485,0,true,11771329536,11771329600⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1087677061067,0,false,-11898718016,-11898717952⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099384246704,0,false,-127388480,-127388416⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨2196419724513,0,true,760820846912,760820865664⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨2603531039,8,false,-6647375614016,-6647375459712⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨2196784249057,0,true,761003310080,761003328896⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨2239006495,8,false,-6813221971136,-6813221809856⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨4473453556,7,false,-6052218642112,-6052218499968⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨5200897183,7,false,-5886554747840,-5886554612864⟩
    { al := (408681/409600), au := (4087659/4096000), zl := (3999/4000), zu := 1,
      A := ⟨1097044705935,1097272607638⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760889230336,760889249088⟩ : DyadicInterval 40),(⟨-6706636498752,-6706636344064⟩ : DyadicInterval 40),(⟨9611400178,9611438348⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761003303296,761003322048⟩ : DyadicInterval 40),(⟨-6813215271488,-6813215110208⟩ : DyadicInterval 40),(⟨8832043492,8832081655⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760751937216,760751955904⟩ : DyadicInterval 40),(⟨-6590727708288,-6590727554112⟩ : DyadicInterval 40),(⟨10535382999,10535421121⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761003303296,761003322048⟩ : DyadicInterval 40),(⟨-6813215271488,-6813215110208⟩ : DyadicInterval 40),(⟨8832043492,8832081655⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11834566709⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11771329536,11771329600⟩ : DyadicInterval 40),(⟨-11898718016,-11898717952⟩ : DyadicInterval 40),(⟨762059691800,762059711130⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-127388480,0⟩ : DyadicInterval 40),(⟨762123383616,762187097120⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨1096908096737,1097272621281⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760820846912,760820865664⟩ : DyadicInterval 40),(⟨-6647375614016,-6647375459712⟩ : DyadicInterval 40),(⟨10073443419,10073481597⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761003310080,761003328896⟩ : DyadicInterval 40),(⟨-6813221971136,-6813221809856⟩ : DyadicInterval 40),(⟨8831996481,8832034708⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6052218642112,-5886554612864⟩ : DyadicInterval 40),(⟨3705400690048,3788232723936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨760889230336,761003322048⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-6813215271488,-6706636344064⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1409_ok : ecellOkT e1409 = true := by decide +kernel
theorem e1409_pos {a z : ℝ} (ha1 : ((408681/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((4087659/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1409 e1409_ok ha1 ha2 hz1 hz2 hz

-- box ['4087659/4096000', '1022127/1024000', '3999/4000', '1']  interval_lower 5129949032435449/274877906944
noncomputable def e1410 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨2196784235413,0,true,761003303296,761003322048⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨2239020139,8,false,-6813215270976,-6813215109696⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨2197012137116,0,true,761117364352,761117383168⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨2011118436,9,false,-6931244918912,-6931244745472⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨2196509917261,0,true,760865995840,760866014528⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨2513338291,8,false,-6686140820416,-6686140665984⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1112512818947,0,true,12924925376,12924925440⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1086510436605,0,false,-13078668928,-13078668864⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099357895002,0,false,-153743552,-153743488⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨2196647641647,0,true,760934934656,760934953408⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨2375613905,8,false,-6748104871936,-6748104716224⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨2197012150690,0,true,761117371136,761117389952⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨2011104862,9,false,-6931252340096,-6931252166656⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨4018531233,8,false,-6170134949952,-6170134795776⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨4746095039,7,false,-5987169918080,-5987169781632⟩
    { al := (4087659/4096000), au := (1022127/1024000), zl := (3999/4000), zu := 1,
      A := ⟨1097272607637,1097500509340⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761003303296,761003322048⟩ : DyadicInterval 40),(⟨-6813215270976,-6813215109696⟩ : DyadicInterval 40),(⟨8832043495,8832081658⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761117364352,761117383168⟩ : DyadicInterval 40),(⟨-6931244918912,-6931244745472⟩ : DyadicInterval 40),(⟨8041056240,8041094464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760865995840,760866014528⟩ : DyadicInterval 40),(⟨-6686140820416,-6686140665984⟩ : DyadicInterval 40),(⟨9768805697,9768843806⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761117364352,761117383168⟩ : DyadicInterval 40),(⟨-6931244918912,-6931244745472⟩ : DyadicInterval 40),(⟨8041056240,8041094464⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,13001191171⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨12924925376,12924925440⟩ : DyadicInterval 40),(⟨-13078668928,-13078668864⟩ : DyadicInterval 40),(⟨762046515388,762046534718⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-153743552,0⟩ : DyadicInterval 40),(⟨762123383616,762200274656⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨1097136013871,1097500522914⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760934934656,760934953408⟩ : DyadicInterval 40),(⟨-6748104871936,-6748104716224⟩ : DyadicInterval 40),(⟨9300476775,9300514941⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761117371136,761117389952⟩ : DyadicInterval 40),(⟨-6931252340096,-6931252166656⟩ : DyadicInterval 40),(⟨8041008767,8041046990⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6170134949952,-5987169781632⟩ : DyadicInterval 40),(⟨3755708274432,3847190877856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨761003303296,761117383168⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-6931244918912,-6813215109696⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1410_ok : ecellOkT e1410 = true := by decide +kernel
theorem e1410_pos {a z : ℝ} (ha1 : ((4087659/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1022127/1024000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1410 e1410_ok ha1 ha2 hz1 hz2 hz

-- box ['2045103/2048000', '818211/819200', '3997/4000', '1999/2000']  interval_lower 18931420282886115/274877906944
noncomputable def e1411 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨2197467940519,0,true,761345451008,761345469888⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨1555315033,9,false,-7213833573888,-7213833400448⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨2197695842223,0,true,761459476608,761459495552⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨1327413329,9,false,-7388046722432,-7388046548928⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨2196644473284,0,true,760933348736,760933367488⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨2378782268,8,false,-6746639427136,-6746639271488⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨2197146750117,0,true,761184730368,761184749248⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1876505435,9,false,-7007418828544,-7007418655104⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1126098683653,0,true,26270697600,26270697664⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1072924571899,0,false,-26913781632,-26913781568⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1147177807353,0,true,46661887104,46661887168⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1051845448199,0,false,-48730262272,-48730262208⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1097445196991,0,false,-2068375104,-2068375040⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1098868731856,0,false,-643083968,-643083904⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨2197062370127,0,true,761142503552,761142522368⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1960885425,9,false,-6959056938496,-6959056765056⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨2197424578957,0,true,761323754688,761323773568⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨1598676595,9,false,-7183599158976,-7183598985536⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨3195028733,8,false,-6422275385280,-6422275231104⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨3918273778,8,false,-6197914415680,-6197914261504⟩
    { al := (2045103/2048000), au := (818211/819200), zl := (3997/4000), zu := (1999/2000),
      A := ⟨1097956312743,1098184214447⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761345451008,761345469888⟩ : DyadicInterval 40),(⟨-7213833573888,-7213833400448⟩ : DyadicInterval 40),(⟨6418561481,6418599736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761459476608,761459495552⟩ : DyadicInterval 40),(⟨-7388046722432,-7388046548928⟩ : DyadicInterval 40),(⟨5583237107,5583275409⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760933348736,760933367488⟩ : DyadicInterval 40),(⟨-6746639427136,-6746639271488⟩ : DyadicInterval 40),(⟨9311294801,9311332967⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761184730368,761184749248⟩ : DyadicInterval 40),(⟨-7007418828544,-7007418655104⟩ : DyadicInterval 40),(⟨7567862354,7567900632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨26587055877,47666179577⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26270697600,26270697664⟩ : DyadicInterval 40),(⟨-26913781632,-26913781568⟩ : DyadicInterval 40),(⟨761801904300,761801923629⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨46661887104,46661887168⟩ : DyadicInterval 40),(⟨-48730262272,-48730262208⟩ : DyadicInterval 40),(⟨761089844334,761089863663⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2068375104,-643083904⟩ : DyadicInterval 40),(⟨762444925568,763157590432⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨1097550742351,1097912951181⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761142503552,761142522368⟩ : DyadicInterval 40),(⟨-6959056938496,-6959056765056⟩ : DyadicInterval 40),(⟨7865020486,7865058705⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761323754688,761323773568⟩ : DyadicInterval 40),(⟨-7183599158976,-7183598985536⟩ : DyadicInterval 40),(⟨6575520799,6575559056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6422275385280,-6197914261504⟩ : DyadicInterval 40),(⟨3861080514368,3973261095520⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨761345451008,761459495552⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-7388046722432,-7213833400448⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1411_ok : ecellOkT e1411 = true := by decide +kernel
theorem e1411_pos {a z : ℝ} (ha1 : ((2045103/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((818211/819200 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1411 e1411_ok ha1 ha2 hz1 hz2 hz

-- box ['818211/819200', '999/1000', '3997/4000', '1999/2000']  interval_lower 94833612746083189/1099511627776
noncomputable def e1412 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨2197695842222,0,true,761459476608,761459495552⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨1327413330,9,false,-7388046721600,-7388046548160⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨2197923743925,0,true,761573490368,761573509376⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627,9,false,-7595157425088,-7595157240640⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨2196872204060,0,true,761047331520,761047350336⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨2151051492,8,false,-6857285404864,-6857285232256⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨2197374537868,0,true,761298715648,761298734528⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1648717684,9,false,-7149710379136,-7149710205696⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1129151069355,0,true,29246984896,29246984960⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1069872186197,0,false,-30046263360,-30046263296⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1154084848338,0,true,53262085184,53262085248⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1044938407214,0,false,-55974117504,-55974117440⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1096802937547,0,false,-2712032256,-2712032192⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1098712639867,0,false,-799278400,-799278336⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨2197290892975,0,true,761256860992,761256879872⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1732362577,9,false,-7095297413696,-7095297240256⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨2197652894995,0,true,761437989824,761438008768⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨1370360557,9,false,-7353036400384,-7353036226944⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨2739013184,8,false,-6591598391680,-6591598237504⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨3461995688,8,false,-6334040533376,-6334040379200⟩
    { al := (818211/819200), au := (999/1000), zl := (3997/4000), zu := (1999/2000),
      A := ⟨1098184214446,1098412116149⟩, Z := ⟨1098686994055,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761459476608,761459495552⟩ : DyadicInterval 40),(⟨-7388046721600,-7388046548160⟩ : DyadicInterval 40),(⟨5583237109,5583275413⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761573490368,761573509376⟩ : DyadicInterval 40),(⟨-7595157425088,-7595157240640⟩ : DyadicInterval 40),(⟨4728239611,4728277967⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761047331520,761047350336⟩ : DyadicInterval 40),(⟨-6857285404864,-6857285232256⟩ : DyadicInterval 40),(⟨8528171690,8528209922⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761298715648,761298734528⟩ : DyadicInterval 40),(⟨-7149710379136,-7149710205696⟩ : DyadicInterval 40),(⟨6755928034,6755966295⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨29639441579,54573220562⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29246984896,29246984960⟩ : DyadicInterval 40),(⟨-30046263360,-30046263296⟩ : DyadicInterval 40),(⟨761723841254,761723860584⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨53262085184,53262085248⟩ : DyadicInterval 40),(⟨-55974117504,-55974117440⟩ : DyadicInterval 40),(⟨760768481867,760768501197⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2712032256,-799278336⟩ : DyadicInterval 40),(⟨762523022784,763479419008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨1097779265199,1098141267219⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761256860992,761256879872⟩ : DyadicInterval 40),(⟨-7095297413696,-7095297240256⟩ : DyadicInterval 40),(⟨7055797243,7055835511⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761437989824,761438008768⟩ : DyadicInterval 40),(⟨-7353036400384,-7353036226944⟩ : DyadicInterval 40),(⟨5742054173,5742092479⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6591598391680,-6334040379200⟩ : DyadicInterval 40),(⟨3929143573216,4057922598720⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨761459476608,761573509376⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-7595157425088,-7388046548160⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1412_ok : ecellOkT e1412 = true := by decide +kernel
theorem e1412_pos {a z : ℝ} (ha1 : ((818211/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1412 e1412_ok ha1 ha2 hz1 hz2 hz

-- box ['1022127/1024000', '4089357/4096000', '1999/2000', '3999/4000']  interval_lower 18240414486826935/549755813888
noncomputable def e1413 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨2197012137115,0,true,761117364352,761117383168⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨2011118437,9,false,-6931244918400,-6931244744960⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨2197240038818,0,true,761231413568,761231432448⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨1783216734,9,false,-7063485508800,-7063485335360⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨2196463386860,0,true,760842703744,760842722496⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨2559868692,8,false,-6665971270080,-6665971115712⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨2196965606717,0,true,761094077632,761094096448⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨2057648835,9,false,-6906095805312,-6906095631872⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1111148924587,0,true,11576142976,11576143040⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1087874330965,0,false,-11699319808,-11699319744⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1126590709009,0,true,26751001344,26751001408⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1072432546543,0,false,-27418115008,-27418114944⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1098844716556,0,false,-667113600,-667113536⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099388457931,0,false,-123176768,-123176704⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨2196740148497,0,true,760981237120,760981255872⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨2283107055,8,false,-6791775972032,-6791775813504⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨2197103532195,0,true,761163102784,761163121600⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨1919723357,9,false,-6982383108416,-6982382934976⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨3836094918,8,false,-6221219986624,-6221219832448⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨4561473299,7,false,-6030794715520,-6030794576192⟩
    { al := (1022127/1024000), au := (4089357/4096000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨1097500509339,1097728411042⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761117364352,761117383168⟩ : DyadicInterval 40),(⟨-6931244918400,-6931244744960⟩ : DyadicInterval 40),(⟨8041056244,8041094466⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761231413568,761231432448⟩ : DyadicInterval 40),(⟨-7063485508800,-7063485335360⟩ : DyadicInterval 40),(⟨7237116387,7237154658⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760842703744,760842722496⟩ : DyadicInterval 40),(⟨-6665971270080,-6665971115712⟩ : DyadicInterval 40),(⟨9926166881,9926205056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761094077632,761094096448⟩ : DyadicInterval 40),(⟨-6906095805312,-6906095631872⟩ : DyadicInterval 40),(⟨8203556004,8203594229⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11637296811,27079081233⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11576142976,11576143040⟩ : DyadicInterval 40),(⟨-11699319808,-11699319744⟩ : DyadicInterval 40),(⟨762061797522,762061816852⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨26751001344,26751001408⟩ : DyadicInterval 40),(⟨-27418115008,-27418114944⟩ : DyadicInterval 40),(⟨761789894276,761789913606⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-667113600,-123176704⟩ : DyadicInterval 40),(⟨762184971968,762456959680⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨1097228520721,1097591904419⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760981237120,760981255872⟩ : DyadicInterval 40),(⟨-6791775972032,-6791775813504⟩ : DyadicInterval 40),(⟨8983678717,8983716879⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761163102784,761163121600⟩ : DyadicInterval 40),(⟨-6982383108416,-6982382934976⟩ : DyadicInterval 40),(⟨7720293403,7720331620⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6221219986624,-6030794576192⟩ : DyadicInterval 40),(⟨3777520671712,3872733396192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨761117364352,761231432448⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-7063485508800,-6931244744960⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1413_ok : ecellOkT e1413 = true := by decide +kernel
theorem e1413_pos {a z : ℝ} (ha1 : ((1022127/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((4089357/4096000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1413 e1413_ok ha1 ha2 hz1 hz2 hz

-- box ['4089357/4096000', '2045103/2048000', '1999/2000', '3999/4000']  interval_lower 20235369394634363/549755813888
noncomputable def e1414 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨2197240038817,0,true,761231413568,761231432448⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨1783216735,9,false,-7063485508160,-7063485334720⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨2197467940520,0,true,761345451008,761345469888⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨1555315032,9,false,-7213833574592,-7213833401152⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨2196691174611,0,true,760956724480,760956743232⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨2332080941,8,false,-6768440245504,-6768440088832⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨2197193451443,0,true,761208100736,761208119616⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1829804109,9,false,-7035129071424,-7035128897984⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1112272207629,0,true,12687100224,12687100288⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1086751047923,0,false,-12835205440,-12835205376⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1129766756157,0,true,29846346944,29846347008⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1069256499395,0,false,-30679189120,-30679189056⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1098679101070,0,false,-832842112,-832842048⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099363532573,0,false,-148105216,-148105152⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨2196968221818,0,true,761095386368,761095405184⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨2055033734,9,false,-6907494082112,-6907493908672⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨2197331485701,0,true,761277173184,761277192064⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨1691769851,9,false,-7121367822016,-7121367648576⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨3380936650,8,false,-6360090629824,-6360090475648⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨4106226524,8,false,-6146398676224,-6146398522048⟩
    { al := (4089357/4096000), au := (2045103/2048000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨1097728411041,1097956312744⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761231413568,761231432448⟩ : DyadicInterval 40),(⟨-7063485508160,-7063485334720⟩ : DyadicInterval 40),(⟨7237116390,7237154661⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761345451008,761345469888⟩ : DyadicInterval 40),(⟨-7213833574592,-7213833401152⟩ : DyadicInterval 40),(⟨6418561478,6418599733⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760956724480,760956743232⟩ : DyadicInterval 40),(⟨-6768440245504,-6768440088832⟩ : DyadicInterval 40),(⟨9151623173,9151661336⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761208100736,761208119616⟩ : DyadicInterval 40),(⟨-7035129071424,-7035128897984⟩ : DyadicInterval 40),(⟨7402584892,7402623167⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨12760579853,30255128381⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨12687100224,12687100288⟩ : DyadicInterval 40),(⟨-12835205440,-12835205376⟩ : DyadicInterval 40),(⟨762049334306,762049353635⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨29846346944,29846347008⟩ : DyadicInterval 40),(⟨-30679189120,-30679189056⟩ : DyadicInterval 40),(⟨761707067714,761707087044⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-832842112,-148105152⟩ : DyadicInterval 40),(⟨762197436192,762539823936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨1097456594042,1097819857925⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761095386368,761095405184⟩ : DyadicInterval 40),(⟨-6907494082112,-6907493908672⟩ : DyadicInterval 40),(⟨8194437309,8194475535⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761277173184,761277192064⟩ : DyadicInterval 40),(⟨-7121367822016,-7121367648576⟩ : DyadicInterval 40),(⟨6910529822,6910568087⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6360090629824,-6146398522048⟩ : DyadicInterval 40),(⟨3835322644640,3942168717792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨761231413568,761345469888⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-7213833574592,-7063485334720⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1414_ok : ecellOkT e1414 = true := by decide +kernel
theorem e1414_pos {a z : ℝ} (ha1 : ((4089357/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((2045103/2048000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1414 e1414_ok ha1 ha2 hz1 hz2 hz

-- box ['1022127/1024000', '4089357/4096000', '3999/4000', '1']  interval_lower 19210041539240219/1099511627776
noncomputable def e1415 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨2197012137115,0,true,761117364352,761117383168⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨2011118437,9,false,-6931244918400,-6931244744960⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨2197240038818,0,true,761231413568,761231432448⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨1783216734,9,false,-7063485508800,-7063485335360⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨2196737761987,0,true,760980042624,760980061376⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨2285493565,8,false,-6790627263168,-6790627104768⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1113959722043,0,true,14353990400,14353990464⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1085063533509,0,false,-14543861504,-14543861440⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099321773096,0,false,-189871104,-189871040⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨2196875567469,0,true,761049014912,761049033664⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨2147688083,8,false,-6859005960128,-6859005786816⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨2197240052312,0,true,761231420352,761231439232⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1783203240,9,false,-7063493829056,-7063493655616⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨3563514456,8,false,-6302262389568,-6302262235392⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨4291181064,8,false,-6097956925952,-6097956771776⟩
    { al := (1022127/1024000), au := (4089357/4096000), zl := (3999/4000), zu := 1,
      A := ⟨1097500509339,1097728411042⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761117364352,761117383168⟩ : DyadicInterval 40),(⟨-6931244918400,-6931244744960⟩ : DyadicInterval 40),(⟨8041056244,8041094466⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761231413568,761231432448⟩ : DyadicInterval 40),(⟨-7063485508800,-7063485335360⟩ : DyadicInterval 40),(⟨7237116387,7237154658⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨760980042624,760980061376⟩ : DyadicInterval 40),(⟨-6790627263168,-6790627104768⟩ : DyadicInterval 40),(⟨8991874791,8991912954⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761231413568,761231432448⟩ : DyadicInterval 40),(⟨-7063485508800,-7063485335360⟩ : DyadicInterval 40),(⟨7237116387,7237154658⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,14448094267⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨14353990400,14353990464⟩ : DyadicInterval 40),(⟨-14543861504,-14543861440⟩ : DyadicInterval 40),(⟨762028453495,762028472824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-189871104,0⟩ : DyadicInterval 40),(⟨762123383616,762218338432⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨1097363939693,1097728424536⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761049014912,761049033664⟩ : DyadicInterval 40),(⟨-6859005960128,-6859005786816⟩ : DyadicInterval 40),(⟨8516518145,8516556314⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761231420352,761231439232⟩ : DyadicInterval 40),(⟨-7063493829056,-7063493655616⟩ : DyadicInterval 40),(⟨7237068340,7237106611⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6302262389568,-6097956771776⟩ : DyadicInterval 40),(⟨3811101769504,3913254597664⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨761117364352,761231432448⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-7063485508800,-6931244744960⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1415_ok : ecellOkT e1415 = true := by decide +kernel
theorem e1415_pos {a z : ℝ} (ha1 : ((1022127/1024000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((4089357/4096000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1415 e1415_ok ha1 ha2 hz1 hz2 hz

-- box ['4089357/4096000', '2045103/2048000', '3999/4000', '1']  interval_lower 6878327994353447/549755813888
noncomputable def e1416 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨2197240038817,0,true,761231413568,761231432448⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨1783216735,9,false,-7063485508160,-7063485334720⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨2197467940520,0,true,761345451008,761345469888⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨1555315032,9,false,-7213833574592,-7213833401152⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨2196965606714,0,true,761094077632,761094096448⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨2057648838,9,false,-6906095803712,-6906095630272⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1115805108416,0,true,16173934976,16173935040⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1083218147136,0,false,-16415411968,-16415411904⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099270177385,0,false,-241476928,-241476864⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨2197103504968,0,true,761163089152,761163107968⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1919750584,9,false,-6982367514368,-6982367340928⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨2197467953922,0,true,761345457728,761345476608⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1555301630,9,false,-7213843049024,-7213842875584⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨3108403225,8,false,-6452497572352,-6452497418176⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨3836149278,8,false,-6221204405952,-6221204251776⟩
    { al := (4089357/4096000), au := (2045103/2048000), zl := (3999/4000), zu := 1,
      A := ⟨1097728411041,1097956312744⟩, Z := ⟨1099236749869,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761231413568,761231432448⟩ : DyadicInterval 40),(⟨-7063485508160,-7063485334720⟩ : DyadicInterval 40),(⟨7237116390,7237154661⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761345451008,761345469888⟩ : DyadicInterval 40),(⟨-7213833574592,-7213833401152⟩ : DyadicInterval 40),(⟨6418561478,6418599733⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761094077632,761094096448⟩ : DyadicInterval 40),(⟨-6906095803712,-6906095630272⟩ : DyadicInterval 40),(⟨8203556013,8203594238⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761345451008,761345469888⟩ : DyadicInterval 40),(⟨-7213833574592,-7213833401152⟩ : DyadicInterval 40),(⟨6418561478,6418599733⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,16293480640⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨16173934976,16173935040⟩ : DyadicInterval 40),(⟨-16415411968,-16415411904⟩ : DyadicInterval 40),(⟨762002653981,762002673310⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-241476928,0⟩ : DyadicInterval 40),(⟨762123383616,762244141344⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨1097591877192,1097956326146⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761163089152,761163107968⟩ : DyadicInterval 40),(⟨-6982367514368,-6982367340928⟩ : DyadicInterval 40),(⟨7720389286,7720427502⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761345457728,761345476608⟩ : DyadicInterval 40),(⟨-7213843049024,-7213842875584⟩ : DyadicInterval 40),(⟨6418512859,6418551114⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6452497572352,-6221204251776⟩ : DyadicInterval 40),(⟨3872725509504,3988372189056⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨761231413568,761345469888⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-7213833574592,-7063485334720⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1416_ok : ecellOkT e1416 = true := by decide +kernel
theorem e1416_pos {a z : ℝ} (ha1 : ((4089357/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((2045103/2048000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1416 e1416_ok ha1 ha2 hz1 hz2 hz

-- box ['2045103/2048000', '818211/819200', '1999/2000', '3999/4000']  interval_lower 42587249208638253/1099511627776
noncomputable def e1417 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨2197467940519,0,true,761345451008,761345469888⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨1555315033,9,false,-7213833573888,-7213833400448⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨2197695842223,0,true,761459476608,761459495552⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨1327413329,9,false,-7388046722432,-7388046548928⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨2196918962362,0,true,761070733312,761070752128⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨2104293190,9,false,-6881449542656,-6881449369216⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨2197421296171,0,true,761322112064,761322131008⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1601959381,9,false,-7181343693056,-7181343519616⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1113659462343,0,true,14057585088,14057585152⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1085363793209,0,false,-14239645824,-14239645760⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1133871522371,0,true,33833947968,33833948032⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1065151733181,0,false,-34908224256,-34908224192⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1098437876187,0,false,-1074276288,-1074276224⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099329582205,0,false,-182060672,-182060608⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨2197196348868,0,true,761209550656,761209569536⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1826906684,9,false,-7036871486016,-7036871312576⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨2197559462656,0,true,761391243520,761391262464⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨1463792896,9,false,-7280515850880,-7280515677440⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨2925637027,8,false,-6519124588160,-6519124433984⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨3650777850,8,false,-6275661915904,-6275661761728⟩
    { al := (2045103/2048000), au := (818211/819200), zl := (1999/2000), zu := (3999/4000),
      A := ⟨1097956312743,1098184214447⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761345451008,761345469888⟩ : DyadicInterval 40),(⟨-7213833573888,-7213833400448⟩ : DyadicInterval 40),(⟨6418561481,6418599736⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761459476608,761459495552⟩ : DyadicInterval 40),(⟨-7388046722432,-7388046548928⟩ : DyadicInterval 40),(⟨5583237107,5583275409⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761070733312,761070752128⟩ : DyadicInterval 40),(⟨-6881449542656,-6881449369216⟩ : DyadicInterval 40),(⟨8365925244,8365963473⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761322112064,761322131008⟩ : DyadicInterval 40),(⟨-7181343693056,-7181343519616⟩ : DyadicInterval 40),(⟨6587379569,6587417892⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨14147834567,34359894595⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨14057585088,14057585152⟩ : DyadicInterval 40),(⟨-14239645824,-14239645760⟩ : DyadicInterval 40),(⟨762032358299,762032377629⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨33833947968,33833948032⟩ : DyadicInterval 40),(⟨-34908224256,-34908224192⟩ : DyadicInterval 40),(⟨761586420370,761586439700⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1074276288,-182060608⟩ : DyadicInterval 40),(⟨762214413920,762660541024⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨1097684721092,1098047834880⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761209550656,761209569536⟩ : DyadicInterval 40),(⟨-7036871486016,-7036871312576⟩ : DyadicInterval 40),(⟨7392311317,7392349591⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761391243520,761391262464⟩ : DyadicInterval 40),(⟨-7280515850880,-7280515677440⟩ : DyadicInterval 40),(⟨6085264288,6085302601⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6519124588160,-6275661761728⟩ : DyadicInterval 40),(⟨3899954264480,4021685696960⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨761345451008,761459495552⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-7388046722432,-7213833400448⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1417_ok : ecellOkT e1417 = true := by decide +kernel
theorem e1417_pos {a z : ℝ} (ha1 : ((2045103/2048000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((818211/819200 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1417 e1417_ok ha1 ha2 hz1 hz2 hz

-- box ['818211/819200', '999/1000', '1999/2000', '3999/4000']  interval_lower 18787670106079835/549755813888
noncomputable def e1418 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨2197695842222,0,true,761459476608,761459495552⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨1327413330,9,false,-7388046721600,-7388046548160⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨2197923743925,0,true,761573490368,761573509376⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627,9,false,-7595157425088,-7595157240640⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨2197146750114,0,true,761184730368,761184749248⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨1876505438,9,false,-7007418826752,-7007418653312⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨2197649140897,0,true,761436111552,761436130496⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1374114655,9,false,-7350028410432,-7350028236928⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1115419434575,0,true,15793827200,15793827264⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1083603820977,0,false,-16024006592,-16024006528⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1139397133783,0,true,39179102336,39179102400⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1059626121769,0,false,-40626928128,-40626928064⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1098064754865,0,false,-1447825792,-1447825728⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099281472578,0,false,-230179328,-230179264⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨2197424551989,0,true,761323741184,761323760064⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1598703563,9,false,-7183580611520,-7183580438080⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨2197787475492,0,true,761505319936,761505338944⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨1235780060,9,false,-7466694553088,-7466694379136⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨2470171183,8,false,-6705189213952,-6705189059264⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨3195082592,8,false,-6422256850816,-6422256696640⟩
    { al := (818211/819200), au := (999/1000), zl := (1999/2000), zu := (3999/4000),
      A := ⟨1098184214446,1098412116149⟩, Z := ⟨1098961871962,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761459476608,761459495552⟩ : DyadicInterval 40),(⟨-7388046721600,-7388046548160⟩ : DyadicInterval 40),(⟨5583237109,5583275413⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761573490368,761573509376⟩ : DyadicInterval 40),(⟨-7595157425088,-7595157240640⟩ : DyadicInterval 40),(⟨4728239611,4728277967⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761184730368,761184749248⟩ : DyadicInterval 40),(⟨-7007418826752,-7007418653312⟩ : DyadicInterval 40),(⟨7567862364,7567900641⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761436111552,761436130496⟩ : DyadicInterval 40),(⟨-7350028410432,-7350028236928⟩ : DyadicInterval 40),(⟨5755904409,5755942715⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨15907806799,39885506007⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨15793827200,15793827264⟩ : DyadicInterval 40),(⟨-16024006592,-16024006528⟩ : DyadicInterval 40),(⟨762008301987,762008321317⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨39179102336,39179102400⟩ : DyadicInterval 40),(⟨-40626928128,-40626928064⟩ : DyadicInterval 40),(⟨761399788378,761399807707⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1447825792,-230179264⟩ : DyadicInterval 40),(⟨762238473248,762847315776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨1097912924213,1098275847716⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761323741184,761323760064⟩ : DyadicInterval 40),(⟨-7183580611520,-7183580438080⟩ : DyadicInterval 40),(⟨6575618242,6575656500⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨761505319936,761505338944⟩ : DyadicInterval 40),(⟨-7466694553088,-7466694379136⟩ : DyadicInterval 40),(⟨5242027212,5242065573⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6705189213952,-6422256696640⟩ : DyadicInterval 40),(⟨3973251731936,4114718009856⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨761459476608,761573509376⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-7595157425088,-7388046548160⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1418_ok : ecellOkT e1418 = true := by decide +kernel
theorem e1418_pos {a z : ℝ} (ha1 : ((818211/819200 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1418 e1418_ok ha1 ha2 hz1 hz2 hz

-- box ['688263/4096000', '86139/512000', '999/1000', '7993/8000']  interval_lower 1810457/1099511627776
noncomputable def e1419 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1284265820028,0,true,170777358016,170777358080⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨914757435524,0,false,-202268856320,-202268856256⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1284493721732,0,true,170972456512,170972456576⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨914529533820,0,false,-202542821568,-202542821504⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1284081065835,0,true,170619171136,170619171200⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨914942189717,0,false,-202046809600,-202046809536⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1284331862400,0,true,170833898112,170833898176⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨914691393152,0,false,-202348240192,-202348240128⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099594144426,0,true,82513536,82513600⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429111126,0,false,-82519808,-82519744⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099606054537,0,true,94422656,94422720⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099417201015,0,false,-94430848,-94430784⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619666,0,false,-8128,-8064⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621584,0,false,-6208,-6144⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1284173439063,0,true,170698264128,170698264192⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨914849816489,0,false,-202157822720,-202157822656⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1284412801275,0,true,170903187392,170903187456⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨914610454277,0,false,-202445537664,-202445537600⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068417419131,0,false,-31542350272,-31542350208⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068497872500,0,false,-31459558592,-31459558528⟩
    { al := (688263/4096000), au := (86139/512000), zl := (999/1000), zu := (7993/8000),
      A := ⟨184754192252,184982093956⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170777358016,170777358080⟩ : DyadicInterval 40),(⟨-202268856320,-202268856256⟩ : DyadicInterval 40),(⟨746527103087,746527122417⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170972456512,170972456576⟩ : DyadicInterval 40),(⟨-202542821568,-202542821504⟩ : DyadicInterval 40),(⟨746488417116,746488436445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170619171136,170619171200⟩ : DyadicInterval 40),(⟨-202046809600,-202046809536⟩ : DyadicInterval 40),(⟨746558429139,746558448469⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170833898112,170833898176⟩ : DyadicInterval 40),(⟨-202348240192,-202348240128⟩ : DyadicInterval 40),(⟨746515897494,746515916824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨82516650,94426761⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨82513536,82513600⟩ : DyadicInterval 40),(⟨-82519808,-82519744⟩ : DyadicInterval 40),(⟨762123380495,762123399824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨94422656,94422720⟩ : DyadicInterval 40),(⟨-94430848,-94430784⟩ : DyadicInterval 40),(⟨762123379538,762123398867⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-8128,-6144⟩ : DyadicInterval 40),(⟨762123386688,762123406944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨184661811287,184901173499⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170698264128,170698264192⟩ : DyadicInterval 40),(⟨-202157822720,-202157822656⟩ : DyadicInterval 40),(⟨746542770757,746542790087⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170903187392,170903187456⟩ : DyadicInterval 40),(⟨-202445537664,-202445537600⟩ : DyadicInterval 40),(⟨746502158806,746502178135⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31542350272,-31459558528⟩ : DyadicInterval 40),(⟨777853162880,777894578016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170777358016,170972456576⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-202542821568,-202268856256⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1419_ok : ecellOkT e1419 = true := by decide +kernel
theorem e1419_pos {a z : ℝ} (ha1 : ((688263/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((86139/512000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1419 e1419_ok ha1 ha2 hz1 hz2 hz

-- box ['688263/4096000', '86139/512000', '7993/8000', '3997/4000']  interval_lower 786767/549755813888
noncomputable def e1420 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1284265820028,0,true,170777358016,170777358080⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨914757435524,0,false,-202268856320,-202268856256⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1284493721732,0,true,170972456512,170972456576⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨914529533820,0,false,-202542821568,-202542821504⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1284104160109,0,true,170638945728,170638945792⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨914919095443,0,false,-202074563008,-202074562944⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1284354985162,0,true,170853693184,170853693248⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨914668270390,0,false,-202376035392,-202376035328⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099582356482,0,true,70726400,70726464⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099440899070,0,false,-70731008,-70730944⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099594251442,0,true,82620544,82620608⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429004110,0,false,-82626816,-82626752⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621567,0,false,-6272,-6208⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623227,0,false,-4608,-4544⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1284184985976,0,true,170708150528,170708150592⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨914838269576,0,false,-202171700416,-202171700352⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1284424362462,0,true,170913084160,170913084224⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨914598893090,0,false,-202459436160,-202459436096⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068413530597,0,false,-31546351936,-31546351872⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068493993795,0,false,-31463549824,-31463549760⟩
    { al := (688263/4096000), au := (86139/512000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨184754192252,184982093956⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170777358016,170777358080⟩ : DyadicInterval 40),(⟨-202268856320,-202268856256⟩ : DyadicInterval 40),(⟨746527103087,746527122417⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170972456512,170972456576⟩ : DyadicInterval 40),(⟨-202542821568,-202542821504⟩ : DyadicInterval 40),(⟨746488417116,746488436445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170638945728,170638945792⟩ : DyadicInterval 40),(⟨-202074563008,-202074562944⟩ : DyadicInterval 40),(⟨746554515145,746554534475⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170853693184,170853693248⟩ : DyadicInterval 40),(⟨-202376035392,-202376035328⟩ : DyadicInterval 40),(⟨746511973245,746511992575⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨70728706,82623666⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨70726400,70726464⟩ : DyadicInterval 40),(⟨-70731008,-70730944⟩ : DyadicInterval 40),(⟨762123381306,762123400635⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨82620544,82620608⟩ : DyadicInterval 40),(⟨-82626816,-82626752⟩ : DyadicInterval 40),(⟨762123380478,762123399808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6272,-4544⟩ : DyadicInterval 40),(⟨762123385888,762123406016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨184673358200,184912734686⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170708150528,170708150592⟩ : DyadicInterval 40),(⟨-202171700416,-202171700352⟩ : DyadicInterval 40),(⟨746540812862,746540832192⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170913084160,170913084224⟩ : DyadicInterval 40),(⟨-202459436160,-202459436096⟩ : DyadicInterval 40),(⟨746500195909,746500215239⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31546351936,-31463549760⟩ : DyadicInterval 40),(⟨777855158496,777896578848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170777358016,170972456576⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-202542821568,-202268856256⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1420_ok : ecellOkT e1420 = true := by decide +kernel
theorem e1420_pos {a z : ℝ} (ha1 : ((688263/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((86139/512000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1420 e1420_ok ha1 ha2 hz1 hz2 hz

-- box ['688263/4096000', '86139/512000', '3997/4000', '1599/1600']  interval_lower 668529/549755813888
noncomputable def e1421 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1284265820028,0,true,170777358016,170777358080⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨914757435524,0,false,-202268856320,-202268856256⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1284493721732,0,true,170972456512,170972456576⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨914529533820,0,false,-202542821568,-202542821504⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1284127254383,0,true,170658720000,170658720064⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨914896001169,0,false,-202102317056,-202102316992⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1284378107924,0,true,170873488000,170873488064⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨914645147628,0,false,-202403831360,-202403831296⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570568476,0,true,58939072,58939136⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452687076,0,false,-58942336,-58942272⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099582448285,0,true,70818176,70818240⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099440807267,0,false,-70822848,-70822784⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623214,0,false,-4608,-4544⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624617,0,false,-3200,-3136⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1284196532923,0,true,170718036928,170718036992⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨914826722629,0,false,-202185578368,-202185578304⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1284435923680,0,true,170922980928,170922980992⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨914587331872,0,false,-202473334912,-202473334848⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068409641810,0,false,-31550353920,-31550353856⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068490114836,0,false,-31467541440,-31467541376⟩
    { al := (688263/4096000), au := (86139/512000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨184754192252,184982093956⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170777358016,170777358080⟩ : DyadicInterval 40),(⟨-202268856320,-202268856256⟩ : DyadicInterval 40),(⟨746527103087,746527122417⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170972456512,170972456576⟩ : DyadicInterval 40),(⟨-202542821568,-202542821504⟩ : DyadicInterval 40),(⟨746488417116,746488436445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170658720000,170658720064⟩ : DyadicInterval 40),(⟨-202102317056,-202102316992⟩ : DyadicInterval 40),(⟨746550600607,746550619936⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170873488000,170873488064⟩ : DyadicInterval 40),(⟨-202403831360,-202403831296⟩ : DyadicInterval 40),(⟨746508048465,746508067795⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨58940700,70820509⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨58939072,58939136⟩ : DyadicInterval 40),(⟨-58942336,-58942272⟩ : DyadicInterval 40),(⟨762123382024,762123401353⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨70818176,70818240⟩ : DyadicInterval 40),(⟨-70822848,-70822784⟩ : DyadicInterval 40),(⟨762123381326,762123400655⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4608,-3136⟩ : DyadicInterval 40),(⟨762123385184,762123405184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨184684905147,184924295904⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170718036928,170718036992⟩ : DyadicInterval 40),(⟨-202185578368,-202185578304⟩ : DyadicInterval 40),(⟨746538854819,746538874148⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170922980928,170922980992⟩ : DyadicInterval 40),(⟨-202473334912,-202473334848⟩ : DyadicInterval 40),(⟨746498232863,746498252193⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31550353920,-31467541376⟩ : DyadicInterval 40),(⟨777857154304,777898579840⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170777358016,170972456576⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-202542821568,-202268856256⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1421_ok : ecellOkT e1421 = true := by decide +kernel
theorem e1421_pos {a z : ℝ} (ha1 : ((688263/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((86139/512000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1421 e1421_ok ha1 ha2 hz1 hz2 hz

-- box ['688263/4096000', '86139/512000', '1599/1600', '1999/2000']  interval_lower 17187/17179869184
noncomputable def e1422 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1284265820028,0,true,170777358016,170777358080⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨914757435524,0,false,-202268856320,-202268856256⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1284493721732,0,true,170972456512,170972456576⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨914529533820,0,false,-202542821568,-202542821504⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1284150348657,0,true,170678493888,170678493952⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨914872906895,0,false,-202130071872,-202130071808⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1284401230686,0,true,170893282432,170893282496⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨914622024866,0,false,-202431627968,-202431627904⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558780408,0,true,47151616,47151680⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099464475144,0,false,-47153664,-47153600⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570645065,0,true,59015680,59015744⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452610487,0,false,-59018880,-59018816⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624608,0,false,-3200,-3136⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625754,0,false,-2048,-1984⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1284208079895,0,true,170727923264,170727923328⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨914815175657,0,false,-202199456512,-202199456448⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1284447484930,0,true,170932877632,170932877696⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨914575770622,0,false,-202487233856,-202487233792⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068405752769,0,false,-31554356224,-31554356160⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068486235626,0,false,-31471533248,-31471533184⟩
    { al := (688263/4096000), au := (86139/512000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨184754192252,184982093956⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170777358016,170777358080⟩ : DyadicInterval 40),(⟨-202268856320,-202268856256⟩ : DyadicInterval 40),(⟨746527103087,746527122417⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170972456512,170972456576⟩ : DyadicInterval 40),(⟨-202542821568,-202542821504⟩ : DyadicInterval 40),(⟨746488417116,746488436445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170678493888,170678493952⟩ : DyadicInterval 40),(⟨-202130071872,-202130071808⟩ : DyadicInterval 40),(⟨746546685613,746546704943⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170893282432,170893282496⟩ : DyadicInterval 40),(⟨-202431627968,-202431627904⟩ : DyadicInterval 40),(⟨746504123175,746504142504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨47152632,59017289⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨47151616,47151680⟩ : DyadicInterval 40),(⟨-47153664,-47153600⟩ : DyadicInterval 40),(⟨762123382553,762123401882⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59015680,59015744⟩ : DyadicInterval 40),(⟨-59018880,-59018816⟩ : DyadicInterval 40),(⟨762123381984,762123401313⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3200,-1984⟩ : DyadicInterval 40),(⟨762123384608,762123404480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨184696452119,184935857154⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170727923264,170727923328⟩ : DyadicInterval 40),(⟨-202199456512,-202199456448⟩ : DyadicInterval 40),(⟨746536896639,746536915968⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170932877632,170932877696⟩ : DyadicInterval 40),(⟨-202487233856,-202487233792⟩ : DyadicInterval 40),(⟨746496269679,746496289009⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31554356224,-31471533184⟩ : DyadicInterval 40),(⟨777859150208,777900580992⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170777358016,170972456576⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-202542821568,-202268856256⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1422_ok : ecellOkT e1422 = true := by decide +kernel
theorem e1422_pos {a z : ℝ} (ha1 : ((688263/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((86139/512000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1422 e1422_ok ha1 ha2 hz1 hz2 hz

-- box ['688263/4096000', '86139/512000', '1999/2000', '7997/8000']  interval_lower 862867/1099511627776
noncomputable def e1423 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1284265820028,0,true,170777358016,170777358080⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨914757435524,0,false,-202268856320,-202268856256⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1284493721732,0,true,170972456512,170972456576⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨914529533820,0,false,-202542821568,-202542821504⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1284173442931,0,true,170698267392,170698267456⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨914849812621,0,false,-202157827328,-202157827264⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1284424353447,0,true,170913076480,170913076544⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨914598902105,0,false,-202459425344,-202459425280⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099546992279,0,true,35363904,35363968⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476263273,0,false,-35365120,-35365056⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558841782,0,true,47212992,47213056⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099464413770,0,false,-47215040,-47214976⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625748,0,false,-2048,-1984⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626639,0,false,-1152,-1088⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1284219626898,0,true,170737809472,170737809536⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨914803628654,0,false,-202213334912,-202213334848⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1284459046205,0,true,170942774272,170942774336⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨914564209347,0,false,-202501133056,-202501132992⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068401863477,0,false,-31558358720,-31558358656⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068482356164,0,false,-31475525376,-31475525312⟩
    { al := (688263/4096000), au := (86139/512000), zl := (1999/2000), zu := (7997/8000),
      A := ⟨184754192252,184982093956⟩, Z := ⟨1098961871962,1099099310916⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170777358016,170777358080⟩ : DyadicInterval 40),(⟨-202268856320,-202268856256⟩ : DyadicInterval 40),(⟨746527103087,746527122417⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170972456512,170972456576⟩ : DyadicInterval 40),(⟨-202542821568,-202542821504⟩ : DyadicInterval 40),(⟨746488417116,746488436445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170698267392,170698267456⟩ : DyadicInterval 40),(⟨-202157827328,-202157827264⟩ : DyadicInterval 40),(⟨746542770112,746542789442⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170913076480,170913076544⟩ : DyadicInterval 40),(⟨-202459425344,-202459425280⟩ : DyadicInterval 40),(⟨746500197427,746500216757⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨35364503,47214006⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35363904,35363968⟩ : DyadicInterval 40),(⟨-35365120,-35365056⟩ : DyadicInterval 40),(⟨762123383022,762123402351⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨47212992,47213056⟩ : DyadicInterval 40),(⟨-47215040,-47214976⟩ : DyadicInterval 40),(⟨762123382548,762123401877⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-2048,-1088⟩ : DyadicInterval 40),(⟨762123384160,762123403904⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨184707999122,184947418429⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170737809472,170737809536⟩ : DyadicInterval 40),(⟨-202213334912,-202213334848⟩ : DyadicInterval 40),(⟨746534938385,746534957715⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170942774272,170942774336⟩ : DyadicInterval 40),(⟨-202501133056,-202501132992⟩ : DyadicInterval 40),(⟨746494306385,746494325714⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31558358720,-31475525312⟩ : DyadicInterval 40),(⟨777861146272,777902582240⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170777358016,170972456576⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-202542821568,-202268856256⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1423_ok : ecellOkT e1423 = true := by decide +kernel
theorem e1423_pos {a z : ℝ} (ha1 : ((688263/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((86139/512000 : ℚ) : ℝ))
    (hz1 : ((1999/2000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7997/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1423 e1423_ok ha1 ha2 hz1 hz2 hz

-- box ['688263/4096000', '86139/512000', '7997/8000', '3999/4000']  interval_lower 156479/274877906944
noncomputable def e1424 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1284265820028,0,true,170777358016,170777358080⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨914757435524,0,false,-202268856320,-202268856256⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1284493721732,0,true,170972456512,170972456576⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨914529533820,0,false,-202542821568,-202542821504⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1284196537205,0,true,170718040576,170718040640⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨914826718347,0,false,-202185583552,-202185583488⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1284447476209,0,true,170932870144,170932870208⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨914575779343,0,false,-202487223360,-202487223296⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535204086,0,true,23576000,23576064⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488051466,0,false,-23576576,-23576512⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099547038438,0,true,35410048,35410112⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099476217114,0,false,-35411264,-35411200⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511626635,0,false,-1152,-1088⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627271,0,false,-512,-448⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1284231173929,0,true,170747695680,170747695744⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨914792081623,0,false,-202227213504,-202227213440⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1284470607511,0,true,170952670848,170952670912⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨914552648041,0,false,-202515032384,-202515032320⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068397973931,0,false,-31562361536,-31562361472⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068478476449,0,false,-31479517760,-31479517696⟩
    { al := (688263/4096000), au := (86139/512000), zl := (7997/8000), zu := (3999/4000),
      A := ⟨184754192252,184982093956⟩, Z := ⟨1099099310915,1099236749870⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170777358016,170777358080⟩ : DyadicInterval 40),(⟨-202268856320,-202268856256⟩ : DyadicInterval 40),(⟨746527103087,746527122417⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170972456512,170972456576⟩ : DyadicInterval 40),(⟨-202542821568,-202542821504⟩ : DyadicInterval 40),(⟨746488417116,746488436445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170718040576,170718040640⟩ : DyadicInterval 40),(⟨-202185583552,-202185583488⟩ : DyadicInterval 40),(⟨746538854119,746538873448⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170932870144,170932870208⟩ : DyadicInterval 40),(⟨-202487223360,-202487223296⟩ : DyadicInterval 40),(⟨746496271169,746496290498⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨23576310,35410662⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23576000,23576064⟩ : DyadicInterval 40),(⟨-23576576,-23576512⟩ : DyadicInterval 40),(⟨762123383334,762123402663⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨35410048,35410112⟩ : DyadicInterval 40),(⟨-35411264,-35411200⟩ : DyadicInterval 40),(⟨762123383019,762123402348⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-1152,-448⟩ : DyadicInterval 40),(⟨762123383840,762123403456⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨184719546153,184958979735⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170747695680,170747695744⟩ : DyadicInterval 40),(⟨-202227213504,-202227213440⟩ : DyadicInterval 40),(⟨746532979957,746532999287⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170952670848,170952670912⟩ : DyadicInterval 40),(⟨-202515032384,-202515032320⟩ : DyadicInterval 40),(⟨746492342925,746492362255⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31562361536,-31479517696⟩ : DyadicInterval 40),(⟨777863142464,777904583648⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170777358016,170972456576⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-202542821568,-202268856256⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1424_ok : ecellOkT e1424 = true := by decide +kernel
theorem e1424_pos {a z : ℝ} (ha1 : ((688263/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((86139/512000 : ℚ) : ℝ))
    (hz1 : ((7997/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3999/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1424 e1424_ok ha1 ha2 hz1 hz2 hz

-- box ['688263/4096000', '86139/512000', '3999/4000', '7999/8000']  interval_lower 388927/1099511627776
noncomputable def e1425 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1284265820028,0,true,170777358016,170777358080⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨914757435524,0,false,-202268856320,-202268856256⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1284493721732,0,true,170972456512,170972456576⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨914529533820,0,false,-202542821568,-202542821504⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1284219631479,0,true,170737813440,170737813504⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨914803624073,0,false,-202213340416,-202213340352⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1284470598971,0,true,170952663488,170952663552⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨914552656581,0,false,-202515022144,-202515022080⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523415833,0,true,11787968,11788032⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499839719,0,false,-11788160,-11788096⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099535235032,0,true,23606976,23607040⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099488020520,0,false,-23607552,-23607488⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627269,0,false,-512,-448⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627650,0,false,-128,-64⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1284242720996,0,true,170757581824,170757581888⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨914780534556,0,false,-202241092288,-202241092224⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1284482168845,0,true,170962567360,170962567424⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨914541086707,0,false,-202528931968,-202528931904⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068394084132,0,false,-31566364608,-31566364544⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068474596480,0,false,-31483510464,-31483510400⟩
    { al := (688263/4096000), au := (86139/512000), zl := (3999/4000), zu := (7999/8000),
      A := ⟨184754192252,184982093956⟩, Z := ⟨1099236749869,1099374188823⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170777358016,170777358080⟩ : DyadicInterval 40),(⟨-202268856320,-202268856256⟩ : DyadicInterval 40),(⟨746527103087,746527122417⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170972456512,170972456576⟩ : DyadicInterval 40),(⟨-202542821568,-202542821504⟩ : DyadicInterval 40),(⟨746488417116,746488436445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170737813440,170737813504⟩ : DyadicInterval 40),(⟨-202213340416,-202213340352⟩ : DyadicInterval 40),(⟨746534937581,746534956910⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170952663488,170952663552⟩ : DyadicInterval 40),(⟨-202515022144,-202515022080⟩ : DyadicInterval 40),(⟨746492344416,746492363746⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨11788057,23607256⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11787968,11788032⟩ : DyadicInterval 40),(⟨-11788160,-11788096⟩ : DyadicInterval 40),(⟨762123383521,762123402850⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨23606976,23607040⟩ : DyadicInterval 40),(⟨-23607552,-23607488⟩ : DyadicInterval 40),(⟨762123383333,762123402662⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-512,-64⟩ : DyadicInterval 40),(⟨762123383648,762123403136⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨184731093220,184970541069⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170757581824,170757581888⟩ : DyadicInterval 40),(⟨-202241092288,-202241092224⟩ : DyadicInterval 40),(⟨746531021391,746531040720⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170962567360,170962567424⟩ : DyadicInterval 40),(⟨-202528931968,-202528931904⟩ : DyadicInterval 40),(⟨746490379355,746490398684⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31566364608,-31483510400⟩ : DyadicInterval 40),(⟨777865138816,777906585184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170777358016,170972456576⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-202542821568,-202268856256⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1425_ok : ecellOkT e1425 = true := by decide +kernel
theorem e1425_pos {a z : ℝ} (ha1 : ((688263/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((86139/512000 : ℚ) : ℝ))
    (hz1 : ((3999/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7999/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1425 e1425_ok ha1 ha2 hz1 hz2 hz

-- box ['688263/4096000', '86139/512000', '7999/8000', '1']  interval_lower 151737/1099511627776
noncomputable def e1426 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1284265820028,0,true,170777358016,170777358080⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨914757435524,0,false,-202268856320,-202268856256⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1284493721732,0,true,170972456512,170972456576⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨914529533820,0,false,-202542821568,-202542821504⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1284242725753,0,true,170757585856,170757585920⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨914780529799,0,false,-202241097984,-202241097920⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627776,0,false,0,0⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨1099523431563,0,true,11803712,11803776⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099499823989,0,false,-11803904,-11803840⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511627649,0,false,-128,-64⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1284254268085,0,true,170767467904,170767467968⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨914768987467,0,false,-202254971264,-202254971200⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1284493730214,0,true,170972463744,170972463808⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨914529525338,0,false,-202542831808,-202542831744⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1068390194079,0,false,-31570368000,-31570367936⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨1068470716261,0,false,-31487503360,-31487503296⟩
    { al := (688263/4096000), au := (86139/512000), zl := (7999/8000), zu := 1,
      A := ⟨184754192252,184982093956⟩, Z := ⟨1099374188822,1099511627776⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170777358016,170777358080⟩ : DyadicInterval 40),(⟨-202268856320,-202268856256⟩ : DyadicInterval 40),(⟨746527103087,746527122417⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170972456512,170972456576⟩ : DyadicInterval 40),(⟨-202542821568,-202542821504⟩ : DyadicInterval 40),(⟨746488417116,746488436445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170757585856,170757585920⟩ : DyadicInterval 40),(⟨-202241097984,-202241097920⟩ : DyadicInterval 40),(⟨746531020598,746531039928⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170972456512,170972456576⟩ : DyadicInterval 40),(⟨-202542821568,-202542821504⟩ : DyadicInterval 40),(⟨746488417116,746488436445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      cm := ⟨0,11803787⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨0,0⟩ : DyadicInterval 40),(⟨762123383616,762123402880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d7,d7⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨11803712,11803776⟩ : DyadicInterval 40),(⟨-11803904,-11803840⟩ : DyadicInterval 40),(⟨762123383521,762123402850⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d8,d8⟩,⟨d9,d9⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-128,0⟩ : DyadicInterval 40),(⟨762123383616,762123402944⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d10,d7⟩⟩,
      cp := ⟨184742640309,184982102438⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170767467904,170767467968⟩ : DyadicInterval 40),(⟨-202254971264,-202254971200⟩ : DyadicInterval 40),(⟨746529062688,746529082018⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170972463744,170972463808⟩ : DyadicInterval 40),(⟨-202542831808,-202542831744⟩ : DyadicInterval 40),(⟨746488415709,746488435038⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d13⟩,⟨d14,d14⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31570368000,-31487503296⟩ : DyadicInterval 40),(⟨777867135264,777908586880⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d16⟩⟩,
      lp := ⟨170777358016,170972456576⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-202542821568,-202268856256⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16] }
theorem e1426_ok : ecellOkT e1426 = true := by decide +kernel
theorem e1426_pos {a z : ℝ} (ha1 : ((688263/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((86139/512000 : ℚ) : ℝ))
    (hz1 : ((7999/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1426 e1426_ok ha1 ha2 hz1 hz2 hz

-- box ['86139/512000', '689961/4096000', '999/1000', '7993/8000']  interval_lower 4235217/1099511627776
noncomputable def e1427 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1284493721731,0,true,170972456512,170972456576⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨914529533821,0,false,-202542821568,-202542821504⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1284721623434,0,true,171167520384,171167520448⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨914301632118,0,false,-202816855168,-202816855104⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1284308739637,0,true,170814102592,170814102656⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨914714515915,0,false,-202320445632,-202320445568⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1284559564688,0,true,171028815872,171028815936⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨914463690864,0,false,-202621985472,-202621985408⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099594250491,0,true,82619584,82619648⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099429005061,0,false,-82625856,-82625792⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099606175774,0,true,94543872,94543936⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099417079778,0,false,-94552064,-94552000⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619645,0,false,-8192,-8128⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621568,0,false,-6272,-6208⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1284401226815,0,true,170893279104,170893279168⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨914622028737,0,false,-202431623360,-202431623296⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1284640603271,0,true,171098178176,171098178240⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨914382652281,0,false,-202719427072,-202719427008⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068340754542,0,false,-31621248832,-31621248768⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068421311886,0,false,-31538344192,-31538344128⟩
    { al := (86139/512000), au := (689961/4096000), zl := (999/1000), zu := (7993/8000),
      A := ⟨184982093955,185209995658⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170972456512,170972456576⟩ : DyadicInterval 40),(⟨-202542821568,-202542821504⟩ : DyadicInterval 40),(⟨746488417116,746488436445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171167520384,171167520448⟩ : DyadicInterval 40),(⟨-202816855168,-202816855104⟩ : DyadicInterval 40),(⟨746449682567,746449701896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170814102592,170814102656⟩ : DyadicInterval 40),(⟨-202320445632,-202320445568⟩ : DyadicInterval 40),(⟨746519821270,746519840600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171028815872,171028815936⟩ : DyadicInterval 40),(⟨-202621985472,-202621985408⟩ : DyadicInterval 40),(⟨746477231336,746477250666⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨82622715,94547998⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨82619584,82619648⟩ : DyadicInterval 40),(⟨-82625856,-82625792⟩ : DyadicInterval 40),(⟨762123380479,762123399808⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨94543872,94543936⟩ : DyadicInterval 40),(⟨-94552064,-94552000⟩ : DyadicInterval 40),(⟨762123379517,762123398847⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-8192,-6208⟩ : DyadicInterval 40),(⟨762123386720,762123406976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨184889599039,185128975495⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170893279104,170893279168⟩ : DyadicInterval 40),(⟨-202431623360,-202431623296⟩ : DyadicInterval 40),(⟨746504123859,746504143189⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171098178176,171098178240⟩ : DyadicInterval 40),(⟨-202719427072,-202719427008⟩ : DyadicInterval 40),(⟨746463458469,746463477799⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31621248832,-31538344128⟩ : DyadicInterval 40),(⟨777892555680,777934027296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170972456512,171167520448⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-202816855168,-202542821504⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1427_ok : ecellOkT e1427 = true := by decide +kernel
theorem e1427_pos {a z : ℝ} (ha1 : ((86139/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((689961/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1427 e1427_ok ha1 ha2 hz1 hz2 hz

-- box ['86139/512000', '689961/4096000', '7993/8000', '3997/4000']  interval_lower 1998843/549755813888
noncomputable def e1428 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1284493721731,0,true,170972456512,170972456576⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨914529533821,0,false,-202542821568,-202542821504⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1284721623434,0,true,171167520384,171167520448⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨914301632118,0,false,-202816855168,-202816855104⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1284331862398,0,true,170833898048,170833898112⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨914691393154,0,false,-202348240128,-202348240064⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1284582715938,0,true,171048631872,171048631936⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨914440539614,0,false,-202649821888,-202649821824⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099582447396,0,true,70817280,70817344⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099440808156,0,false,-70821952,-70821888⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099594357526,0,true,82726592,82726656⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099428898026,0,false,-82732864,-82732800⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621551,0,false,-6272,-6208⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623215,0,false,-4608,-4544⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1284412787972,0,true,170903176000,170903176064⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨914610467580,0,false,-202445521664,-202445521600⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1284652178701,0,true,171108085440,171108085504⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨914371076851,0,false,-202733346176,-202733346112⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068336856422,0,false,-31625260736,-31625260672⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068417423606,0,false,-31542345664,-31542345600⟩
    { al := (86139/512000), au := (689961/4096000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨184982093955,185209995658⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170972456512,170972456576⟩ : DyadicInterval 40),(⟨-202542821568,-202542821504⟩ : DyadicInterval 40),(⟨746488417116,746488436445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171167520384,171167520448⟩ : DyadicInterval 40),(⟨-202816855168,-202816855104⟩ : DyadicInterval 40),(⟨746449682567,746449701896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170833898048,170833898112⟩ : DyadicInterval 40),(⟨-202348240128,-202348240064⟩ : DyadicInterval 40),(⟨746515897505,746515916835⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171048631872,171048631936⟩ : DyadicInterval 40),(⟨-202649821888,-202649821824⟩ : DyadicInterval 40),(⟨746473297305,746473316634⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨70819620,82729750⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨70817280,70817344⟩ : DyadicInterval 40),(⟨-70821952,-70821888⟩ : DyadicInterval 40),(⟨762123381326,762123400655⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨82726592,82726656⟩ : DyadicInterval 40),(⟨-82732864,-82732800⟩ : DyadicInterval 40),(⟨762123380462,762123399792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6272,-4544⟩ : DyadicInterval 40),(⟨762123385888,762123406016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨184901160196,185140550925⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170903176000,170903176064⟩ : DyadicInterval 40),(⟨-202445521664,-202445521600⟩ : DyadicInterval 40),(⟨746502161063,746502180393⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171108085440,171108085504⟩ : DyadicInterval 40),(⟨-202733346176,-202733346112⟩ : DyadicInterval 40),(⟨746461490659,746461509988⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31625260736,-31542345600⟩ : DyadicInterval 40),(⟨777894556416,777936033248⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170972456512,171167520448⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-202816855168,-202542821504⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1428_ok : ecellOkT e1428 = true := by decide +kernel
theorem e1428_pos {a z : ℝ} (ha1 : ((86139/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((689961/4096000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1428 e1428_ok ha1 ha2 hz1 hz2 hz

-- box ['689961/4096000', '69081/409600', '999/1000', '7993/8000']  interval_lower 1668255/274877906944
noncomputable def e1429 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1284721623433,0,true,171167520384,171167520448⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨914301632119,0,false,-202816855168,-202816855104⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1284949525136,0,true,171362549696,171362549760⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨914073730416,0,false,-203090957056,-203090956992⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1284536413437,0,true,171008999488,171008999552⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨914486842115,0,false,-202594149760,-202594149696⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1284787266976,0,true,171223699072,171223699136⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨914235988576,0,false,-202895798976,-202895798912⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099594356573,0,true,82725632,82725696⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099428898979,0,false,-82731968,-82731904⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099606297031,0,true,94665152,94665216⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099416958521,0,false,-94673344,-94673280⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619624,0,false,-8192,-8128⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621552,0,false,-6272,-6208⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1284629014562,0,true,171088259520,171088259584⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨914394240990,0,false,-202705492160,-202705492096⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1284868405267,0,true,171293134464,171293134528⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨914154850285,0,false,-202993384768,-202993384704⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068263995560,0,false,-31700250240,-31700250176⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068344656892,0,false,-31617232640,-31617232576⟩
    { al := (689961/4096000), au := (69081/409600), zl := (999/1000), zu := (7993/8000),
      A := ⟨185209995657,185437897360⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171167520384,171167520448⟩ : DyadicInterval 40),(⟨-202816855168,-202816855104⟩ : DyadicInterval 40),(⟨746449682567,746449701896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171362549696,171362549760⟩ : DyadicInterval 40),(⟨-203090957056,-203090956992⟩ : DyadicInterval 40),(⟨746410899365,746410918695⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171008999488,171008999552⟩ : DyadicInterval 40),(⟨-202594149760,-202594149696⟩ : DyadicInterval 40),(⟨746481164882,746481184211⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171223699072,171223699136⟩ : DyadicInterval 40),(⟨-202895798976,-202895798912⟩ : DyadicInterval 40),(⟨746438516677,746438536006⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨82728797,94669255⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨82725632,82725696⟩ : DyadicInterval 40),(⟨-82731968,-82731904⟩ : DyadicInterval 40),(⟨762123380495,762123399824⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨94665152,94665216⟩ : DyadicInterval 40),(⟨-94673344,-94673280⟩ : DyadicInterval 40),(⟨762123379496,762123398826⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-8192,-6208⟩ : DyadicInterval 40),(⟨762123386720,762123406976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨185117386786,185356777491⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171088259520,171088259584⟩ : DyadicInterval 40),(⟨-202705492160,-202705492096⟩ : DyadicInterval 40),(⟨746465428368,746465447698⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171293134464,171293134528⟩ : DyadicInterval 40),(⟨-202993384768,-202993384704⟩ : DyadicInterval 40),(⟨746424709531,746424728861⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31700250240,-31617232576⟩ : DyadicInterval 40),(⟨777931999904,777973528000⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨171167520384,171362549760⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-203090957056,-202816855104⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1429_ok : ecellOkT e1429 = true := by decide +kernel
theorem e1429_pos {a z : ℝ} (ha1 : ((689961/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((69081/409600 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1429 e1429_ok ha1 ha2 hz1 hz2 hz

-- box ['689961/4096000', '69081/409600', '7993/8000', '3997/4000']  interval_lower 6434159/1099511627776
noncomputable def e1430 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1284721623433,0,true,171167520384,171167520448⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨914301632119,0,false,-202816855168,-202816855104⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1284949525136,0,true,171362549696,171362549760⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨914073730416,0,false,-203090957056,-203090956992⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1284559564686,0,true,171028815872,171028815936⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨914463690866,0,false,-202621985472,-202621985408⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1284810446714,0,true,171243536000,171243536064⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨914212808838,0,false,-202923676544,-202923676480⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099582538323,0,true,70908224,70908288⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099440717229,0,false,-70912896,-70912832⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099594463625,0,true,82832704,82832768⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099428791927,0,false,-82838976,-82838912⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621535,0,false,-6272,-6208⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623203,0,false,-4608,-4544⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1284640589963,0,true,171098166784,171098166848⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨914382665589,0,false,-202719411072,-202719411008⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1284879994947,0,true,171303052160,171303052224⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨914143260605,0,false,-203007324480,-203007324416⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068260087838,0,false,-31704272320,-31704272256⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068340759025,0,false,-31621244224,-31621244160⟩
    { al := (689961/4096000), au := (69081/409600), zl := (7993/8000), zu := (3997/4000),
      A := ⟨185209995657,185437897360⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171167520384,171167520448⟩ : DyadicInterval 40),(⟨-202816855168,-202816855104⟩ : DyadicInterval 40),(⟨746449682567,746449701896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171362549696,171362549760⟩ : DyadicInterval 40),(⟨-203090957056,-203090956992⟩ : DyadicInterval 40),(⟨746410899365,746410918695⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171028815872,171028815936⟩ : DyadicInterval 40),(⟨-202621985472,-202621985408⟩ : DyadicInterval 40),(⟨746477231337,746477250666⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171243536000,171243536064⟩ : DyadicInterval 40),(⟨-202923676544,-202923676480⟩ : DyadicInterval 40),(⟨746434572810,746434592139⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨70910547,82835849⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨70908224,70908288⟩ : DyadicInterval 40),(⟨-70912896,-70912832⟩ : DyadicInterval 40),(⟨762123381314,762123400643⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨82832704,82832768⟩ : DyadicInterval 40),(⟨-82838976,-82838912⟩ : DyadicInterval 40),(⟨762123380447,762123399776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6272,-4544⟩ : DyadicInterval 40),(⟨762123385888,762123406016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨185128962187,185368367171⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171098166784,171098166848⟩ : DyadicInterval 40),(⟨-202719411072,-202719411008⟩ : DyadicInterval 40),(⟨746463460734,746463480063⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171303052160,171303052224⟩ : DyadicInterval 40),(⟨-203007324480,-203007324416⟩ : DyadicInterval 40),(⟨746422736830,746422756160⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31704272320,-31621244160⟩ : DyadicInterval 40),(⟨777934005696,777975539040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨171167520384,171362549760⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-203090957056,-202816855104⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1430_ok : ecellOkT e1430 = true := by decide +kernel
theorem e1430_pos {a z : ℝ} (ha1 : ((689961/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((69081/409600 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1430 e1430_ok ha1 ha2 hz1 hz2 hz

-- box ['86139/512000', '689961/4096000', '3997/4000', '1599/1600']  interval_lower 3759807/1099511627776
noncomputable def e1431 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1284493721731,0,true,170972456512,170972456576⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨914529533821,0,false,-202542821568,-202542821504⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1284721623434,0,true,171167520384,171167520448⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨914301632118,0,false,-202816855168,-202816855104⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1284354985160,0,true,170853693184,170853693248⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨914668270392,0,false,-202376035392,-202376035328⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1284605867187,0,true,171068447488,171068447552⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨914417388365,0,false,-202677659008,-202677658944⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570644238,0,true,59014848,59014912⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452611314,0,false,-59018048,-59017984⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099582539214,0,true,70909120,70909184⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099440716338,0,false,-70913728,-70913664⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623202,0,false,-4608,-4544⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624609,0,false,-3200,-3136⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1284424349159,0,true,170913072768,170913072832⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨914598906393,0,false,-202459420160,-202459420096⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1284663754160,0,true,171117992640,171117992704⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨914359501392,0,false,-202747265536,-202747265472⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068332958048,0,false,-31629272832,-31629272768⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068413535073,0,false,-31546347328,-31546347264⟩
    { al := (86139/512000), au := (689961/4096000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨184982093955,185209995658⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170972456512,170972456576⟩ : DyadicInterval 40),(⟨-202542821568,-202542821504⟩ : DyadicInterval 40),(⟨746488417116,746488436445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171167520384,171167520448⟩ : DyadicInterval 40),(⟨-202816855168,-202816855104⟩ : DyadicInterval 40),(⟨746449682567,746449701896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170853693184,170853693248⟩ : DyadicInterval 40),(⟨-202376035392,-202376035328⟩ : DyadicInterval 40),(⟨746511973246,746511992576⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171068447488,171068447552⟩ : DyadicInterval 40),(⟨-202677659008,-202677658944⟩ : DyadicInterval 40),(⟨746469362787,746469382116⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨59016462,70911438⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59014848,59014912⟩ : DyadicInterval 40),(⟨-59018048,-59017984⟩ : DyadicInterval 40),(⟨762123381984,762123401313⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨70909120,70909184⟩ : DyadicInterval 40),(⟨-70913728,-70913664⟩ : DyadicInterval 40),(⟨762123381282,762123400611⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4608,-3136⟩ : DyadicInterval 40),(⟨762123385184,762123405184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨184912721383,185152126384⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170913072768,170913072832⟩ : DyadicInterval 40),(⟨-202459420160,-202459420096⟩ : DyadicInterval 40),(⟨746500198167,746500217496⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171117992640,171117992704⟩ : DyadicInterval 40),(⟨-202747265536,-202747265472⟩ : DyadicInterval 40),(⟨746459522736,746459542065⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31629272832,-31546347264⟩ : DyadicInterval 40),(⟨777896557248,777938039296⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170972456512,171167520448⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-202816855168,-202542821504⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1431_ok : ecellOkT e1431 = true := by decide +kernel
theorem e1431_pos {a z : ℝ} (ha1 : ((86139/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((689961/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1431 e1431_ok ha1 ha2 hz1 hz2 hz

-- box ['86139/512000', '689961/4096000', '1599/1600', '1999/2000']  interval_lower 3521961/1099511627776
noncomputable def e1432 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1284493721731,0,true,170972456512,170972456576⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨914529533821,0,false,-202542821568,-202542821504⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1284721623434,0,true,171167520384,171167520448⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨914301632118,0,false,-202816855168,-202816855104⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1284378107922,0,true,170873488000,170873488064⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨914645147630,0,false,-202403831360,-202403831296⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1284629018437,0,true,171088262784,171088262848⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨914394237115,0,false,-202705496832,-202705496768⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558841018,0,true,47212224,47212288⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099464414534,0,false,-47214272,-47214208⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570720839,0,true,59091456,59091520⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452534713,0,false,-59094656,-59094592⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624600,0,false,-3200,-3136⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625749,0,false,-2048,-1984⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1284435910377,0,true,170922969536,170922969600⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨914587345175,0,false,-202473318912,-202473318848⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1284675329651,0,true,171127899776,171127899840⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨914347925901,0,false,-202761185088,-202761185024⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068329059419,0,false,-31633285248,-31633285184⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068409646286,0,false,-31550349312,-31550349248⟩
    { al := (86139/512000), au := (689961/4096000), zl := (1599/1600), zu := (1999/2000),
      A := ⟨184982093955,185209995658⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170972456512,170972456576⟩ : DyadicInterval 40),(⟨-202542821568,-202542821504⟩ : DyadicInterval 40),(⟨746488417116,746488436445⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171167520384,171167520448⟩ : DyadicInterval 40),(⟨-202816855168,-202816855104⟩ : DyadicInterval 40),(⟨746449682567,746449701896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170873488000,170873488064⟩ : DyadicInterval 40),(⟨-202403831360,-202403831296⟩ : DyadicInterval 40),(⟨746508048465,746508067795⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171088262784,171088262848⟩ : DyadicInterval 40),(⟨-202705496832,-202705496768⟩ : DyadicInterval 40),(⟨746465427745,746465447075⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨47213242,59093063⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨47212224,47212288⟩ : DyadicInterval 40),(⟨-47214272,-47214208⟩ : DyadicInterval 40),(⟨762123382548,762123401877⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59091456,59091520⟩ : DyadicInterval 40),(⟨-59094656,-59094592⟩ : DyadicInterval 40),(⟨762123381975,762123401305⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3200,-1984⟩ : DyadicInterval 40),(⟨762123384608,762123404480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨184924282601,185163701875⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨170922969536,170922969600⟩ : DyadicInterval 40),(⟨-202473318912,-202473318848⟩ : DyadicInterval 40),(⟨746498235122,746498254451⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171127899776,171127899840⟩ : DyadicInterval 40),(⟨-202761185088,-202761185024⟩ : DyadicInterval 40),(⟨746457554674,746457574003⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31633285248,-31550349248⟩ : DyadicInterval 40),(⟨777898558240,777940045504⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨170972456512,171167520448⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-202816855168,-202542821504⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1432_ok : ecellOkT e1432 = true := by decide +kernel
theorem e1432_pos {a z : ℝ} (ha1 : ((86139/512000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((689961/4096000 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1432 e1432_ok ha1 ha2 hz1 hz2 hz

-- box ['689961/4096000', '69081/409600', '3997/4000', '1599/1600']  interval_lower 193613/34359738368
noncomputable def e1433 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1284721623433,0,true,171167520384,171167520448⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨914301632119,0,false,-202816855168,-202816855104⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1284949525136,0,true,171362549696,171362549760⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨914073730416,0,false,-203090957056,-203090956992⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1284582715936,0,true,171048631872,171048631936⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨914440539616,0,false,-202649821888,-202649821824⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1284833626451,0,true,171263372480,171263372544⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨914189629101,0,false,-202951554880,-202951554816⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570720011,0,true,59090624,59090688⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452535541,0,false,-59093824,-59093760⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099582630157,0,true,71000064,71000128⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099440625395,0,false,-71004736,-71004672⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623190,0,false,-4608,-4544⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624601,0,false,-3200,-3136⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1284652165393,0,true,171108074048,171108074112⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨914371090159,0,false,-202733330176,-202733330112⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1284891584648,0,true,171312969792,171312969856⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨914131670904,0,false,-203021264384,-203021264320⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068256179864,0,false,-31708294592,-31708294528⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068336860904,0,false,-31625256064,-31625256000⟩
    { al := (689961/4096000), au := (69081/409600), zl := (3997/4000), zu := (1599/1600),
      A := ⟨185209995657,185437897360⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171167520384,171167520448⟩ : DyadicInterval 40),(⟨-202816855168,-202816855104⟩ : DyadicInterval 40),(⟨746449682567,746449701896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171362549696,171362549760⟩ : DyadicInterval 40),(⟨-203090957056,-203090956992⟩ : DyadicInterval 40),(⟨746410899365,746410918695⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171048631872,171048631936⟩ : DyadicInterval 40),(⟨-202649821888,-202649821824⟩ : DyadicInterval 40),(⟨746473297305,746473316634⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171263372480,171263372544⟩ : DyadicInterval 40),(⟨-202951554880,-202951554816⟩ : DyadicInterval 40),(⟨746430628519,746430647848⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨59092235,71002381⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59090624,59090688⟩ : DyadicInterval 40),(⟨-59093824,-59093760⟩ : DyadicInterval 40),(⟨762123381976,762123401305⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨71000064,71000128⟩ : DyadicInterval 40),(⟨-71004736,-71004672⟩ : DyadicInterval 40),(⟨762123381302,762123400632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4608,-3136⟩ : DyadicInterval 40),(⟨762123385184,762123405184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨185140537617,185379956872⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171108074048,171108074112⟩ : DyadicInterval 40),(⟨-202733330176,-202733330112⟩ : DyadicInterval 40),(⟨746461492923,746461512253⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171312969792,171312969856⟩ : DyadicInterval 40),(⟨-203021264384,-203021264320⟩ : DyadicInterval 40),(⟨746420763991,746420783320⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31708294592,-31625256000⟩ : DyadicInterval 40),(⟨777936011616,777977550176⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨171167520384,171362549760⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-203090957056,-202816855104⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1433_ok : ecellOkT e1433 = true := by decide +kernel
theorem e1433_pos {a z : ℝ} (ha1 : ((689961/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((69081/409600 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1433 e1433_ok ha1 ha2 hz1 hz2 hz

-- box ['689961/4096000', '69081/409600', '1599/1600', '1999/2000']  interval_lower 5956781/1099511627776
noncomputable def e1434 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1284721623433,0,true,171167520384,171167520448⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨914301632119,0,false,-202816855168,-202816855104⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1284949525136,0,true,171362549696,171362549760⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨914073730416,0,false,-203090957056,-203090956992⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1284605867185,0,true,171068447488,171068447552⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨914417388367,0,false,-202677659008,-202677658944⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1284856806188,0,true,171283208640,171283208704⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨914166449364,0,false,-202979433920,-202979433856⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099558901637,0,true,47272832,47272896⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099464353915,0,false,-47274880,-47274816⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570796626,0,true,59167232,59167296⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452458926,0,false,-59170496,-59170432⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624591,0,false,-3200,-3136⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511625744,0,false,-2048,-1984⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1284663740851,0,true,171117981248,171117981312⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨914359514701,0,false,-202747249536,-202747249472⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1284903174381,0,true,171322887360,171322887424⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨914120081171,0,false,-203035204544,-203035204480⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068252271636,0,false,-31712317184,-31712317120⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068332962531,0,false,-31629268224,-31629268160⟩
    { al := (689961/4096000), au := (69081/409600), zl := (1599/1600), zu := (1999/2000),
      A := ⟨185209995657,185437897360⟩, Z := ⟨1098824433008,1098961871963⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171167520384,171167520448⟩ : DyadicInterval 40),(⟨-202816855168,-202816855104⟩ : DyadicInterval 40),(⟨746449682567,746449701896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171362549696,171362549760⟩ : DyadicInterval 40),(⟨-203090957056,-203090956992⟩ : DyadicInterval 40),(⟨746410899365,746410918695⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171068447488,171068447552⟩ : DyadicInterval 40),(⟨-202677659008,-202677658944⟩ : DyadicInterval 40),(⟨746469362787,746469382117⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171283208640,171283208704⟩ : DyadicInterval 40),(⟨-202979433920,-202979433856⟩ : DyadicInterval 40),(⟨746426683701,746426703031⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨47273861,59168850⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨47272832,47272896⟩ : DyadicInterval 40),(⟨-47274880,-47274816⟩ : DyadicInterval 40),(⟨762123382543,762123401872⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59167232,59167296⟩ : DyadicInterval 40),(⟨-59170496,-59170432⟩ : DyadicInterval 40),(⟨762123381999,762123401328⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-3200,-1984⟩ : DyadicInterval 40),(⟨762123384608,762123404480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨185152113075,185391546605⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171117981248,171117981312⟩ : DyadicInterval 40),(⟨-202747249536,-202747249472⟩ : DyadicInterval 40),(⟨746459525001,746459544330⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171322887360,171322887424⟩ : DyadicInterval 40),(⟨-203035204544,-203035204480⟩ : DyadicInterval 40),(⟨746418791038,746418810368⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31712317184,-31629268160⟩ : DyadicInterval 40),(⟨777938017696,777979561472⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨171167520384,171362549760⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-203090957056,-202816855104⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1434_ok : ecellOkT e1434 = true := by decide +kernel
theorem e1434_pos {a z : ℝ} (ha1 : ((689961/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((69081/409600 : ℚ) : ℝ))
    (hz1 : ((1599/1600 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1999/2000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1434 e1434_ok ha1 ha2 hz1 hz2 hz

-- box ['69081/409600', '691659/4096000', '999/1000', '7993/8000']  interval_lower 9123319/1099511627776
noncomputable def e1435 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1284949525135,0,true,171362549696,171362549760⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨914073730417,0,false,-203090957056,-203090956992⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1285177426838,0,true,171557544384,171557544448⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨913845828714,0,false,-203365127296,-203365127232⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1284764087237,0,true,171203861888,171203861952⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨914259168315,0,false,-202867922048,-202867921984⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1285014969264,0,true,171418547776,171418547840⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨914008286288,0,false,-203169680640,-203169680576⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099594462670,0,true,82831744,82831808⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099428792882,0,false,-82838016,-82837952⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099606418305,0,true,94786432,94786496⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099416837247,0,false,-94794624,-94794560⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619603,0,false,-8192,-8128⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621536,0,false,-6272,-6208⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1284856802315,0,true,171283205312,171283205376⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨914166453237,0,false,-202979429248,-202979429184⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1285096207265,0,true,171488056192,171488056256⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨913927048287,0,false,-203267410688,-203267410624⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068187142182,0,false,-31779354496,-31779354432⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068267907513,0,false,-31696223872,-31696223808⟩
    { al := (69081/409600), au := (691659/4096000), zl := (999/1000), zu := (7993/8000),
      A := ⟨185437897359,185665799062⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171362549696,171362549760⟩ : DyadicInterval 40),(⟨-203090957056,-203090956992⟩ : DyadicInterval 40),(⟨746410899365,746410918695⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171557544384,171557544448⟩ : DyadicInterval 40),(⟨-203365127296,-203365127232⟩ : DyadicInterval 40),(⟨746372067565,746372086894⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171203861888,171203861952⟩ : DyadicInterval 40),(⟨-202867922048,-202867921984⟩ : DyadicInterval 40),(⟨746442459953,746442479283⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171418547776,171418547840⟩ : DyadicInterval 40),(⟨-203169680640,-203169680576⟩ : DyadicInterval 40),(⟨746399753441,746399772770⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨82834894,94790529⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨82831744,82831808⟩ : DyadicInterval 40),(⟨-82838016,-82837952⟩ : DyadicInterval 40),(⟨762123380447,762123399776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨94786432,94786496⟩ : DyadicInterval 40),(⟨-94794624,-94794560⟩ : DyadicInterval 40),(⟨762123379475,762123398805⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-8192,-6208⟩ : DyadicInterval 40),(⟨762123386720,762123406976⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨185345174539,185584579489⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171283205312,171283205376⟩ : DyadicInterval 40),(⟨-202979429248,-202979429184⟩ : DyadicInterval 40),(⟨746426684362,746426703692⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171488056192,171488056256⟩ : DyadicInterval 40),(⟨-203267410688,-203267410624⟩ : DyadicInterval 40),(⟨746385911993,746385931322⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31779354496,-31696223808⟩ : DyadicInterval 40),(⟨777971495520,778013080128⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨171362549696,171557544448⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-203365127296,-203090956992⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1435_ok : ecellOkT e1435 = true := by decide +kernel
theorem e1435_pos {a z : ℝ} (ha1 : ((69081/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((691659/4096000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1435 e1435_ok ha1 ha2 hz1 hz2 hz

-- box ['69081/409600', '691659/4096000', '7993/8000', '3997/4000']  interval_lower 2220945/274877906944
noncomputable def e1436 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1284949525135,0,true,171362549696,171362549760⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨914073730417,0,false,-203090957056,-203090956992⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1285177426838,0,true,171557544384,171557544448⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨913845828714,0,false,-203365127296,-203365127232⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1284787266974,0,true,171223699072,171223699136⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨914235988578,0,false,-202895798976,-202895798912⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1285038177489,0,true,171438405568,171438405632⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨913985078063,0,false,-203197599488,-203197599424⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099582629265,0,true,70999168,70999232⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099440626287,0,false,-71003840,-71003776⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099594569741,0,true,82938816,82938880⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099428685811,0,false,-82945152,-82945088⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621519,0,false,-6272,-6208⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623192,0,false,-4608,-4544⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1284868391953,0,true,171293123072,171293123136⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨914154863599,0,false,-202993368768,-202993368704⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1285107811186,0,true,171497984320,171497984384⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨913915444366,0,false,-203281371072,-203281371008⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068183224850,0,false,-31783386752,-31783386688⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068264000050,0,false,-31700245632,-31700245568⟩
    { al := (69081/409600), au := (691659/4096000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨185437897359,185665799062⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171362549696,171362549760⟩ : DyadicInterval 40),(⟨-203090957056,-203090956992⟩ : DyadicInterval 40),(⟨746410899365,746410918695⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171557544384,171557544448⟩ : DyadicInterval 40),(⟨-203365127296,-203365127232⟩ : DyadicInterval 40),(⟨746372067565,746372086894⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171223699072,171223699136⟩ : DyadicInterval 40),(⟨-202895798976,-202895798912⟩ : DyadicInterval 40),(⟨746438516677,746438536006⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171438405568,171438405632⟩ : DyadicInterval 40),(⟨-203197599488,-203197599424⟩ : DyadicInterval 40),(⟨746395799804,746395819134⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨71001489,82941965⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨70999168,70999232⟩ : DyadicInterval 40),(⟨-71003840,-71003776⟩ : DyadicInterval 40),(⟨762123381302,762123400632⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨82938816,82938880⟩ : DyadicInterval 40),(⟨-82945152,-82945088⟩ : DyadicInterval 40),(⟨762123380463,762123399792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6272,-4544⟩ : DyadicInterval 40),(⟨762123385888,762123406016⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨185356764177,185596183410⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171293123072,171293123136⟩ : DyadicInterval 40),(⟨-202993368768,-202993368704⟩ : DyadicInterval 40),(⟨746424711803,746424731132⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171497984320,171497984384⟩ : DyadicInterval 40),(⟨-203281371072,-203281371008⟩ : DyadicInterval 40),(⟨746383934416,746383953746⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31783386752,-31700245568⟩ : DyadicInterval 40),(⟨777973506400,778015096256⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨171362549696,171557544448⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-203365127296,-203090956992⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1436_ok : ecellOkT e1436 = true := by decide +kernel
theorem e1436_pos {a z : ℝ} (ha1 : ((69081/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((691659/4096000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1436 e1436_ok ha1 ha2 hz1 hz2 hz

-- box ['691659/4096000', '173127/1024000', '999/1000', '7993/8000']  interval_lower 5793341/549755813888
noncomputable def e1437 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1285177426837,0,true,171557544384,171557544448⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨913845828715,0,false,-203365127296,-203365127232⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1285405328540,0,true,171752504512,171752504576⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨913617927012,0,false,-203639365952,-203639365888⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1284991761037,0,true,171398689728,171398689792⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨914031494515,0,false,-203141762496,-203141762432⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1285242671552,0,true,171613361984,171613362048⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨913780584000,0,false,-203443630592,-203443630528⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099594568785,0,true,82937856,82937920⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099428686767,0,false,-82944192,-82944128⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099606539598,0,true,94907712,94907776⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099416715954,0,false,-94915968,-94915904⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511619583,0,false,-8256,-8192⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621520,0,false,-6272,-6208⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1285084590065,0,true,171478116608,171478116672⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨913938665487,0,false,-203253434560,-203253434496⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1285324009263,0,true,171682943360,171682943424⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨913699246289,0,false,-203541504960,-203541504896⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068110194410,0,false,-31858561600,-31858561536⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068191063753,0,false,-31775317952,-31775317888⟩
    { al := (691659/4096000), au := (173127/1024000), zl := (999/1000), zu := (7993/8000),
      A := ⟨185665799061,185893700764⟩, Z := ⟨1098412116148,1098549555102⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171557544384,171557544448⟩ : DyadicInterval 40),(⟨-203365127296,-203365127232⟩ : DyadicInterval 40),(⟨746372067565,746372086894⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171752504512,171752504576⟩ : DyadicInterval 40),(⟨-203639365952,-203639365888⟩ : DyadicInterval 40),(⟨746333187143,746333206473⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171398689728,171398689792⟩ : DyadicInterval 40),(⟨-203141762496,-203141762432⟩ : DyadicInterval 40),(⟨746403706511,746403725841⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171613361984,171613362048⟩ : DyadicInterval 40),(⟨-203443630592,-203443630528⟩ : DyadicInterval 40),(⟨746360941672,746360961001⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨82941009,94911822⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨82937856,82937920⟩ : DyadicInterval 40),(⟨-82944192,-82944128⟩ : DyadicInterval 40),(⟨762123380463,762123399792⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨94907712,94907776⟩ : DyadicInterval 40),(⟨-94915968,-94915904⟩ : DyadicInterval 40),(⟨762123379486,762123398816⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-8256,-6208⟩ : DyadicInterval 40),(⟨762123386720,762123407008⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨185572962289,185812381487⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171478116608,171478116672⟩ : DyadicInterval 40),(⟨-203253434560,-203253434496⟩ : DyadicInterval 40),(⟨746387891732,746387911061⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171682943360,171682943424⟩ : DyadicInterval 40),(⟨-203541504960,-203541504896⟩ : DyadicInterval 40),(⟨746347065896,746347085225⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31858561600,-31775317888⟩ : DyadicInterval 40),(⟨778011042560,778052683680⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨171557544384,171752504576⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-203639365952,-203365127232⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1437_ok : ecellOkT e1437 = true := by decide +kernel
theorem e1437_pos {a z : ℝ} (ha1 : ((691659/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((173127/1024000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((7993/8000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1437 e1437_ok ha1 ha2 hz1 hz2 hz

-- box ['691659/4096000', '173127/1024000', '7993/8000', '3997/4000']  interval_lower 5673027/549755813888
noncomputable def e1438 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1285177426837,0,true,171557544384,171557544448⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨913845828715,0,false,-203365127296,-203365127232⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1285405328540,0,true,171752504512,171752504576⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨913617927012,0,false,-203639365952,-203639365888⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1285014969262,0,true,171418547776,171418547840⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨914008286290,0,false,-203169680640,-203169680576⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1285265908265,0,true,171633240576,171633240640⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨913757347287,0,false,-203471590656,-203471590592⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099582720221,0,true,71090112,71090176⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099440535331,0,false,-71094784,-71094720⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099594675874,0,true,83044928,83044992⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099428579678,0,false,-83051264,-83051200⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511621503,0,false,-6336,-6272⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623180,0,false,-4608,-4544⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1285096193946,0,true,171488044800,171488044864⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨913927061606,0,false,-203267394688,-203267394624⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1285335627424,0,true,171692881856,171692881920⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨913687628128,0,false,-203555485952,-203555485888⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068106267457,0,false,-31862604032,-31862603968⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068187146679,0,false,-31779349888,-31779349824⟩
    { al := (691659/4096000), au := (173127/1024000), zl := (7993/8000), zu := (3997/4000),
      A := ⟨185665799061,185893700764⟩, Z := ⟨1098549555101,1098686994056⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171557544384,171557544448⟩ : DyadicInterval 40),(⟨-203365127296,-203365127232⟩ : DyadicInterval 40),(⟨746372067565,746372086894⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171752504512,171752504576⟩ : DyadicInterval 40),(⟨-203639365952,-203639365888⟩ : DyadicInterval 40),(⟨746333187143,746333206473⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171418547776,171418547840⟩ : DyadicInterval 40),(⟨-203169680640,-203169680576⟩ : DyadicInterval 40),(⟨746399753442,746399772771⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171633240576,171633240640⟩ : DyadicInterval 40),(⟨-203471590656,-203471590592⟩ : DyadicInterval 40),(⟨746356978251,746356997581⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨71092445,83048098⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨71090112,71090176⟩ : DyadicInterval 40),(⟨-71094784,-71094720⟩ : DyadicInterval 40),(⟨762123381291,762123400620⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨83044928,83044992⟩ : DyadicInterval 40),(⟨-83051264,-83051200⟩ : DyadicInterval 40),(⟨762123380446,762123399776⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-6336,-4544⟩ : DyadicInterval 40),(⟨762123385888,762123406048⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨185584566170,185823999648⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171488044800,171488044864⟩ : DyadicInterval 40),(⟨-203267394688,-203267394624⟩ : DyadicInterval 40),(⟨746385914270,746385933600⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171692881856,171692881920⟩ : DyadicInterval 40),(⟨-203555485952,-203555485888⟩ : DyadicInterval 40),(⟨746345083442,746345102772⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31862604032,-31779349824⟩ : DyadicInterval 40),(⟨778013058528,778054704896⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨171557544384,171752504576⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-203639365952,-203365127232⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1438_ok : ecellOkT e1438 = true := by decide +kernel
theorem e1438_pos {a z : ℝ} (ha1 : ((691659/4096000 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((173127/1024000 : ℚ) : ℝ))
    (hz1 : ((7993/8000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((3997/4000 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1438 e1438_ok ha1 ha2 hz1 hz2 hz

-- box ['69081/409600', '691659/4096000', '3997/4000', '1599/1600']  interval_lower 4322073/549755813888
noncomputable def e1439 : ECellT :=
  let d0 : CorrectionIntegerLogTableKernel.Datum := ⟨2199023255552,1,true,762123383616,762123402880⟩
    let d1 : CorrectionIntegerLogTableKernel.Datum := ⟨1284949525135,0,true,171362549696,171362549760⟩
    let d2 : CorrectionIntegerLogTableKernel.Datum := ⟨914073730417,0,false,-203090957056,-203090956992⟩
    let d3 : CorrectionIntegerLogTableKernel.Datum := ⟨1285177426838,0,true,171557544384,171557544448⟩
    let d4 : CorrectionIntegerLogTableKernel.Datum := ⟨913845828714,0,false,-203365127296,-203365127232⟩
    let d5 : CorrectionIntegerLogTableKernel.Datum := ⟨1284810446711,0,true,171243536000,171243536064⟩
    let d6 : CorrectionIntegerLogTableKernel.Datum := ⟨914212808841,0,false,-202923676544,-202923676480⟩
    let d7 : CorrectionIntegerLogTableKernel.Datum := ⟨1285061385714,0,true,171458262912,171458262976⟩
    let d8 : CorrectionIntegerLogTableKernel.Datum := ⟨913961869838,0,false,-203225518976,-203225518912⟩
    let d9 : CorrectionIntegerLogTableKernel.Datum := ⟨1099570795797,0,true,59166400,59166464⟩
    let d10 : CorrectionIntegerLogTableKernel.Datum := ⟨1099452459755,0,false,-59169664,-59169600⟩
    let d11 : CorrectionIntegerLogTableKernel.Datum := ⟨1099582721114,0,true,71091008,71091072⟩
    let d12 : CorrectionIntegerLogTableKernel.Datum := ⟨1099440534438,0,false,-71095680,-71095616⟩
    let d13 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511623179,0,false,-4608,-4544⟩
    let d14 : CorrectionIntegerLogTableKernel.Datum := ⟨1099511624592,0,false,-3200,-3136⟩
    let d15 : CorrectionIntegerLogTableKernel.Datum := ⟨1284879981634,0,true,171303040768,171303040832⟩
    let d16 : CorrectionIntegerLogTableKernel.Datum := ⟨914143273918,0,false,-203007308480,-203007308416⟩
    let d17 : CorrectionIntegerLogTableKernel.Datum := ⟨1285119415133,0,true,171507912320,171507912384⟩
    let d18 : CorrectionIntegerLogTableKernel.Datum := ⟨913903840419,0,false,-203295331584,-203295331520⟩
    let d19 : CorrectionIntegerLogTableKernel.Datum := ⟨1068179307264,0,false,-31787419200,-31787419136⟩
    let d20 : CorrectionIntegerLogTableKernel.Datum := ⟨1068260092328,0,false,-31704267648,-31704267584⟩
    { al := (69081/409600), au := (691659/4096000), zl := (3997/4000), zu := (1599/1600),
      A := ⟨185437897359,185665799062⟩, Z := ⟨1098686994055,1098824433009⟩,
      eAl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171362549696,171362549760⟩ : DyadicInterval 40),(⟨-203090957056,-203090956992⟩ : DyadicInterval 40),(⟨746410899365,746410918695⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d1,d1⟩,⟨d2,d2⟩⟩,
      eAh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171557544384,171557544448⟩ : DyadicInterval 40),(⟨-203365127296,-203365127232⟩ : DyadicInterval 40),(⟨746372067565,746372086894⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d3,d3⟩,⟨d4,d4⟩⟩,
      eBl := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171243536000,171243536064⟩ : DyadicInterval 40),(⟨-202923676544,-202923676480⟩ : DyadicInterval 40),(⟨746434572811,746434592140⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d5,d5⟩,⟨d6,d6⟩⟩,
      eBh := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171458262912,171458262976⟩ : DyadicInterval 40),(⟨-203225518976,-203225518912⟩ : DyadicInterval 40),(⟨746391845688,746391865017⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d7,d7⟩,⟨d8,d8⟩⟩,
      cm := ⟨59168021,71093338⟩,
      ecmL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨59166400,59166464⟩ : DyadicInterval 40),(⟨-59169664,-59169600⟩ : DyadicInterval 40),(⟨762123381999,762123401329⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d9,d9⟩,⟨d10,d10⟩⟩,
      ecmH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨71091008,71091072⟩ : DyadicInterval 40),(⟨-71095680,-71095616⟩ : DyadicInterval 40),(⟨762123381291,762123400620⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d11,d11⟩,⟨d12,d12⟩⟩,
      bcm := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-4608,-3136⟩ : DyadicInterval 40),(⟨762123385184,762123405184⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d13,d14⟩⟩,
      cp := ⟨185368353858,185607787357⟩,
      ecpL := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171303040768,171303040832⟩ : DyadicInterval 40),(⟨-203007308480,-203007308416⟩ : DyadicInterval 40),(⟨746422739101,746422758431⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d15,d15⟩,⟨d16,d16⟩⟩,
      ecpH := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨171507912320,171507912384⟩ : DyadicInterval 40),(⟨-203295331584,-203295331520⟩ : DyadicInterval 40),(⟨746381956711,746381976040⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d17,d17⟩,⟨d18,d18⟩⟩,
      bcp := ⟨(⟨762123383616,762123402880⟩ : DyadicInterval 40),(⟨-31787419200,-31704267584⟩ : DyadicInterval 40),(⟨777975517408,778017112480⟩ : DyadicInterval 40),⟨d0,d0⟩,⟨d19,d20⟩⟩,
      lp := ⟨171362549696,171557544448⟩, lpw := ⟨d1,d3⟩,
      lm := ⟨-203365127296,-203090956992⟩, lmw := ⟨d4,d2⟩,
      table := [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20] }
theorem e1439_ok : ecellOkT e1439 = true := by decide +kernel
theorem e1439_pos {a z : ℝ} (ha1 : ((69081/409600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((691659/4096000 : ℚ) : ℝ))
    (hz1 : ((3997/4000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1599/1600 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  ecellOkT_sound e1439 e1439_ok ha1 ha2 hz1 hz2 hz

end CKLaneC2R.EpCells.B023

end


