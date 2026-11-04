-- Prove2me | Definitions.Def_OAIQ098E183
-- name    : OAIQ098E183
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T05:14:11.264213+00:00
-- url     : https://prove2.me/theorems/452f87b5-68c8-44e5-94d2-3501cd5bf334
-- title:
--   Definitions bundle OAIQ098E183 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1997 declarations of OpenAI's Lean: 1997 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.hm21_1_1_6.s1_3`, `OAI.SharpPlanar.CachedData.hm21_1_1_6.s1_4`, `OAI.SharpPlanar.CachedData.hm21_1_1_6.s1_5`, `OAI.SharpPlanar.CachedData.hm21_1_1_6.s1_6`, `OAI.SharpPlanar.CachedData.hm21_1_1_6.s1_7`, `OAI.SharpPlanar.CachedData.hm21_1_1_6.s1_8`, `OAI.SharpPlanar.CachedData.hm21_1_1_6.s1_9`, `OAI.SharpPlanar.CachedData.hm21_1_1_6.s2`, `OAI.SharpPlanar.CachedData.hm21_1_1_6.s2_0`, `OAI.SharpPlanar.CachedData.hm21_1_1_6.s2_1`, `OAI.SharpPlanar.CachedData.hm21_1_1_6.s2_10`, `OAI.SharpPlanar.CachedData.hm21_1_1_6.s2_11`, `OAI.SharpPlanar.CachedData.hm21_1_1_6.s2_12`, `OAI.SharpPlanar.CachedData.hm21_1_1_6.s2_13`, `OAI.SharpPlanar.CachedData.hm21_1_1_6.s2_14`, `OAI.SharpPlanar.CachedData.hm21_1_1_6.s2_15`, `OAI.SharpPlanar.CachedData.hm21_1_1_6.s2_2`, `OAI.SharpPlanar.CachedData.hm21_1_1_6.s2_3`, `OAI.SharpPlanar.CachedData.hm21_1_1_6.s2_4`, `OAI.SharpPlanar.CachedData.hm21_1_1_6.s2_5`, `OAI.SharpPlanar.CachedData.hm21_1_1_6.s2_6`, `OAI.SharpPlanar.CachedData.hm21_1_1_6.s2_7`, `OAI.SharpPlanar.CachedData.hm21_1_1_6.s2_8`, `OAI.SharpPlanar.CachedData.hm21_1_1_6.s2_9`, `OAI.SharpPlanar.CachedData.hm21_1_1_6.s3`, `OAI.SharpPlanar.CachedData.hm21_1_1_6.s3_0`, `OAI.SharpPlanar.CachedData.hm21_1_1_6.s3_1`, `OAI.SharpPlanar.CachedData.hm21_1_1_6.s3_10`, `OAI.SharpPlanar.CachedData.hm21_1_1_6.s3_11`, `OAI.SharpPlanar.CachedData.hm21_1_1_6.s3_12`, `OAI.SharpPlanar.CachedData.hm21_1_1_6.s3_13`, `OAI.SharpPlanar.CachedData.hm21_1_1_6.s3_14`, `OAI.SharpPlanar.CachedData.hm21_1_1_6.s3_15`, `OAI.SharpPlanar.CachedData.hm21_1_1_6.s3_2`, `OAI.SharpPlanar.CachedData.hm21_1_1_6.s3_3`, `OAI.SharpPlanar.CachedData.hm21_1_1_6.s3_4`, `OAI.SharpPlanar.CachedData.hm21_1_1_6.s3_5`, `OAI.SharpPlanar.CachedData.hm21_1_1_6.s3_6`, `OAI.SharpPlanar.CachedData.hm21_1_1_6.s3_7`, `OAI.SharpPlanar.CachedData.hm21_1_1_6.s3_8` and 1957 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_LowBlock21_10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/LowBlock21_10.lean), [`PlanarPacking_Certificate_LowBlock21_11`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/LowBlock21_11.lean), [`PlanarPacking_Certificate_LowBlock24_0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/LowBlock24_0.lean), [`PlanarPacking_Certificate_LowBlock24_1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/LowBlock24_1.lean), [`PlanarPacking_Certificate_LowBlock24_10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/LowBlock24_10.lean), [`PlanarPacking_Certificate_LowBlock24_11`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/LowBlock24_11.lean), [`PlanarPacking_Certificate_TableMoments13`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TableMoments13.lean).
--
--   **Imports.** It imports the bundle `OAIQ098E017` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098E240`; the statements `OAI.SharpPlanar.CachedData.hm24_0_0_5.realContains_e`, `OAI.SharpPlanar.CachedData.hm24_0_1_2.realContains_e` and `OAI.SharpPlanar.CachedData.hm24_0_1_3.realContains_e`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098E017

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock21_10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid
namespace hm21_1_1_6
noncomputable def s1_3 : CBox := ⟨⟨(-121),121⟩,⟨(-121),121⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-180),180⟩,⟨(-180),180⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-250),250⟩,⟨(-250),250⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-333),333⟩,⟨(-333),333⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-413),413⟩,⟨(-413),413⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-473),473⟩,⟨(-473),473⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-496),496⟩,⟨(-496),496⟩⟩
noncomputable def s2_0 : CBox := ⟨⟨(-20717),(-20696)⟩,⟨11378,11398⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-29993),(-29958)⟩,⟨23634,23666⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-10238),(-10192)⟩,⟨15383,15428⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-596),(-539)⟩,⟨4010,4071⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨145,215⟩,⟨380,453⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-17),72⟩,⟨(-32),57⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-52),74⟩,⟨(-68),58⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-86),91⟩,⟨(-91),86⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-96),96⟩,⟨(-96),96⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-108),108⟩,⟨(-108),108⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-102),102⟩,⟨(-102),102⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-119),119⟩,⟨(-119),119⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-104),104⟩,⟨(-104),104⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-82),82⟩,⟨(-82),82⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-54),54⟩,⟨(-54),54⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-24),24⟩,⟨(-24),24⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨(-2390248537899039),(-2390248537898991)⟩,⟨5180331175311652,5180331175311699⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-2335579043486524),(-2335579043486452)⟩,⟨11248921398674865,11248921398674937⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨2099644201371888,2099644201371935⟩,⟨8403524135225993,8403524135226042⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨2940259214053950,2940259214053983⟩,⟨2311207484191434,2311207484191466⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨1014981540788641,1014981540788676⟩,⟨(-188293750616836),(-188293750616803)⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨72376013256826,72376013256865⟩,⟨(-180401275100426),(-180401275100386)⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-17630733641923),(-17630733641880)⟩,⟨(-19541974025823),(-19541974025781)⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨(-2545566913819),(-2545566913770)⟩,⟨893957911122,893957911167⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨(-10798036759),(-10798036706)⟩,⟨222682278364,222682278416⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨14372921822,14372921882⟩,⟨7321714365,7321714422⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨937567753,937567813⟩,⟨(-635355803),(-635355745)⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨2741864,2741915⟩,⟨(-86661140),(-86661087)⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-5566252),(-5566202)⟩,⟨(-5930715),(-5930663)⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-1005854),(-1005812)⟩,⟨(-219126),(-219085)⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-177362),(-177329)⟩,⟨34421,34454⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-29330),(-29308)⟩,⟨12241,12265⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨(-14944249560102761794895),(-14944249560101986812672)⟩,⟨24943869966648132857875,24943869966648907840583⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-21234722199063663207151),(-21234722199061484558045)⟩,⟨65837076001970436667224,65837076001972615319423⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨9604332430339243227278,9604332430342193923960⟩,⟨71713129554853871257776,71713129554856821960342⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨35325549144125198660428,35325549144129515202627⟩,⟨35722762052960909018208,35722762052965225561687⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨25397304298765501459089,25397304298768992793600⟩,⟨(-1040499954867271672384),(-1040499954863780339548)⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨5006096182220941933482,5006096182223622677046⟩,⟨(-8506024731641517461955),(-8506024731638836718453)⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨(-1744988902465191310505),(-1744988902464029427898)⟩,⟨(-2547661498788163475121),(-2547661498787001592318)⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨(-790862786457514165789),(-790862786457129453052)⟩,⟨201737901423998426504,201737901424383139192⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-13148118348993508317),(-13148118348900435704)⟩,⟨189870854396569239084,189870854396662311702⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨37465098374780003297,37465098374795778524⟩,⟨16341771365566603301,16341771365582378529⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨6235499375615994648,6235499375617839179⟩,⟨(-5741874726954710535),(-5741874726952866005)⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-380026535335355679),(-380026535335122457)⟩,⟨(-1750127259435530739),(-1750127259435297520)⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-364970615132095024),(-364970615132065808)⟩,⟨(-183431503698018905),(-183431503697989689)⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-102437259615061846),(-102437259615057916)⟩,⟨25660627190350149,25660627190354080⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-22523291993556798),(-22523291993556120)⟩,⟨20755440238410759,20755440238411435⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-3760210225799576),(-3760210225799427)⟩,⟨5891438874894705,5891438874894857⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨(-4638753708900403788078378),(-4638753708900402783489537)⟩,⟨13155303155518425831913747,13155303155518426856040588⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨3165173244838558983745110,3165173244838562129746805⟩,⟨34620309974785024366330844,34620309974785027584945753⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨37888268515261615584750527,37888268515261620689799991⟩,⟨20848138662470037785111584,20848138662470042984343379⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨46259919596380472060016925,46259919596380480068289026⟩,⟨(-48471917402056268996343355),(-48471917402056260974275579)⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-22185294413133744259621379),(-22185294413133727263901126)⟩,⟨(-100507300517859197496090479),(-100507300517859180546550731)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-95709620972135773929583961),(-95709620972135750306029487)⟩,⟨(-53954863169210161247947444),(-53954863169210137632755251)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-79484223101124987400474840),(-79484223101124964577823649)⟩,⟨28452326552912013349681781,28452326552912036185186946⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-15611719328106522493191704),(-15611719328106505895309279)⟩,⟨47803563979209326681656030,47803563979209343277423724⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨14838971161234084859207001,14838971161234094553043250⟩,⟨19889301014135590887452234,19889301014135600580142672⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨10733944855617939079077305,10733944855617944187185916⟩,⟨(-468992704064091120848165),(-468992704064086012084251)⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨2330045389902163941122136,2330045389902167381628412⟩,⟨(-3616880674670702402494007),(-3616880674670698962067000)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨(-536561511247827086406130),(-536561511247823944121983)⟩,⟨(-1589092911265454461835425),(-1589092911265451319615311)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-600986890102483417264074),(-600986890102480214031582)⟩,⟨(-288334750901275831749071),(-288334750901272628499917)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-270252502581378945136756),(-270252502581376518123035)⟩,⟨55308659158492538002574,55308659158494965026885⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-89359194566593738689986),(-89359194566591873843315)⟩,⟨69126023275317773933246,69126023275319638780966⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-19399390876795163152673),(-19399390876794513772754)⟩,⟨24109696396213936933728,24109696396214586313484⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
end hm21_1_1_6
namespace hm21_1_1_7
noncomputable def s0_0 : CBox := ⟨⟨(-92),92⟩,⟨(-92),92⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-269),269⟩,⟨(-269),269⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-490),490⟩,⟨(-490),490⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-755),755⟩,⟨(-755),755⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-1032),1032⟩,⟨(-1032),1032⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-1256),1256⟩,⟨(-1256),1256⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-1364),1364⟩,⟨(-1364),1364⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-1300),1300⟩,⟨(-1300),1300⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-1273),1273⟩,⟨(-1273),1273⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-1544),1544⟩,⟨(-1544),1544⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-1614),1614⟩,⟨(-1614),1614⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-1443),1443⟩,⟨(-1443),1443⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-1057),1057⟩,⟨(-1057),1057⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-563),563⟩,⟨(-563),563⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-317),317⟩,⟨(-317),317⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-105),105⟩,⟨(-105),105⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-29),29⟩,⟨(-29),29⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-69),69⟩,⟨(-69),69⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-114),114⟩,⟨(-114),114⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-164),164⟩,⟨(-164),164⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-216),216⟩,⟨(-216),216⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-266),266⟩,⟨(-266),266⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-299),299⟩,⟨(-299),299⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-353),353⟩,⟨(-353),353⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-488),488⟩,⟨(-488),488⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-599),599⟩,⟨(-599),599⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-662),662⟩,⟨(-662),662⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-648),648⟩,⟨(-648),648⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-558),558⟩,⟨(-558),558⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-420),420⟩,⟨(-420),420⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-256),256⟩,⟨(-256),256⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-90),90⟩,⟨(-90),90⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨16698,16719⟩,⟨10490,10510⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨29540,29571⟩,⟨12204,12239⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨15523,15571⟩,⟨1020,1070⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨3181,3242⟩,⟨(-1352),(-1290)⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨188,264⟩,⟨(-358),(-282)⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-46),37⟩,⟨(-72),20⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-70),52⟩,⟨(-64),52⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-80),75⟩,⟨(-75),75⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-108),108⟩,⟨(-108),108⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-107),107⟩,⟨(-107),107⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-90),90⟩,⟨(-90),90⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-28),28⟩,⟨(-28),28⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨3939877262079608,3939877262079648⟩,⟨453408703271311,453408703271353⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨7955875619065321,7955875619065376⟩,⟨(-927604950135486),(-927604950135433)⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨5108262801564504,5108262801564542⟩,⟨(-3286299305970082),(-3286299305970047)⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨858367806082198,858367806082229⟩,⟨(-2501993342730520),(-2501993342730494)⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-373592593914429),(-373592593914400)⟩,⟨(-636811138012470),(-636811138012442)⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨(-140876512954061),(-140876512954028)⟩,⟨(-2916724041716),(-2916724041683)⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-8607523235780),(-8607523235744)⟩,⟨17359217207614,17359217207652⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨1348983199687,1348983199725⟩,⟨1503565435001,1503565435038⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨158832555766,158832555803⟩,⟨(-60352095754),(-60352095716)⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨515254201,515254244⟩,⟨(-12505623358),(-12505623315)⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨(-772840620),(-772840575)⟩,⟨(-449937792),(-449937750)⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨(-63150047),(-63150005)⟩,⟨29210642,29210684⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-2191043),(-2190996)⟩,⟨6247119,6247164⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨232052,232093⟩,⟨815105,815144⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨95680,95710⟩,⟨115416,115448⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨20745,20766⟩,⟨16438,16460⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨16076085498343683299299,16076085498344124786801⟩,⟨6206066077359752066786,6206066077360193553593⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨40711990108925336741946,40711990108926527507146⟩,⟨5659858673334702125858,5659858673335892888261⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨41128224538025117234177,41128224538026951345631⟩,⟨(-13262516660886141918974),(-13262516660884307810954)⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨17195468497699163484734,17195468497701789703019⟩,⟨(-24868372216030538106090),(-24868372216027911887882)⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-3615437757580123630612),(-3615437757578021920882)⟩,⟨(-15018710314512739827593),(-15018710314510638116715)⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-5750363464965310560259),(-5750363464963701613159)⟩,⟨(-1941448680494345434354),(-1941448680492736487370)⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨(-1313845342410081425686),(-1313845342409318238295)⟩,⟨1406318321819232057521,1406318321819995244820⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨239342170982149099072,239342170982387050223⟩,⟨457365902337493834325,457365902337731785510⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨120328598083237542645,120328598083295312965⟩,⟨(-21562189405371932310),(-21562189405314161994)⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨4003419148295004583,4003419148305449201⟩,⟨(-26363911227422470143),(-26363911227412025527)⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-4779674870323141091),(-4779674870321825580)⟩,⟨(-2945594354506132207),(-2945594354504816698)⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-1055276587902977646),(-1055276587902831751)⟩,⟨577524144337960717,577524144338106614⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-46383518784160820),(-46383518784140242)⟩,⟨273857781188647324,273857781188667905⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨38043494378108430,38043494378110860⟩,⟨61740803637972595,61740803637975025⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨18450749801288184,18450749801288734⟩,⟨10399630732406826,10399630732407371⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨4697322656983111,4697322656983225⟩,⟨1209053542362945,1209053542363061⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨6915839038053200841731661,6915839038053201381903959⟩,⟨2037545862268750243865261,2037545862268750772646788⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨17816525424541721721340486,17816525424541723422837340⟩,⟨(-2617241992088920461308912),(-2617241992088918800577324)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨9660994167702925545851946,9660994167702928320022661⟩,⟨(-20319173282447590184372151),(-20319173282447587455903797)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-26931686585163451266245884),(-26931686585163446961175583)⟩,⟨(-22523087318051720179742342),(-22523087318051715877315924)⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-52132280330311139402492301),(-52132280330311130227368635)⟩,⟨15574347244696643797400053,15574347244696652998330137⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-24530231254493752302292734),(-24530231254493739406726327)⟩,⟨53304185805496798005326046,53304185805496810903220309⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨19260901706857041518248045,19260901706857054087296009⟩,⟨41344901865328779212417419,41344901865328791774522658⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨26893821004946699707041802,26893821004946708905589160⟩,⟨5800322515692121980781788,5800322515692131180985995⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨10011291993561885409501015,10011291993561890818187376⟩,⟨(-9433324701089787403187693),(-9433324701089781994079649)⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-1019936215243069486234236),(-1019936215243066614542151)⟩,⟨(-5948361423301020738216704),(-5948361423301017866892404)⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-2219811364317338119497652),(-2219811364317336214149495)⟩,⟨(-1031929343205891631111573),(-1031929343205889725695360)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨(-859719624338916831788026),(-859719624338914965699565)⟩,⟨439800075152673590097920,439800075152675456212769⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-111408879164865846933751),(-111408879164864097063005)⟩,⟨371430915317380623387843,371430915317382373246328⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨57716521377677061724788,57716521377678596614688⟩,⟨151173740699742141580870,151173740699743676466345⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨49011526550645843039040,49011526550646961420510⟩,⟨45179429659333197030924,45179429659334315412432⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨16005352742942206566315,16005352742942583182132⟩,⟨8899423546058552509221,8899423546058929125269⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-2836362920539022959273509),(-2836362920539009481792126)⟩,⟨9527209570821546175640684,9527209570821559640200735⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-434254578866156297985397525),(-434254578866156294781521329)⟩,⟨1046752061245394666716132809,1046752061245394669918395405⟩⟩
 def realAnswer : RBox := ⟨(-437090941786695321044671034),(-437090941786695304163313455)⟩
end hm21_1_1_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock21_11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid
namespace hm21_1_1_8
noncomputable def s0_0 : CBox := ⟨⟨(-126),126⟩,⟨(-126),126⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-355),355⟩,⟨(-355),355⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-563),563⟩,⟨(-563),563⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-701),701⟩,⟨(-701),701⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-940),940⟩,⟨(-940),940⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-1298),1298⟩,⟨(-1298),1298⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-1569),1569⟩,⟨(-1569),1569⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-1643),1643⟩,⟨(-1643),1643⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-1464),1464⟩,⟨(-1464),1464⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-1617),1617⟩,⟨(-1617),1617⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-1809),1809⟩,⟨(-1809),1809⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-1676),1676⟩,⟨(-1676),1676⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-1241),1241⟩,⟨(-1241),1241⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-659),659⟩,⟨(-659),659⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-363),363⟩,⟨(-363),363⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-120),120⟩,⟨(-120),120⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-23),23⟩,⟨(-23),23⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-52),52⟩,⟨(-52),52⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-78),78⟩,⟨(-78),78⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-118),118⟩,⟨(-118),118⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-182),182⟩,⟨(-182),182⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-264),264⟩,⟨(-264),264⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-354),354⟩,⟨(-354),354⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-434),434⟩,⟨(-434),434⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-474),474⟩,⟨(-474),474⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-467),467⟩,⟨(-467),467⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-583),583⟩,⟨(-583),583⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-664),664⟩,⟨(-664),664⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-645),645⟩,⟨(-645),645⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-527),527⟩,⟨(-527),527⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-342),342⟩,⟨(-342),342⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-123),123⟩,⟨(-123),123⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨770,788⟩,⟨(-14407),(-14387)⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-2790),(-2759)⟩,⟨(-23291),(-23261)⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-5029),(-4992)⟩,⟨(-10364),(-10323)⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-2079),(-2032)⟩,⟨(-1593),(-1543)⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-324),(-267)⟩,⟨(-51),5⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-42),17⟩,⟨(-16),41⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-35),42⟩,⟨(-26),48⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-59),59⟩,⟨(-57),59⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-73),73⟩,⟨(-73),73⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-107),107⟩,⟨(-107),107⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-95),95⟩,⟨(-95),95⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-75),75⟩,⟨(-75),75⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-51),51⟩,⟨(-51),51⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-23),23⟩,⟨(-23),23⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨(-486668496441538),(-486668496441509)⟩,⟨(-2362622044498373),(-2362622044498345)⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-2067345346848291),(-2067345346848253)⟩,⟨(-4427319961438750),(-4427319961438711)⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-2915978085086731),(-2915978085086701)⟩,⟨(-2321048165240032),(-2321048165240000)⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨(-1636965980592112),(-1636965980592086)⟩,⟨8538597073411,8538597073433⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-295204011278885),(-295204011278861)⟩,⟨355433405648010,355433405648031⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨29819763719080,29819763719107⟩,⟨84254663533656,84254663533683⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨12437259552987,12437259553013⟩,⟨1045114418902,1045114418931⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨570796461592,570796461621⟩,⟨(-1193920556122),(-1193920556097)⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨(-79261619546),(-79261619514)⟩,⟨(-80969376252),(-80969376222)⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨(-7863466506),(-7863466470)⟩,⟨3221559220,3221559258⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨(-48872382),(-48872341)⟩,⟨615911102,615911139⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨38213926,38213967⟩,⟨30439674,30439713⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨4667047,4667087⟩,⟨(-669479),(-669441)⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨438617,438649⟩,⟨(-424698),(-424664)⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨40191,40221⟩,⟨(-101206),(-101178)⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨3167,3188⟩,⟨(-19059),(-19039)⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨1749572931299307192874,1749572931299520194399⟩,⟨(-8762903405290781860831),(-8762903405290568858740)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-763385656785997085361),(-763385656785438076423)⟩,⟨(-21356420883897020288793),(-21356420883896461277983)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-10643381109386682299212),(-10643381109385635157188)⟩,⟨(-19918230357243384329203),(-19918230357242337185719)⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-14544018310415816864582),(-14544018310414466874297)⟩,⟨(-6476478863834134159255),(-6476478863832784169299)⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-7461511409278192344408),(-7461511409277046720621)⟩,⟨3435939605743063606571,3435939605744209229765⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-388465808365360206940),(-388465808364528541221)⟩,⟨3242462628278091997232,3242462628278923663092⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨904188240096072659045,904188240096505823418⟩,⟨532880062434342423895,532880062434775588289⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨215797864362228288805,215797864362361263317⟩,⟨(-187183690085143990689),(-187183690085011016193)⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-28252249608594671035),(-28252249608563369552)⟩,⟨(-62624770738516170775),(-62624770738484869291)⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨(-15130370043693961251),(-15130370043688166787)⟩,⟨1670159368276010417,1670159368281804880⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-892923492750026162),(-892923492749215406)⟩,⟨3128977022744011237,3128977022744821995⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨501100300843319444,501100300843404008⟩,⟨498803926648241136,498803926648325701⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨163865184785851319,163865184785862933⟩,⟨(-21453109035618382),(-21453109035606769)⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨28463461012881616,28463461012883210⟩,⟨(-32996705980091947),(-32996705980090356)⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨2549611560183031,2549611560183384⟩,⟨(-12559118278379617),(-12559118278379265)⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-189034131130743),(-189034131130666)⟩,⟨(-2939323963591946),(-2939323963591874)⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨756118903181749082673723,756118903181749325478379⟩,⟨(-3171727566478133341990862),(-3171727566478133093464462)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-1625849965117943718876886),(-1625849965117942953855756)⟩,⟨(-7998261890493591005558236),(-7998261890493590220819542)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-9493971450126697889922312),(-9493971450126696618011792)⟩,⟨(-3842827126068250744685918),(-3842827126068249453863960)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-9495130432136979284974447),(-9495130432136977271908891)⟩,⟨12997784802525402705963191,12997784802525404718137085⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨8945000338403081153684378,8945000338403085488189137⟩,⟨23523117397868999677082351,23523117397869003999275271⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨25765084096074545653665807,25765084096074551772697479⟩,⟨9383108984737200374615056,9383108984737206493560659⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨18623496866789713575709139,18623496866789719574827281⟩,⟨(-10866858578580713613252456),(-10866858578580707610958822)⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨1434751455137970869051972,1434751455137975285230977⟩,⟨(-13091845221312912576753454),(-13091845221312908161565888)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-5101262907434987991021674),(-5101262907434985384164397)⟩,⟨(-4300134887810277797144393),(-4300134887810275190387092)⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-2837302471606316116984894),(-2837302471606314722872969)⟩,⟨865223406423961780732511,865223406423963175013802⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-357806769118260041454351),(-357806769118259122465991)⟩,⟨1164994787997816596923589,1164994787997817515869476⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨282710855844720912423233,282710855844721865251040⟩,⟨395925747905909213106028,395925747905910165926507⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨195583244045351210847477,195583244045352063130866⟩,⟨26658711430098251408717,26658711430099103698973⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨71764530273390707695066,71764530273391542640286⟩,⟨(-41812985580699039026555),(-41812985580698204080148)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨18775721005942975572161,18775721005943546085746⟩,⟨(-28840421221467154753634),(-28840421221466584240405)⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨3138798100172820328117,3138798100173005739155⟩,⟨(-8948307611263135695919),(-8948307611262950285067)⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨4525687670490656213176984,4525687670490662751209518⟩,⟨826001585564419617494532,826001585564426161072972⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨482681791637304922976676079,482681791637304924499150196⟩,⟨171435475316784670975330385,171435475316784672497660664⟩⟩
 def realAnswer : RBox := ⟨487207479307795579089853063,487207479307795587350359714⟩
end hm21_1_1_8
namespace hm21_1_1_9
noncomputable def s0_0 : CBox := ⟨⟨(-125),125⟩,⟨(-125),125⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-363),363⟩,⟨(-363),363⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-616),616⟩,⟨(-616),616⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-841),841⟩,⟨(-841),841⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-955),955⟩,⟨(-955),955⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-1061),1061⟩,⟨(-1061),1061⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-1466),1466⟩,⟨(-1466),1466⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-1718),1718⟩,⟨(-1718),1718⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-1665),1665⟩,⟨(-1665),1665⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-1504),1504⟩,⟨(-1504),1504⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-1774),1774⟩,⟨(-1774),1774⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-1712),1712⟩,⟨(-1712),1712⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-1290),1290⟩,⟨(-1290),1290⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-686),686⟩,⟨(-686),686⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-379),379⟩,⟨(-379),379⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-124),124⟩,⟨(-124),124⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-23),23⟩,⟨(-23),23⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-52),52⟩,⟨(-52),52⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-84),84⟩,⟨(-84),84⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-123),123⟩,⟨(-123),123⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-162),162⟩,⟨(-162),162⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-197),197⟩,⟨(-197),197⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-233),233⟩,⟨(-233),233⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-344),344⟩,⟨(-344),344⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-466),466⟩,⟨(-466),466⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-543),543⟩,⟨(-543),543⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-543),543⟩,⟨(-543),543⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-483),483⟩,⟨(-483),483⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-510),510⟩,⟨(-510),510⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-466),466⟩,⟨(-466),466⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-323),323⟩,⟨(-323),323⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-120),120⟩,⟨(-120),120⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-8429),(-8409)⟩,⟨4087,4105⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-12355),(-12334)⟩,⟨8980,9001⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-4277),(-4251)⟩,⟨6201,6228⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-225),(-192)⟩,⟨1682,1715⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨70,111⟩,⟨155,196⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-12),36⟩,⟨(-25),33⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-26),42⟩,⟨(-42),32⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-48),48⟩,⟨(-48),43⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-62),62⟩,⟨(-62),62⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-51),51⟩,⟨(-51),51⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-62),62⟩,⟨(-62),62⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-45),45⟩,⟨(-45),45⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-23),23⟩,⟨(-23),23⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨(-1131244302099711),(-1131244302099692)⟩,⟨649012951546800,649012951546825⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-1924761863363764),(-1924761863363736)⟩,⟨1820827533610270,1820827533610297⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-688282028723509),(-688282028723485)⟩,⟨1912644812567070,1912644812567096⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨301107723192927,301107723192949⟩,⟨848678592190122,848678592190143⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨241792678760749,241792678760768⟩,⟨87143407186484,87143407186501⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨38506640419784,38506640419806⟩,⟨(-32504012158406),(-32504012158385)⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-2061924125144),(-2061924125124)⟩,⟨(-6842403606098),(-6842403606073)⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨(-769558429213),(-769558429186)⟩,⟨(-40322659990),(-40322659964)⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨(-25186190008),(-25186189982)⟩,⟨62261707027,62261707054⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨3745667547,3745667581⟩,⟨3502912169,3502912201⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨353907745,353907775⟩,⟨(-136814481),(-136814450)⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨6288030,6288061⟩,⟨(-29837546),(-29837517)⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-1739798),(-1739767)⟩,⟨(-2425262),(-2425231)⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-372366),(-372339)⟩,⟨(-119156),(-119130)⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-69778),(-69754)⟩,⟨8559,8580⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-11814),(-11794)⟩,⟨4160,4179⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨(-4117466848710146280554),(-4117466848710058320297)⟩,⟨(-105897880838315353288),(-105897880838227393383)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-9659834008633351410126),(-9659834008633091018408)⟩,⟨2054868962463726535101,2054868962463986925921⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-8225764175225981894287),(-8225764175225464768784)⟩,⟨6511143815689544165571,6511143815690061290599⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-1719917827336029309421),(-1719917827335434519820)⟩,⟨7250902065624899352590,7250902065625494142518⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨2277756723606761344238,2277756723607335756931⟩,⟨3144637540881634485879,3144637540882208898783⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨1555962783549550819154,1555962783549936841955⟩,⟨(-135956828751254607647),(-135956828750868584942)⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨156967340219839236580,156967340220047528072⟩,⟨(-483933009975017178867),(-483933009974808887369)⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨(-114052993850436664217),(-114052993850367464490)⟩,⟨(-82089438865499128330),(-82089438865429928600)⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-26894792223106130579),(-26894792223090726912)⟩,⟨21321476130672387687,21321476130687791351⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨2797553876351131021,2797553876353943030⟩,⟨7199620511458892639,7199620511461704649⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨1676269990519140117,1676269990519553372⟩,⟨6095943970386172,6095943970799428⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨175837161211525385,175837161211574309⟩,⟨(-324849464989316281),(-324849464989267355)⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-36289654017344322),(-36289654017338708)⟩,⟨(-79515021651550214),(-79515021651544602)⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-21392880752664318),(-21392880752663363)⟩,⟨(-9170388616157741),(-9170388616156785)⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-6848899602084434),(-6848899602084247)⟩,⟨775064679424051,775064679424237⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-1476214071354835),(-1476214071354791)⟩,⟨590254609162927,590254609162969⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨(-1289226434188981383136100),(-1289226434188981281801124)⟩,⟨(-236647017494071800159672),(-236647017494071701347727)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-3181723005780487921410306),(-3181723005780487600348591)⟩,⟨830181291404770340777736,830181291404770653592007⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-1324883943373563532726059),(-1324883943373563000869556)⟩,⟨3927031633875690223835037,3927031633875690748832877⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨5539325636014985550396812,5539325636014986382647346⟩,⟨3514176292587492930185410,3514176292587493763653938⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨9377154928953422305797068,9377154928953424106121896⟩,⟨(-4374135860874365937976077),(-4374135860874364132546197)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨3007153371830054246235885,3007153371830056809679164⟩,⟨(-10985911598012130483436595),(-10985911598012127920372100)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-5267938570105183261661353),(-5267938570105180734919211)⟩,⟨(-7371820253765616104870345),(-7371820253765613579369373)⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-5604052105857528914740054),(-5604052105857527050411934)⟩,⟨(-32863802462853184935207),(-32863802462851320118649)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-1589952862449917135175096),(-1589952862449916033073859)⟩,⟨2397182092066358840025232,2397182092066359942124575⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨531022752764211115588793,531022752764211709146260⟩,⟨1182154875356802458226789,1182154875356803051720388⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨532357507963213066997145,532357507963213460118094⟩,⟨86347735411227409050109,86347735411227802192030⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨156806339511775114166027,156806339511775537230043⟩,⟨(-151245923938580047244004),(-151245923938579624179422)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-1829094955780906795843),(-1829094955780526500077)⟩,⟨(-89295574473764423727350),(-89295574473764043434595)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-24133375444538132160623),(-24133375444537739822071)⟩,⟨(-29216068841936476399131),(-29216068841936084060605)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-14487253711161413453080),(-14487253711161162146242)⟩,⟨(-6287081475700126344972),(-6287081475699875037830)⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-4303859086950110774758),(-4303859086950032319245)⟩,⟨(-726659411846306623505),(-726659411846228167877)⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨136903561462101951378806,136903561462104763462880⟩,⟨(-1887149020753379447334164),(-1887149020753376637331043)⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨58709166998824660389429927,58709166998824661032407869⟩,⟨(-197243793697400906666316196),(-197243793697400906022906687)⟩⟩
 def realAnswer : RBox := ⟨58846070560286762240808733,58846070560286765895870749⟩
end hm21_1_1_9
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock24_0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid
namespace hm24_0_0_2
noncomputable def s0_0 : CBox := ⟨⟨(-14910937279083368480308419272),(-14910937279083361840370331965)⟩,⟨(-9573338305576714291081955960),(-9573338305576707650366157413)⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-47719547862825808365060292221),(-47719547862825790705617786983)⟩,⟨(-15865459781787992234474652798),(-15865459781787974573501666460)⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-73963382422335231668121194419),(-73963382422335212901866633534)⟩,⟨12614286433400116472032442678,12614286433400135238380372334⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-56849456072706559083082519860),(-56849456072706549605756705468)⟩,⟨68642011221635311141557892502,68642011221635320616003916222⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨19122793278916734346151027629,19122793278916738478102510884⟩,⟨90095659200966550999101931727,90095659200966555130778707011⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨81367460990869291312611213184,81367460990869292455938110121⟩,⟨25772910361568719705947521112,25772910361568720851274053157⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨46626061946276188333653816467,46626061946276188709552288382⟩,⟨(-54378719735144159707731499943),(-54378719735144159333058469507)⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-27586731950192583585963824809),(-27586731950192583445082082966)⟩,⟨(-46989485380392855208289404844),(-46989485380392855067166152949)⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-36413945192475188500290781302),(-36413945192475188444722958969)⟩,⟨8322139391821064872774781750,8322139391821064928498278519⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-2370807349412388678700563499),(-2370807349412388658145121926)⟩,⟨22631275426844767924587523426,22631275426844767945064312397⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨10513060726446274508716049424,10513060726446274515803839882⟩,⟨5799137069145523903478599164,5799137069145523910521871712⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨4472099192803155721509819633,4472099192803155723875812276⟩,⟨(-2745359092860461860151528085),(-2745359092860461857814850471)⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨216122441854262814069607453,216122441854262814637787434⟩,⟨(-1741142751998887650152218393),(-1741142751998887649495987993)⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-211418607661953590518374744),(-211418607661953590363667710)⟩,⟨(-321602547299833752179002712),(-321602547299833752015412361)⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-34413743718343239234792662),(-34413743718343239208828138)⟩,⟨(-18691479767754200503260957),(-18691479767754200485397078)⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-629096727135919948093021),(-629096727135919946675462)⟩,⟨(-138147613225269831329925),(-138147613225269830924369)⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-37648146110408990128579848215),(-37648146110408956495632950137)⟩,⟨(-47655773397094423218272220080),(-47655773397094389581038061123)⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-139072548757522817215413100210),(-139072548757522671614009505964)⟩,⟨(-107637946795020258033087872409),(-107637946795020112422949991042)⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-268548953814927334955404870658),(-268548953814926941209387983136)⟩,⟨(-49129511531112788067526677388),(-49129511531112394320902016410)⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-299679146977448893015519230982),(-299679146977448146778520913162)⟩,⟨168723996181714764368624087087,168723996181715510586284718844⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-66768328512794145953622791421),(-66768328512792323171458448262)⟩,⟨378988770176853450095058811100,378988770176855272875318492608⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨302213754271993398909172709653,302213754271996463609245616011⟩,⟨256974056165403981647302549793,256974056165407046366011600196⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨345392268054823400901426579380,345392268054828029651927209112⟩,⟨(-168287760199402619905597431455),(-168287760199397991170727073077)⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-40089302763015149950031118325),(-40089302763009447261633145609)⟩,⟨(-351534814602930338484190477038),(-351534814602924635790877728143)⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-305653202804459201209055007323),(-305653202804454124186001277457)⟩,⟨(-62335853702639704174769745317),(-62335853702634627146600367910)⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-135653339322802262133314401521),(-135653339322798956061153849198)⟩,⟨226663857047602917651291104853,226663857047606223713693434027⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨125372670745590672886047704306,125372670745592461521825729921⟩,⟨174508532339349432310247589112,174508532339351220953836016513⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨166533094887709767575007572345,166533094887710636244546509793⟩,⟨(-16732369904152158302364412753),(-16732369904151289633172845059)⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨67463917357907518724775609556,67463917357907816309496869878⟩,⟨(-103616046707278210462138684180),(-103616046707277912882228633077)⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-10652830559870186519939026769),(-10652830559870050227928286560)⟩,⟨(-83642593919663618754857104931),(-83642593919663482462752111345)⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-28085487120398868409654442665),(-28085487120398822940910867527)⟩,⟨(-39981771694229255487361712403),(-39981771694229210017115393583)⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-12113210716226717693445797110),(-12113210716226707786330647345)⟩,⟨(-10424053664141909060902978590),(-10424053664141899153103360362)⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-4326321022174848279747228259),(-4326321022174848250583832752)⟩,⟨(-97744429285747362662654678115),(-97744429285747362622724426023)⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-83559538920624998652890040651),(-83559538920624998542048822124)⟩,⟨(-273449384180199797346698358109),(-273449384180199797213539268012)⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-322075400490364765776153441633),(-322075400490364765527981008371)⟩,⟨(-318286055279959869353882808097),(-318286055279959869104194786302)⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-588372040734830680602076923833),(-588372040734830680176990282887)⟩,⟨(-36900309012751279315737503848),(-36900309012751278943564196904)⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-458395084722419165014624581290),(-458395084722419164304992362974)⟩,⟨517753243338815652034757180915,517753243338815652739407022919⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨251418243480550541743438588539,251418243480550542950791575852⟩,⟨713634986614447392037927941387,713634986614447393301282618011⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨783427781613880106961922887274,783427781613880109250609124263⟩,⟨43255042289648993540151247608,43255042289648995778527569610⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨288136596865553961461606158920,288136596865553965562793072849⟩,⟨(-722748595987169236469011465255),(-722748595987169232350631607092)⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-576782264362158156897492099791),(-576782264362158149501101679129)⟩,⟨(-466647937159347334650477373996),(-466647937159347327235915072400)⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-575940660467613099477393204086),(-575940660467613084877889856594)⟩,⟨365327933987149472012056904546,365327933987149486573789014851⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨101050923658094222892785786596,101050923658094256784003263735⟩,⟨595537339156577754837160356975,595537339156577788761036255402⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨481962715131944725215488647879,481962715131944821580807725855⟩,⟨174154381957446214176893092528,174154381957446310540763811547⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨349738202575212097278121341379,349738202575212281258810636762⟩,⟨(-214340901849403793231554139868),(-214340901849403609274218060689)⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨93728304607372310933176608467,93728304607372630474105171207⟩,⟨(-284227714437799867326716885342),(-284227714437799547785536722023)⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-29709339879775716630566918952),(-29709339879775440789672041117)⟩,⟨(-179587681756705644249760565722),(-179587681756705368400814118943)⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-24304558620123621085552624724),(-24304558620123522038246348447)⟩,⟨(-56006186815319774579473378401),(-56006186815319675528378825592)⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨28594989526485670465840768819,28594989526485843821612705438⟩,⟨(-95467813975272178332065109964),(-95467813975272004960214963963)⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨12904828173708256122256848214,12904828173708727831231725473⟩,⟨(-293098300476992479283604060345),(-293098300476992007541471199806)⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-200360013404944721278940220282),(-200360013404944194374005645981)⟩,⟨(-425772525169911011249693762011),(-425772525169910484342614921438)⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨(-565201748811632097712891128635),(-565201748811631805916539214616)⟩,⟨(-259092449526389497303872465587),(-259092449526389205587141037632)⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-662233241269779409219867104274),(-662233241269779262159701967767)⟩,⟨329486520910814775360684051432,329486520910814922413424589795⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨(-49508024258567188790037605659),(-49508024258567136549698010404)⟩,⟨819236252617177607882415925375,819236252617177660210185625444⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨774065264699108725407997446320,774065264699108748691823685126⟩,⟨388173018625675034118851173364,388173018625675057320482923748⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨628862263909240717842097371889,628862263909240729740427783906⟩,⟨(-613524561856601798976489595651),(-613524561856601787047686281873)⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨(-384068678168384443864090808110),(-384068678168384437440885895647)⟩,⟨(-770802898318812179292418874036),(-770802898318812172837789725337)⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨(-808899248590734234582510828995),(-808899248590734231134130268314)⟩,⟨100963656387540453438997022603,100963656387540456815809557614⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨(-210864625644019447442065693615),(-210864625644019445689162867544)⟩,⟨711116353119725782280853079696,711116353119725784100787244587⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨439532179829105866816425837098,439532179829105867786293794790⟩,⟨469395730072486011764894196342,469395730072486012730834275512⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨521718064360709345199686324239,521718064360709345745033990820⟩,⟨(-34721532582684180418067370463),(-34721532582684179925391547371)⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨279119727968292547698136849338,279119727968292547997135666017⟩,⟨(-266210141629191005356265115184),(-266210141629191005056371693383)⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨76564925941006274282425686664,76564925941006274411940013889⟩,⟨(-223603744488353809562960636742),(-223603744488353809413816802222)⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨6798444745149491980816222188,6798444745149492014391174276⟩,⟨(-79291763172808495109736243947),(-79291763172808495066792227138)⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨95972106928570625022659897200,95972106928571406168540293497⟩,⟨(-11207167905716209527735029404),(-11207167905715428367380990196)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨261718981010170975250898126809,261718981010174449949005994571⟩,⟨(-104307192546773733423803067502),(-104307192546770258695984587676)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨277773838636236197349888766664,277773838636245962224700788356⟩,⟨(-347528710547385655374409871017),(-347528710547375890497992812932)⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-45035216144337717276589035270),(-45035216144318371284442993218)⟩,⟨(-577696347573294679011788770187),(-577696347573275333092704919775)⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-588906100830529379030084948733),(-588906100830479158943246719807)⟩,⟨(-351201377845787572839284682931),(-351201377845737352758992734874)⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-641027633776150818272882821929),(-641027633776060460812349100868)⟩,⟨418953030220502656186273123257,418953030220593013729567302382⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨195121773875958253978170104758,195121773876104751320990155415⟩,⟨796618271282869901818477784571,796618271283016399081246898488⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨848038548038119886934272706782,848038548038316037794779721262⟩,⟨25267671428966862242794280472,25267671429163013134577468483⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨234439304507224157353694564353,234439304507416190471115546840⟩,⟨(-817735503976114578136870193028),(-817735503975922544988207858357)⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨(-702222953743975492788923447240),(-702222953743837687130551695122)⟩,⟨(-437348674575334633518679172319),(-437348674575196827936078649012)⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-615392136159519458722798937878),(-615392136159437458883376173842)⟩,⟨476362225012575734185513216982,476362225012657734099645797687⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨124779359700577109530353376543,124779359700621133346226580325⟩,⟨691025362654353195398174702261,691025362654397219208773223468⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨531083202435337431834671950614,531083202435353911557234814714⟩,⟨270009631554192621293051553290,270009631554209100953935616186⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨442472518404038449336391532030,442472518404046584300270458150⟩,⟨(-111964266533290260972478706796),(-111964266533282126007334130573)⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨212423812903562485865105844207,212423812903565338080635661368⟩,⟨(-193500290595132570214088007862),(-193500290595129717974678631398)⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨53996318859753412662612567754,53996318859754048792270921065⟩,⟨(-81898336789850367652399578402),(-81898336789849731511269873843)⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨2708978539648812999365793926,2708978539648813021841315514⟩,⟨37095807663521955839422939683,37095807663521955865897478807⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨38631233640743840749159263434,38631233640743840835739979250⟩,⟨102053926826198816165516272469,102053926826198816260383482699⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨140616462462226588083599075602,140616462462226588283816662989⟩,⟨105823094045884586466404287956,105823094045884586667217978275⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨236781908002158154237182360791,236781908002158154608494638926⟩,⟨(-37650225993818532370491025221),(-37650225993818532017117379158)⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨124382973496798470040292283749,124382973496798470766155593832⟩,⟨(-275007269394373770914494826691),(-275007269394373770190207916809)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-230378386679151076471909718647),(-230378386679151075046336709506)⟩,⟨(-272671382108181040464026566491),(-272671382108181039022213227701)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-371965317693647256534037691699),(-371965317693647253615598473303)⟩,⟨141071678271915610758799369257,141071678271915613664179429184⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨40330287280958410135782172536,40330287280958416027954243819⟩,⟨420421542856637923825297040572,420421542856637929720795504955⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨428302669509426319090164513750,428302669509426331990132882515⟩,⟨61982601339611801093921608480,61982601339611813997487392510⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨171197901932702846999290798183,171197901932702883446599093698⟩,⟨(-395613413877903603871796352671),(-395613413877903567428398180799)⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-303893527255028107868885177891),(-303893527255027985503665272058)⟩,⟨(-285204170687415482089884446470),(-285204170687415359724348263622)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨(-364289299442014179624045207426),(-364289299442013734236626915850)⟩,⟨128336289088157422744261331156,128336289088157868132083866316⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-103907743353393375886460779852),(-103907743353392430986653946851)⟩,⟨317788648042216205382618622289,317788648042217150285326245840⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨99409431978079360122627770861,99409431978081119012042055301⟩,⟨239148075549577386678385919190,239148075549579145567723578145⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨126045695057354731628492170988,126045695057356303233420199461⟩,⟨104527157360640296020880086679,104527157360641867623922664321⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨50475221318733955843447139578,50475221318734529543431886116⟩,⟨24163328688902102857015031325,24163328688902676556016611203⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-15337596997320097115873141068),(-15337596997147278181393981937)⟩,⟨(-26042043211893938174063446815),(-26042043211721119239357236511)⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-42768285738053887448791688063),(-42768285738053887238126267629)⟩,⟨(-74076843850932732936769985842),(-74076843850932732723970172733)⟩⟩
 def realAnswer : RBox := ⟨(-58105882735373984564764829131),(-58105882735201165419420249566)⟩
end hm24_0_0_2
namespace hm24_0_0_3
noncomputable def s0_0 : CBox := ⟨⟨1663136765893271670413273707,1663136765893272823909123617⟩,⟨(-2589839018525947008178318945),(-2589839018525945854815552699)⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨2710852911276592768456270491,2710852911276595779054739882⟩,⟨(-8128863731981269351074547274),(-8128863731981266340732896953)⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-2037411214541031238516280906),(-2037411214541028154832496022)⟩,⟨(-12129517882596435207832257221),(-12129517882596432124165425946)⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-10564443890462796384521168396),(-10564443890462794911214853805)⟩,⟨(-8835723924332080354840573159),(-8835723924332078881104167530)⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-12865362940840031289298102720),(-12865362940840030695636026922)⟩,⟨2626453604212651086098085036,2626453604212651679803525611⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-3429083917054482399555287273),(-3429083917054482250953063116)⟩,⟨10418727112950060590404741116,10418727112950060738764372276⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨6059382548442767046829783905,6059382548442767089641027871⟩,⟨5355557276014763172005840274,5355557276014763214936751856⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨4575834985743837824710228839,4575834985743837838453077249⟩,⟨(-2570587020145981399864510726),(-2570587020145981386136720003)⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-594227223795574905060478953),(-594227223795574900576060808)⟩,⟨(-2906303762805451740763427812),(-2906303762805451736287389833)⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-1417382726179636854435875093),(-1417382726179636853118281500)⟩,⟨(-186840118234379481806810963),(-186840118234379480493050544)⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-288311399474728920979104277),(-288311399474728920636366785)⟩,⟨487732564985941292427518370,487732564985941292777528669⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨86109055380175611895105752,86109055380175611977381191⟩,⟨150861326051471048233028451,150861326051471048316559475⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨36582899770653031976813527,36582899770653031992538961⟩,⟨5750007333781411719443077,5750007333781411732105668⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨3819054715112919272338161,3819054715112919274595128⟩,⟨(-2349966937267507863773719),(-2349966937267507861670392)⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨97872979785702514521087,97872979785702514631805⟩,⟨(-171401624161792411718697),(-171401624161792411551259)⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨177784931661703965710,177784931661703966372⟩,⟨(-786741015203329014709),(-786741015203329012354)⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨16595814901225823596302181923,16595814901225835308820353505⟩,⟨(-13109400512997447734855327656),(-13109400512997436023845987558)⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨37147323003082295410158928737,37147323003082345602563287579⟩,⟨(-47952499383728936050196789736),(-47952499383728885860839203864)⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨16733784118480294296881453372,16733784118480427412974057255⟩,⟨(-90863545141550905205816302120),(-90863545141550772089942743880)⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-55291128389248021779151398751),(-55291128389247776569281306961)⟩,⟨(-98714860485768904116796363599),(-98714860485768658900509443002)⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-120062618114086202770586906304),(-120062618114085626236627910129)⟩,⟨(-21576277834098679187319854621),(-21576277834098102652709328348)⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-78259215882511413115418838327),(-78259215882510487946675427807)⟩,⟨91165852955346827408754184470,91165852955347752571776494118⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨47746749449074596774541925977,47746749449075925471982293150⟩,⟨99470297858911675262728657714,99470297858913003964656390841⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨95162935116151713841038139549,95162935116153257236445978992⟩,⟨(-10203203448580224111841347759),(-10203203448578680717711419021)⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨16358382766071012435771229075,16358382766072298229409050369⟩,⟨(-77365243102478845018113328455),(-77365243102477559225824760195)⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-53442686855156546320261869884),(-53442686855155763268595335597)⟩,⟨(-32501855183381841455270748006),(-32501855183381058401277858897)⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-38751442196382750323579380850),(-38751442196382353277184857374)⟩,⟨27463806964736665245111825901,27463806964737062289805669936⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨3279671456455363980547147994,3279671456455544230457362901⟩,⟨34465421991461367183712361773,34465421991461547433679019513⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨20131695508850618303058633726,20131695508850676374120895454⟩,⟨13215518143318926114691343321,13215518143318984186672249783⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨15500295176508040547984614526,15500295176508065844428913271⟩,⟨(-1939942560778227967657111750),(-1939942560778202671227366744)⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨7149559585285196511344544870,7149559585285204647308868474⟩,⟨(-5013179198691218961008498662),(-5013179198691210825302368666)⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨1828301850847169261381114653,1828301850847170999264426328⟩,⟨(-2124145095926262043511415062),(-2124145095926260305743235867)⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨51097180263023472585593130622,51097180263023472606629881078⟩,⟨(-2259909065785917132250587343),(-2259909065785917116993249336)⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨142055117083173955196890031710,142055117083173955266509919216⟩,⟨(-43361966406648825222924055099),(-43361966406648825165219022068)⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨163393852464146945599364726055,163393852464146945727984058661⟩,⟨(-165073270831339434691897505690),(-165073270831339434564104795104)⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨19019503810749814418655234891,19019503810749814606253107173⟩,⟨(-296210370866591030327617687552),(-296210370866591030112661404046)⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-253944327093641490557058448423),(-253944327093641490210228565100)⟩,⟨(-225858376628381785891883787092),(-225858376628381785542419044907)⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-340993264118827712079479663737),(-340993264118827711475877663888)⟩,⟨118972070618289811652326535576,118972070618289812228331293653⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-21303386718116892259862296050),(-21303386718116891227509907026)⟩,⟨361557019009793260474094844759,361557019009793261530283723541⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨321029686831450761971606575494,321029686831450763801802223434⟩,⟨129530471345017457786542523618,129530471345017459609023229687⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨200740670316478239671799823241,200740670316478242838764780840⟩,⟨(-245942002368319225434499956941),(-245942002368319222275742380360)⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-149241349194605016973212683217),(-149241349194605011003838193530)⟩,⟨(-237446110876817444283540704010),(-237446110876817438298000078513)⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-235654652700028344447463381093),(-235654652700028331073150475514)⟩,⟨39104104533426552029091297275,39104104533426565390045604549⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-66932093070692232159383937853),(-66932093070692195526376303649)⟩,⟨183573957210777647001825291004,183573957210777683635352797883⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨78884458648656001931453372345,78884458648656069673747284195⟩,⟨129291305781602539030683118848,129291305781602606781959688379⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨102215341334026205350708040082,102215341334026320180187162593⟩,⟨33833683334738263345824912575,33833683334738378175218902220⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨63440449828285868458224522532,63440449828285965877976598125⟩,⟨(-10467073708551826634341383692),(-10467073708551729217552531514)⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨19597189502667807231177315482,19597189502667841889553622480⟩,⟨(-8503295936917227403112315084),(-8503295936917192746118456590)⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨66568707719694977138302477735,66568707719695098030153989027⟩,⟨19940786847874499828530157537,19940786847874620709046410790⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨203400711218320787184104888907,203400711218321114596794205351⟩,⟨9000318521412196661081678603,9000318521412524050489045566⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨292782819377381837127991917153,292782819377382199572586332623⟩,⟨(-137568106872014607443398992924),(-137568106872014245000336328878)⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨176080538930784346738499961363,176080538930784544809936395275⟩,⟨(-383021039301054232418535274045),(-383021039301054034292434625938)⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-218706223119454337448974141723),(-218706223119454239351841789711)⟩,⟨(-441391737329253526666764040575),(-441391737329253428564449073802)⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨(-533930465858667361118348096978),(-533930465858667326947909316830)⟩,⟨(-33443338788357836173497565303),(-33443338788357802061110164505)⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-248228492060380010449554275639),(-248228492060379995662952932371)⟩,⟨491729234144048497067205478113,491729234144048511906925971066⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨378870197964974312604593065942,378870197964974320005728479061⟩,⟨390646549249379322647751931995,390646549249379330029894336157⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨465021356512682809255461652198,465021356512682813150819291594⟩,⟨(-229948274843193509119828415804),(-229948274843193505244145048277)⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨(-57773021501491523148084886760),(-57773021501491521166939387796)⟩,⟨(-473931102136450199245338573600),(-473931102136450197220970689886)⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨(-405005887623974238044496928624),(-405005887623974237004064827221)⟩,⟨(-121192789622740345834394490980),(-121192789622740344833279732679)⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨(-261364642440723118989863019806),(-261364642440723118451196795016)⟩,⟨243781775291682758413302421489,243781775291682758954119562137⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨18501266339015224206726548975,18501266339015224475115343271⟩,⟨283709795432023545938299702800,283709795432023546236418080836⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨142120476878653548128784232120,142120476878653548289856230972⟩,⟨149235347483884886119585035233,149235347483884886280181039066⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨117997928969881962393725221699,117997928969881962473092113007⟩,⟨40441723283706935912021349568,40441723283706935980607385983⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨41583367763476905777757869323,41583367763476905800504303125⟩,⟨3566706096866072867287173092,3566706096866072884914998681⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨9768958946007639310453166432,9768958946008320322882371526⟩,⟨83671405899533827304395250072,83671405899534508304443180777⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨90549471110135712576365143647,90549471110138729639743095164⟩,⟨227323177345830366258092159617,227323177345833383296135804798⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨299451133035429270959627816953,299451133035437684831506375077⟩,⟨239592510567695438625384515682,239592510567703852495872408179⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨492549737016522704829013726031,492549737016539190550748653272⟩,⟨(-37939872508249717884741936460),(-37939872508233232101754146936)⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨295876473214960038905686480914,295876473215002215067854675661⟩,⟨(-494568314825997684804764644811),(-494568314825955508637028551200)⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-345224460355181262381224956761),(-345224460355106682659788003457)⟩,⟨(-530346948745781931528946850074),(-530346948745707351875159755802)⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨(-646095789035112087271216369140),(-646095789034993344996784979811)⟩,⟨156744632293754626920863550366,156744632293873369259400661787⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨(-21694613913597046793764212594),(-21694613913441278508566848520)⟩,⟨673216700776754290384882039209,673216700776910058645700818763⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨634831795208860926765566261736,634831795209010083993039042799⟩,⟨183702208265137649398801930994,183702208265286806601834304060⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨333704273040577927997637877903,333704273040682702859023271390⟩,⟨(-533039853928099965292889795721),(-533039853927995190373809962560)⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-353705057303907009157552966558),(-353705057303845881748207138731)⟩,⟨(-458834391627797569322179791925),(-458834391627736441968525676294)⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-504784951847178711863069951265),(-504784951847146530361771110078)⟩,⟨90339487355642420218895468918,90339487355674601723951439490⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-194334054006611206777315752937),(-194334054006599363419543222326)⟩,⟨381244723338110144084308459218,381244723338121987486826733807⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨79177862728080377869070249169,79177862728086146877071803983⟩,⟨313668184133119352697636221028,313668184133125121704756276097⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨135859807848001646864638031000,135859807848003650600709666330⟩,⟨149212125096851336988634090773,149212125096853340707714653510⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨57243404229153381295767428507,57243404229153825959394300005⟩,⟨37743143893166703729180317248,37743143893167148384675093086⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨(-38815655903345132336830768466),(-38815655903345132309005283241)⟩,⟨2833817896946046902241254503,2833817896946046925767315881⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-106453219971170204189735265643),(-106453219971170204090438270528)⟩,⟨40275708583825603073085738048,40275708583825603163509964689⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-109752860630439490966401688977),(-109752860630439490757799264396)⟩,⟨145701467885601914191966954509,145701467885601914399924625909⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨38471804255651095145412305843,38471804255651095508637409293⟩,⟨243212853536848800695650692456,243212853536848801077728021775⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨278974735358953794218264345538,278974735358953794953940573688⟩,⟨126572633163463416360851194589,126572633163463417098209506015⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨273243723966102162297066783470,273243723966102163740296158283⟩,⟨(-230149962857754755745814061292),(-230149962857754754319206538305)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-138304548480842402060375916964),(-138304548480842399199394662532)⟩,⟨(-366673942114861892859664298388),(-366673942114861889985631339177)⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-407217163228410183186903841407),(-407217163228410177481402189257)⟩,⟨38241294357096178338418939311,38241294357096184040730161998⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-59800094707542574405000108297),(-59800094707542562143130111972)⟩,⟨407357515889177996420298486809,407357515889178008678694730064⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨369462566646345981468468026551,369462566646346015465820979494⟩,⟨160720902075404803587048181699,160720902075404837587901989003⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨262540987207511630107183532979,262540987207511742373090945483⟩,⟨(-278830753617482759728373978572),(-278830753617482647462413257045)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨(-115704204865959152972577271710),(-115704204865958750524897023309)⟩,⟨(-329749640911220823300477759477),(-329749640911220420853212219744)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-283632739985706565577089421496),(-283632739985705722952626066302)⟩,⟨(-93002741645071782829805459668),(-93002741645070940208412722821)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-211285261803537193958142124350),(-211285261803535640995074573707)⟩,⟨87713564367203669563293398626,87713564367205222526442117289⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-91670485674247091279744791244),(-91670485674245713375697868333)⟩,⟨110503235286039890850548867682,110503235286041268756478671014⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-21107565170588746180038482153),(-21107565170588245053699320214)⟩,⟨44089751600123371561700668127,44089751600123872689012098354⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨31535672940021295240715609751,31535672940154816094834521787⟩,⟨1492055611755814437613818048,1492055611889335291413560742⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨90501937727914425241759102251,90501937727914425422412203221⟩,⟨7464474015627734401854077035,7464474015627734581306872945⟩⟩
 def realAnswer : RBox := ⟨122037610667935720482374712002,122037610668069241517346725008⟩
end hm24_0_0_3
namespace hm24_0_0_4
noncomputable def s0_0 : CBox := ⟨⟨337369020533013991048260590,337369020533014141304470074⟩,⟨216699105179896533311840983,216699105179896683585126870⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨1038616184079848664913532315,1038616184079849049811991804⟩,⟨347414072084723560994572776,347414072084723945925346606⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨1492167097464005366413532569,1492167097464005746517395809⟩,⟨(-246803358124717767054569571),(-246803358124717386948428836)⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨1030324374322256242878753179,1030324374322256414821287941⟩,⟨(-1219927997536962042902750392),(-1219927997536961871008365567)⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-270379768290600833975495862),(-270379768290600769954364294)⟩,⟨(-1378787319570761501901362856),(-1378787319570761437885269604)⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-1001648786979130465354739162),(-1001648786979130450900638137)⟩,⟨(-342096356562047242003706899),(-342096356562047227527617122)⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-461924686264361629704395880),(-461924686264361626021157861)⟩,⟨507193716744026327512524524,507193716744026331187135973⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨179955346214161656309750389,179955346214161657315307841⟩,⟨334924534915025253199211827,334924534915025254205361579⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨174569031169254999672437612,174569031169254999943778511⟩,⟨(-31602858620005795633109829),(-31602858620005795361575325)⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨10598734273045277934543545,10598734273045277997811175⟩,⟨(-66930697721892805469625917),(-66930697721892805405743017)⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-17110358187283038448252348),(-17110358187283038435222047)⟩,⟨(-10787029570895876433499230),(-10787029570895876420895379)⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-3857975607514308574182277),(-3857975607514308571951200)⟩,⟨2051009560275406039519680,2051009560275406041703347⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-110232123987797952104061),(-110232123987797951889510)⟩,⟨588135405758468902083552,588135405758468902366692⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨20366196623673166856488,20366196623673166877947⟩,⟨35046864867805100683718,35046864867805100707216⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨678440452154905493729,678440452154905494548⟩,⟨401426181581106134192,401426181581106134734⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨786452635937486141,786452635937486160⟩,⟨181028546591443214,181028546591443230⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨3423609020364842127567307803,3423609020364845185907734965⟩,⟨4334547208656997572635757375,4334547208657000631374398113⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨12400801092843535629616885405,12400801092843548605183022989⟩,⟨9615197017732877630843620424,9615197017732890607206787174⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨23058835817722757681477485071,23058835817722791435442611263⟩,⟨4274733262210830735860576669,4274733262210864489884753116⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨24389748318706998486924507306,24389748318707058926852773301⟩,⟨(-13590255207513836822128656450),(-13590255207513776383797326884)⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨5228070391951315604825156752,5228070391951452389416764102⟩,⟨(-28530623161345239326005222771),(-28530623161345102541580077028)⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-20629642651430329099322882040),(-20629642651430119591319470554)⟩,⟨(-17877770478768164195700628278),(-17877770478767954686379890478)⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-21490262113534346793998951805),(-21490262113534060657600039073)⟩,⟨10161310712361960541376140556,10161310712362246676808713292⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨1940736726304866256724969246,1940736726305179634922407531⟩,⟨19326925450257767498636730310,19326925450258080877082952927⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨14691896759057403192501122156,14691896759057647505500787834⟩,⟨3216841812873385493235821586,3216841812873629806502107232⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨5841735507724378704750339730,5841735507724517863135686340⟩,⟨(-9453975431547078556472827088),(-9453975431546939398503536470)⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-4513484202980063634566902267),(-4513484202979997506951826868)⟩,⟨(-6456071201894957876799967479),(-6456071201894891748907085420)⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-5351430102114505937129955067),(-5351430102114477876680887546)⟩,⟨480856323927460888888206973,480856323927488949330842451⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-1942004969152756349476626034),(-1942004969152747847911339461)⟩,⟨2934289795602477626343786421,2934289795602486127777551227⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨264920948641380708898905304,264920948641384230784678692⟩,⟨2154671347715000812367201219,2154671347715004334254612295⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨671170686811802373497012709,671170686811803465354415500⟩,⟨958926375665150396929816926,958926375665151488820444222⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨279366050517522654869959624,279366050517522883482997496⟩,⟨240504769030692321322143775,240504769030692549949680156⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨885369510561577339414493238,885369510561577345401097343⟩,⟨20033807056735205792223885145,20033807056735205800535605146⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨16876641684289747333724851815,16876641684289747356256166482⟩,⟨55347926116469385160555843301,55347926116469385187854580445⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨63454987893912213583584031288,63454987893912213632937665698⟩,⟨62910562514659462251348368232,62910562514659462301039572141⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨111847460818006514253167621164,111847460818006514334692836178⟩,⟨7348719975934381306186350342,7348719975934381377109988127⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨83467214351387938058803130769,83467214351387938187884188735⟩,⟨(-93419835712266366417450069846),(-93419835712266366289411366496)⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-42223785109522359715370209766),(-42223785109522359509253629162)⟩,⟨(-122211074818298048505126899912),(-122211074818298048288818278449)⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-125158087992176636502619651647),(-125158087992176636137021982750)⟩,⟨(-7838671137990131552066983769),(-7838671137990131194932291439)⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-43672560013670349298916728887),(-43672560013670348691436453788)⟩,⟨106958023455815637783691194415,106958023455815638393763903954⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨78661836350475774596039794078,78661836350475775607921085137⟩,⟨64771400967898256343771553088,64771400967898257358429397468⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨73428448885385306279024779171,73428448885385308119741106910⟩,⟨(-45729197791437190161191505592),(-45729197791437188325658756958)⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-11345180740711479017329815854),(-11345180740711475066376992593)⟩,⟨(-69944607435947340201457290216),(-69944607435947336246411472931)⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-52445906549999752344230630157),(-52445906549999741898509163617)⟩,⟨(-19293419419294601830385853773),(-19293419419294591384802492577)⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-35849782056362540702783568642),(-35849782056362521989299589990)⟩,⟨21775359837358550087184045376,21775359837358568798080412270⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-9160132993050711242628853719),(-9160132993050680292777790611)⟩,⟨27570514471746622207391978126,27570514471746653157264302420⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨2765814628900212025649365406,2765814628900237829071425566⟩,⟨16808320191248661248308310132,16808320191248687052546928190⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨2231253589679328521985607500,2231253589679337616954053080⟩,⟨5142966156703581615366173745,5142966156703590710712347859⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨(-10429322780703709425679473584),(-10429322780703646208403715427)⟩,⟨34813264117216561244540584894,34813264117216624467809213101⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-4707777396665842698766679643),(-4707777396665672279692172134)⟩,⟨105865568601137270870773291839,105865568601137441302106894990⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨70841862117291469188450667608,70841862117291656176298426309⟩,⟨151000947732174115196213967100,151000947732174302184881773340⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨194675799564688553380301898575,194675799564688654276256289249⟩,⟨89750279810220437169565489748,89750279810220538037376660430⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨220654159988157095282516253115,220654159988157144366278606933⟩,⟨(-108881729630468542929846481232),(-108881729630468493848794347756)⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨16923389034145445255639602525,16923389034145461962642149355⟩,⟨(-260999694842283781708357114937),(-260999694842283764972452900793)⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-234292148844321292057853711328),(-234292148844321284964013771982)⟩,⟨(-119055483699220322606894876921),(-119055483699220315538793040101)⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨(-182010169063171102192439767829),(-182010169063171098757122806454)⟩,⟨175481837334768849489401199604,175481837334768852933590150085⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨103258099811961479393249728830,103258099811961481147262175506⟩,⟨210421371494726253112253414613,210421371494726254875498308704⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨208268665161938584448476102220,208268665161938585339832348790⟩,⟨(-24781887471566382063937728887),(-24781887471566381192145655291)⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨52240164631066542971998520728,52240164631066543400840161112⟩,⟨(-173008442588710995056465088613),(-173008442588710994610342931389)⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨(-101412401657255951032201077103),(-101412401657255950806017112764)⟩,⟨(-109152576831529869243797255780),(-109152576831529869018492864120)⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-115714583713941966512609351340),(-115714583713941966390382174872)⟩,⟨7390920364887794230496911612,7390920364887794340154663304⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-59844191739493339740594588205),(-59844191739493339675901147102)⟩,⟨56905973097553983113706788283,56905973097553983178589318466⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-16021145505693112083082173783),(-16021145505693112055841662235)⟩,⟨46701855429645980036189219518,46701855429645980067863571905⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-1403416703137893217995785594),(-1403416703137893211054442306)⟩,⟨16355840746975350853657296259,16355840746975350862692606721⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨(-54710476785028972638242833783),(-54710476785028527368142125279)⟩,⟨6386487578227236912106998499,6386487578227682190148325690⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-148086219962339014634702862666),(-148086219962337049886442697252)⟩,⟨58954901808936676059977917521,58954901808938640824434313099⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-154995587205114586009754102194),(-154995587205109148634545982538)⟩,⟨193519860769866748018847407327,193519860769872185394958304730⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨23968687040738136656352942083,23968687040748673134688298082⟩,⟨314968787846186044001972839133,314968787846196580441803861645⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨311512948398725737668232523051,311512948398752303688663916119⟩,⟨186952857675350834416563010805,186952857675377400433446060769⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨329090580050537702629637270726,329090580050583871584930769603⟩,⟨(-213357097247241972532516890659),(-213357097247195803535755800941)⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨(-94432003779162857555080695622),(-94432003779090670746577201232)⟩,⟨(-393023541640308376088941659109),(-393023541640236189318937597006)⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨(-400839966261854370473780075777),(-400839966261761592578294035769)⟩,⟨(-13891259638970470674979388169),(-13891259638877692765243495806)⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-107955275942055657122592268414),(-107955275941968763113678079235)⟩,⟨369642444396356244872562837461,369642444396443138895815191233⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨303473331559245108509235787265,303473331559304856881582097146⟩,⟨190970675453961560366349115215,190970675454021308705747288342⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨256586797667891321881002864006,256586797667925498902042263476⟩,⟨(-196978003401217533127762083214),(-196978003401183356075586382531)⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-49051521334533748651325589550),(-49051521334516104635566986335)⟩,⟨(-276561327508789468037180611502),(-276561327508771824023426891614)⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-205264715789731232192509926125),(-205264715789724848486699438491)⟩,⟨(-104902543047787819477708470767),(-104902543047781435796242235502)⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-166770987144688306873511929750),(-166770987144685238471085220385)⟩,⟨41994430893542387756045995543,41994430893545456158932614190⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-78608239543721427777385772270),(-78608239543720372043763444147)⟩,⟨71542383203868282019184521178,71542383203869337761872520762⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-19786704199788920158230125509),(-19786704199788687047023930587)⟩,⟨30008016768704214449794583214,30008016768704447565323588113⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨(-2223308033677423859362877597),(-2223308033677423840893601151)⟩,⟨(-30461436702116950340126586722),(-30461436702116950318192988887)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-31492692224591129681740262143),(-31492692224591129610911570307)⟩,⟨(-83281772238705539171571158123),(-83281772238705539093621728641)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-113228315451143753372241630322),(-113228315451143753210244035740)⟩,⟨(-85371812401065734815154282089),(-85371812401065734652634150545)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-187365534032542984780274097434),(-187365534032542984485406565212)⟩,⟨29482976549071105607037310964,29482976549071105887053376989⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-96601305334725535702536759215),(-96601305334725535140752269618)⟩,⟨212252386870478155159346008849,212252386870478155719786265476⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨172443842134369008209872396134,172443842134369009280623918842⟩,⟨205366309545487736125148488411,205366309545487737208654066806⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨271099118461600368788290248878,271099118461600370911066495520⟩,⟨(-101693615044270425122733204913),(-101693615044270423009737789511)⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-27183687841525462647544926402),(-27183687841525458508512585144)⟩,⟨(-295827742297473054072473032735),(-295827742297473049931146375952)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-290584707887976639401245175681),(-290584707887976630664470470797)⟩,⟨(-43263549548274547093996685424),(-43263549548274538354706799870)⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-113164346033985319424790255175),(-113164346033985295635261738103)⟩,⟨258786300026718934981277340246,258786300026718958768459871020⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨191879854467374271369722119868,191879854467374348621585786124⟩,⟨181262346925788441724886823447,181262346925788518976477586230⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨223867406519472845657306497062,223867406519473118396960557702⟩,⟨(-78236952381786512755362156525),(-78236952381786240015394838855)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨62432000017841251759146150764,62432000017841815326246904471⟩,⟨(-189863191426073959058130999514),(-189863191426073395488651920721)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-58045642755157393607135655629),(-58045642755156365240587422226)⟩,⟨(-140002481395130600340358000294),(-140002481395129571973872036099)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-72658156506759408581416400979),(-72658156506758502518893757440)⟩,⟨(-60296529949933176920889145020),(-60296529949932270859755654252)⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-28884075250070111934609696097),(-28884075250069783633234418351)⟩,⟨(-13828685853331011099158540398),(-13828685853330682798494555394)⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-10002611918824620271326821118),(-10002611918746160600004066396)⟩,⟨23365090280758340628433151411,23365090280836800300044691845⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-32244213004310992018399686956),(-32244213004310991899815569681)⟩,⟨67695291119442119600377085033,67695291119442119719299317005⟩⟩
 def realAnswer : RBox := ⟨(-42246824923135612289826508074),(-42246824923057152499719636077)⟩
end hm24_0_0_4
namespace hm24_0_0_5
noncomputable def s0_0 : CBox := ⟨⟨(-22588094204917950471380596),(-22588094204917934809610029)⟩,⟨35158550274188511560291679,35158550274188527220309742⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-35620962678367087235387484),(-35620962678367047859286128)⟩,⟨106169744294616557929730537,106169744294616597302579840⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨23917033622420051325028057,23917033622420088814844230⟩,⟨146881505979853997072096711,146881505979854034561670804⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨112740984386821809079982714,112740984386821825130416030⟩,⟨96149996358317979288681300,96149996358317995343424569⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨118292352334949008536042910,118292352334949014061919954⟩,⟨(-22251643514256812111579579),(-22251643514256806585241221)⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨27297554727308932233208369,27297554727308933362557428⟩,⟨(-77122483194949378440176810),(-77122483194949377312414971)⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-34017119354686647828909278),(-34017119354686647576196757)⟩,⟨(-31911351547186103728070299),(-31911351547186103474870772)⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-19653352093020306839502270),(-19653352093020306780433244)⟩,⟨10095641005093094178837272,10095641005093094237895379⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨1332529228470838128838492,1332529228470838142032873⟩,⟨8416622521349640430786892,8416622521349640443989936⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨2541512588727201030271399,2541512588727201032760461⟩,⟨468207558539381579574964,468207558539381582023471⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨323935954753601424948617,323935954753601425322100⟩,⟨(-484056430485784730515439),(-484056430485784730125378)⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-39564773877891469426803),(-39564773877891469380164)⟩,⟨(-79708953436342264012187),(-79708953436342263964111)⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-7701166344314502604009),(-7701166344314502599893)⟩,⟨(-1653015699493246089133),(-1653015699493246086172)⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-263621488221459538206),(-263621488221459537991)⟩,⟨145940714443256968995,145940714443256969191⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-1358022171988608639),(-1358022171988608620)⟩,⟨2236631819743715439,2236631819743715459⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-152587256853745),(-152587256853729)⟩,⟨654469601800110,654469601800126⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-905690287645028504054321360),(-905690287645027865018390652)⟩,⟨715280373610734024733683303,715280373610734663685545069⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-1991068122706738239283356635),(-1991068122706735555389625173)⟩,⟨2565580342368861980437797869,2565580342368864664164743368⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-873606435948441515697353730),(-873606435948434668220461098)⟩,⟨4681610606074071013495406551,4681610606074077860959595190⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨2672527416636932668537577669,2672527416636944586934170578⟩,⟨4821248586083303968240637302,4821248586083315886955163248⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨5424571102882814234888170174,5424571102882840200491488106⟩,⟨1013208300744688708838798231,1013208300744714674476015946⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨3267767561498119503127523939,3267767561498157466679663698⟩,⟨(-3735267666071696504216251622),(-3735267666071658540906787567)⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-1730210940701065397570802837),(-1730210940701016088427212997)⟩,⟨(-3715230309578043078624268808),(-3715230309577993769314180165)⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-3141098455217908076453970292),(-3141098455217857156946671501)⟩,⟨294122836667080492940847547,294122836667131412409471886⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-505666177953523566374704977),(-505666177953486415804653426)⟩,⟨2232819130139365315201951724,2232819130139402465729895252⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨1338412447165421326920478422,1338412447165441119045787569⟩,⟨840155534067799248805231427,840155534067819040990082973⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨860767163707608246494077452,860767163707617060665637539⟩,⟨(-593589265542340313495737631),(-593589265542331499360490639)⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-56233826137017772094839841),(-56233826137014276341534096)⟩,⟨(-664948028024308207186374890),(-664948028024304711432551325)⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-342234548374012200793449444),(-342234548374011204862704658)⟩,⟨(-228348435484800854029782751),(-228348435484799858083978001)⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-239651051729090201675945181),(-239651051729089809349858947)⟩,⟨28938302597125392598008360,28938302597125784923953140⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-102898406995047858962460823),(-102898406995047741725030955)⟩,⟨71890245732708258604686149,71890245732708375838700934⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-25310034798059064115996997),(-25310034798059040054108580)⟩,⟨29393841128469635653719885,29393841128469659714150538⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-6283771655346100344055842569),(-6283771655346100341428795089)⟩,⟨277490588958946978053703219,277490588958946979932899429⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-17251985448927886795200471534),(-17251985448927886786637441096)⟩,⟨5254797019511467382617597830,5254797019511467389655586382⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-19378042061580275436294816816),(-19378042061580275420936406378)⟩,⟨19514315091602637561909157868,19514315091602637577157461282⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-2270420842538804358599406939),(-2270420842538804337147631390)⟩,⟨33787678845771115428518997407,33787678845771115453255123544⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨27494976283109572182980655868,27494976283109572220796726864⟩,⟨24677875184302646568448371978,24677875184302646606593536802⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨35042823857649239260384506291,35042823857649239322403331293⟩,⟨(-11988413724563393241372473319),(-11988413724563393182362741827)⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨2299547262290303713221463545,2299547262290303812070884792⟩,⟨(-34663630891507872264083732329),(-34663630891507872162832450758)⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-28511532739276166837612742403),(-28511532739276166674905288386)⟩,⟨(-11779793120928872634296888025),(-11779793120928872472285292281)⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-16720976434689651220056222025),(-16720976434689650959954373159)⟩,⟨20129588670151870634601344825,20129588670151870893952672332⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨11210500572163043288193932654,11210500572163043739781409627⟩,⟨18167876696066341660097247356,18167876696066342113013018068⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨16610102506013294869920870267,16610102506013295805702405045⟩,⟨(-2632257329363614220149915916),(-2632257329363613285370467640)⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨4449257953730495419354861996,4449257953730497802351632292⟩,⟨(-11987918392375338792712380751),(-11987918392375336409686730177)⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-4809008345393219074509526046),(-4809008345393214939752299123)⟩,⟨(-7952860056865569791345256030),(-7952860056865565655992496080)⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-5949514284241339811862437063),(-5949514284241333138081003891)⟩,⟨(-1984069779729787619910705449),(-1984069779729780946133437197)⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-3562701554983402394705105716),(-3562701554983396926659324593)⟩,⟨584675766262152910395535793,584675766262158378261581637⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-1079752829914005016936832481),(-1079752829914003107430672107)⟩,⟨468383272853254051609620172,468383272853255961033343915⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨(-14564968781759968805729334474),(-14564968781759942354427253304)⟩,⟨(-4363752574819829117614773810),(-4363752574819802668847108420)⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-44080734832743322839439954865),(-44080734832743251866107836392)⟩,⟨(-1969949824847347871598817867),(-1969949824847276903430094113)⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-62302949718727707777087126126),(-62302949718727630600826008410)⟩,⟨29184778644919928252915149898,29184778644920005428825295754⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨(-36597955436507783546258488196),(-36597955436507742451892732009)⟩,⟨79158988343123494852181035921,79158988343123535958136368987⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨43365864507813570560443786681,43365864507813590206458976603⟩,⟨88247710693281966403010741896,88247710693281986050158573588⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨102071330933795810881902057208,102071330933795817439681175964⟩,⟨6843409634774133607355382964,6843409634774140153625849864⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨45682239568351806258746246687,45682239568351808961773959011⟩,⟨(-89310280176840257918837678444),(-89310280176840255205836329285)⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨(-65025832561303459978565966834),(-65025832561303458696260749586)⟩,⟨(-67845207425889063750262962495),(-67845207425889062471270813223)⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨(-76176823346821360504888021322),(-76176823346821359866336628579)⟩,⟨37095354326167202737730108133,37095354326167203372817661955⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨8499841484662189376236872526,8499841484662189683156934452⟩,⟨73223301594886222991343645020,73223301594886223305343528386⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨59127196031602874873489943891,59127196031602875026529795813⟩,⟨18014242159069206061709894664,18014242159069206208678908564⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨36469456434108313252373703890,36469456434108313327766284277⟩,⟨(-33751177956967608400859477541),(-33751177956967608325180463374)⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-2361084615303544392723399660),(-2361084615303544356879531054)⟩,⟨(-37757731554575421514056059016),(-37757731554575421473965752007)⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-18228751350771068199098749156),(-18228751350771068178190435015)⟩,⟨(-19198626658781345113751100943),(-19198626658781345092902600554)⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-14787237441304462046452757924),(-14787237441304462036340697734)⟩,⟨(-5077504559129121229744035581),(-5077504559129121221088674163)⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-5146552899658263224489422198),(-5146552899658263221618499456)⟩,⟨(-441770026714247087603012691),(-441770026714247085416366785)⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨(-3340149950350407168932027202),(-3340149950350174253835701878)⟩,⟨(-28618973494052610071337831288),(-28618973494052377160314063585)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-30707537277784208085856841903),(-30707537277783184491945077232)⟩,⟨(-77175016990605160732731096949),(-77175016990604137147099689406)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-100050245952200189640093405690),(-100050245952197378542540876104)⟩,⟨(-80215509875455435000729880191),(-80215509875452623903645725152)⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-161131565727179157740081561942),(-161131565727173770381632415973)⟩,⟨12112245748444832773246095713,12112245748450220151053539487⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-94503946747118885985827747496),(-94503946747105498954143633752)⟩,⟨156972735421693003760760268355,156972735421706390794251719197⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨105489851340202098209042235500,105489851340224963787801458814⟩,⟨163369729585754730642686127827,163369729585777596201113568755⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨191268715076977595827438526749,191268715077012704545309321621⟩,⟨(-45510701767919023103032714593),(-45510701767883914366666385644)⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨7081044909646906125202698596,7081044909691115628827083031⟩,⟨(-190938156089936456858874413248),(-190938156089892247361912680710)⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-172191250112123835668548117856),(-172191250112083336907313955107)⟩,⟨(-50751399333551835551679454403),(-50751399333511336797173739111)⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨(-87432171767248372997653211302),(-87432171767221114509376150558)⟩,⟨138224911373404927648779655471,138224911373432186152109739535⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨87759764561433440755219217677,87759764561448728306468304389⟩,⟨114793071130410204343667018401,114793071130425491880989802970⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨121220999736054196505594222553,121220999736061935590352237510⟩,⟨(-21305689672186439495842008917),(-21305689672178700410229139836)⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨45302199212267564726297126244,45302199212270317471831884225⟩,⟨(-88414333194071812572538970221),(-88414333194069059816409247744)⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-17818532839076954067364205858),(-17818532839075648443314747743)⟩,⟨(-70935741682057594720993275731),(-70935741682056289097135536639)⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-30138911770279002722143844845),(-30138911770278557714576463975)⟩,⟨(-33130179331887049383432849472),(-33130179331886604379734432128)⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-12584597445955044040432567160),(-12584597445954946271472312816)⟩,⟨(-8298489380555956487215066125),(-8298489380555858720092774338)⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨19124228121956751571742591662,19124228121956751585573751401⟩,⟨(-1395459972778126081874739042),(-1395459972778126070275206936)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨52123300953459142012577959136,52123300953459142061530517415⟩,⟨(-19700039551217717013824667435),(-19700039551217716969441003333)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨53125757520819380480143252030,53125757520819380581437663905⟩,⟨(-70394422358093471591429106465),(-70394422358093471490473179630)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-18075176014677044077346509172),(-18075176014677043904649759024)⟩,⟨(-115474684686917247160223705374),(-115474684686917246978171854729)⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-129192120503641402697637822639),(-129192120503641402356077696079)⟩,⟨(-58981959312916872555224020516),(-58981959312916872212805643058)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-123482463021211624661372598512),(-123482463021211624010606162026)⟩,⟨103366738022789119171827828443,103366738022789119814768306833⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨59819141858168591386854929059,59819141858168592635337009124⟩,⟨160352353140037898893391643382,160352353140037900147736089682⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨171930195657209454150656426322,171930195657209456555496625263⟩,⟨(-15451796790466137023562694097),(-15451796790466134620041997733)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨25035800007617010895975659023,25035800007617015879043443639⟩,⟨(-165832853718659358738039358602),(-165832853718659353756428151537)⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-145014776120175125657690940266),(-145014776120175112342686408893)⟩,⟨(-63743947355425094730025593838),(-63743947355425081413766230613)⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-100118892420032591182217556142),(-100118892420032548655047916985)⟩,⟨105637061045546466547608886460,105637061045546509075058723643⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨42322034733340432096540875735,42322034733340579968266251335⟩,⟨121589128252377165267472343581,121589128252377313139011123839⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨101676445068959501879248760569,101676445068959803426955247138⟩,⟨33528268418074340322395145059,33528268418074641868654827033⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨74215599687621848806244712248,74215599687622393594332825407⟩,⟨(-30730166532469369439362881600),(-30730166532468824651237494449)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨31728257702580777002168096846,31728257702581253638519468376⟩,⟨(-38219489791335531320407551247),(-38219489791335054683245999046)⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨7247926843464822075612369846,7247926843464994138184758511⟩,⟨(-15138031432454253671670936350),(-15138031432454081608686801470)⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-13042273036083012118060047664),(-13042273036045904377891279303)⟩,⟨(-9976153964108166892633190866),(-9976153964071059152661489583)⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-38103559409703560627623690834),(-38103559409703560563551547971)⟩,⟨(-31412668775155819992214627034),(-31412668775155819928017829348)⟩⟩
 def realAnswer : RBox := ⟨(-51145832445786572745783738498),(-51145832445749464941342827274)⟩
end hm24_0_0_5
namespace hm24_0_0_6
noncomputable def s0_0 : CBox := ⟨⟨(-3053365634370059916374601),(-3053365634370058556264119)⟩,⟨(-1962113598216098401320808),(-1962113598216097041060482)⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-9044731221644438195587343),(-9044731221644434839010885)⟩,⟨(-3043752742251721675231198),(-3043752742251718318382068)⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-12050945603187891744850086),(-12050945603187888662935863)⟩,⟨1931412066392861874451149,1931412066392864956386618⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-7479894595515826698235343),(-7479894595515825448531971)⟩,⟨8685976078398480698934075,8685976078398481948316158⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨1524851052426462448375741,1524851052426462846151791⟩,⟨8463054073154323604094684,8463054073154324001835970⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨4953800780741117057132758,4953800780741117130536014⟩,⟨1814894046028431786038881,1814894046028431859537095⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨1839261486096240090912585,1839261486096240105439800⟩,⟨(-1904277803060928675762628),(-1904277803060928661257649)⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-472797089063094196102535),(-472797089063094193205690)⟩,⟨(-963039636772267084396093),(-963039636772267081499602)⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-339266078895933978808682),(-339266078895933978271568)⟩,⟨46267546866480428147493,46267546866480428683413⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-16917917797188050350395),(-16917917797188050271066)⟩,⟨80825043167482087174449,80825043167482087255636⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨11500068580119274114707,11500068580119274124501⟩,⟨8132138456214138275078,8132138456214138284380⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨1384749843797160203914,1384749843797160204801⟩,⟨(-643663198796825062307),(-643663198796825061455)⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨20389632662929637928,20389632662929637980⟩,⟨(-85374672144939894092),(-85374672144939894022)⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-895677241929074137),(-895677241929074118)⟩,⟨(-1685132050997998526),(-1685132050997998508)⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-6323822808383882),(-6323822808383864)⟩,⟨(-3914633754772206),(-3914633754772190)⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-466313465848),(-466313465829)⟩,⟨(-109737757631),(-109737757614)⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-124534029129699041223904501),(-124534029129698929981584537)⟩,⟨(-157701298346534441672250812),(-157701298346534330415142182)⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-442331278997362108090909544),(-442331278997361645521997545)⟩,⟨(-343589654712460896160652447),(-343589654712460433562658353)⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-792122186109633484739741624),(-792122186109632327099675922)⟩,⟨(-148779611216824908974918354),(-148779611216823751332580103)⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-794269426008498575847591065),(-794269426008496617027548640)⟩,⟨437993841360825946830756151,437993841360827905598052008⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-163599430546818951606604064),(-163599430546814843519241544)⟩,⟨859605150060786350237417442,859605150060790458319045558⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨563704216064102354518823067,563704216064108088254379750⟩,⟨497825581019664194157284071,497825581019669927930097714⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨535369676269386248587106875,535369676269393331690032777⟩,⟨(-245539048221967980529382152),(-245539048221960897450365402)⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-36973073473035750828621622),(-36973073473028853982837274)⟩,⟨(-425551903418941588644902995),(-425551903418934691794118926)⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-282879567011898645441277982),(-282879567011893936160145207)⟩,⟨(-66190899669682079028898228),(-66190899669677369742228477)⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-100713937091972977160027905),(-100713937091970630375974705)⟩,⟨157958824279348730812182413,157958824279351077589132845⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨65074775022056402879069240,65074775022057382272834909⟩,⟨95668223215637389779752448,95668223215638369177474641⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨68875617380300419628121073,68875617380300782657557671⟩,⟨(-5461801859283168497759300),(-5461801859282805468348061)⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨22379758457673660786220547,22379758457673758039756569⟩,⟨(-33271454169466478576859815),(-33271454169466381324760422)⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-2633811977712228199020965),(-2633811977712191773726123)⟩,⟨(-22215881523898974518951774),(-22215881523898938093647393)⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-6417309503742029086874564),(-6417309503742018596593729)⟩,⟨(-9201914343318329936480824),(-9201914343318319445907947)⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-2577276949003000119443065),(-2577276949002998009222679)⟩,⟨(-2219646499581984441259907),(-2219646499581982330917643)⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-72475433383598267376999665),(-72475433383598266885433129)⟩,⟨(-1642466143182709979304036905),(-1642466143182709978612144016)⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-1363475956385982059341131919),(-1363475956385982057509118903)⟩,⟨(-4481246572429315561168031566),(-4481246572429315558929737720)⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-5001130339835508265145276231),(-5001130339835508261219350374)⟩,⟨(-4974202346935859661065742894),(-4974202346935859657109933967)⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-8506006508263805894654590302),(-8506006508263805888400009688)⟩,⟨(-584280485709541448287950646),(-584280485709541442880738452)⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-6080515999315333284784204996),(-6080515999315333275389934403)⟩,⟨6743883794565416684922007023,6743883794565416694229886185⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨2836529101011173718611809079,2836529101011173732691302943⟩,⟨8374137901324010900507431515,8374137901324010915326762071⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨8001122967143251663308894814,8001122967143251686679058205⟩,⟨560455078527491562144413434,560455078527491584946946095⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨2647818077611235821996183687,2647818077611235858007047767⟩,⟨(-6334255956979516893027502612),(-6334255956979516856861216187)⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-4293130362688516214092769112),(-4293130362688516158691221308)⟩,⟨(-3597484783691542108526578073),(-3597484783691542052956168083)⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-3746391071786634630506738639),(-3746391071786634537626340292)⟩,⟨2290405354154881179831572119,2290405354154881272428597357⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨508737179330496470341933699,508737179330496654668672416⟩,⟨3287448393470312088155820431,3287448393470312272686788664⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨2283686089883707344775423646,2283686089883707797859140898⟩,⟨855063499460076566117614799,855063499460077019196400653⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨1470308598326201920164908396,1470308598326202681752887916⟩,⟨(-885096995411486015448694079),(-885096995411485253974791116)⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨358132304189522696273077231,358132304189523895555017344⟩,⟨(-1069928553102670393906951156),(-1069928553102669194624348185)⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-102998317106685364813396835),(-102998317106684399242296287)⟩,⟨(-629303882989575680388129322),(-629303882989574714784107072)⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-81935742810939712147427766),(-81935742810939378088556831)⟩,⟨(-188909854120310968286124084),(-188909854120310634212282175)⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨1521538990791136537223018336,1521538990791145758563711609⟩,⟨(-5078007437050181987052114719),(-5078007437050172764818341653)⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨686917333934003310405541807,686917333934027938430178392⟩,⟨(-15295493992324594996890204779),(-15295493992324570367053477325)⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-10019495149195381327674097148),(-10019495149195354783226866631)⟩,⟨(-21422056510133493241601692799),(-21422056510133466697029370514)⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨(-26823547007755926914546842451),(-26823547007755912958467768285)⟩,⟨(-12436642490664680927263277648),(-12436642490664666975160833518)⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-29412161107889383060148278129),(-29412161107889376506351055776)⟩,⟨14393583139138700229030888667,14393583139138706782434049759⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨(-2303698824597260157643616894),(-2303698824597258020040580869)⟩,⟨33266323182309617972032823737,33266323182309620113453978841⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨28371739969827727173524850319,28371739969827728038214588427⟩,⟨14607447671492716253931037579,14607447671492717115401067400⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨21075760610380242602719348158,21075760610380242999558327495⟩,⟨(-20080777132220506560599857072),(-20080777132220506162730596196)⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨(-11105678494489320892345803118),(-11105678494489320700708609234)⟩,⟨(-22982678855706175782022298380),(-22982678855706175589302775638)⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨(-21454583046817572340466977090),(-21454583046817572248283585833)⟩,⟨2428127722073870794328569003,2428127722073870884378252537⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨(-5176547469892674387807960686),(-5176547469892674345832150748)⟩,⟨16840309887327980008002754585,16840309887327980051754433526⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨9361030053291440037671573195,9361030053291440058773407842⟩,⟨10154568061600473974154852847,10154568061600473995179335893⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨10267305509689390917842894523,10267305509689390928800923203⟩,⟨(-628292079185268596654053957),(-628292079185268586890233335)⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨5132688800073625469700392872,5132688800073625475299351842⟩,⟨(-4866117928045012379354105301),(-4866117928045012373739455209)⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨1340999726534404652750773370,1340999726534404655042560775⟩,⟨(-3901771985319924736512601955),(-3901771985319924733822527338)⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨115884381464913093669117265,115884381464913094243144279⟩,⟨(-1349519392071146492188081844),(-1349519392071146491427968825)⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨12475457813333062562180161386,12475457813333164087751232226⟩,⟨(-1455756468538907183561880052),(-1455756468538805656250901930)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨33516506381053129113362888222,33516506381053573500375198483⟩,⟨(-13328764282997814636866044247),(-13328764282997370246327291622)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨34595454995809896293340452377,34595454995811107405089023799⟩,⟨(-43105489577643406622505752045),(-43105489577642195510554882075)⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-5099932573642047537100555618),(-5099932573639752000553979273)⟩,⟨(-68693901332030695399799002847),(-68693901332028399871360612509)⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-65917303375241294074357542932),(-65917303375235672351487792301)⟩,⟨(-39810048144341590910102255644),(-39810048144335969187998934720)⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-67586077733211934440664359322),(-67586077733202497212780315592)⟩,⟨43465141885677962916947844198,43465141885687400153137920871⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨18276957502921301238336730866,18276957502935531288548278442⟩,⟨77571429327654619848085239799,77571429327668849890892856798⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨75796433166501948047418303434,75796433166519503858544069990⟩,⟨2995149570991974074063057854,2995149571009529887784477605⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨19881812401212491790803934498,19881812401228221782669962282⟩,⟨(-66845962926826522217685722037),(-66845962926810792223188807952)⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨(-52466951691398259228286238342),(-52466951691387895550980154357)⟩,⟨(-33358326812514551649565464682),(-33358326812504187977990524831)⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-42798526007813328815724294116),(-42798526007807630135260573999)⟩,⟨32583911479965337813721510384,32583911479971036499375928788⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨7711436109774623685335248468,7711436109777452547236071202⟩,⟨44278652183002258896843103635,44278652183005087758440566412⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨31736405307921980715162157938,31736405307922969928292158251⟩,⟨16303373292933278514027332897,16303373292934267723315040859⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨25143925388549367871860857916,25143925388549830835750824948⟩,⟨(-6300474650958206185346192056),(-6300474650957743221389713050)⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨11635901377152952957008867870,11635901377153109269398544442⟩,⟨(-10580647730275429678310633549),(-10580647730275273364545219652)⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨2900304412815157189313832226,2900304412815191359037946078⟩,⟨(-4398051620701212015232900840),(-4398051620701177844857690951)⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨729884170946604446865161153,729884170946604452936014781⟩,⟨10005442356616078061809351048,10005442356616078069077398442⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨10269371968311173576636294022,10269371968311173599813195257⟩,⟨27185256125928733555435467169,27185256125928733581053882700⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨36470549350799075818350151250,36470549350799075870779382239⟩,⟨27549677370127086677513411084,27549677370127086730125202754⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨59307078230610302918266417142,59307078230610303011932955961⟩,⟨(-9234318519104270411833627427),(-9234318519104270323075471414)⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨30010772888092341792402328464,30010772888092341966330251622⟩,⟨(-65530574636708880786173138044),(-65530574636708880612701283098)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-51634389796626011704079207734),(-51634389796626011382358147958)⟩,⟨(-61873859506186727123012224388),(-61873859506186726797290956159)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-79040650124259237213294379895),(-79040650124259236595621836590)⟩,⟨29322747455997663284519130229,29322747455997663899264214326⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨7315840090387809946511586736,7315840090387811109637774205⟩,⟨83271159757516966739793965402,83271159757516967903552338974⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨78867479107012479010779645201,78867479107012481377890071107⟩,⟨12071205776136905559065254631,12071205776136907926878468640⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨29921899301292860108389850204,29921899301292866320052288751⟩,⟨(-67719250683147911505315492246),(-67719250683147905294210985971)⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-48465225903058892975535293749),(-48465225903058873465502086260)⟩,⟨(-46084107408140632727076026310),(-46084107408140613217230949428)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨(-55033194706367858013582050605),(-55033194706367791202780921132)⟩,⟨19078390917702630346448287410,19078390917702697157340974593⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-15005005107314871394835198496),(-15005005107314736936974878622)⟩,⟨45375754490774075834632684069,45375754490774210293216064774⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨13557555679506091311528307742,13557555679506331819233225427⟩,⟨32785089519893172435385981392,32785089519893412943072651986⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨16753490046647407757279611138,16753490046647616704950086280⟩,⟨13912975291319051384518797240,13912975291319260331799311618⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨6611488147309546921486510108,6611488147309622070119606736⟩,⟨3165669534562735676305044903,3165669534562810824741297261⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨6559566882695801176971379271,6559566882710474932629435482⟩,⟨(-5903800417117441054383190149),(-5903800417102767298615738658)⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨20528291344010862261508759837,20528291344010862291015376743⟩,⟨(-17414573768618534845452516600),(-17414573768618534816178408265)⟩⟩
 def realAnswer : RBox := ⟨27087858226706663438380139108,27087858226721337223744812225⟩
end hm24_0_0_6
namespace hm24_0_0_7
noncomputable def s0_0 : CBox := ⟨⟨146091600021952700250304,146091600021952801515409⟩,⟨(-227291512947883891842995),(-227291512947883790588868)⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨222942528350985823891805,222942528350986069201327⟩,⟨(-660502126894578878636102),(-660502126894578633346171)⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-133686353580849742444258),(-133686353580849525239315)⟩,⟨(-847644547306623050932090),(-847644547306622833728734)⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-573824842726742314307683),(-573824842726742230916535)⟩,⟨(-498936966736996599500100),(-498936966736996516088440)⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-519327130254784564076279),(-519327130254784539522486)⟩,⟨89488228023631376917865,89488228023631401473878⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-103414674902415523062544),(-103414674902415518958379)⟩,⟨273036330611248211004357,273036330611248215103683⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨91518223994938245404843,91518223994938246119523⟩,⟨90967911281900465396040,90967911281900466111551⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨40530213249120832955745,40530213249120833077772⟩,⟨(-19011956339695849378614),(-19011956339695849256545)⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-1355049539097808565924),(-1355049539097808547191)⟩,⟨(-11758847091550652838990),(-11758847091550652820184)⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-2213815397263908645238),(-2213815397263908642940)⟩,⟨(-516997656019159386818),(-516997656019159384590)⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-175514281650100418963),(-175514281650100418748)⟩,⟨235919647388986155677,235919647388986155909⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨9079312092415001158,9079312092415001189⟩,⟨20788330787978787402,20788330787978787434⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨822536514345225958,822536514345225976⟩,⟨213957447958130308,213957447958130326⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨9379970712550742,9379970712550759⟩,⟨(-4818597406995033),(-4818597406995012)⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨9836013998872,9836013998888⟩,⟨(-15654086873192),(-15654086873174)⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨68819599,68819616⟩,⟨(-290384040),(-290384020)⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨23536661895691861047528592,23536661895691877650441927⟩,⟨(-18584625340798922715120161),(-18584625340798906114436451)⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨50822323618016953521309395,50822323618017021865678774⟩,⟨(-65368767333542184604233726),(-65368767333542116264210536)⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨21718325450040855949918341,21718325450041023711113181⟩,⟨(-114884780518713352348613044),(-114884780518713184587765942)⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-61531809079886369711544283),(-61531809079886093754186091)⟩,⟨(-112167401710896842831062597),(-112167401710896566866203759)⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-116774091900428991586653499),(-116774091900428434409711975)⟩,⟨(-22637546176459562096850348),(-22637546176459004919079797)⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-65016788252804088893062575),(-65016788252803346457123599)⟩,⟨72931484886210307855886888,72931484886211050286922757⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨29870929632884445949436884,29870929632885318297299470⟩,⟨66142365673309136094215282,66142365673310008445021097⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨49432179073543908925342483,49432179073544709871082673⟩,⟨(-3962262154331983193454575),(-3962262154331182248267127)⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨7421495937963994323171115,7421495937964506181973353⟩,⟨(-30729553645617527664835050),(-30729553645617015806656376)⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-15984939082343064884167911),(-15984939082342826278816958)⟩,⟨(-10350592810228444558120934),(-10350592810228205952043565)⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-9116910797931911725193427),(-9116910797931818410405311)⟩,⟨6116839592075046448673620,6116839592075139763092137⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨452961320532836981021510,452961320532869305478824⟩,⟨6116982957826771728155480,6116982957826804052612611⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨2773201034155489050406987,2773201034155497192493095⟩,⟨1880425641553130177016855,1880425641553138319220395⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨1765501219606911855556126,1765501219606914754753055⟩,⟨(-205438871819001115226283),(-205438871818998216029845)⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨705388364182865423494459,705388364182866228154245⟩,⟨(-491039596791955662434306),(-491039596791954857795892)⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨166851979860698592926212,166851979860698751573482⟩,⟨(-193696746232937867744840),(-193696746232937709106287)⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨367981543386006996633342758,367981543386006996789527496⟩,⟨(-16225074716450571547395792),(-16225074716450571437179557)⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨997734710854053559800816509,997734710854053560302287800⟩,⟨(-303246017725273754261427187),(-303246017725273753852674122)⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨1094456934553581227504300705,1094456934553581228377636222⟩,⟨(-1098613191396584237819946372),(-1098613191396584236953552457)⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨128824966503225858143333393,128824966503225859311637707⟩,⟨(-1835534884723357266570221485),(-1835534884723357265214638802)⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-1417894069469031588051933356),(-1417894069469031586088126521)⟩,⟨(-1284246309925976857277294207),(-1284246309925976855294088904)⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-1715410248333836008612137042),(-1715410248333836005576684323)⟩,⟨575265003788790894862012531,575265003788790897741649055⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-116764482800665404502881830),(-116764482800665399993744765)⟩,⟨1583157191041455829099650027,1583157191041455833723690080⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨1206349107333731984339863585,1206349107333731991231232977⟩,⟨510146514421765099058935522,510146514421765105920593046⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨663482593468856279001161763,663482593468856289178979286⟩,⟨(-784903387822258759798296017),(-784903387822258749653007777)⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-401134690183628638894318299),(-401134690183628622617773976)⟩,⟨(-662255291121854665015417797),(-662255291121854648687102621)⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-557761473181090725818757457),(-557761473181090694624798779)⟩,⟨84242705198756456231078181,84242705198756487389395972⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-140856230180098494540161788),(-140856230180098420695671699)⟩,⟨372927114936599734602293778,372927114936599808447486512⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨139638727261788921327539103,139638727261789041538527418⟩,⟨233010981959692095572440700,233010981959692215802137708⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨164929798136881773874294320,164929798136881958606238016⟩,⟨55410983653910406368548880,55410983653910591100405228⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨95279983210069038202579797,95279983210069184361820716⟩,⟨(-15552586971560240364854303),(-15552586971560094210775323)⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨28329499893717397050553155,28329499893717447148267598⟩,⟨(-12285686915983670595285284),(-12285686915983620499898124)⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨1517506377160590672263536978,1517506377160593428259748166⟩,⟨454736137947037525726243079,454736137947040281452737738⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨4549181215694383777488914379,4549181215694391103758764347⟩,⟨205304467928634965570395257,205304467928642291295205736⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨6313523238455601717977210786,6313523238455609543722943725⟩,⟨(-2948443005452937463481502211),(-2948443005452929637773959660)⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨3622506988028128183103330815,3622506988028132243413013998⟩,⟨(-7791020379995121021226484881),(-7791020379995116959747429080)⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-4094984145875869012296303524),(-4094984145875867138486420585)⟩,⟨(-8402664553428276573398498711),(-8402664553428274699471214421)⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨(-9293462010323694871680426598),(-9293462010323694272276605638)⟩,⟨(-664064150580774671046944634),(-664064150580774072728638436)⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-4003729333139092882564264986),(-4003729333139092647218591030)⟩,⟨7725841151178922043949549501,7725841151178922280185869577⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨5315577705828821069327665852,5315577705828821175147799797⟩,⟨5612059784557791144047999222,5612059784557791249593699904⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨5943710144617858083792689800,5943710144617858133650890003⟩,⟨(-2849937212300652372478421820),(-2849937212300652322909932497)⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨(-594207880069645837817186711),(-594207880069645815169800799)⟩,⟨(-5388534700474991855113866611),(-5388534700474991831915612476)⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨(-4111403952001476965851215821),(-4111403952001476955129635781)⟩,⟨(-1275004956645001594461274889),(-1275004956645001584184631749)⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨(-2423622087031274414472788696),(-2423622087031274409447115670)⟩,⟨2225510634072682797210528542,2225510634072682802254011453⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨143243477326282616335752829,143243477326282618615509885⟩,⟨2393174245380136181843507024,2393174245380136184410835839⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨1113446726396320407011505186,1113446726396320408303835211⟩,⟨1176198888821123906126970525,1176198888821123907415790243⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨882456102577979319038811173,882456102577979319652172963⟩,⟨303572984360432209767527009,303572984360432210287663225⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨303316052429600528764617253,303316052429600528937101059⟩,⟨26055960020798254719287421,26055960020798254848450866⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨543832078573178188714979795,543832078573216122088892702⟩,⟨4661356022715188006085542234,4661356022715225938822574151⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨4958942549799513230103901964,4958942549799678599933784510⟩,⟨12476567840246831868113011223,12476567840246997236656112301⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨15918541166827266847580936992,15918541166827714096140335589⟩,⟨12788979264046442369884931105,12788979264046889618369509934⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨25102364924490050070727938090,25102364924490888465893625694⟩,⟨(-1840333118551899888071693507),(-1840333118551061489995896346)⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨14374568663369680399339082255,14374568663371703959657187535⟩,⟨(-23726636926556406118925556193),(-23726636926554382558329114658)⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-15350864245765472066576014988),(-15350864245762133401996580508)⟩,⟨(-23966623419457110131491179336),(-23966623419453771469819754322)⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨(-26966623468705675193432573473),(-26966623468700731337897025241)⟩,⟨6291065882645145412218062503,6291065882650089270293847862⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨(-1081836932090157146750916320),(-1081836932084181361135730568)⟩,⟨25791322153332833151968740769,25791322153338808936717278840⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨22243781154908072081105816501,22243781154913309108633236512⟩,⟨6675788204156849332095480375,6675788204162086358741261827⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨10909380712778665708178363656,10909380712782043212532477414⟩,⟨(-17070787132776184331435888769),(-17070787132772806825211445675)⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-10369922632582189820671044021),(-10369922632580368948935630374)⟩,⟨(-13677544956783524710547344976),(-13677544956781703840470263258)⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-13863583311630958086811661917),(-13863583311630071751358969352)⟩,⟨2392243917483723498479989427,2392243917484609834024829357⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-5029155011734543789845865623),(-5029155011734239090154650910)⟩,⟨9764588299048545324295895904,9764588299048850025181385487⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨1909546062364112049983904966,1909546062364252762897350766⟩,⟨7639392973461811000874615291,7639392973461951713768310653⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨3183845058130870008918003057,3183845058130917072179837170⟩,⟨3502928404288727143700940619,3502928404288774206543538321⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨1317451795489126233067227581,1317451795489136469577214647⟩,⟨868843467493472593210188481,868843467493482829522511377⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨(-4486854386772735058314181336),(-4486854386772735055040609559)⟩,⟨327222966859848658205754201,327222966859848660929159069⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-12153153043780642299482579559),(-12153153043780642287991044396)⟩,⟨4588540885226923181820813635,4588540885226923192194672465⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-12245685489295221483950184364),(-12245685489295221460527619963)⟩,⟨16195772586418145826052736179,16195772586418145849390972701⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨4043641390614466005140577321,4043641390614466044241744997⟩,⟨26108588475933817956462880961,26108588475933817997770440887⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨28491209862185682278181666033,28491209862185682353699470375⟩,⟨13088545999700966620272939641,13088545999700966695998229067⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨26574763960329134007978755418,26574763960329134147721261901⟩,⟨(-22108377454334362845361891509),(-22108377454334362707371346327)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-12320307255001089847421871793),(-12320307255001089587961357134)⟩,⟨(-33395507915204564349320747793),(-33395507915204564088607475407)⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-34570106714908016991601766563),(-34570106714908016508872373960)⟩,⟨2967487358576107365842096529,2967487358576107848311959354⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-4987996068284627473051257650),(-4987996068284626508639374193)⟩,⟨32150621304480705979897352891,32150621304480706944018647282⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨27106622577548731624494672800,27106622577548734107971092659⟩,⟨12039118955425824864162834351,12039118955425827347851300054⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨18182243604996079062857116151,18182243604996086734774698457⟩,⟨(-19059242830533905956584908669),(-19059242830533898284569930512)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨(-7371773510009076479158726979),(-7371773510009050604796480609)⟩,⟨(-21350854451237498783198414640),(-21350854451237472908874310242)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-17357443181377604947585855120),(-17357443181377553557489246035)⟩,⟨(-5755946804951999716741776249),(-5755946804951948326951402904)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-12414056202074640668992591929),(-12414056202074549659551643634)⟩,⟨5126884486837098057816488962,5126884486837189067264981980⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-5229355225864807355187072369),(-5229355225864728842355065811)⟩,⟨6294772686271151575429322644,6294772686271230088420926120⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-1185142831461770645074656727),(-1185142831461742512671872013)⟩,⟨2475040941221029644276537698,2475040941221057776759381590⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨2252754952850455335059939070,2252754952855440710987160753⟩,⟨3373283650805465508757244149,3373283650810450884632957947⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨6729365308027706010774784204,6729365308027706022407118690⟩,⟨10540201987632755219934442064,10540201987632755231743606112⟩⟩
 def realAnswer : RBox := ⟨8982120260878161345734723274,8982120260883146733494279443⟩
end hm24_0_0_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock24_1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid
namespace hm24_0_0_8
noncomputable def s0_0 : CBox := ⟨⟨14804679858531109945427,14804679858531116541169⟩,⟨9517825235734999110523,9517825235735005706970⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨42207659604078502827816,42207659604078518513430⟩,⟨14289303410763811750829,14289303410763827437678⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨52179475349895377469966,52179475349895390866838⟩,⟨(-8096497560521940493820),(-8096497560521927096842)⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨29130860977893100166274,29130860977893105039506⟩,⟨(-33183257054893587347548),(-33183257054893582475460)⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-4590807900404019130961),(-4590807900404017803715)⟩,⟨(-27903001607352436428957),(-27903001607352435101832)⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-13181926693862448131193),(-13181926693862447930662)⟩,⟨(-5155684140153901814341),(-5155684140153901613590)⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-3941140211744478719433),(-3941140211744478688536)⟩,⟨3854641052772352836845,3854641052772352867718⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨670113373556302540003,670113373556302544532⟩,⟨1495442209181430348419,1495442209181430352943⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨357699382023213065131,357699382023213065727⟩,⟨(-33957869338215937484),(-33957869338215936895)⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨13688110198695703353,13688110198695703427⟩,⟨(-53302450647593107976),(-53302450647593107901)⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-4264640162964008923),(-4264640162964008902)⟩,⟨(-3324104791356901122),(-3324104791356901101)⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-275080374213739607),(-275080374213739589)⟩,⟨113292568861300431,113292568861300447⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-1956322586287029),(-1956322586287012)⟩,⟨7017615069508531,7017615069508548⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨23101772350573,23101772350589⟩,⟨46275358639703,46275358639719⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨34459011573,34459011591⟩,⟨21909217714,21909217730⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨160537,160559⟩,⟨38254,38270⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨2426769144110627535718533,2426769144110629703376706⟩,⟨3073713274802696524648834,3073713274802698692601112⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨8452951888099774680277356,8452951888099783514924633⟩,⟨6577854624440286839904216,6577854624440295675119773⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨14580119806539369723791061,14580119806539390997137507⟩,⟨2774083272943633887538459,2774083272943655160931379⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨13861515929642388472536361,13861515929642422494706317⟩,⟨(-7564359493907591535354583),(-7564359493907557514117895)⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨2740314234695173207677557,2740314234695239340375316⟩,⟨(-13882340271039876435957149),(-13882340271039810303363987)⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-8257871187375859670663512),(-8257871187375775536084784)⟩,⟨(-7431054442844058998388281),(-7431054442843974863244909)⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-7151841755820692743196232),(-7151841755820598708896603)⟩,⟨3180082610669091744650995,3180082610669185778633558⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨369185866914119762461502,369185866914201175714766⟩,⟨5025827341967545597257799,5025827341967627010564394⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨2921945901316077927310175,2921945901316126624577635⟩,⟨727646260999443825722545,727646260999492523051407⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨930980761019863360243309,930980761019884596262401⟩,⟨(-1415944742043039242343800),(-1415944742043018006389733)⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-503251282712729405862989),(-503251282712721623574652)⟩,⟨(-760465245429969609935955),(-760465245429961827617398)⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-475507466648755345194098),(-475507466648752825992026)⟩,⟨32725137052404470903012,32725137052406990105279⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-138278444814674649260870),(-138278444814674052638260)⟩,⟨202305395657129350112936,202305395657129946727154⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨14019031448818334498921,14019031448818536440324⟩,⟨122785611706017869351118,122785611706018071292536⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨32878759263334192477601,32878759263334246484531⟩,⟨47316626494470716606960,47316626494470770615256⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨12737813706100050393907,12737813706100060829127⟩,⟨10974638766455288101461,10974638766455298537223⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨3178269750722112433356732,3178269750722112454979785⟩,⟨72137995306313630321291082,72137995306313630352138760⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨59013810483601275974172610,59013810483601276053972236⟩,⟨194376002883357938869288402,194376002883357938967592022⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨211172844940114236939318154,211172844940114237106618319⟩,⟨210712556075404868738615693,210712556075404868907324834⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨346596356966305553292692868,346596356966305553549773924⟩,⟨24843081246394469156931294,24843081246394469377816089⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨237348347222790611295323494,237348347222790611661683592⟩,⟨(-260861121951763275800369773),(-260861121951763275437813524)⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-102084184398375648727937793),(-102084184398375648212554364)⟩,⟨(-307494642622577014439131935),(-307494642622577013895051545)⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-274124687280457636519279716),(-274124687280457635718644038)⟩,⟨(-21233675516987668682998425),(-21233675516987667902701139)⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-86002923443059451368264081),(-86002923443059450224102141)⟩,⟨201051653298534938431922415,201051653298534939581047212⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨125578779871566766067533653,125578779871566767693347761⟩,⟨107079903905622643694197291,107079903905622645325488721⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨102446189576820942399390537,102446189576820944911417925⟩,⟨(-61477133009546862447097055),(-61477133009546859943338687)⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-12200849684865853701438847),(-12200849684865849092285761)⟩,⟨(-82812477843164080456840346),(-82812477843164075842250007)⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-53291912002901990370624594),(-53291912002901979838524127)⟩,⟨(-20303717221455848285615318),(-20303717221455837753599229)⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-32313336587288067835693398),(-32313336587288051226730707)⟩,⟨19277712340908431686219975,19277712340908448292500807⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-7501857898975680664448841),(-7501857898975655765095350)⟩,⟨22246895006152987683760191,22246895006153012583123255⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨2054884766251251998272291,2054884766251271355927711⟩,⟨12622868726230086062433321,12622868726230105420796062⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨1611886154900279572400407,1611886154900286145668461⟩,⟨3717338240297901608923400,3717338240297908182507619⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨(-118917045258992848195381921),(-118917045258992127608393283)⟩,⟨396803941572303894815515924,396803941572304615473771089⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-53689810794700397441926879),(-53689810794698490745712237)⟩,⟨1183894100932079725398407550,1183894100932081632238050628⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨759192562846099826302798248,759192562846101845070659638⟩,⟨1628153389134679967559418223,1628153389134681986337475229⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨1980110763215643831942817479,1980110763215644866184317972⟩,⟨923272495660086452934358819,923272495660087486875018052⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨2100528339050829288018210213,2100528339050829756867790155⟩,⟨(-1019419141055057077497820226),(-1019419141055056608678817264)⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨167342607268938212516933044,167342607268938359059718674⟩,⟨(-2271835042452956167783961494),(-2271835042452956020971189854)⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-1840923448716033533001102445),(-1840923448716033476525108266)⟩,⟨(-960225719452100594386367786),(-960225719452100538125889527)⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨(-1307648573014669073881730701),(-1307648573014669049317603852)⟩,⟨1231262595583383253653058691,1231262595583383278281104770⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨639948373596261082166956173,639948373596261093386263284⟩,⟨1345081400887691624261457025,1345081400887691635548580994⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨1184284218823140163082917768,1184284218823140168191402983⟩,⟨(-127160671358000445534932181),(-127160671358000440550820624)⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨274780630695956767478969206,274780630695956769680562799⟩,⟨(-878339364441708110064292803),(-878339364441708107765226121)⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨(-462979663519807946521040854),(-462979663519807945466262130)⟩,⟨(-506167704219477111412936895),(-506167704219477110361725342)⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-488106103800214824701082005),(-488106103800214824174772126)⟩,⟨28562580189574396910357904,28562580189574397376132805⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-235848160043515838329155410),(-235848160043515838069567530)⟩,⟨222931895651824148366472491,222931895651824148626743771⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-60132388449514541098015197),(-60132388449514540994722793)⟩,⟨174636718879333497024338129,174636718879333497146701703⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-5126224304790767503386801),(-5126224304790767477956276)⟩,⟨59651323017291573556214989,59651323017291573590459243⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨(-1523969385929416303369338682),(-1523969385929403902243775762)⟩,⟨177766157630387385337184696,177766157630399786666644726⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-4063878765828018477702042138),(-4063878765827964631676672983)⟩,⟨1614348888322588181647574276,1614348888322642028083620776⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-4136792125343168847276235088),(-4136792125343024328368497295)⟩,⟨5143811595266208285680230399,5143811595266352804612157323⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨580997067074406656554768065,580997067074674592180147130⟩,⟨8026474667839209136016814132,8026474667839477070728554781⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨7472902778770189388066260277,7472902778770826740345936254⟩,⟨4541623549996289132578703796,4541623549996926484770011700⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨7436614047739243711784295401,7436614047740277235816295255⟩,⟨(-4743956822052241759864340899),(-4743956822051208234941634437)⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨(-1894649227441025034487453078),(-1894649227439522069985868016)⟩,⟨(-8203007415198950492265462319),(-8203007415197447528526406582)⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨(-7679307811999699705066832532),(-7679307811997919817600249586)⟩,⟨(-340774231034041831654645309),(-340774231032261943934906018)⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-1961295176839847280827100636),(-1961295176838321594106830533)⟩,⟨6476885509146082509849992207,6476885509147608196828747744⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨4860090157337716828540635670,4860090157338680000152014184⟩,⟨3121861294004233937661676213,3121861294005197108738971644⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨3824798062121501639787608990,3824798062122010743544745543⟩,⟨(-2887800679732001129292871813),(-2887800679731492025072151991)⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-649322613491030133304309214),(-649322613490787134722909884)⟩,⟨(-3798184091248262520260122349),(-3798184091248019521703178539)⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-2628851971265894465112964446),(-2628851971265812340354155315)⟩,⟨(-1357459133830317402416958300),(-1357459133830235277982934704)⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-2030940827915825066934656005),(-2030940827915787644396125871)⟩,⟨506404314961781728791948865,506404314961819151335603044⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-922725062539693776060156426),(-922725062539681377458139963)⟩,⟨838303767885979130405921290,838303767885991529119706847⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-227744425528900700301122083),(-227744425528898017096194844)⟩,⟨345316558784124719753805821,345316558784127403011230998⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨(-128363551613392963529565912),(-128363551613392962460553716)⟩,⟨(-1760580153299833363666649076),(-1760580153299833362376541683)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-1793965570960469600170130525),(-1793965570960469596107260857)⟩,⟨(-4753936407753783761492418807),(-4753936407753783756982096006)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-6293194981919232067249128900),(-6293194981919232058158994117)⟩,⟨(-4762771305771771005474929757),(-4762771305771770996350738367)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-10057087273901693465706217191),(-10057087273901693449766333244)⟩,⟨1549318219445220005185838276,1549318219445220020258271825⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-4994783924841139580811997782),(-4994783924841139551963260919)⟩,⟨10839059961636395596266916114,10839059961636395625033150140⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨8283028000127521915555538014,8283028000127521967344253533⟩,⟨9987268900038431350799685081,9987268900038431403259557548⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨12346470425600644237178693798,12346470425600644333469804334⟩,⟨(-4529451447718055531131833172),(-4529451447718055435309708241)⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-1052682923189539257744032664),(-1052682923189539082625225725)⟩,⟨(-12558139910123574832871247128),(-12558139910123574657659246383)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-11468315999664413113345393555),(-11468315999664412769736687440)⟩,⟨(-1803202692612456929414184364),(-1803202692612456585700365312)⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-4238483170763635877008902325),(-4238483170763635008038600811)⟩,⟨9494167774842238395783122221,9494167774842239264683125095⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨6558391999621120726877795128,6558391999621123366723241169⟩,⟨6277110023499083957603273601,6277110023499086597407154908⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨7248050148429317996686789263,7248050148429326764806059549⟩,⟨(-2492367576852090040897899754),(-2492367576852081272764837025)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨1932003185548648619098772707,1932003185548665805333806027⟩,⟨(-5809795907460800845793524749),(-5809795907460783659446052535)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-1696430869237795530890399831),(-1696430869237765397018155740)⟩,⟨(-4113031570986050807530506774),(-4113031570986020673660960053)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-2069493216413726192148330039),(-2069493216413700378183226294)⟩,⟨(-1719829750844887383453412127),(-1719829750844861569545075776)⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-810725318573353948659232709),(-810725318573344733491914233)⟩,⟨(-388225444160510370847002809),(-388225444160501155707994924)⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-1449237718673207031449399829),(-1449237718671721976086379671)⟩,⟨742144759819834582338172436,742144759821319637722318816⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-4529364766859396733321744992),(-4529364766859396729128386972)⟩,⟨2256316090509323774257115124,2256316090509323778353434342⟩⟩
 def realAnswer : RBox := ⟨(-5978602485532603764871144821),(-5978602485531118705114766643)⟩
end hm24_0_0_8
namespace hm24_0_0_9
noncomputable def s0_0 : CBox := ⟨⟨(-551189597956688783605),(-551189597956688401639)⟩,⟨857167391036830963942,857167391036831345872⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-814147524212962846679),(-814147524212961954930)⟩,⟨2397652466525179367817,2397652466525180259496⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨435856232578121671379,435856232578122406032⟩,⟨2855736593105067089933,2855736593105067824582⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨1706385548074932516221,1706385548074932769354⟩,⟨1512364134809586314975,1512364134809586568162⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨1333502422932135072732,1333502422932135136546⟩,⟨(-209116336464542300058),(-209116336464542236236)⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨228463404200104005992,228463404200104014746⟩,⟨(-566304619159716739398),(-566304619159716730653)⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-144543085867604017922),(-144543085867604016717)⟩,⟨(-151939745842399795291),(-151939745842399794087)⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-49139316788189800598),(-49139316788189800431)⟩,⟨21032006395271994544,21032006395271994715⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨732255099333004914,732255099333004949⟩,⟨9700424257275071594,9700424257275071629⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨1145806814830191966,1145806814830191988⟩,⟨319756098809164882,319756098809164900⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨56113581099923631,56113581099923649⟩,⟨(-68980094847645048),(-68980094847645029)⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-1269596376522630),(-1269596376522611)⟩,⟨(-3256931287359768),(-3256931287359750)⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-53772633883397),(-53772633883379)⟩,⟨(-15867137924656),(-15867137924639)⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-205076516399),(-205076516382)⟩,⟨99934757603,99934757623⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-43833786),(-43833770)⟩,⟨68285525,68285542⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-33),(-17)⟩,⟨67,94⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-356804354069016825942806),(-356804354069016574312203)⟩,⟨281677025553589767138612,281677025553590018734737⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-756778453687519635956940),(-756778453687518620675596)⟩,⟨971631044180994273344819,971631044180995288560120⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-314965066260132071860851),(-314965066260129673858539)⟩,⟨1644854090516177086539870,1644854090516179484536668⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨826656270844051824994234,826656270844055553601453⟩,⟨1522787805735105250857728,1522787805735108979568165⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨1467191998479171980856862,1467191998479178959095420⟩,⟨294807249325356818796898,294807249325363797047155⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨755076500639117045668716,755076500639125522537869⟩,⟨(-831285203333490831760759),(-831285203333482354949411)⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-300973986239498466252168),(-300973986239489453725930)⟩,⟨(-687554507896964140777398),(-687554507896955128220794)⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-454344070030130550389873),(-454344070030123192273259)⟩,⟨30346261598075891893583,30346261598083250005636⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-63378858604132189180324),(-63378858604128069542304)⟩,⟨247052049750583519521522,247052049750587639154173⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨111529415367474245861294,111529415367475926542568⟩,⟨74448277382058463075266,74448277382060143761712⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨56402834856706990671444,56402834856707567800008⟩,⟨(-36815119727460683889660),(-36815119727460106763290)⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-2090903408528192204070),(-2090903408528017631606)⟩,⟨(-32867342323310541109438),(-32867342323310366536999)⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-13121683986710340340247),(-13121683986710301470498)⟩,⟨(-9040429560224086661376),(-9040429560224047791091)⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-7591738050843268817904),(-7591738050843256312839)⟩,⟨850211035818374115442,850211035818386620508⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-2821460786858296793779),(-2821460786858293571340)⟩,⟨1956992443091616640733,1956992443091619863100⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-641652436356028361986),(-641652436356027751780)⟩,⟨744591744155866795495,744591744155867405672⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-12570424631775169085985839),(-12570424631775169080570435)⟩,⟨553404126023648163509440,553404126023648167280268⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-33660530929896633666780904),(-33660530929896633649652090)⟩,⟨10208514861333274965112058,10208514861333274978960086⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-36061025868836743483875241),(-36061025868836743454905316)⟩,⟨36081733002779027053005594,36081733002779027081721642⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-4256815692486305204545145),(-4256815692486305167422195)⟩,⟨58176713554536419603642495,58176713554536419646980607⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨42662495873526278182676237,42662495873526278242176676⟩,⟨38993610389662511654125570,38993610389662511714287815⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨48999102941733500422914959,48999102941733500509608526⟩,⟨(-16102672247623054854481058),(-16102672247623054772482747)⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨3424720225260765142836796,3424720225260765262875854⟩,⟨(-42195163584729792932241010),(-42195163584729792809003957)⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-29787838917980011423097278),(-29787838917980011252752657)⟩,⟨(-12887918853549765859868123),(-12887918853549765690259307)⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-15362910378465032799369402),(-15362910378465032566927826)⟩,⟨17861330031005782542286261,17861330031005782773908855⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨8375718450030939577301522,8375718450030939919696400⟩,⟨14088457944667740925003664,14088457944667741268571623⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨10930501329209134901637828,10930501329209135508509420⟩,⟨(-1569986634244367649005969),(-1569986634244367042871059)⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨2601574842328986075615190,2601574842328987410960297⟩,⟨(-6769987485397980312011846),(-6769987485397978976658230)⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-2365806424911991614192249),(-2365806424911989574901411)⟩,⟨(-3983493421122942273363569),(-3983493421122940233731344)⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-2667503734857952487338730),(-2667503734857949504019753)⟩,⟨(-902821311184837673618515),(-902821311184834690300396)⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-1486514040301114254602023),(-1486514040301111975490757)⟩,⟨241337084530503700964114,241337084530505979989318⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-433584303259023964004257),(-433584303259023197287675)⟩,⟨187982570403339390061672,187982570403340156740126⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨(-92229343031502397431704166),(-92229343031502229926694427)⟩,⟨(-27642443629418073979735783),(-27642443629417906491462551)⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-273868315398451036823023316),(-273868315398450595664432479)⟩,⟨(-12480282264324343466924152),(-12480282264323902341879436)⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-373225394610848769451629411),(-373225394610848306534042424)⟩,⟨173765235380133633143308772,173765235380134096058477754⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨(-209172486484411772078074078),(-209172486484411538038969013)⟩,⟨447343433324849454026731359,447343433324849688134623962⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨225584908945967067430285933,225584908945967171696913711⟩,⟨466767814051465211491778828,466767814051465315765479309⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨493676007859760321088979938,493676007859760353053961619⟩,⟨37452297270906547808577245,37452297270906579713881713⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨204710268973930251692390900,204710268973930263647984277⟩,⟨(-389937751872247496863152269),(-389937751872247484861215985)⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨(-253524912464050911474384307),(-253524912464050906379143563)⟩,⟨(-270850023756086684300781717),(-270850023756086679218765587)⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨(-270590692205611154588317017),(-270590692205611152316856625)⟩,⟨127736040493565848678137514,127736040493565850935494457⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨24173504053065687176974716,24173504053065688152033061⟩,⟨231374372021314237863095420,231374372021314238863101343⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨166803863516856807026276266,166803863516856807464516717⟩,⟨52638391321991274312669022,52638391321991274731941254⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨93970043339381320410506340,93970043339381320605963876⟩,⟨(-85616963584960974231680768),(-85616963584960974035592271)⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-5060103382212595841573557),(-5060103382212595756983010)⟩,⟨(-88494373316764662400231361),(-88494373316764662304323969)⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-39676226296001789363785234),(-39676226296001789317192218)⟩,⟨(-42037756773668633939455374),(-42037756773668633892979925)⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-30720527443150796384148014),(-30720527443150796362450465)⟩,⟨(-10587760615759384842803749),(-10587760615759384824570339)⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-10427798004677977339492989),(-10427798004677977333450205)⟩,⟨(-896470308431607865703998),(-896470308431607861253388)⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨(-51651262938095370116897757),(-51651262938091766300736719)⟩,⟨(-442881787573139953471916370),(-442881787573136349713753704)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-467147768658870614037997764),(-467147768658855029056846960)⟩,⟨(-1176616681132987779198517364),(-1176616681132972194333821097)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-1477465581214068054348675148),(-1477465581214026544505358154)⟩,⟨(-1189438285971806556880998369),(-1189438285971765047044625925)⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-2281330501023908852702532226),(-2281330501023832739016915992)⟩,⟨163017675001107013093575854,163017675001183127034082414⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-1275501722101411865387711608),(-1275501722101233422685376939)⟩,⟨2092176435271611071819285457,2092176435271789514546537163⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨1303179477284839292163133699,1303179477285123691617110653⟩,⟨2051170793689004753087434582,2051170793689289152298947439⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨2218098385289047181423172116,2218098385289453338306997836⟩,⟨(-507173450939763778974743359),(-507173450939357621887472337)⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨95132285471352684196840838,95132285471823936162013453⟩,⟨(-2032514253348481280583848268),(-2032514253348010028684399641)⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-1676437766921859844471475157),(-1676437766921464742002852505)⟩,⟨(-512173354794932145705843131),(-512173354794537043304576876)⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨(-794116422769160163636094237),(-794116422768916003022774233)⟩,⟨1229978764216871826240691608,1229978764217115986989578282⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨714854673588216381878517840,714854673588342912640669314⟩,⟨950756474815785541996554470,950756474815912072643510808⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨924986411927240885457589670,924986411927300105379499138⟩,⟨(-156653242662092783658867440),(-156653242662033563731197868)⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨325695764836525339063963965,325695764836545014697705889⟩,⟨(-629120370217946320195622670),(-629120370217926644483373880)⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-119375298598810856927635704),(-119375298598802010159443075)⟩,⟨(-479940899246253768106143681),(-479940899246244921339130843)⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-196200523085482138231889982),(-196200523085479234740905879)⟩,⟨(-216054155285084395672818988),(-216054155285081492208317746)⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-80454021821106411728009272),(-80454021821105786525880382)⟩,⟨(-53064204036901777828712045),(-53064204036901152638974816)⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨614069034440747342153529896,614069034440747342605457892⟩,⟨(-44759704454737629059426302),(-44759704454737628686433420)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨1652974129492570077871548466,1652974129492570079445098117⟩,⟨(-623450251392830756755265745),(-623450251392830755340865018)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨1646591323295211540188632753,1646591323295211543348016342⟩,⟨(-2173653343549894164470522232),(-2173653343549894161323355281)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-527652694128134652789992759),(-527652694128134647625488364)⟩,⟨(-3443597871469297833561807640),(-3443597871469297828094283048)⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-3665435531810167953728709792),(-3665435531810167943988475215)⟩,⟨(-1694308567573434677195476006),(-1694308567573434667426111367)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-3336403772003740402869086478),(-3336403772003740385363298917)⟩,⟨2758514431974833377099672434,2758514431974833394376991397⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨1480185838227128964186455050,1480185838227128995643510303⟩,⟨4057459770474867445462511316,4057459770474867477075597399⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨4055158421732539254976057070,4055158421732539311506523782⟩,⟨(-331755949766341743282682454),(-331755949766341686781951490)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨579358287896529433383084465,579358287896529542273636867⟩,⟨(-3636371364235730147665343961),(-3636371364235730038808582289)⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-2955943005132590053916996524),(-2955943005132589783684508767)⟩,⟨(-1326404157823664716829209928),(-1326404157823664446576077459)⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-1926315400644183261082705467),(-1926315400644182453668352192)⟩,⟨2006064357747645519309018028,2006064357747646326738545542⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨749033921510405479545184098,749033921510408120732135930⟩,⟨2187166943885640408671666272,2187166943885643049854215042⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨1728576710463707521055499591,1728576710463712630108700653⟩,⟨576432913303730053784972996,576432913303735162801759471⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨1211325347726118598289072037,1211325347726127467270771124⟩,⟨(-498963440866950274128422141),(-498963440866941405145874237)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨502772341188164483379117618,502772341188172027619357285⟩,⟨(-604778833619059080486654881),(-604778833619051536228570317)⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨113043320501050698858592426,113043320501053382006196392⟩,⟨(-236054723161515412495241060),(-236054723161512729338786578)⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-214447691659878630055968573),(-214447691659484662255298102)⟩,⟨(-538832535905975764838330544),(-538832535905581797045350390)⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-668647547157113191168916468),(-668647547157113189871836521)⟩,⟨(-1685848966415853283008439074),(-1685848966415853281668140411)⟩⟩
 def realAnswer : RBox := ⟨(-883095238816991821324885041),(-883095238816597852027134623)⟩
end hm24_0_0_9
namespace hm24_0_0_10
noncomputable def s0_0 : CBox := ⟨⟨(-44666108118457481855),(-44666108118457461935)⟩,⟨(-28728313885697785995),(-28728313885697766074)⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-122589740702758883093),(-122589740702758837455)⟩,⟨(-41750723261839591214),(-41750723261839545572)⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-140690214120931962366),(-140690214120931926085)⟩,⟨21116348521754489386,21116348521754525665⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-70688436637903881675),(-70688436637903869814)⟩,⟨79003962514454870009,79003962514454881866⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨8562544339690189578,8562544339690192360⟩,⟨57393411547574630076,57393411547574632857⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨21919232775448909637,21919232775448909999⟩,⟨9111301901817678474,9111301901817678835⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨5277390580027245882,5277390580027245941⟩,⟨(-4885849333829286003),(-4885849333829285942)⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-595140752545363525),(-595140752545363502)⟩,⟨(-1455878635769286348),(-1455878635769286325)⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-237425025973643821),(-237425025973643799)⟩,⟨13510527204722310,13510527204722329⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-6684702437983196),(-6684702437983177)⟩,⟨22260485647772266,22260485647772282⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨1010429445785493,1010429445785512⟩,⟨854721767508825,854721767508841⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨34911409804918,34911409804937⟩,⟨(-12928335488207),(-12928335488189)⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨115737575386,115737575403⟩,⟨(-374152627995),(-374152627978)⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-393894242),(-393894226)⟩,⟨(-825116178),(-825116162)⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-123040),(-123023)⟩,⟨(-79610),(-79594)⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),0⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-29425085086379355817261),(-29425085086379329535125)⟩,⟨(-37276942050626723289218),(-37276942050626697003443)⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-100518103200676282779545),(-100518103200676177782510)⟩,⟨(-78361547910446029873038),(-78361547910445924869097)⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-167015348955633707847027),(-167015348955633464557150)⟩,⟨(-32184748626988945088222),(-32184748626988701797759)⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-150573168363677459868350),(-150573168363677092045434)⟩,⟨81311735852647120096607,81311735852647487909251⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-28539177848629515531065),(-28539177848628852735207)⟩,⟨139577132366900676827453,139577132366901339622135⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨75327942874988509197641,75327942874989278018806⟩,⟨69062389180879933357296,69062389180880702183787⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨59503411684527598353772,59503411684528375980083⟩,⟨(-25639845730651438917476),(-25639845730650661293782)⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-2224503289862841269328),(-2224503289862242566683)⟩,⟨(-36977378378117650865758),(-36977378378117052162762)⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-18806145721776171929170),(-18806145721775858163121)⟩,⟨(-4965663686995041543200),(-4965663686994727776728)⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-5359216392089751076403),(-5359216392089631315072)⟩,⟨7909252889682101657156,7909252889682221418113⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨2424637313021073427435,2424637313021111960463⟩,⟨3766224360340437188407,3766224360340475721583⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨2045283161226819120721,2045283161226830011625⟩,⟨(-119518998778582458511),(-119518998778571567604)⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨532052154947647090764,532052154947649370546⟩,⟨(-766165705271326218749),(-766165705271323939000)⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-46398082142470211710),(-46398082142469514661)⟩,⟨(-422516935823208045829),(-422516935823207348780)⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-104841385161912434733),(-104841385161912261667)⟩,⟨(-151427244379814374706),(-151427244379814201633)⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-39173044700212958031),(-39173044700212925907)⟩,⟨(-33764104488829192659),(-33764104488829160532)⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-86723471090602491249522),(-86723471090602490657676)⟩,⟨(-1971417948785518431648569),(-1971417948785518430792983)⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-1589340184913588388573325),(-1589340184913588386410515)⟩,⟨(-5246202583043389477301010),(-5246202583043389474614949)⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-5548655999529597970139431),(-5548655999529597965703381)⟩,⟨(-5554394033239135685736526),(-5554394033239135681259357)⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-8788874064177237506195717),(-8788874064177237499620326)⟩,⟨(-656206522195799051730341),(-656206522195799046114925)⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-5765872014368564430934901),(-5765872014368564422042670)⟩,⟨6279854216537915939499317,6279854216537915948288098⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨2286026230250779189318126,2286026230250779201060517⟩,⟨7027723928127983775905304,7027723928127983788338718⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨5846051183673256754099833,5846051183673256771173864⟩,⟨496127835659343906371799,496127835659343922993530⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨1738197152892301434249039,1738197152892301456880215⟩,⟨(-3972483621598892701459392),(-3972483621598892678730176)⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-2286672482860113645673260),(-2286672482860113615970981)⟩,⟨(-1983905244097588002115940),(-1983905244097587972303557)⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-1743906597591080487189616),(-1743906597591080444893396)⟩,⟨1027095401841465517939504,1027095401841465560086059⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨181733072987706728210665,181733072987706799959315⟩,⟨1298602863311044269218799,1298602863311044341057205⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨774102896439564581798255,774102896439564734189944⟩,⟨300022233764973470789537,300022233764973623180522⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨441995918681973533926130,441995918681973759368198⟩,⟨(-261319681973192617218463),(-261319681973192391815470)⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨97788944197501055827880,97788944197501377542906⟩,⟨(-287873078528305558386047),(-287873078528305236670964)⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-25509823016850963843801),(-25509823016850722356043)⟩,⟨(-157554042715781329520427),(-157554042715781088023258)⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-19730774439572612456207),(-19730774439572531976096)⟩,⟨(-45515399174520297647070),(-45515399174520217162822)⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨5782977060667816568954157,5782977060667851605808780⟩,⟨(-19293231236635709960243079),(-19293231236635674919851410)⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨2610905324418047918423358,2610905324418139769925921⟩,⟨(-57018405799014013094164004),(-57018405799013921235600781)⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-35794855879526077504191986),(-35794855879525981968922796)⟩,⟨(-77000654754192652140438950),(-77000654754192556604653953)⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨(-90958674339862657464546221),(-90958674339862609770791165)⟩,⟨(-42650903186769494538456735),(-42650903186769446858855270)⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-93353178901265118387625428),(-93353178901265097515268035)⟩,⟨44928203648080526628729984,44928203648080547499616224⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨(-7537766377304908789791456),(-7537766377304902537738768)⟩,⟨96553547966688192782150057,96553547966688199046072328⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨74339475017391302821484602,74339475017391305117125411⟩,⟨39278836714699838311612034,39278836714699840598286477⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨50492950827317278828502783,50492950827317279774826319⟩,⟨(-46984588042988342755143661),(-46984588042988341806359252)⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨(-22947524369940229380887418),(-22947524369940228972094582)⟩,⟨(-48994288496781695048688825),(-48994288496781694637257652)⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨(-40685871376477579917885827),(-40685871376477579741695689)⟩,⟨4133120688062174044010166,4133120688062174215698839⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨(-9075208890610594097981954),(-9075208890610594026116006)⟩,⟨28511263486486093787126557,28511263486486093862312481⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨14250117926575382371813414,14250117926575382404622795⟩,⟨15701634964162930445331807,15701634964162930478041481⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨14440213177494777680114161,14440213177494777695843431⟩,⟨(-806391114664818311782085),(-806391114664818297955300)⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨6743679322932227620240248,6743679322932227627728931⟩,⟨(-6355342044840420357105960),(-6355342044840420349599192)⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨1677819072340848758443484,1677819072340848761340239⟩,⟨(-4863707590222934258788349),(-4863707590222934255325855)⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨141096754737289167967807,141096754737289168668835⟩,⟨(-1640620053053822739848215),(-1640620053053822738888603)⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨115835597192796160366177540,115835597192797102891039908⟩,⟨(-13506892155964229220901540),(-13506892155963286681198316)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨306600555265269663659014456,306600555265273723379065407⟩,⟨(-121661943197179584335674099),(-121661943197175524585916156)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨307797834020584042185701709,307797834020594772759941248⟩,⟨(-381940098651792031385639831),(-381940098651781300809607703)⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-41159682470068708967503990),(-41159682470049248801559925)⟩,⟨(-583579156929843710356095327),(-583579156929824250254130093)⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-527179052009749635200003198),(-527179052009704670761091307)⟩,⟨(-322403382355293076397505141),(-322403382355248111964911175)⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-509192046880043979459215340),(-509192046879973544075460727)⟩,⟨322194700215294047415990825,322194700215364482859137291⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨122180462934633507281976160,122180462934732293636360572⟩,⟨539814686101325468306610007,539814686101424254612147000⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨484175942142418500904688100,484175942142530798814907096⟩,⟨23838119821183702677701372,23838119821296000603275096⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨120370479098076146308104036,120370479098168236361099492⟩,⟨(-390541599649883247429953754),(-390541599649791157361163477)⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨(-280161504265470058271991588),(-280161504265414351536571894)⟩,⟨(-181805421824292079196993553),(-181805421824236372492544158)⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-212708821610553146379354228),(-212708821610524842742785659)⟩,⟨159265684526945268776786736,159265684526973572439117668⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨34012343283564367276976026,34012343283577356572160717⟩,⟨202744251960681543925348148,202744251960694533219313899⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨135503907447900314356373283,135503907447904557012252951⟩,⟨70330885131719162916055821,70330885131723405554857655⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨102076401956174861457720513,102076401956176743732226232⟩,⟨(-25326570933964204673912975),(-25326570933962322399163198)⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨45529954035123209456278759,45529954035123821390285256⟩,⟨(-41327885459536674205422075),(-41327885459536062265769003)⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨11127517035208363922676646,11127517035208495025653408⟩,⟨(-16870223233927694219747997),(-16870223233927563114139231)⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨14046731018056929650482250,14046731018056929767610298⟩,⟨192761898680465110411854863,192761898680465110554332637⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨194999159394432226495882375,194999159394432226939035805⟩,⟨517275684944685519948029948,517275684944685520442103493⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨675700110894253441439843592,675700110894253442420487784⟩,⟨512337817476271922292828096,512337817476271923277413507⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨1061204442903987030904670719,1061204442903987032592549882⟩,⟨(-161729841139151814427772735),(-161729841139151812835121868)⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨517265886222940024076198619,517265886222940027053717535⟩,⟨(-1115598256270889756797882662),(-1115598256270889753829611230)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-826818729378486026934529721),(-826818729378486021746911522)⟩,⟨(-1003136467768634392628901940),(-1003136467768634387371310460)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-1200099578030994369602219736),(-1200099578030994360261071231)⟩,⟨435339855283518678198505141,435339855283518687492942816⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨94044958724619708415315513,94044958724619724822311155⟩,⟨1178537137813684821894904893,1178537137813684838310436493⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨1037743777081699302734815996,1037743777081699333773298267⟩,⟨167506208692430916860451567,167506208692430947908708488⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨373582042498168407850605734,373582042498168483497235568⟩,⟨(-828300474860453928287915488),(-828300474860453852646720849)⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-552259454009036044945238500),(-552259454009035822674204694)⟩,⟨(-532041436301994829917903249),(-532041436301994607651723681)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨(-594008308279617292695859657),(-594008308279616576651435938)⟩,⟨202598014468173573171484564,202598014468174289217165859⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-154787041164992082133125736),(-154787041164990715217733696)⟩,⟨462875430088440564888360641,462875430088441931814297721⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨132082793450713035363707956,132082793450715384661598668⟩,⟨321073915725044386210770500,321073915725046735508422806⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨159064334027648195529705218,159064334027650179896780708⟩,⟨132282056339673363171201838,132282056339675347533253824⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨61857775017419688602174087,61857775017420391725345954⟩,⟨29624324547079005245615660,29624324547079708366309085⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨177283731722496756157669539,177283731722590994004715829⟩,⟨(-54915522064521343032798535),(-54915522064427105183233071)⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨555495236253995522424565668,555495236253995522814555549⟩,⟨(-177600343336493340060311529),(-177600343336493339686748711)⟩⟩
 def realAnswer : RBox := ⟨732778967976492278482235207,732778967976586516919271378⟩
end hm24_0_0_10
namespace hm24_0_0_11
noncomputable def s0_0 : CBox := ⟨⟨1361224958703533588,1361224958703534546⟩,⟨(-2115929734617510104),(-2115929734617509144)⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨1946518141288336133,1946518141288338273⟩,⟨(-5698489350747486417),(-5698489350747484280)⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-930008910173510439),(-930008910173508791)⟩,⟨(-6302335187366398517),(-6302335187366396871)⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-3326587147654795020),(-3326587147654794494)⟩,⟨(-3004641267853627702),(-3004641267853627180)⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-2247075102631633117),(-2247075102631632986)⟩,⟨318300085832551120,318300085832551246⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-330334163004291581),(-330334163004291552)⟩,⟨772085073366741741,772085073366741774⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨150374130915602292,150374130915602311⟩,⟨166808302516103330,166808302516103350⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨39282141367583287,39282141367583305⟩,⟨(-15336602529408417),(-15336602529408400)⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-207578272415298),(-207578272415280)⟩,⟨(-5297104844896664),(-5297104844896643)⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-394716861256756),(-394716861256739)⟩,⟨(-126494393216625),(-126494393216608)⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-11864471618505),(-11864471618487)⟩,⟨13533637811571,13533637811590⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨120750883079,120750883099⟩,⟨342007171363,342007171381⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨2385004525,2385004544⟩,⟨767537346,767537364⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨3040188,3040206⟩,⟨(-1425920),(-1425903)⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨128,145⟩,⟨(-216),(-192)⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨0,16⟩,⟨(-16),16⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨3540450750624274425251,3540450750624276921504⟩,⟨(-2794423170643637812442),(-2794423170643635316539)⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨7376524898349868361483,7376524898349878234278⟩,⟨(-9453702066623137876943),(-9453702066623128004805)⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨2989837403681765557253,2989837403681787997534⟩,⟨(-15417462830779948668436),(-15417462830779926228214)⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-7271464222666016133601),(-7271464222665983145665)⟩,⟨(-13536302067155310803087),(-13536302067155277814221)⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-12072838541220423596484),(-12072838541220366359054)⟩,⟨(-2511184312487749914135),(-2511184312487692676598)⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-5743368668447798759269),(-5743368668447735354625)⟩,⟨6206564111499564596840,6206564111499628001037⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨1985923414073604643688,1985923414073665656092⟩,⟨4682591564223467616811,4682591564223528629420⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨2736689457271204649742,2736689457271248948761⟩,⟨(-146580116942693577878),(-146580116942649278890)⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨353509225386224835184,353509225386246567809⟩,⟨(-1301878826119331658776),(-1301878826119309926180)⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-510092848542692896604),(-510092848542685135449)⟩,⟨(-350787909685096339614),(-350787909685088578438)⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-228696054278249491777),(-228696054278247152069)⟩,⟨145215186350417207103,145215186350419546803⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨6167054969590807642,6167054969591425520⟩,⟨115741221196967135020,115741221196967752896⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨40679128456528134436,40679128456528256038⟩,⟨28471737408950064407,28471737408950186009⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨21380647396721255295,21380647396721290635⟩,⟨(-2301434840748421733),(-2301434840748386390)⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨7388708591121498807,7388708591121507275⟩,⟨(-5106355506591154967),(-5106355506591146500)⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨1615181020339746232,1615181020339747784⟩,⟨(-1873557528748874953),(-1873557528748873402)⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨281070423447685667104775,281070423447685667227667⟩,⟨(-12354874487070971134601),(-12354874487070971050142)⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨743326707528417331077927,743326707528417331460852⟩,⟨(-224947599301178697703192),(-224947599301178697396095)⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨777769728274805394980363,777769728274805395609403⟩,⟨(-775718446062658467193294),(-775718446062658466570300)⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨91927242678352653354367,91927242678352654126611⟩,⟨(-1207093653220124170187941),(-1207093653220124169280967)⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-840396257030196401362369),(-840396257030196400182129)⟩,⟨(-775114029176727429178028),(-775114029176727427983112)⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-916393458269733155578498),(-916393458269733153957281)⟩,⟨295034485541458369118757,295034485541458370647568⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-65218715381510791907261),(-65218715381510789814652)⟩,⟨736398222885057716661903,736398222885057718812636⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨481661391798770820382099,481661391798770823139516⟩,⟨213121406901203335308197,213121406901203338053751⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨232924326422633979007704,232924326422633982484242⟩,⟨(-266165456895124305303781),(-266165456895124301840690)⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-114510336877267830202607),(-114510336877267825485636)⟩,⟨(-196263569730637168164289),(-196263569730637163429976)⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-140271457160717679551356),(-140271457160717671819593)⟩,⟨19114243568243288598449,19114243568243296320275⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-31455149235877732280190),(-31455149235877716468654)⟩,⟨80474556215258080719521,80474556215258096531099⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨26242131945847256932693,26242131945847279583256⟩,⟨44587077805317781576389,44587077805317804231018⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨28243743429138771284333,28243743429138802824822⟩,⟨9629360888447716872688,9629360888447748413173⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨15181143183944410257616,15181143183944433521019⟩,⟨(-2451333699040803112387),(-2451333699040779849923)⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨4343614740050110205910,4343614740050117886521⟩,⟨(-1882689995440021992304),(-1882689995440014312100)⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨3669005359855870603269428,3669005359855877267003022⟩,⟨1099851435605612796316107,1099851435605619459370215⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨10791889809112650376738927,10791889809112667764901817⟩,⟨496543057556386041833020,496543057556403428645050⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨14442082363942722235710147,14442082363942740159942485⟩,⟨(-6703319679016562438819660),(-6703319679016544514687294)⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨7906162005640713937026924,7906162005640722767682888⟩,⟨(-16813706413347046858435391),(-16813706413347038025132299)⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-8134758120306276719072158),(-8134758120306272921057172)⟩,⟨(-16973756309908812505078746),(-16973756309908808706785796)⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨(-17168021183469714355885698),(-17168021183469713239936821)⟩,⟨(-1378110280848338529241702),(-1378110280848337415438627)⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-6851648825411217405642934),(-6851648825411217008023338)⟩,⟨12884666270995890251221192,12884666270995890650417481⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨7916257109751488339033259,7916257109751488499654590⟩,⟨8557785557742959825695044,8557785557742959985900354⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨8065125295357768418925518,8065125295357768486677839⟩,⟨(-3747804240337136551448070),(-3747804240337136484144212)⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨(-641971881878021954076693),(-641971881878021926592323)⟩,⟨(-6504378794150726356428684),(-6504378794150726328206276)⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨(-4430556016886085292547826),(-4430556016886085280820771)⟩,⟨(-1422372115360570619263462),(-1422372115360570608064353)⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨(-2385204068447235447960623),(-2385204068447235442984084)⟩,⟨2156267630399478743359094,2156267630399478748349832⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨116764426274157696286774,116764426274157698341439⟩,⟨2142164791126645863020959,2142164791126645865366151⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨925470823742857695340620,925470823742857696440113⟩,⟨983488807286235057036930,983488807286235058133907⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨700030134757587454438327,700030134757587454940623⟩,⟨241710934122111003449047,241710934122111003867432⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨234655697103387576735613,234655697103387576874147⟩,⟨20188579175296326330292,20188579175296326430684⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨3210978167184775803782571,3210978167184999904953250⟩,⟨27542522330845907950587174,27542522330846132048307238⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨28804717146457265747482201,28804717146458227139958763⟩,⟨72630553930698572182995490,72630553930699533568586099⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨89760137715447573874647474,89760137715450095644079047⟩,⟨72410148560586772803920734,72410148560589294572932070⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨135713902620461810184778580,135713902620466333333494923⟩,⟨(-9446021269350866712921600),(-9446021269346343549610977)⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨74085215109062005997002887,74085215109072306425045046⟩,⟨(-120762934984929380606426397),(-120762934984919080176929108)⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-72418250749695197700547912),(-72418250749679338793471393)⟩,⟨(-114915707362822465463619755),(-114915707362806606569766399)⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨(-119434437149826547973888391),(-119434437149804704481417948)⟩,⟨26756468366566710261971620,26756468366588553765103171⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨(-5417218509672240488119979),(-5417218509647912114282285)⟩,⟨104856581885741961393125808,104856581885766289763702831⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨82712400743710613567739454,82712400743730127257914592⟩,⟨25716811826345610708306239,25716811826365124395114637⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨37839583332934159382909752,37839583332945714219566078⟩,⟨(-58015186325195390323923828),(-58015186325183835480835426)⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-32258591370901096303511544),(-32258591370895340433172628)⟩,⟨(-43263526928299994051089413),(-43263526928294238185988279)⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-40399910350635822675276105),(-40399910350633232544868518)⟩,⟨6712994533817103483223356,6712994533819693613865013⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-13806813951508780730326643),(-13806813951507949044734905)⟩,⟨26532926596986308761492959,26532926596987140450461748⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨4884813316395881096914575,4884813316396245173887308⟩,⟨19736714184474212071477653,19736714184474576148404567⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨7913986349285577363839847,7913986349285694611931258⟩,⟨8722498175957492686878332,8722498175957609933875407⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨3215891746490673949246645,3215891746490698942892692⟩,⟨2121301513701814787809051,2121301513701839780946961⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨(-55008854319473847700645787),(-55008854319473847659811549)⟩,⟨4007473857813494654773522,4007473857813494688210624⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-147158786214332682984798707),(-147158786214332682843770519)⟩,⟨55446190679640476325681369,55446190679640476451905578⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-144922663226003934997734240),(-144922663226003934718793260)⟩,⟨190953276122665114101190084,190953276122665114378975974⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨45064165287212823398954281,45064165287212823845456877⟩,⟨297301369732945098381183895,297301369732945098854882157⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨308676204292329289678242681,308676204292329290500580780⟩,⟨143563983311592737505615850,143563983311592738330620207⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨274192634674288105700347521,274192634674288107135862065⟩,⟨(-225298905232740897577899785),(-225298905232740896161861756)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-116398374262057717031684118),(-116398374262057714535102459)⟩,⟨(-322698390373952504710976911),(-322698390373952502201685167)⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-311384119420895117508766944),(-311384119420895113175197045)⟩,⟨24221446588709282384298253,24221446588709286715641426⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-44021221266168341602751978),(-44021221266168333554475598)⟩,⟨269234173755294155393750196,269234173755294163439456567⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨211007201654173848987086492,211007201654173868235595207⟩,⟨95654551847077382673052798,95654551847077401922856590⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨133591465196667885601784856,133591465196667941226428603⟩,⟨(-138215605592083625497764656),(-138215605592083569871736764)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨(-49817047464692685679661382),(-49817047464692509199168739)⟩,⟨(-146662048997599597220075809),(-146662048997599420739907999)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-112681364315812625733550514),(-112681364315812293256189939)⟩,⟨(-37785930976473264643105016),(-37785930976472932168505066)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-77367667868046834130725687),(-77367667868046268396350079)⟩,⟨31785828274569586797092884,31785828274570152531528929⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-31640179659554985241800338),(-31640179659554510743370520)⟩,⟨38032729797646680096310123,38032729797647154596019968⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-7057639224531092635937428),(-7057639224530925132917264)⟩,⟨14736126527325529045593270,14736126527325696549241782⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨12533852734207068930759500,12533852734227599031267793⟩,⟨52425607064342731015403769,52425607064363261115161428⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨42751256502264096501002545,42751256502264096599764570⟩,⟨164546162056035402165793026,164546162056035402270037229⟩⟩
 def realAnswer : RBox := ⟨55285109236471165331762045,55285109236491695731032363⟩
end hm24_0_0_11
namespace hm24_0_0_12
noncomputable def s0_0 : CBox := ⟨⟨91883843118911787,91883843118911843⟩,⟨59124085329645014,59124085329645073⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨242832708663175026,242832708663175132⟩,⟨83193709338482980,83193709338483088⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨258842045905898479,258842045905898563⟩,⟨(-37544870695985930),(-37544870695985848)⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨117109383577018626,117109383577018667⟩,⟨(-128449157969721483),(-128449157969721448)⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-10829879789729750),(-10829879789729726)⟩,⟨(-80697776758870388),(-80697776758870365)⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-24955649785133093),(-24955649785133076)⟩,⟨(-10978672594300053),(-10978672594300036)⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-4837915475355255),(-4837915475355238)⟩,⟨4249086975245584,4249086975245603⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨362919997128078,362919997128097⟩,⟨973230308132342,973230308132359⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨108612316983411,108612316983432⟩,⟨(-2425082732166),(-2425082732146)⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨2186878094037,2186878094057⟩,⟨(-6439803081761),(-6439803081742)⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-167061421844),(-167061421821)⟩,⟨(-151315451644),(-151315451626)⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-3085877231),(-3085877212)⟩,⟨1042335168,1042335185⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-4668847),(-4668831)⟩,⟨14029406,14029423⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨4765,4782⟩,⟨10326,10342⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-14),16⟩,⟨0,16⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨0,16⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨243264585834244315770,243264585834244533060⟩,⟨308240078461043179205,308240078461043396523⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨815038995224794505503,815038995224795356388⟩,⟨636530613973093535468,636530613973094386413⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨1304671184498756070229,1304671184498757967657⟩,⟨254600309788852154333,254600309788854051765⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨1115580113836480368873,1115580113836483081255⟩,⟨(-596121939394733370444),(-596121939394730658138)⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨202514921544461100150,202514921544465631791⟩,⟨(-957362395698853121380),(-957362395698848589747)⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-468856279791293261793),(-468856279791288467593)⟩,⟨(-437894887708537153190),(-437894887708532358955)⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-337865499179530030338),(-337865499179525640996)⟩,⟨141017911910692805982,141017911910697195308⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨8729013740724809002,8729013740727814524⟩,⟨185719087990673883814,185719087990676889338⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨82642682874448931713,82642682874450312045⟩,⟨23058683808139658696,23058683808141039031⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨21051736368077681764,21051736368078143014⟩,⟨(-30167187129984200240),(-30167187129983738990)⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-7974926609994749046),(-7974926609994618758)⟩,⟨(-12733893166520956600),(-12733893166520826313)⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-6005813857269369361),(-6005813857269337202)⟩,⟨289229914992232861,289229914992265020⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-1396920618020521340),(-1396920618020515376)⟩,⟨1980343040893317439,1980343040893323402⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨104621900472450916,104621900472452576⟩,⟨991917068083745508,991917068083747166⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨227996499378879474,227996499378879870⟩,⟨330500146631672250,330500146631672643⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨82141277907782938,82141277907783019⟩,⟨70827493377892301,70827493377892382⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨1613435372402269444083,1613435372402269455143⟩,⟨36733591987121524111870,36733591987121524128059⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨29185032928552977312854,29185032928552977352838⟩,⟨96544853121756973514420,96544853121756973564472⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨99412380426636891348161,99412380426636891428377⟩,⟨99835556305959178099146,99835556305959178180177⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨151976513549027152269260,151976513549027152383953⟩,⟨11800666315098362752982,11800666315098362850348⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨95521096632047813471021,95521096632047813618234⟩,⟨(-103098907434667781028509),(-103098907434667780883201)⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-34904107317081344278753),(-34904107317081344096266)⟩,⟨(-109545374516444505899067),(-109545374516444505705259)⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-85038797658484936241857),(-85038797658484935993477)⟩,⟨(-7845714692370504782776),(-7845714692370504541237)⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-23953631162066402988899),(-23953631162066402683517)⟩,⟨53540485332816244316010,53540485332816244622702⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨28402803413365072897869,28402803413365073268059⟩,⟨25070279331459206063084,25070279331459206434777⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨20249616107446437580344,20249616107446438066183⟩,⟨(-11703831215944066711701),(-11703831215944066227700)⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-1841860835592611584201),(-1841860835592610822298)⟩,⟨(-13890662396182298348836),(-13890662396182297585925)⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-7669581777451300887775),(-7669581777451299383782)⟩,⟨(-3023120203664830791771),(-3023120203664829287778)⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-4123257090727254823201),(-4123257090727252736192)⟩,⟨2415818944721766774028,2415818944721768860651⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-869218586656678109436),(-869218586656675274806)⟩,⟨2540228445218972777000,2540228445218975611633⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨215930088694212124665,215930088694214178841⟩,⟨1340904699588477018236,1340904699588479072498⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨164674273834967065389,164674273834967737247⟩,⟨379976293967363050738,379976293967363722634⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨(-191746844710516381449945),(-191746844710515219912488)⟩,⟨639592510179797020483304,639592510179798182140406⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-86561742184010391020981),(-86561742184007374079256)⟩,⟨1872376621862072055580117,1872376621862075072758735⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨1150734044041432058025040,1150734044041435140707319⟩,⟨2483027366354835684134738,2483027366354838766834771⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨2849070572235542799642735,2849070572235544299344871⟩,⟨1343448738036285090761616,1343448738036286590009977⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨2829121265156782692363997,2829121265156783325985273⟩,⟨(-1350177777587088391571368),(-1350177777587087757998195)⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨230794190111713905557028,230794190111714087453530⟩,⟨(-2798350754398520271754986),(-2798350754398520089502952)⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-2047200977612254426172871),(-2047200977612254362536831)⟩,⟨(-1095602913854911786897358),(-1095602913854911723515411)⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨(-1329611840472279379221314),(-1329611840472279354358397)⟩,⟨1222695240066188431849889,1222695240066188456777235⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨561100599099694967287210,561100599099694977445365⟩,⟨1217065378522700448572336,1217065378522700458800334⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨953248119604076344537848,953248119604076348682093⟩,⟨(-91335368116853552176336),(-91335368116853548142962)⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨204351000129412803105311,204351000129412804705179⟩,⟨(-631154289516474608917628),(-631154289516474607240846)⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨(-299100123510574808686269),(-299100123510574807990341)⟩,⟨(-332150952015202132222716),(-332150952015202131528624)⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-291311474748310136666568),(-291311474748310136346033)⟩,⟨15489823114131612549535,15489823114131612829434⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-131480450334963482593877),(-131480450334963482446563)⟩,⟨123539516077406329750410,123539516077406329898039⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-31919916351492703642161),(-31919916351492703586755)⟩,⟨92359299186300924138787,92359299186300924205589⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-2647928325973238925918),(-2647928325973238912725)⟩,⟨30765642958647304284062,30765642958647304302406⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨(-6003118968831122787581147),(-6003118968831073945559403)⟩,⟨699730541596780869013309,699730541596829711770110⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-15771695489521240102677767),(-15771695489521031407830395)⟩,⟨6251511034452031864014282,6251511034452240560324059⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-15615204381543434670723679),(-15615204381542891417681420)⟩,⟨19336873705557528084960853,19336873705558071338093327⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨1986861847495463672041229,1986861847496427402355171⟩,⟨28931172253738292941610212,28931172253739256668873518⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨25358816454000923126670507,25358816454003086151221375⟩,⟨15605620139932825696437390,15605620139934988720681296⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨23773836980681127155230291,23773836980684400400503731⟩,⟨(-14920977855801603100722334),(-14920977855798329852750692)⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨(-5370826108700453547246718),(-5370826108696025888466259)⟩,⟨(-24223647136414608590243213),(-24223647136410180933595465)⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨(-20816858481467812437177696),(-20816858481462980945102880)⟩,⟨(-1126009876227502311219381),(-1126009876222670818509937)⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-5036314573399077667508377),(-5036314573395287192717022)⟩,⟨16058373082384084209607572,16058373082387874685056689⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨11012893715942158499336427,11012893715944355595153226⟩,⟨7219495067575247591974833,7219495067577444686567092⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨8066453771285806122013889,8066453771286879134866540⟩,⟨(-5989512413715864473902979),(-5989512413714791460074166)⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-1214457118587187033209501),(-1214457118586713576548016)⟩,⟨(-7379637411558428206266996),(-7379637411557954749646632)⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-4762531762646403265852679),(-4762531762646253813078780)⟩,⟨(-2484610932571669640921128),(-2484610932571520188759336)⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-3498165719245628009293638),(-3498165719245563455866908)⟩,⟨863641158033910154617838,863641158033974708052438⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-1531784862542028178034641),(-1531784862542007585392908)⟩,⟨1389186712083650130574000,1389186712083670723410121⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-370696239672070617130543),(-370696239672066249552601)⟩,⟨561944801919093976070524,561944801919098343738379⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨(-1048039448628056335283790),(-1048039448628056326533789)⟩,⟨(-14389825771352454254706685),(-14389825771352454243979011)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-14451830322533202451620349),(-14451830322533202418663758)⟩,⟨(-38376253878346614899938812),(-38376253878346614863038701)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-49466795740391452506373058),(-49466795740391452434242358)⟩,⟨(-37577650516304493198579934),(-37577650516304493126139122)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-76350187125760520379576741),(-76350187125760520257712519)⟩,⟨11510009811179126628719157,11510009811179126743466600⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-36525116918018160610878824),(-36525116918018160401334651)⟩,⟨78291693291034287969408983,78291693291034288178249114⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨56276324037286174504777471,56276324037286174859102007⟩,⟨68702100398960887723749200,68702100398960888083041632⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨79542069576150869781824388,79542069576150870399732184⟩,⟨(-28528292280393340758167298),(-28528292280393340143429139)⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-5714823602310401861658356),(-5714823602310400813471287)⟩,⟨(-75417391482042722240772593),(-75417391482042721192053265)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-64031325568174505968806920),(-64031325568174504056970821)⟩,⟨(-10603433084082965167804255),(-10603433084082963255348849)⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-22451169350809239859440190),(-22451169350809235369039935)⟩,⟨49275188050049360816004720,49275188050049365306123550⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨31709599967159940534236217,31709599967159953295518266⟩,⟨30749019655417739179900363,30749019655417751940826060⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨33194164308433135565506260,33194164308433175437722572⟩,⟨(-11228816862150663024779542),(-11228816862150623152486675)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨8455503588513331011087482,8455503588513405140741954⟩,⟨(-25145292218147831963573202),(-25145292218147757833259426)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-7011883875286008269795654),(-7011883875285883387318604)⟩,⟨(-17089461282208288909843598),(-17089461282208164027380505)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-8335943588820324157193122),(-8335943588820220150215318)⟩,⟨(-6937284607689649202235941),(-6937284607689545195555975)⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-3217984591333501097346286),(-3217984591333464518609536)⟩,⟨(-1541281699055361501077916),(-1541281699055324922486659)⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-14097012931951507510159023),(-14097012931947400215989229)⟩,⟨2551396944349941877400012,2551396944354049171774997⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-44324415607430077946692653),(-44324415607430077920906024)⟩,⟨9410839108929621990604979,9410839108929622014754977⟩⟩
 def realAnswer : RBox := ⟨(-58421428539381585556851676),(-58421428539377478036895253)⟩
end hm24_0_0_12
namespace hm24_0_0_13
noncomputable def s0_0 : CBox := ⟨⟨(-2370501234548149),(-2370501234548132)⟩,⟨3683140596284856,3683140596284874⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-3282361847883405),(-3282361847883383)⟩,⟨9552628552893035,9552628552893058⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨1399052714325218,1399052714325238⟩,⟨9814994031968277,9814994031968297⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨4580070887869703,4580070887869726⟩,⟨4214736718165835,4214736718165852⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨2676808346172405,2676808346172423⟩,⟨(-339554662660620),(-339554662660602)⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨336825397968208,336825397968227⟩,⟨(-745345691800199),(-745345691800182)⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-111001255057745),(-111001255057727)⟩,⟨(-129644795252492),(-129644795252473)⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-22293874778258),(-22293874778239)⟩,⟨7941226060273,7941226060292⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨13008887156,13008887179⟩,⟨2060737570357,2060737570374⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨97325567047,97325567067⟩,⟨34809860097,34809860116⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨1785246708,1785246728⟩,⟨(-1913131529),(-1913131509)⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-8368048),(-8368030)⟩,⟨(-25811496),(-25811477)⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-76630),(-76609)⟩,⟨(-26250),(-26232)⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-45),(-29)⟩,⟨4,27⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-16),0⟩,⟨(-16),16⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-16),0⟩,⟨(-16),16⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-24771846500681118917),(-24771846500681101440)⟩,⟨19548089974614808268,19548089974614825743⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-50702795416476286168),(-50702795416476218454)⟩,⟨64863468764661235002,64863468764661302712⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-20012931736205708301),(-20012931736205560180)⟩,⟨101917159866604993790,101917159866605141906⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨45114846760327892575,45114846760328098462⟩,⟨84874284267263157413,84874284267263363308⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨70087659993170345939,70087659993170677184⟩,⟨15073233194356772640,15073233194357103886⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨30823155398590962094,30823155398591296804⟩,⟨(-32700031188612196210),(-32700031188611861504)⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-9244365885972305579),(-9244365885972014001)⟩,⟨(-22508178944406101522),(-22508178944405809946)⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-11637372875482258382),(-11637372875482070084)⟩,⟨471087418969440002,471087418969628301⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-1387776264611430341),(-1387776264611349369)⟩,⟨4844257790094575545,4844257790094656514⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨1647473908679284476,1647473908679309808⟩,⟨1166425034344289982,1166425034344315314⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨654694805288762506,654694805288769222⟩,⟨(-404406165886287523),(-404406165886280806)⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-12391991781141613),(-12391991781140051)⟩,⟨(-287760100205728086),(-287760100205726524)⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-89013407442800866),(-89013407442800581)⟩,⟨(-63278062342767233),(-63278062342766946)⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-42484834981871617),(-42484834981871529)⟩,⟨4389285204507571,4389285204507659⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-13647081408592574),(-13647081408592541)⟩,⟨9397462743878822,9397462743878857⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-2866973626023995),(-2866973626023975)⟩,⟨3324275808008018,3324275808008036⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-4431491396656054987993),(-4431491396656054986011)⟩,⟨194492480608760203096,194492480608760204446⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-11574964771204073140941),(-11574964771204073134891)⟩,⟨3495262494081864232269,3495262494081864237089⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-11829482588310181350343),(-11829482588310181340695)⟩,⟨11760433320339832754442,11760433320339832763989⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-1397848178639122645683),(-1397848178639122634337)⟩,⟨17663071298834421263875,17663071298834421277277⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨11675780249036807800848,11675780249036807817376⟩,⟨10866570147609911497698,10866570147609911514453⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨12088635010540968361182,12088635010540968382585⟩,⟨(-3811699502593906417415),(-3811699502593906397296)⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨869881851676414522434,869881851676414548184⟩,⟨(-9065717011330573759502),(-9065717011330573733004)⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-5494269845710985258944),(-5494269845710985227438)⟩,⟨(-2485184572547709094061),(-2485184572547709062686)⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-2491036751349279164741),(-2491036751349279128039)⟩,⟨2798073202843426426571,2798073202843426463119⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨1104300944567684248514,1104300944567684294377⟩,⟨1928771423703225438686,1928771423703225484730⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨1269882799904143014477,1269882799904143083988⟩,⟨(-163736624284533081815),(-163736624284533012398)⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨268207505611701841456,268207505611701973537⟩,⟨(-674783441898121862474),(-674783441898121730389)⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-205302599155599448236),(-205302599155599270771)⟩,⟨(-351996916010483401211),(-351996916010483223712)⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-210901202442505596802),(-210901202442505361615)⟩,⟨(-72428717203410845960),(-72428717203410610776)⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-109329235941251808290),(-109329235941251640825)⟩,⟨17557637958863177407,17557637958863344864⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-30683183940810161009),(-30683183940810106740)⟩,⟨13295706303553335048,13295706303553389317⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨(-102919221797444163231428),(-102919221797443976302547)⟩,⟨(-30857484860882136428234),(-30857484860881949518795)⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-299866981541060896360936),(-299866981541060413092895)⟩,⟨(-13929158706958592389034),(-13929158706958109159335)⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-394072325143225157177248),(-394072325143224667776484)⟩,⟨182348489200605333862362,182348489200605823260220⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨(-210727320043775267911167),(-210727320043775032947384)⟩,⟨445645803146729857643139,445645803146730092678714⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨206863783678224805061643,206863783678224902625210⟩,⟨435287653778568206839632,435287653778568304410878⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨421056533813609144871973,421056533813609172348206⟩,⟨35654041521144664327076,35654041521144691748943⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨161718353545929744084253,161718353545929753410877⟩,⟨(-300267190405312875003516),(-300267190405312865639099)⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨(-174331923008370595670165),(-174331923008370592098967)⟩,⟨(-190698622689136874664682),(-190698622689136871102690)⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨(-169543137910495911810466),(-169543137910495910385101)⟩,⟨77544996104056801625669,77544996104056803040999⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨11985422137673416581416,11985422137673417127834⟩,⟨128964577663787091139265,128964577663787091701052⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨82999378308170816699395,82999378308170816920728⟩,⟨27100289480493341357834,27100289480493341568831⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨42697374062765675992365,42697374062765676081739⟩,⟨(-38298937934095358164380),(-38298937934095358074788)⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-1895691022452639795322),(-1895691022452639760114)⟩,⟨(-36569093605764818502895),(-36569093605764818462440)⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-15222811900496046180086),(-15222811900496046161774)⟩,⟨(-16225520597469566871280),(-16225520597469566853005)⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-11248266327476793901100),(-11248266327476793892887)⟩,⟨(-3891059949708562299534),(-3891059949708562292748)⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-3723395323971208776494),(-3723395323971208774240)⟩,⟨(-320586248690859539272),(-320586248690859537662)⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨(-140754510208508819271329),(-140754510208498992875864)⟩,⟨(-1207781064936645975099278),(-1207781064936636148848276)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-1252406651172200398206405),(-1252406651172158579762204)⟩,⟨(-3161378333046625829071367),(-3161378333046584010913703)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-3845297656044963603289619),(-3845297656044855574357847)⟩,⟨(-3108398673051826829312869),(-3108398673051718800398953)⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-5693132617595050770374602),(-5693132617594861225780825)⟩,⟨385702799569796639975107,385702799569986185157296⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-3034411579610109075583377),(-3034411579609689786145989)⟩,⟨4915532453367959321982297,4915532453368378611479409⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨2837870865881518604876646,2837870865882142245906716⟩,⟨4540123915469582139864875,4540123915470205780386822⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨4535247889374772124337337,4535247889375600598109079⟩,⟨(-995094888706639882723829),(-995094888705811408558305)⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨215615649204744047404217,215615649205629780598215⟩,⟨(-3814943719255208649046183),(-3814943719254322915966190)⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-2877971654801215633800376),(-2877971654800535957547260)⟩,⟨(-910403525373986612452610),(-910403525373306936318106)⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨(-1271495120889228363005332),(-1271495120888842717079898)⟩,⟨1929808443272391546167413,1929808443272777192308050⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨1026566059768587867497542,1026566059768772518643396⟩,⟨1388334497420445062729161,1388334497420629713707083⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨1244339436691958878541189,1244339436692038767667985⟩,⟨(-202796343291075409802331),(-202796343290995520668883)⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨412731183353813736836632,412731183353838527695783⟩,⟨(-789108034962703163537735),(-789108034962678372576177)⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-140948003980169306292370),(-140948003980158740844874)⟩,⟨(-572332475362273287776093),(-572332475362262722329845)⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-225094877234130150523579),(-225094877234126811909691)⟩,⟨(-248310065399207906101705),(-248310065399204567519685)⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-90640855440461864547206),(-90640855440461160003890)⟩,⟨(-59795989726505412764261),(-59795989726504708235627)⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨3474693142925674463458971,3474693142925674466060437⟩,⟨(-253001162561661444407380),(-253001162561661442293756)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨9237993736942754095748675,9237993736942754104660846⟩,⟨(-3477063430772382399240333),(-3477063430772382391297419)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨8994205724294572479218421,8994205724294572496584151⟩,⟨(-11828793287297926623163914),(-11828793287297926605874990)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-2713623534562651675165498),(-2713623534562651647944487)⟩,⟨(-18099438438318958653159466),(-18099438438318958624219951)⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-18330397756617853319967715),(-18330397756617853271010038)⟩,⟨(-8577853693458068794382644),(-8577853693458068745253509)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-15890192321685182816452069),(-15890192321685182733441238)⟩,⟨12975876136925762176189355,12975876136925762258030828⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨6454185049933185232591183,6454185049933185372318975⟩,⟨18098558719720951507944759,18098558719720951648402059⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨16861447867242108143459718,16861447867242108377732495⟩,⟨(-1243814063584148018761176),(-1243814063584147784605786)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨2357285378824653148062497,2357285378824653567559638⟩,⟨(-14057351992122695303266647),(-14057351992122694883907240)⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-10622027196854529038096049),(-10622027196854528071228239)⟩,⟨(-4864211380958039752688717),(-4864211380958038785764791)⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-6533254557003529528519259),(-6533254557003526826150146)⟩,⟨6715381228670790045706571,6715381228670792748159365⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨2336305718133432895023986,2336305718133441210568719⟩,⟨6935071498404689419485684,6935071498404697735013835⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨5179697000265836705704730,5179697000265851962830518⟩,⟨1746582504659487142877656,1746582504659502399858712⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨3484480818641873338097966,3484480818641898784779983⟩,⟨(-1427829168000243534104621),(-1427829168000218087419642)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨1404038787587284517696391,1404038787587305561620611⟩,⟨(-1686518359476788524447698),(-1686518359476767480459725)⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨310700973667508918206742,310700973667516291632904⟩,⟨(-648668195187624064738305),(-648668195187616691281147)⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-460157007880883959099338),(-460157007880124085297904)⟩,⟨(-3478346178836956249603483),(-3478346178836196375853862)⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-1908700865471476502627597),(-1908700865471476497131550)⟩,⟨(-10956628798823250038131443),(-10956628798823250032192437)⟩⟩
 def realAnswer : RBox := ⟨(-2368857873352360561726935),(-2368857873351600482429454)⟩
end hm24_0_0_13
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock24_10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid
namespace hm24_0_1_2
noncomputable def s0_0 : CBox := ⟨⟨(-46),46⟩,⟨(-46),46⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-119),119⟩,⟨(-119),119⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-191),191⟩,⟨(-191),191⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-259),259⟩,⟨(-259),259⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-318),318⟩,⟨(-318),318⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-368),368⟩,⟨(-368),368⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-401),401⟩,⟨(-401),401⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-416),416⟩,⟨(-416),416⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-405),405⟩,⟨(-405),405⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-375),375⟩,⟨(-375),375⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-331),331⟩,⟨(-331),331⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-278),278⟩,⟨(-278),278⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-205),205⟩,⟨(-205),205⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-119),119⟩,⟨(-119),119⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-75),75⟩,⟨(-75),75⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-30),30⟩,⟨(-30),30⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-24),24⟩,⟨(-24),24⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-56),56⟩,⟨(-56),56⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-87),87⟩,⟨(-87),87⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-119),119⟩,⟨(-119),119⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-154),154⟩,⟨(-154),154⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-188),188⟩,⟨(-188),188⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-220),220⟩,⟨(-220),220⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-248),248⟩,⟨(-248),248⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-267),267⟩,⟨(-267),267⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-272),272⟩,⟨(-272),272⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-270),270⟩,⟨(-270),270⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-248),248⟩,⟨(-248),248⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-211),211⟩,⟨(-211),211⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-164),164⟩,⟨(-164),164⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-104),104⟩,⟨(-104),104⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-40),40⟩,⟨(-40),40⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨0,18⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-16),21⟩,⟨(-5),28⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-16),32⟩,⟨(-16),32⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-29),46⟩,⟨(-43),41⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-58),63⟩,⟨(-58),58⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-77),77⟩,⟨(-77),77⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-87),87⟩,⟨(-87),87⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-96),96⟩,⟨(-96),96⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-103),103⟩,⟨(-103),103⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-112),112⟩,⟨(-112),112⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-101),101⟩,⟨(-101),101⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-120),120⟩,⟨(-120),120⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-106),106⟩,⟨(-106),106⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-83),83⟩,⟨(-83),83⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-55),55⟩,⟨(-55),55⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-24),24⟩,⟨(-24),24⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨27060609950336,27060609950356⟩,⟨111357454788322,111357454788343⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨101635360753424,101635360753451⟩,⟨193713183105994,193713183106023⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨121732627065008,121732627065041⟩,⟨84511650102443,84511650102476⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨54166278421550,54166278421590⟩,⟨(-5025692689487),(-5025692689446)⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨6639400519388,6639400519436⟩,⟨(-10018037223257),(-10018037223210)⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨(-766829108666),(-766829108613)⟩,⟨(-1513637651823),(-1513637651770)⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-161505005807),(-161505005746)⟩,⟨11726525555,11726525616⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨(-2800349817),(-2800349750)⟩,⟨10790560310,10790560372⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨505954922,505954986⟩,⟨321613963,321614027⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨22115016,22115084⟩,⟨(-16806166),(-16806095)⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨(-248714),(-248651)⟩,⟨(-1221701),(-1221636)⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨(-57427),(-57370)⟩,⟨(-23322),(-23261)⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-3586),(-3535)⟩,⟨1605,1655⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-196),(-156)⟩,⟨288,331⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-21),12⟩,⟨32,66⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-16),16⟩,⟨0,20⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨(-12886998710631260831151),(-12886998710631151055823)⟩,⟨(-118231394563983138294),(-118231394563873360991)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-27841537689206010808041),(-27841537689205676163715)⟩,⟨6899878632375026209185,6899878632375360857280⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-19525010036145610769919),(-19525010036145041543787)⟩,⟨17868116084782391404959,17868116084782960631905⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-1540505804307064374845),(-1540505804306542724200)⟩,⟨15441538324754233675620,15441538324754755324544⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨4790096873140103529348,4790096873140542454681⟩,⟨4306242662159650217226,4306242662160089142251⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨1859365653148535126309,1859365653148753049950⟩,⟨(-741597633491664884966),(-741597633491446961082)⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨(-26707966223402702295),(-26707966223316090257)⟩,⟨(-485038970315100980185),(-485038970315014368180)⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨(-94580273604855139636),(-94580273604832816111)⟩,⟨(-16960154766417301726),(-16960154766394978201)⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-5814292602542273382),(-5814292602538591337)⟩,⟨15237322886821633024,15237322886825315072⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨2144273196005540841,2144273196005969839⟩,⟨1336657423204503086,1336657423204932086⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨278278599819922892,278278599819965675⟩,⟨(-264640130309983339),(-264640130309940557)⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-23568639969952439),(-23568639969948276)⟩,⟨(-57219531108229470),(-57219531108225304)⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-11244427693156325),(-11244427693155918)⟩,⟨(-1699842816432364),(-1699842816431951)⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-1976666461466766),(-1976666461466690)⟩,⟨1541258659122347,1541258659122426⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-222940747705268),(-222940747705236)⟩,⟨614196527315134,614196527315168⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-8789746221499),(-8789746221481)⟩,⟨140944654500562,140944654500584⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨(-407409349197926344042955749),(-407409349197926271577068114)⟩,⟨(-381341118105041496334646409),(-381341118105041423864255328)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-1205430054689766508653414579),(-1205430054689766304215580784)⟩,⟨(-666587172485925606128595401),(-666587172485925401729496375)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-1574588791074868120848626649),(-1574588791074867823712251116)⟩,⟨(-32591586811627002986125611),(-32591586811626705987180673)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-1005840594118055483873114039),(-1005840594118055156016673361)⟩,⟨802877947561741912518221455,802877947561742240294857329⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-29173284582778406831287219),(-29173284582778110522423904)⟩,⟨829046561769441569074281389,829046561769441865413640482⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨355543971670800836288206329,355543971670801052924814557⟩,⟨250055448741480888833455249,250055448741481105486437829⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨166786473196788975998867952,166786473196789104521929942⟩,⟨(-88814587782676185152126561),(-88814587782676056636418416)⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-7552065428689160472828351),(-7552065428689097156168881)⟩,⟨(-70106688775066328295271001),(-70106688775066264978033420)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-23023164333202624381541177),(-23023164333202597851511627)⟩,⟨(-5240650764958192345779615),(-5240650764958165815497355)⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-3898023560646504666383089),(-3898023560646494799934240)⟩,⟨6335870809003223023093428,6335870809003232889468036⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨1380293415211514776813692,1380293415211518522600928⟩,⟨1851942073465183204876180,1851942073465186950670007⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨727862793961176095934256,727862793961177911141432⟩,⟨(-113250497867324225942705),(-113250497867322410739413)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨117064425636194002034630,117064425636194989659850⟩,⟨(-219393511978544015016952),(-219393511978543027389806)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-21220402922711169120408),(-21220402922710461295531)⟩,⟨(-87249682373285153924376),(-87249682373284446098652)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-22383754001654612929526),(-22383754001654235796420)⟩,⟨(-24437582741211014772020),(-24437582741210637639005)⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-7206823453044717182665),(-7206823453044609691835)⟩,⟨(-4641308445850764504720),(-4641308445850657013984)⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-622077623628386277389801849),(-622077623628386001869046312)⟩,⟨107513360641178822957654697,107513360641179098443212931⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-1464319225550363588476909546),(-1464319225550363582944466524)⟩,⟨1378589349185574563669230961,1378589349185574569175766236⟩⟩
 def realAnswer : RBox := ⟨(-2086396849178749865966711395),(-2086396849178749584713512836)⟩
end hm24_0_1_2
namespace hm24_0_1_3
noncomputable def s0_0 : CBox := ⟨⟨(-98),98⟩,⟨(-98),98⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-281),281⟩,⟨(-281),281⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-469),469⟩,⟨(-469),469⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-665),665⟩,⟨(-665),665⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-1059),1059⟩,⟨(-1059),1059⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-877),877⟩,⟨(-877),877⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-638),638⟩,⟨(-638),638⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-359),359⟩,⟨(-359),359⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-214),214⟩,⟨(-214),214⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-76),76⟩,⟨(-76),76⟩⟩
noncomputable def ans : CBox := ⟨⟨176219729627133749672352564,176219729627134105698896727⟩,⟨738985348922971342242145138,738985348922971698313959647⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨1751029392073738315542935914,1751029392073738322522910491⟩,⟨1676271899561581347803724233,1676271899561581354813573131⟩⟩
 def realAnswer : RBox := ⟨1927249121700872065115288478,1927249121700872428321807218⟩
end hm24_0_1_3
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock24_11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid
namespace hm24_0_1_10
noncomputable def s0_0 : CBox := ⟨⟨(-493),493⟩,⟨(-493),493⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-1557),1557⟩,⟨(-1557),1557⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-2839),2839⟩,⟨(-2839),2839⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-4315),4315⟩,⟨(-4315),4315⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-5665),5665⟩,⟨(-5665),5665⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-6203),6203⟩,⟨(-6203),6203⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-7028),7028⟩,⟨(-7028),7028⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-9589),9589⟩,⟨(-9589),9589⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-10191),10191⟩,⟨(-10191),10191⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-8487),8487⟩,⟨(-8487),8487⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-9097),9097⟩,⟨(-9097),9097⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-9094),9094⟩,⟨(-9094),9094⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-6964),6964⟩,⟨(-6964),6964⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-3744),3744⟩,⟨(-3744),3744⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-2059),2059⟩,⟨(-2059),2059⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-651),651⟩,⟨(-651),651⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-77),77⟩,⟨(-77),77⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-214),214⟩,⟨(-214),214⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-337),337⟩,⟨(-337),337⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-540),540⟩,⟨(-540),540⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-860),860⟩,⟨(-860),860⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-1248),1248⟩,⟨(-1248),1248⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-1621),1621⟩,⟨(-1621),1621⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-1823),1823⟩,⟨(-1823),1823⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-1889),1889⟩,⟨(-1889),1889⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-2568),2568⟩,⟨(-2568),2568⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-3008),3008⟩,⟨(-3008),3008⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-2936),2936⟩,⟨(-2936),2936⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-2412),2412⟩,⟨(-2412),2412⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-1685),1685⟩,⟨(-1685),1685⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-1134),1134⟩,⟨(-1134),1134⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-425),425⟩,⟨(-425),425⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-16),0⟩,⟨(-16),10⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-19),5⟩,⟨(-16),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-31),16⟩,⟨(-16),27⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-40),34⟩,⟨(-28),44⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-61),61⟩,⟨(-60),65⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-88),88⟩,⟨(-88),88⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-112),112⟩,⟨(-112),112⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-128),128⟩,⟨(-128),128⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-156),156⟩,⟨(-156),156⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-220),220⟩,⟨(-220),220⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-274),274⟩,⟨(-274),274⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-386),386⟩,⟨(-386),386⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-380),380⟩,⟨(-380),380⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-310),310⟩,⟨(-310),310⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-201),201⟩,⟨(-201),201⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-72),72⟩,⟨(-72),72⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨7019397639678,7019397639694⟩,⟨(-18568001930413),(-18568001930397)⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨3569255472786,3569255472802⟩,⟨(-38615588395251),(-38615588395231)⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-11634608845500),(-11634608845483)⟩,⟨(-24923443772784),(-24923443772766)⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨(-10096801579863),(-10096801579844)⟩,⟨(-3849532415852),(-3849532415831)⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-2123464697998),(-2123464697973)⟩,⟨1514502184817,1514502184840⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨86177794334,86177794360⟩,⟨400710550359,400710550384⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨44149708060,44149708090⟩,⟨2668767439,2668767471⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨863888669,863888698⟩,⟨(-3375835773),(-3375835744)⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨(-197350347),(-197350312)⟩,⟨(-87818070),(-87818039)⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨(-6773520),(-6773483)⟩,⟨9363550,9363586⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨356270,356306⟩,⟨478507,478543⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨33135,33168⟩,⟨(-6365),(-6331)⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨1017,1050⟩,⟨(-2173),(-2141)⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-82),(-51)⟩,⟨(-244),(-212)⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-39),(-11)⟩,⟨(-39),(-12)⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-17),0⟩,⟨(-16),0⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨(-129354613875196465104),(-129354613875190421165)⟩,⟨609380824362548334532,609380824362554378398⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨89088957953988069879,89088957954003692828⟩,⟨1412563151037868437424,1412563151037884060167⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨768790757691066756546,768790757691095189748⟩,⟨1122181652025996380719,1122181652026024813836⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨832809687299714045275,832809687299743443174⟩,⟨153468480235445831691,153468480235475229670⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨256458099403610324885,256458099403636321999⟩,⟨(-280303575555033829534),(-280303575555007832402)⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-57433274919243917283),(-57433274919229451939)⟩,⟨(-116247660922873486386),(-116247660922859021056)⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨(-34061556579769324759),(-34061556579763095712)⟩,⟨8114774831342684149,8114774831348913199⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨848838487672713743,848838487674511429⟩,⟨7739188956424564579,7739188956426362264⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨1493743107215328145,1493743107215678594⟩,⟨(-51955229966037523),(-51955229965687077)⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨11714722127427894,11714722127477764⟩,⟨(-262108250644932638),(-262108250644882766)⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-44239475703699380),(-44239475703694053)⟩,⟨(-8410852206867430),(-8410852206862102)⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-3577195413230647),(-3577195413230148)⟩,⟨7295230339695071,7295230339695574⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨1014074901479189,1014074901479260⟩,⟨1299762676264558,1299762676264630⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨393425500160521,393425500160545⟩,⟨9888727727849,9888727727875⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨90484176874590,90484176874608⟩,⟨(-59895012529726),(-59895012529709)⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨15080570101739,15080570101755⟩,⟨(-18852192370650),(-18852192370633)⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨(-8535593221607576262766358),(-8535593221607574805584584)⟩,⟨(-2947776999380307447239463),(-2947776999380305990590708)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-22642743107492976839847703),(-22642743107492972642159220)⟩,⟨(-1550883257069179656559001),(-1550883257069175460980541)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-24222415351566135632419739),(-24222415351566129278434724)⟩,⟨11681286488212524241227634,11681286488212530593105686⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-8560541689837368568249919),(-8560541689837361155885119)⟩,⟨21520967091560735656431961,21520967091560743068962382⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨8288939614609902485233052,8288939614609909646064196⟩,⟨13661808146901318966269458,13661808146901326128057906⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨9075686894502489117541947,9075686894502494744492547⟩,⟨(-371912225200735233230443),(-371912225200729606495194)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨1465106170674397252855504,1465106170674400840308095⟩,⟨(-4075743956776746277648133),(-4075743956776742690258189)⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-1435629520557025012384159),(-1435629520557023123579834)⟩,⟨(-1064817151068163070523759),(-1064817151068161181669121)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-511530516588826178344108),(-511530516588825341608344)⟩,⟨425353144246787663684073,425353144246788500407696⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨103101948831504896012810,103101948831505220394127⟩,⟨209204353256777102259312,209204353256777426641744⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨79210932856322569080624,79210932856322698052016⟩,⟨(-13370162175483921424336),(-13370162175483792452936)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨6660391708430644510118,6660391708430707680881⟩,⟨(-27402836632840809707675),(-27402836632840746536737)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-7110521202511289827838),(-7110521202511249789549)⟩,⟨(-7522040878434010783966),(-7522040878433970745739)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-3995220206406402660325),(-3995220206406373675740)⟩,⟨(-118107416086020360745),(-118107416085991376221)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-1347912064488547367201),(-1347912064488529139705)⟩,⟨757229145282597476517,757229145282615704005⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-288762903674491213635),(-288762903674485592454)⟩,⟨290631918425995450955,290631918426001072141⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-7816793544134565379611396),(-7816793544134558836276416)⟩,⟨6240506155241101179373923,6240506155241107722064570⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-12611024639794543534099921),(-12611024639794543401371107)⟩,⟨29836226836094408847796764,29836226836094408980407622⟩⟩
 def realAnswer : RBox := ⟨(-20427818183929109013711317),(-20427818183929102137647523)⟩
end hm24_0_1_10
namespace hm24_0_1_11
noncomputable def s0_0 : CBox := ⟨⟨(-390),390⟩,⟨(-390),390⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-1102),1102⟩,⟨(-1102),1102⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-1755),1755⟩,⟨(-1755),1755⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-2983),2983⟩,⟨(-2983),2983⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-4503),4503⟩,⟨(-4503),4503⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-5681),5681⟩,⟨(-5681),5681⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-5674),5674⟩,⟨(-5674),5674⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-7171),7171⟩,⟨(-7171),7171⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-8630),8630⟩,⟨(-8630),8630⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-7660),7660⟩,⟨(-7660),7660⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-7047),7047⟩,⟨(-7047),7047⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-7507),7507⟩,⟨(-7507),7507⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-5891),5891⟩,⟨(-5891),5891⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-3184),3184⟩,⟨(-3184),3184⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-1742),1742⟩,⟨(-1742),1742⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-545),545⟩,⟨(-545),545⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-60),60⟩,⟨(-60),60⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-171),171⟩,⟨(-171),171⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-300),300⟩,⟨(-300),300⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-447),447⟩,⟨(-447),447⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-591),591⟩,⟨(-591),591⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-682),682⟩,⟨(-682),682⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-965),965⟩,⟨(-965),965⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-1416),1416⟩,⟨(-1416),1416⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-1731),1731⟩,⟨(-1731),1731⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-1720),1720⟩,⟨(-1720),1720⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-1823),1823⟩,⟨(-1823),1823⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-2187),2187⟩,⟨(-2187),2187⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-2111),2111⟩,⟨(-2111),2111⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-1665),1665⟩,⟨(-1665),1665⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-1033),1033⟩,⟨(-1033),1033⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-351),351⟩,⟨(-351),351⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨0,16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-16),16⟩,⟨(-5),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-16),28⟩,⟨(-27),21⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-45),45⟩,⟨(-45),45⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-60),60⟩,⟨(-60),60⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-90),90⟩,⟨(-90),90⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-121),121⟩,⟨(-121),121⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-147),147⟩,⟨(-147),147⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-160),160⟩,⟨(-160),160⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-187),187⟩,⟨(-187),187⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-205),205⟩,⟨(-205),205⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-196),196⟩,⟨(-196),196⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-143),143⟩,⟨(-143),143⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-56),56⟩,⟨(-56),56⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨(-8772630585113),(-8772630585097)⟩,⟨(-383669260154),(-383669260138)⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-16756731175289),(-16756731175272)⟩,⟨3899234640716,3899234640734⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-8865238747269),(-8865238747251)⟩,⟨8486791925639,8486791925656⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨(-138892499336),(-138892499319)⟩,⟨4860504550672,4860504550691⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨976625912882,976625912904⟩,⟨674164006486,674164006506⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨158859098871,158859098890⟩,⟨(-102393770048),(-102393770026)⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-6433787670),(-6433787646)⟩,⟨(-19686104708),(-19686104683)⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨(-1642509015),(-1642508989)⟩,⟨236093811,236093834⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨(-771445),(-771424)⟩,⟨104703674,104703697⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨5593799,5593824⟩,⟨1113865,1113891⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨139165,139192⟩,⟨(-265369),(-265339)⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨(-10494),(-10466)⟩,⟨(-13691),(-13661)⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-1250),(-1223)⟩,⟨27,55⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-102),(-78)⟩,⟨75,100⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-18),9⟩,⟨7,28⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-16),16⟩,⟨0,16⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨234765274296097081866,234765274296099128165⟩,⟨8882051901114215831,8882051901116262161⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨520206836705258230722,520206836705264467299⟩,⟨(-125569820205624687415),(-125569820205618450768)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨367692642083676436298,367692642083687647047⟩,⟨(-363357663489224000989),(-363357663489212790231)⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-1240041820612669273),(-1240041820601832801)⟩,⟨(-324237600063303557320),(-324237600063292720887)⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-125557148242884854783),(-125557148242874624134)⟩,⟨(-76231658752091596880),(-76231658752081366233)⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-39903995977726818488),(-39903995977721070523)⟩,⟨31308175987394913449,31308175987400661416⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨6071826471828720412,6071826471831144423⟩,⟨12482621968945187660,12482621968947611669⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨2950963557019247540,2950963557019953523⟩,⟨(-1049117539450519951),(-1049117539449813970)⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-169431854399739432),(-169431854399598517)⟩,⟨(-586597616475883291),(-586597616475742373)⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨(-106338800011233917),(-106338800011213205)⟩,⟨23325149769434576,23325149769455289⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨1637704539889681,1637704539892030⟩,⟨18900894433049996,18900894433052346⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨3422368764592552,3422368764592789⟩,⟨583662940962873,583662940963112⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨408710756489459,408710756489496⟩,⟨(-584466208887040),(-584466208887002)⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-47802449519148),(-47802449519128)⟩,⟨(-165187033700845),(-165187033700823)⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-37334643903137),(-37334643903120)⟩,⟨(-29766972061506),(-29766972061487)⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-9983737205619),(-9983737205603)⟩,⟨(-3741436198863),(-3741436198846)⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨(-820954825527478765811374),(-820954825527478280691876)⟩,⟨2854447455867612063939363,2854447455867612549257977⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-103133034087598978650517),(-103133034087597579013935)⟩,⟨7481037298306962971886069,7481037298306964372253071⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨4332488299541737745053237,4332488299541739870632970⟩,⟨7779638618688556183519130,7779638618688558309726197⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨7343023365922419556104362,7343023365922422045878735⟩,⟨2382381643528113442329378,2382381643528115931975216⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨4378200946888720226040684,4378200946888722640906611⟩,⟨(-3112294983449729980637280),(-3112294983449727566076681)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-377780875962777017434776),(-377780875962775114495224)⟩,⟨(-3061424529148470802200780),(-3061424529148468899167398)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-1440562283355400162740595),(-1440562283355398948003935)⟩,⟨(-372336894650922511139843),(-372336894650921296392319)⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-316975690127926340916550),(-316975690127925702382682)⟩,⟨534974647114800073034800,534974647114800711552674⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨169614760751090426272187,169614760751090707594739⟩,⟨161960079693652196348401,161960079693652477675478⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨69505263245223715607593,69505263245223823693348⟩,⟨(-45954951892878781478121),(-45954951892878673392892)⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-8716900680311593537320),(-8716900680311550863396)⟩,⟨(-27736163016970926863604),(-27736163016970884189653)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨(-10286824310328596730086),(-10286824310328573991755)⟩,⟨(-939746176424392310314),(-939746176424369572057)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-2341555796459803836630),(-2341555796459788879145)⟩,⟨3032488160902383505892,3032488160902398463407⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨198296222214965684294,198296222214977197061⟩,⟨1478668793828882646449,1478668793828894159238⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨364766153659248711036,364766153659255420051⟩,⟨451546640301408085517,451546640301414794533⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨126278573400995729317,126278573400997705634⟩,⟨88648775124960922643,88648775124962898961⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨2202289117229476835809510,2202289117229479037633877⟩,⟨2429660918278434872631461,2429660918278437074658455⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨10009697641532187606325309,10009697641532187652161339⟩,⟨3630531152989222310454992,3630531152989222356310670⟩⟩
 def realAnswer : RBox := ⟨12211986758761664342134819,12211986758761666789795216⟩
end hm24_0_1_11
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid

namespace tm0_13_1
noncomputable def s1_0 : CBox := ⟨⟨1,27⟩,⟨229,249⟩⟩
end tm0_13_1

end SharpPlanar.CachedData

end OAI
end


