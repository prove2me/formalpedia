-- Prove2me | Definitions.Def_OAIQ098D195
-- name    : OAIQ098D195
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T15:50:27.49416+00:00
-- url     : https://prove2.me/theorems/36fc4f7a-1b1a-4108-8b71-d31224174e21
-- title:
--   Definitions bundle OAIQ098D195 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1373 declarations of OpenAI's Lean: 1373 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.hm24_1_1_11.s4`, `OAI.SharpPlanar.CachedData.hm24_1_1_11.s4_0`, `OAI.SharpPlanar.CachedData.hm24_1_1_11.s4_1`, `OAI.SharpPlanar.CachedData.hm24_1_1_11.s4_10`, `OAI.SharpPlanar.CachedData.hm24_1_1_11.s4_11`, `OAI.SharpPlanar.CachedData.hm24_1_1_11.s4_12`, `OAI.SharpPlanar.CachedData.hm24_1_1_11.s4_13`, `OAI.SharpPlanar.CachedData.hm24_1_1_11.s4_14`, `OAI.SharpPlanar.CachedData.hm24_1_1_11.s4_15`, `OAI.SharpPlanar.CachedData.hm24_1_1_11.s4_2`, `OAI.SharpPlanar.CachedData.hm24_1_1_11.s4_3`, `OAI.SharpPlanar.CachedData.hm24_1_1_11.s4_4`, `OAI.SharpPlanar.CachedData.hm24_1_1_11.s4_5`, `OAI.SharpPlanar.CachedData.hm24_1_1_11.s4_6`, `OAI.SharpPlanar.CachedData.hm24_1_1_11.s4_7`, `OAI.SharpPlanar.CachedData.hm24_1_1_11.s4_8`, `OAI.SharpPlanar.CachedData.hm24_1_1_11.s4_9`, `OAI.SharpPlanar.CachedData.hm24_1_1_11.s5`, `OAI.SharpPlanar.CachedData.hm24_1_1_11.s5_0`, `OAI.SharpPlanar.CachedData.hm24_1_1_11.s5_1`, `OAI.SharpPlanar.CachedData.hm24_1_1_11.s5_10`, `OAI.SharpPlanar.CachedData.hm24_1_1_11.s5_11`, `OAI.SharpPlanar.CachedData.hm24_1_1_11.s5_12`, `OAI.SharpPlanar.CachedData.hm24_1_1_11.s5_13`, `OAI.SharpPlanar.CachedData.hm24_1_1_11.s5_14`, `OAI.SharpPlanar.CachedData.hm24_1_1_11.s5_15`, `OAI.SharpPlanar.CachedData.hm24_1_1_11.s5_2`, `OAI.SharpPlanar.CachedData.hm24_1_1_11.s5_3`, `OAI.SharpPlanar.CachedData.hm24_1_1_11.s5_4`, `OAI.SharpPlanar.CachedData.hm24_1_1_11.s5_5`, `OAI.SharpPlanar.CachedData.hm24_1_1_11.s5_6`, `OAI.SharpPlanar.CachedData.hm24_1_1_11.s5_7`, `OAI.SharpPlanar.CachedData.hm24_1_1_11.s5_8`, `OAI.SharpPlanar.CachedData.hm24_1_1_11.s5_9`, `OAI.SharpPlanar.CachedData.hm24_1_1_2.ans`, `OAI.SharpPlanar.CachedData.hm24_1_1_2.atomAnswer`, `OAI.SharpPlanar.CachedData.hm24_1_1_2.s0`, `OAI.SharpPlanar.CachedData.hm24_1_1_2.s0_0`, `OAI.SharpPlanar.CachedData.hm24_1_1_2.s0_1`, `OAI.SharpPlanar.CachedData.hm24_1_1_2.s0_10` and 1333 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_LowBlock24_10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/LowBlock24_10.lean), [`PlanarPacking_Certificate_LowBlock24_11`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/LowBlock24_11.lean), [`PlanarPacking_Certificate_LowBlock25_0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/LowBlock25_0.lean), [`PlanarPacking_Certificate_LowBlock25_1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/LowBlock25_1.lean), [`PlanarPacking_Certificate_LowBlock28_1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/LowBlock28_1.lean).
--
--   **Imports.** It imports the bundle `OAIQ098D003` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098D272`, `OAIQ098D401`, `OAIQ098D402`, `OAIQ098D403` and `OAIQ098D564`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098D003

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
open IntegerIntervals
namespace hm24_1_1_2
noncomputable def s0_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-28),28⟩,⟨(-28),28⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-40),40⟩,⟨(-40),40⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-49),49⟩,⟨(-49),49⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-53),53⟩,⟨(-53),53⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-44),44⟩,⟨(-44),44⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-30),30⟩,⟨(-30),30⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-17),17⟩,⟨(-17),17⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-34),34⟩,⟨(-34),34⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-27),27⟩,⟨(-27),27⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨0,16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-16),16⟩,⟨(-12),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-26),26⟩,⟨(-26),26⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-22),22⟩,⟨(-22),22⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨(-15003063702815),(-15003063702798)⟩,⟨35253742788066,35253742788084⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-11532091868940),(-11532091868920)⟩,⟨71200904889228,71200904889247⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨14835703142278,14835703142299⟩,⟨45200050228613,45200050228635⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨14340396118202,14340396118226⟩,⟨8838438253444,8838438253468⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨3366062651085,3366062651113⟩,⟨(-1233091016289),(-1233091016267)⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨73092096379,73092096405⟩,⟨(-485774659514),(-485774659487)⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-39608854762),(-39608854730)⟩,⟨(-23334655918),(-23334655888)⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨(-2349083126),(-2349083093)⟩,⟨2052080581,2052080613⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨65411392,65411424⟩,⟨151765741,151765773⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨7525621,7525657⟩,⟨(-408810),(-408775)⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨126410,126442⟩,⟨(-309086),(-309052)⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨(-9413),(-9384)⟩,⟨(-13573),(-13541)⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-1050),(-1022)⟩,⟨(-159),(-131)⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-97),(-71)⟩,⟨32,57⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-20),0⟩,⟨0,21⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-16),16⟩,⟨0,16⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨(-4230199779408316651530),(-4230199779408229554920)⟩,⟨178458286694775170653,178458286694862266902⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-9220864483518480433187),(-9220864483518212467042)⟩,⟨2716311845689758843985,2716311845690026809361⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-6615660824960917308761),(-6615660824960456135205)⟩,⟨6343297659608466536953,6343297659608927710234⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-617817973311394613162),(-617817973310969816251)⟩,⟨5517679996037667479760,5517679996038092276976⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨1658686612340212499263,1658686612340571713532⟩,⟨1666839984221294481993,1666839984221653696341⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨706202549127860745834,706202549128039432618⟩,⟨(-207169063900771065011),(-207169063900592378276)⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨11976475019696322369,11976475019767420188⟩,⟨(-179162739458553589611),(-179162739458482491784)⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨(-34175478241022747030),(-34175478241004419490)⟩,⟨(-11437567378909477549),(-11437567378891150008)⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-3233305109885008610),(-3233305109881987297)⟩,⟨5366294960975279042,5366294960978300358⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨704487059438439099,704487059438790763⟩,⟨702361074324634658,702361074324986321⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨136572422019788696,136572422019823715⟩,⟨(-69167412095659925),(-69167412095624907)⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-679462926517041),(-679462926513644)⟩,⟨(-24407396265727404),(-24407396265724010)⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-3643361514316031),(-3643361514315701)⟩,⟨(-2356178273374916),(-2356178273374590)⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-896999517007809),(-896999517007752)⟩,⟨181332259718837,181332259718893⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-169296553171404),(-169296553171377)⟩,⟨155348159615355,155348159615379⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-25324037570219),(-25324037570201)⟩,⟨41540989316813,41540989316834⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨(-12624874373280725429751316),(-12624874373280723023662338)⟩,⟨(-10752678892608932944708786),(-10752678892608930539744302)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-38596165764257650582410380),(-38596165764257643094740145)⟩,⟨(-10338956408177821019444846),(-10338956408177813565231828)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-34201710075973072628823884),(-34201710075973061082851571)⟩,⟨31317563518055699274718931,31317563518055710723474152⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨32792692954464724474477530,32792692954464740985585720⟩,⟨55936904122959145794043721,55936904122959162255916475⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨87952415384914632532515740,87952415384914664546455001⟩,⟨(-1693376460115901557034),(-1693376460083860298401)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨49604818703086390762990871,49604818703086430013979980⟩,⟨(-63855772788651839340958460),(-63855772788651800078299755)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-14234528749624121931091856),(-14234528749624089254291356)⟩,⟨(-50354554481230016597434473),(-50354554481229983928062172)⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-24660359284080268098097117),(-24660359284080248081737012)⟩,⟨(-7570683190987430376050323),(-7570683190987410358586309)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-7624077868566050858558499),(-7624077868566041240976902)⟩,⟨7095608679461664305247593,7095608679461673923101806⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨889071115188226543962093,889071115188230485778798⟩,⟨3564936603251012854282039,3564936603251016795909015⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨1156164441326862887778285,1156164441326864588808663⟩,⟨334371431292392146452002,334371431292393847528770⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨297314747738895234823002,297314747738896267421948⟩,⟨(-250591453423372012759593),(-250591453423370980160991)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-158696128609943112811),(-158696128609285788375)⟩,⟨(-130985950097003962901697),(-130985950097003305582363)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-30925011314858248224094),(-30925011314857721103470)⟩,⟨(-35963275436107863387196),(-35963275436107336266374)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-16540012996701831713977),(-16540012996701541229939)⟩,⟨(-6261514727287545475228),(-6261514727287254990692)⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-4589768846713094305517),(-4589768846713010826337)⟩,⟨(-485140836995339327833),(-485140836995255848497)⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨6780033915182328777743013,6780033915182359049766294⟩,⟨(-7505535220992245264689462),(-7505535220992215017373844)⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨1914878987258167762311994685,1914878987258167769546727868⟩,⟨(-1802770687396520590460617385),(-1802770687396520583259763565)⟩⟩
end hm24_1_1_2
namespace hm24_1_1_3
noncomputable def s0_0 : CBox := ⟨⟨(-24),24⟩,⟨(-24),24⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-56),56⟩,⟨(-56),56⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-89),89⟩,⟨(-89),89⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-122),122⟩,⟨(-122),122⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-153),153⟩,⟨(-153),153⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-178),178⟩,⟨(-178),178⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-194),194⟩,⟨(-194),194⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-208),208⟩,⟨(-208),208⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-208),208⟩,⟨(-208),208⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-203),203⟩,⟨(-203),203⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-185),185⟩,⟨(-185),185⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-158),158⟩,⟨(-158),158⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-115),115⟩,⟨(-115),115⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-68),68⟩,⟨(-68),68⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-42),42⟩,⟨(-42),42⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-21),21⟩,⟨(-21),21⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-29),29⟩,⟨(-29),29⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-41),41⟩,⟨(-41),41⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-54),54⟩,⟨(-54),54⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-68),68⟩,⟨(-68),68⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-81),81⟩,⟨(-81),81⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-96),96⟩,⟨(-96),96⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-105),105⟩,⟨(-105),105⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-112),112⟩,⟨(-112),112⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-112),112⟩,⟨(-112),112⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-103),103⟩,⟨(-103),103⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-96),96⟩,⟨(-96),96⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-87),87⟩,⟨(-87),87⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-74),74⟩,⟨(-74),74⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-52),52⟩,⟨(-52),52⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-24),24⟩,⟨(-24),24⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨0,16⟩,⟨(-16),16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-5),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-22),16⟩,⟨(-28),16⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-32),32⟩,⟨(-32),26⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-39),39⟩,⟨(-39),39⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-35),35⟩,⟨(-35),35⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-28),28⟩,⟨(-28),28⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨61920969408566,61920969408583⟩,⟨5253366407583,5253366407600⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨115827240639190,115827240639213⟩,⟨(-18714136391953),(-18714136391931)⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨62245252400418,62245252400446⟩,⟨(-46721420789903),(-46721420789878)⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨5979368156194,5979368156221⟩,⟨(-27142808716501),(-27142808716468)⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-3843521012756),(-3843521012722)⟩,⟨(-4581871400357),(-4581871400324)⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨(-812156956150),(-812156956116)⟩,⟨174032908754,174032908791⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-12297370121),(-12297370081)⟩,⟨77969954583,77969954620⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨4881111985,4881112025⟩,⟨2417136564,2417136607⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨200850721,200850760⟩,⟨(-214367056),(-214367013)⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨(-6342964),(-6342921)⟩,⟨(-12075334),(-12075292)⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨(-613934),(-613893)⟩,⟨36359,36402⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨(-14829),(-14791)⟩,⟨27075,27116⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨643,677⟩,⟨1857,1891⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨137,168⟩,⟨87,118⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨12,38⟩,⟨(-10),18⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨0,16⟩,⟨(-16),16⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨1240569969568238349607,1240569969568363401858⟩,⟨5721750491378278763211,5721750491378403815944⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨5920317806479204741776,5920317806479615397810⟩,⟨11939469544380557563591,11939469544380968220431⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨10337644153561066367390,10337644153561715878947⟩,⟨7500091321208324897415,7500091321208974409043⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨7773549587066083084720,7773549587066659926600⟩,⟨(-579715147870365995379),(-579715147869789154029)⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨1862196385048008849886,1862196385048526556828⟩,⟨(-2765140506562820639761),(-2765140506562302932847)⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-498219556827353973761),(-498219556827095033230)⟩,⟨(-930684995138512269238),(-930684995138253328642)⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨(-258023817397248544593),(-258023817397148058685)⟩,⟨39483201752047357782,39483201752147843675⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨(-4824964641497755649),(-4824964641471064054)⟩,⟨52942099149577491731,52942099149604183327⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨8976913575852659646,8976913575857337128⟩,⟨2738883241984379595,2738883241989057078⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨756838525883989433,756838525884562738⟩,⟨(-1310929980946444423),(-1310929980945871116)⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-159967920129581790),(-159967920129529268)⟩,⟨(-174206344532936518),(-174206344532883995)⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-36380589626197062),(-36380589626192072)⟩,⟨11836254733639150,11836254733644142⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-1877318408309319),(-1877318408308772)⟩,⟨6621745388976965,6621745388977508⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨710864637117241,710864637117316⟩,⟨1282365648434188,1282365648434262⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨322562969221605,322562969221638⟩,⟨182722492332186,182722492332220⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨76683374977726,76683374977744⟩,⟨18061410650071,18061410650091⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨(-12151058476986003531833661),(-12151058476986000522515251)⟩,⟨15884935482740556517167952,15884935482740559531747172⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-9927770443506961226302910),(-9927770443506951864734106)⟩,⟨47261101772502359837930832,47261101772502369249852683⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨40404944758349125039476622,40404944758349139531661460⟩,⟨39194678833355964151303570,39194678833355978767606087⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨65609035718851476609604862,65609035718851497709109318⟩,⟨(-44480612586341115502686757),(-44480612586341094352924930)⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-7914588325655820256891640),(-7914588325655778697801510)⟩,⟨(-108176811197482114491203424),(-108176811197482072971349193)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-84348396397230226300987142),(-84348396397230174649611820)⟩,⟨(-55080383048692413908902753),(-55080383048692362268423642)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-61541673330986605940733872),(-61541673330986562312500412)⟩,⟨23701309679327056199961819,23701309679327099837793937⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-6370378903402663563395520),(-6370378903402636414604881)⟩,⟨32297869290069809568906678,32297869290069836715710334⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨10241575259394145296969741,10241575259394158538757771⟩,⟨8744580247897110610892571,8744580247897123852550254⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨4487587298729166682433504,4487587298729172181292471⟩,⟨(-1742792749228106620527895),(-1742792749228101121441851)⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨230012910793982934588061,230012910793985307724657⟩,⟨(-1580746612114740614402638),(-1580746612114738241337071)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨(-391489798963944008973786),(-391489798963942584404602)⟩,⟨(-345680533271219342740261),(-345680533271217918164978)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-175587251162649276119531),(-175587251162648355623381)⟩,⟨27809819274219222216663,27809819274220142719523⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-41708865658319260285549),(-41708865658318530908067)⟩,⟨49743143035299955895050,49743143035300685271668⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-4700146538454350283132),(-4700146538453977049633)⟩,⟨23889263930143412601902,23889263930143785834530⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨412605087421140463886,412605087421243778108⟩,⟨6359662561787203182969,6359662561787306496933⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-10311233440407629837836634),(-10311233440407589956829335)⟩,⟨(-7365628343805115535245859),(-7365628343805075622987577)⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-2289807666557965498683806027),(-2289807666557965489556146964)⟩,⟨(-2192047868657452540910057171),(-2192047868657452531743331690)⟩⟩
end hm24_1_1_3
namespace hm24_1_1_4
noncomputable def s0_0 : CBox := ⟨⟨(-42),42⟩,⟨(-42),42⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-107),107⟩,⟨(-107),107⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-165),165⟩,⟨(-165),165⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-208),208⟩,⟨(-208),208⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-261),261⟩,⟨(-261),261⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-332),332⟩,⟨(-332),332⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-392),392⟩,⟨(-392),392⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-439),439⟩,⟨(-439),439⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-464),464⟩,⟨(-464),464⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-463),463⟩,⟨(-463),463⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-432),432⟩,⟨(-432),432⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-367),367⟩,⟨(-367),367⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-267),267⟩,⟨(-267),267⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-148),148⟩,⟨(-148),148⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-87),87⟩,⟨(-87),87⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-34),34⟩,⟨(-34),34⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-18),18⟩,⟨(-18),18⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-35),35⟩,⟨(-35),35⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-51),51⟩,⟨(-51),51⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-71),71⟩,⟨(-71),71⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-97),97⟩,⟨(-97),97⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-129),129⟩,⟨(-129),129⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-165),165⟩,⟨(-165),165⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-202),202⟩,⟨(-202),202⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-232),232⟩,⟨(-232),232⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-253),253⟩,⟨(-253),253⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-256),256⟩,⟨(-256),256⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-246),246⟩,⟨(-246),246⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-212),212⟩,⟨(-212),212⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-164),164⟩,⟨(-164),164⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-104),104⟩,⟨(-104),104⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-40),40⟩,⟨(-40),40⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-16),10⟩,⟨(-16),1⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-18),16⟩,⟨(-16),15⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-32),16⟩,⟨(-21),20⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-41),28⟩,⟨(-32),41⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-51),48⟩,⟨(-46),51⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-67),67⟩,⟨(-67),67⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-66),66⟩,⟨(-66),66⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-76),76⟩,⟨(-76),76⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-50),50⟩,⟨(-50),50⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-34),34⟩,⟨(-34),34⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-18),18⟩,⟨(-18),18⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨(-17461065850267),(-17461065850247)⟩,⟨(-73552111523686),(-73552111523666)⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-66219781612571),(-66219781612547)⟩,⟨(-126903355225018),(-126903355224994)⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-78808362402746),(-78808362402719)⟩,⟨(-53934002468171),(-53934002468142)⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨(-34151077377786),(-34151077377752)⟩,⟨4072857560980,4072857561010⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-3756606672202),(-3756606672168)⟩,⟨6471519916508,6471519916540⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨569760649735,569760649771⟩,⟨885860581877,885860581916⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨99206892007,99206892045⟩,⟨(-22138690973),(-22138690934)⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨476084398,476084440⟩,⟨(-7117588688),(-7117588649)⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨(-368962485),(-368962438)⟩,⟨(-131274260),(-131274216)⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨(-11317325),(-11317272)⟩,⟨14651816,14651866⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨412215,412271⟩,⟨742698,742751⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨43296,43346⟩,⟨1520,1572⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨1907,1954⟩,⟨(-2089),(-2043)⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨5,44⟩,⟨(-286),(-243)⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-27),1⟩,⟨(-51),(-20)⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-16),2⟩,⟨(-18),0⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨5627717003232067618581,5627717003232212909351⟩,⟨(-2279571366830377283142),(-2279571366830231992762)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨11162460865799533519278,11162460865799988347543⟩,⟨(-8210477127238184508144),(-8210477127237729680416)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨5792278628524267503064,5792278628524931803668⟩,⟨(-12025641193700690085420),(-12025641193700025784553)⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-2113289069659682744879),(-2113289069659073038774)⟩,⟨(-7931469326093282772258),(-7931469326092673065573)⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-3268293392435281595695),(-3268293392434743159704)⟩,⟨(-1372210814206140752885),(-1372210814205602316959)⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-870282046318972195015),(-870282046318681622395)⟩,⟨729597233125780368806,729597233126070941378⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨103034661615035045543,103034661615142590793⟩,⟨265280683164602766975,265280683164710312245⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨58229230292408916108,58229230292437627478⟩,⟨(-8278053588912269838),(-8278053588883558467)⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨526587109512861136,526587109518079052⟩,⟨(-10531701182498399360),(-10531701182493181449)⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨(-1667981477544967296),(-1667981477544283599)⟩,⟨(-449523392295685796),(-449523392295002095)⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-144156721097755573),(-144156721097690645)⟩,⟨233064194260080685,233064194260145615⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨25432622034225629,25432622034231150⟩,⟨37072843396791934,37072843396797453⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨8186628580951224,8186628580951854⟩,⟨(-176478902296155),(-176478902295525)⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨1211109786072135,1211109786072225⟩,⟨(-1279573818205172),(-1279573818205083)⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨90205476239252,90205476239286⟩,⟨(-439440843472535),(-439440843472501)⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-8106486273180),(-8106486273158)⟩,⟨(-95334900426075),(-95334900426055)⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨14924720858938839536328279,14924720858938842357580087⟩,⟨10221680465762141458187973,10221680465762144271161989⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨43268169819495235862224722,43268169819495244696917142⟩,⟨6644324822350885006684374,6644324822350893786879802⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨33444021520147462428619494,33444021520147476241898079⟩,⟨(-38831515431903477483743457),(-38831515431903463786873531)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-44635010558197980376225316),(-44635010558197960179811114)⟩,⟨(-57353524566472598429207899),(-57353524566472578269592300)⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-99254944526048415475736964),(-99254944526048375381987095)⟩,⟨14601332052042603959536897,14601332052042644093904527⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-44840333350381636705146425),(-44840333350381586206463105)⟩,⟨82765254899745751572062820,82765254899745802077473397⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨27660238217519089881158874,27660238217519133112062509⟩,⟨55861946264056915433437944,55861946264056958655309467⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨31376414225252238335355082,31376414225252265586079732⟩,⟨2881738800084159035865032,2881738800084186288959121⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨7288881546128403236096063,7288881546128416695101663⟩,⟨(-10836447667584159228058262),(-10836447667584145769139049)⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-2253466907603148086489634),(-2253466907603142433054837)⟩,⟨(-4159693052931112318264836),(-4159693052931106665016068)⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-1590050681356662112253791),(-1590050681356659662225512)⟩,⟨(-11833093334616851078641),(-11833093334614400974462)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨(-286640419535000020470363),(-286640419534998578584791)⟩,⟨441167721650876295627281,441167721650877737501440⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨55712275889355732799862,55712275889356711567191⟩,⟨172170324563695682929675,172170324563696661691156⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨57324345251260333483590,57324345251261070460946⟩,⟨33969980417847619068358,33969980417848356047156⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨25129765716722087925776,25129765716722441850918⟩,⟨669476713248045356236,669476713248399282422⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨6418863340573086809410,6418863340573204672311⟩,⟨(-1536048037455716770235),(-1536048037455598907110)⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-5789487400066828408036700),(-5789487400066789278542625)⟩,⟨10399810243972997112026627,10399810243973036212268873⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-1871386322755823762077024927),(-1871386322755823753366519440)⟩,⟨2170042206404235143045656017,2170042206404235151722994118⟩⟩
end hm24_1_1_4
namespace hm24_1_1_5
noncomputable def s0_0 : CBox := ⟨⟨(-74),74⟩,⟨(-74),74⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-208),208⟩,⟨(-208),208⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-336),336⟩,⟨(-336),336⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-451),451⟩,⟨(-451),451⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-524),524⟩,⟨(-524),524⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-540),540⟩,⟨(-540),540⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-576),576⟩,⟨(-576),576⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-711),711⟩,⟨(-711),711⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-809),809⟩,⟨(-809),809⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-848),848⟩,⟨(-848),848⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-805),805⟩,⟨(-805),805⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-691),691⟩,⟨(-691),691⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-500),500⟩,⟨(-500),500⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-272),272⟩,⟨(-272),272⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-158),158⟩,⟨(-158),158⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-56),56⟩,⟨(-56),56⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-25),25⟩,⟨(-25),25⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-59),59⟩,⟨(-59),59⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-93),93⟩,⟨(-93),93⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-131),131⟩,⟨(-131),131⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-171),171⟩,⟨(-171),171⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-209),209⟩,⟨(-209),209⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-243),243⟩,⟨(-243),243⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-256),256⟩,⟨(-256),256⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-270),270⟩,⟨(-270),270⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-332),332⟩,⟨(-332),332⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-382),382⟩,⟨(-382),382⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-400),400⟩,⟨(-400),400⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-369),369⟩,⟨(-369),369⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-300),300⟩,⟨(-300),300⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-197),197⟩,⟨(-197),197⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-72),72⟩,⟨(-72),72⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨0,16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-16),18⟩,⟨(-5),27⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-16),32⟩,⟨(-16),32⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-35),44⟩,⟨(-38),44⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-58),59⟩,⟨(-58),58⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-70),70⟩,⟨(-70),70⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-106),106⟩,⟨(-106),106⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-96),96⟩,⟨(-96),96⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-79),79⟩,⟨(-79),79⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-55),55⟩,⟨(-55),55⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-24),24⟩,⟨(-24),24⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨(-62688665696596),(-62688665696576)⟩,⟨38504008690356,38504008690373⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-97162752626797),(-97162752626773)⟩,⟨100385184528621,100385184528643⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-25310153520364),(-25310153520338)⟩,⟨90258547061785,90258547061812⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨14939560596690,14939560596719⟩,⟨30594907671965,30594907671994⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨7370268045754,7370268045788⟩,⟨1333982831650,1333982831683⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨637024363336,637024363375⟩,⟨(-857848448303),(-857848448264)⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-58744788155),(-58744788110)⟩,⟨(-86685992030),(-86685991983)⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨(-7079620090),(-7079620041)⟩,⟨2395400840,2395400892⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨28896078,28896134⟩,⟨416659499,416659556⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨19581733,19581795⟩,⟨4548222,4548284⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨542714,542777⟩,⟨(-765857),(-765795)⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨(-20270),(-20210)⟩,⟨(-44304),(-44246)⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-3130),(-3074)⟩,⟨(-893),(-839)⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-306),(-257)⟩,⟨93,143⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-47),(-12)⟩,⟨15,49⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-17),16⟩,⟨0,20⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨(-2659765763415361164066),(-2659765763415231208460)⟩,⟨(-4278310058652173665382),(-4278310058652043709555)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-8332896552898532445578),(-8332896552898142368632)⟩,⟨(-7963829791608977417968),(-7963829791608587340841)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-10755447515272650254749),(-10755447515272124737463)⟩,⟨(-2977659463635582997148),(-2977659463635057480358)⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-6237027612921202664562),(-6237027612920666188245)⟩,⟨2984903401614886544924,2984903401615423020805⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-605827049153691577902),(-605827049153253434559)⟩,⟨2953676251468395621123,2953676251468833764596⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨767961764428591064860,767961764428852970653⟩,⟨604555007484555532822,604555007484817438635⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨206376595744439311822,206376595744533460919⟩,⟨(-137917035580915657316),(-137917035580821508236)⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨(-18986514574547556641),(-18986514574522896026)⟩,⟨(-48468921571907169003),(-48468921571882508384)⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-9296024571948495620),(-9296024571943941283)⟩,⟨1848121055056696204,1848121055061250542⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨(-4539934198631727),(-4539934198011364)⟩,⟨1577153454478465181,1577153454479085544⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨244142559887461668,244142559887525719⟩,⟨70165852497337927,70165852497401977⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨26666625806201136,26666625806206428⟩,⟨(-32790901252254215),(-32790901252248924)⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-2447053930868428),(-2447053930867877)⟩,⟨(-7399530264685107),(-7399530264684555)⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-1524171614525153),(-1524171614525061)⟩,⟨(-738509062811134),(-738509062811040)⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-431630409742371),(-431630409742339)⟩,⟨47882662585502,47882662585532⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-85586847979589),(-85586847979569)⟩,⟨36283640601550,36283640601568⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨6819621984538470009255513,6819621984538472105007913⟩,⟨(-11172680736960917667238068),(-11172680736960915562965236)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨3096157123368787243526777,3096157123368793805257991⟩,⟨(-31593193806819181460927354),(-31593193806819174853372818)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-29673597954925055478998837),(-29673597954925045166171190)⟩,⟨(-22641878453937682093404431),(-22641878453937671694897617)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-39832846182062349787864941),(-39832846182062334464903196)⟩,⟨35424833725361059760086413,35424833725361075103132435⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨16135078424408905590217368,16135078424408936390138562⟩,⟨72458806486260182947945209,72458806486260213715331991⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨64406601068555175354080097,64406601068555214538010267⟩,⟨28339047035665041997196443,28339047035665081178701418⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨40136974829462581497366965,40136974829462615412537331⟩,⟨(-24714912144671433813147510),(-24714912144671399891402375)⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-279616788434430745399802),(-279616788434409121352609)⟩,⟨(-24124299871118781177379224),(-24124299871118759555438217)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-8998634033711919746726084),(-8998634033711908959760271)⟩,⟨(-4656159698500411043719543),(-4656159698500400256525439)⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-3021496632729521345407408),(-3021496632729516770425469)⟩,⟨2168733496000627202492702,2168733496000631777577374⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨163690449692049841294237,163690449692051838313232⟩,⟨1255639482266960781418854,1255639482266962778377129⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨385563725208977544361083,385563725208978689571124⟩,⟨176370154670637900780819,176370154670639046003839⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨131459319604081181023052,131459319604082017283692⟩,⟨(-66585730467412760199392),(-66585730467411923935435)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨19895586542447155839832,19895586542447735349758⟩,⟨(-50972674078123971712171),(-50972674078123392203822)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-2918119261986739645559),(-2918119261986448061826)⟩,⟨(-20558614307435075849346),(-20558614307434784266451)⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-2154485686479828352625),(-2154485686479720788455)⟩,⟨(-5025870213363430199441),(-5025870213363322635406)⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨8242688944585937506406884,8242688944585967930005490⟩,⟨3461383863899168174166934,3461383863899198619415505⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨1637495091953446408955314403,1637495091953446415554524018⟩,⟨1270023041737847901477229018,1270023041737847908098495990⟩⟩
end hm24_1_1_5
namespace hm24_1_1_6
noncomputable def s0_0 : CBox := ⟨⟨(-98),98⟩,⟨(-98),98⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-284),284⟩,⟨(-284),284⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-483),483⟩,⟨(-483),483⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-684),684⟩,⟨(-684),684⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-853),853⟩,⟨(-853),853⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-947),947⟩,⟨(-947),947⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-941),941⟩,⟨(-941),941⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-913),913⟩,⟨(-913),913⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-1120),1120⟩,⟨(-1120),1120⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-1254),1254⟩,⟨(-1254),1254⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-1238),1238⟩,⟨(-1238),1238⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-1083),1083⟩,⟨(-1083),1083⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-787),787⟩,⟨(-787),787⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-421),421⟩,⟨(-421),421⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-240),240⟩,⟨(-240),240⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-24),24⟩,⟨(-24),24⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-55),55⟩,⟨(-55),55⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-83),83⟩,⟨(-83),83⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-121),121⟩,⟨(-121),121⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-180),180⟩,⟨(-180),180⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-250),250⟩,⟨(-250),250⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-333),333⟩,⟨(-333),333⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-413),413⟩,⟨(-413),413⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-473),473⟩,⟨(-473),473⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-496),496⟩,⟨(-496),496⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-474),474⟩,⟨(-474),474⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-420),420⟩,⟨(-420),420⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-415),415⟩,⟨(-415),415⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-368),368⟩,⟨(-368),368⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-252),252⟩,⟨(-252),252⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-96),96⟩,⟨(-96),96⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨0,16⟩,⟨(-16),16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-5),18⟩,⟨(-16),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-16),28⟩,⟨(-30),16⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-31),32⟩,⟨(-39),28⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-52),48⟩,⟨(-52),46⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-66),66⟩,⟨(-66),66⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-93),93⟩,⟨(-93),93⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-96),96⟩,⟨(-96),96⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-108),108⟩,⟨(-108),108⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-102),102⟩,⟨(-102),102⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-119),119⟩,⟨(-119),119⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-104),104⟩,⟨(-104),104⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-82),82⟩,⟨(-82),82⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-54),54⟩,⟨(-54),54⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-24),24⟩,⟨(-24),24⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨45545832009181,45545832009197⟩,⟨38540051640067,38540051640085⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨102398437168599,102398437168624⟩,⟨49252074831505,49252074831529⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨76570577977190,76570577977215⟩,⟨(-4090821254431),(-4090821254406)⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨19773366092966,19773366092995⟩,⟨(-19948582561474),(-19948582561445)⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-1043790728104),(-1043790728069)⟩,⟨(-6159843752630),(-6159843752598)⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨(-868562203339),(-868562203303)⟩,⟨(-248075218432),(-248075218392)⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-50696688365),(-50696688321)⟩,⟨74237983200,74237983244⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨4299506520,4299506569⟩,⟨4908611386,4908611435⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨329183361,329183413⟩,⟨(-171520585),(-171520532)⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨(-3636747),(-3636688)⟩,⟨(-17823230),(-17823169)⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨(-852047),(-851988)⟩,⟨(-145378),(-145323)⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨(-28587),(-28535)⟩,⟨35474,35528⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨606,654⟩,⟨2969,3015⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨205,248⟩,⟨164,206⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨26,56⟩,⟨(-8),26⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨0,20⟩,⟨(-16),16⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨(-2601123478563431897574),(-2601123478563338171257)⟩,⟨2316403115390805682697,2316403115390899408936⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-4438003277130840967103),(-4438003277130570592943)⟩,⟨6644130168758595908079,6644130168758866282303⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-708908474879534311367),(-708908474879196465188)⟩,⟨7743255607968132653640,7743255607968470500343⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨2868852516531602641927,2868852516532005798519⟩,⟨3915379795447690207230,3915379795448093364035⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨2137244798525342509289,2137244798525642842676⟩,⟨15137953687012257677,15137953687312590936⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨311606918116600562491,311606918116788891156⟩,⟨(-627886472366341302604),(-627886472366152973933)⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨(-130397522542820321227),(-130397522542749292253)⟩,⟨(-124682173765455323216),(-124682173765384294235)⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨(-31567187339212470429),(-31567187339194510181)⟩,⟨21853177278688164322,21853177278706124564⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨3039786361294223806,3039786361297517757⟩,⟨6415397246283296137,6415397246286590092⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨1160349895693872379,1160349895694328046⟩,⟨(-305601922737864312),(-305601922737408647)⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨1128105397917662,1128105397966908⟩,⟨(-196220144808057379),(-196220144808008135)⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-30549339433914263),(-30549339433909679)⟩,⟨(-12771391704441609),(-12771391704437029)⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-5040944543894146),(-5040944543893732)⟩,⟨3577715257030751,3577715257031167⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-195325947003713),(-195325947003632)⟩,⟨1342633057186741,1342633057186822⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨143951903978263,143951903978291⟩,⟨319401392524326,319401392524356⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨49465702602231,49465702602249⟩,⟨56728045318254,56728045318272⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨(-6943581216048541312330493),(-6943581216048540009065060)⟩,⟨(-3753103395202719174123201),(-3753103395202717877507681)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-19165743747888602184747890),(-19165743747888598082147167)⟩,⟨(-824721731530994964914110),(-824721731530990893732281)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-12652311500162443674277882),(-12652311500162437177398124)⟩,⟨18791619436447946019613811,18791619436447952464934009⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨23201845915372999126704452,23201845915373008789570510⟩,⟨22876355771274701471454654,22876355771274711126310162⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨43834253072293129831763160,43834253072293149385010374⟩,⟨(-13183959904598933616232143),(-13183959904598914041808729)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨14307111850904695798055544,14307111850904720938416686⟩,⟨(-41432734532575775636412031),(-41432734532575750496165118)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-17836248996334231035683282),(-17836248996334209059977851)⟩,⟨(-23750985544050050397696869),(-23750985544050028425821459)⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-15292976709110849141737747),(-15292976709110835005068189)⟩,⟨1763282739149671582735354,1763282739149685720880453⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-2324954483095866596037815),(-2324954483095859486886592)⟩,⟨6123889071696079328768539,6123889071696086437677988⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨1658491375913489592987933,1658491375913492629721596⟩,⟨1785095063242561101088816,1785095063242564137786749⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨810604541984956765486553,810604541984958103832929⟩,⟨(-221490281747947090055884),(-221490281747945751671892)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨79191733505662868519447,79191733505663624775595⟩,⟨(-273506807086252502921917),(-273506807086251746676285)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-58489151179570207987984),(-58489151179569625545439)⟩,⟨(-81111396238587501234885),(-81111396238586918793546)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-36626991117990139656159),(-36626991117989769551974)⟩,⟨(-7780102218585120661042),(-7780102218584750555563)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-13617749752950925946513),(-13617749752950707807842)⟩,⟨4341670496678799988404,4341670496679018127514⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-3168076683485755422207),(-3168076683485676456523)⟩,⟨2053421206561965554809,2053421206562044520551⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨1593531956467936761833646,1593531956467956353221454⟩,⟨(-5360474504067593010165894),(-5360474504067573431974853)⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨713096834465267721752544993,713096834465267725946642747⟩,⟨(-1025251540436263231663290782),(-1025251540436263227481110440)⟩⟩
end hm24_1_1_6
namespace hm24_1_1_7
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
noncomputable def s2_0 : CBox := ⟨⟨(-16),10⟩,⟨(-16),1⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-17),16⟩,⟨(-16),15⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-32),16⟩,⟨(-21),20⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-42),28⟩,⟨(-32),42⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-56),56⟩,⟨(-54),56⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-65),65⟩,⟨(-65),65⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-108),108⟩,⟨(-108),108⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-107),107⟩,⟨(-107),107⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-90),90⟩,⟨(-90),90⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-28),28⟩,⟨(-28),28⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨15558789868494,15558789868511⟩,⟨(-38445165716998),(-38445165716980)⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨10076329181352,10076329181372⟩,⟨(-78571036597764),(-78571036597744)⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-19949846211485),(-19949846211457)⟩,⟨(-49925348751144),(-49925348751123)⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨(-17923457182475),(-17923457182448)⟩,⟨(-8556692260967),(-8556692260938)⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-3887928108305),(-3887928108276)⟩,⟨2199284175855,2199284175882⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨53840762104,53840762135⟩,⟨652315758301,652315758334⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨64510349262,64510349297⟩,⟨14633112175,14633112214⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨2160593946,2160593988⟩,⟨(-4379268027),(-4379267990)⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨(-219986496),(-219986457)⟩,⟨(-177644463),(-177644422)⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨(-11393040),(-11392998)⟩,⟨8321115,8321156⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨187614,187652⟩,⟨655849,655894⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨35704,35746⟩,⟨7704,7746⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨1904,1946⟩,⟨(-1596),(-1556)⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨26,65⟩,⟨(-256),(-217)⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-25),2⟩,⟨(-50),(-19)⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-16),3⟩,⟨(-18),0⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨1615502295386431238440,1615502295386487452648⟩,⟨1284843183297869674673,1284843183297925888879⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨4344316189604496819198,4344316189604652602252⟩,⟨1914237634081707647775,1914237634081863430676⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨4625896376361035384339,4625896376361229141929⟩,⟨(-405797783789637266677),(-405797783789443509464)⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨1996062695561827159667,1996062695562079005412⟩,⟨(-2132105368922359874361),(-2132105368922108028682)⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-242900332223550249935),(-242900332223370451268)⟩,⟨(-1275670782947453118830),(-1275670782947273320072)⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-417029889651203450056),(-417029889651090624735)⟩,⟨(-108445323845477228544),(-108445323845364403234)⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨(-58199990783077332443),(-58199990783031211745)⟩,⟨96156156747923139924,96156156747969260621⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨18036881711477605878,18036881711489234091⟩,⟨16241523688954012868,16241523688965641079⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨3518688052380527522,3518688052382605375⟩,⟨(-2896812567313020965),(-2896812567310943114)⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨(-387415174362634128),(-387415174362349363)⟩,⟨(-679853059938314447),(-679853059938029682)⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-125268961194735403),(-125268961194704114)⟩,⟨34451526570349220,34451526570380510⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-2422541604864059),(-2422541604860916)⟩,⟨22102064830640998,22102064830644140⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨3330924162981240,3330924162981546⟩,⟨2562315409820604,2562315409820909⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨919375875174075,919375875174132⟩,⟨(-150513537442616),(-150513537442557)⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨179486251201108,179486251201130⟩,⟨(-162699759561621),(-162699759561595)⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨26744637618674,26744637618691⟩,⟨(-44867314616835),(-44867314616816)⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨(-1748856998091169161621378),(-1748856998091168476306526)⟩,⟨3685662176407877937086176,3685662176407878626610296⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨116074267011469325653927,116074267011471483039321⟩,⟨9935949390427993448598229,9935949390427995624140511⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨10148391618384917522818928,10148391618384920962743850⟩,⟨5992022794792978631080741,5992022794792982097076002⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨11163041879680793707778912,11163041879680798896445883⟩,⟨(-12915234757003459534431396),(-12915234757003454343816313)⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-8640980573657748445427805),(-8640980573657737845028736)⟩,⟨(-22597340271259321045620639),(-22597340271259310456777191)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-22674527854688801765712477),(-22674527854688788039832737)⟩,⟨(-5800676747041421259978598),(-5800676747041407533174075)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-11886900336776129700146860),(-11886900336776117606343210)⟩,⟨10774176900323505511454237,10774176900323517607080967⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨1821143746297973758400269,1821143746297981596856419⟩,⟨8220247047714281253271219,8220247047714289090876702⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨3518702167528733114290285,3518702167528737078754507⟩,⟨891607206966086592745628,891607206966090557387912⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨877304272045934978051434,877304272045936678752281⟩,⟨(-1050018487745980898916657),(-1050018487745979198213333)⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-187831047820749621077193),(-187831047820748862782156)⟩,⟨(-439537967931287657815896),(-439537967931286899538972)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨(-162424397641188898362055),(-162424397641188470826594)⟩,⟨(-22000842074556214872890),(-22000842074555787330844)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-41324451582017716342425),(-41324451582017377112351)⟩,⟨40934529701962045781848,40934529701962385012012⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-1020205749726722995952),(-1020205749726515764399)⟩,⟨21939344934239648397055,21939344934239855627813⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨3866295055466297788569,3866295055466436109742⟩,⟨7494478565867086099906,7494478565867224420920⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨1515021726161886283532,1515021726161934447813⟩,⟨1642065426727214042500,1642065426727262206772⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-2946990317671368948349726),(-2946990317671358227652007)⟩,⟨(-542291199439438887744729),(-542291199439428160231379)⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-548014887696837046130983628),(-548014887696837043859276172)⟩,⟨(-340354037334453450866496082),(-340354037334453448589446415)⟩⟩
end hm24_1_1_7
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
open IntegerIntervals
namespace hm24_1_1_8
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
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨0,16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-16),16⟩,⟨(-15),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),22⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-28),31⟩,⟨(-28),32⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-42),42⟩,⟨(-42),42⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-60),60⟩,⟨(-60),60⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-73),73⟩,⟨(-73),73⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-107),107⟩,⟨(-107),107⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-95),95⟩,⟨(-95),95⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-75),75⟩,⟨(-75),75⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-51),51⟩,⟨(-51),51⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-23),23⟩,⟨(-23),23⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨(-25169964817924),(-25169964817906)⟩,⟨(-1684638331953),(-1684638331936)⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-47421553511895),(-47421553511876)⟩,⟨9278867463141,9278867463161⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-25079462043216),(-25079462043200)⟩,⟨21423725660268,21423725660286⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨(-1346664157539),(-1346664157518)⟩,⟨12214477503102,12214477503122⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨2120940762572,2120940762594⟩,⟨1819469504152,1819469504179⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨374942771908,374942771932⟩,⟨(-177865272651),(-177865272626)⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-6493833260),(-6493833232)⟩,⟨(-42092055595),(-42092055566)⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨(-3190758576),(-3190758547)⟩,⟨(-208235895),(-208235867)⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨(-49931326),(-49931298)⟩,⟨181732124,181732155⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨8353966,8354003⟩,⟨4677275,4677310⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨352212,352251⟩,⟨(-312885),(-312845)⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨(-6407),(-6369)⟩,⟨(-24866),(-24828)⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-1646),(-1609)⟩,⟨(-715),(-679)⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-183),(-148)⟩,⟨35,67⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-31),(-6)⟩,⟨5,30⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-16),16⟩,⟨0,16⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨513652848087650835976,513652848087679479038⟩,⟨(-939052025328956741039),(-939052025328928097956)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨589481992925898563611,589481992925974579931⟩,⟨(-2396678675967787474217),(-2396678675967711457755)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-638591278458735630417),(-638591278458632666251)⟩,⟨(-2341037159287732400347),(-2341037159287629435977)⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-1297532217655837018411),(-1297532217655704137238)⟩,⟨(-825188396290000131103),(-825188396289867249932)⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-640250927607544575940),(-640250927607448000362)⟩,⟨258264871352011737332,258264871352108312860⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-11149369044898549941),(-11149369044839421923)⟩,⟨231507433515213422790,231507433515272550819⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨58052543030589060053,58052543030614182755⟩,⟨19595427050369530807,19595427050394653507⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨6446642333221908397,6446642333228681686⟩,⟨(-11777179145603399993),(-11777179145596626706)⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-2060145239130287836),(-2060145239129087402)⟩,⟨(-1520202444633792867),(-1520202444632592433)⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨(-317910659753594081),(-317910659753434290)⟩,⟨313506304661815394,313506304661975185⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨38862170241790740,38862170241807974⟩,⟨64458837495136577,64458837495153811⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨12858505947242367,12858505947244143⟩,⟨(-2308738649062113),(-2308738649060336)⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨875559068366686,875559068366889⟩,⟨(-2341516806946982),(-2341516806946778)⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-253004223586258),(-253004223586218)⟩,⟨(-499281811574127),(-499281811574087)⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-127092480635912),(-127092480635889)⟩,⟨(-73015040321413),(-73015040321387)⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-30944261550841),(-30944261550822)⟩,⟨(-6964870262675),(-6964870262657)⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨1706037627824068697723443,1706037627824069015904024⟩,⟨702379769370672809630671,702379769370673125563558⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨4493673881743181008870093,4493673881743182014854721⟩,⟨(-298683137588148189763341),(-298683137588147192836848)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨2449379361313918287868523,2449379361313919899897926⟩,⟨(-4772913219483967758133895),(-4772913219483966157384064)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-6243434465796709575466085),(-6243434465796707147151868)⟩,⟨(-4718435535660775141036221),(-4718435535660772712582047)⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-10130847692363222133880242),(-10130847692363217144411634)⟩,⟨4748618493201993332484780,4748618493201998327345243⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-1832677996545788025655851),(-1832677996545781512975989)⟩,⟨10780154425305824537606041,10780154425305831049454665⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨5587791129522286954336189,5587791129522292730255436⟩,⟨5124992458705294130804145,5124992458705299906014206⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨3823117244549675993467903,3823117244549679755922183⟩,⟨(-1272361686416425019281985),(-1272361686416421256415219)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨234211973813936621708463,234211973813938531905875⟩,⟨(-1744430907843678894456715),(-1744430907843676984362141)⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-566066562152642174237325),(-566066562152641353955549)⟩,⟨(-362730873964292839698592),(-362730873964292019409572)⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-203930660106173422558481),(-203930660106173052051086)⟩,⟨122516588909635031928179,122516588909635402442026⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨1039002710308129198201,1039002710308340483658⟩,⟨82551093363036352814204,82551093363036564096378⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨23847346327198533807922,23847346327198702475882⟩,⟨17541812683403066804428,17541812683403235472641⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨11195974480230027775238,11195974480230133491433⟩,⟨(-1308843382240680200395),(-1308843382240574483834)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨3481766044304381219671,3481766044304455590766⟩,⟨(-2613588238809265586303),(-2613588238809191215180)⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨705213985635504388546,705213985635529350977⟩,⟨(-917113943152999398689),(-917113943152974436266)⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-107316511730569487656551),(-107316511730564384231630)⟩,⟨1399725703648379709389258,1399725703648384809768677⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-140764350254932247414737587),(-140764350254932246333053425)⟩,⟨255349988571557251794107270,255349988571557252873788267⟩⟩
end hm24_1_1_8
namespace hm24_1_1_9
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
noncomputable def s2_0 : CBox := ⟨⟨0,16⟩,⟨(-16),16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-5),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-16),16⟩,⟨(-18),16⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-30),26⟩,⟨(-32),26⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-34),34⟩,⟨(-34),34⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-62),62⟩,⟨(-62),62⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-51),51⟩,⟨(-51),51⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-62),62⟩,⟨(-62),62⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-45),45⟩,⟨(-45),45⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-23),23⟩,⟨(-23),23⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨3386066262978,3386066262995⟩,⟨13211791198625,13211791198641⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨12882019935154,12882019935171⟩,⟨22815014203173,22815014203189⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨15455204021648,15455204021667⟩,⟨9202411858178,9202411858196⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨6586741384159,6586741384176⟩,⟨(-1513142453276),(-1513142453259)⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨550391203001,550391203023⟩,⟨(-1453189704652),(-1453189704632)⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨(-168354050454),(-168354050434)⟩,⟨(-162345860254),(-162345860231)⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-21039847388),(-21039847364)⟩,⟨12305974420,12305974447⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨599594799,599594825⟩,⟨1761852662,1761852687⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨110518959,110518986⟩,⟨(-15921542),(-15921516)⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨466092,466122⟩,⟨(-5756523),(-5756494)⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨(-266741),(-266709)⟩,⟨(-111793),(-111763)⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨(-12088),(-12057)⟩,⟨10493,10525⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨69,101⟩,⟨1103,1131⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨64,93⟩,⟨65,92⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨5,27⟩,⟨(-9),18⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨0,16⟩,⟨(-16),16⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨(-466870248829722443751),(-466870248829709861547)⟩,⟨(-159486087591347011896),(-159486087591334429712)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-1137993497812808863120),(-1137993497812777091371)⟩,⟨(-76707280932317344922),(-76707280932285573260)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-1017304173139847198074),(-1017304173139795837983)⟩,⟨485296320034170980954,485296320034222340962⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-267213020131173506352),(-267213020131113280693)⟩,⟨668187882739471395758,668187882739531621431⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨178436532366294553788,178436532366342012040⟩,⟨273127967498986025214,273127967499033483486⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨109433497207931991167,109433497207959714423⟩,⟨(-17456921514891098453),(-17456921514863375208)⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨3163609808898417386,3163609808910393931⟩,⟨(-29519713524088676787),(-29519713524076700238)⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨(-6364925604831761591),(-6364925604828390704)⟩,⟨(-1751689294217451286),(-1751689294214080399)⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-485312653600125117),(-485312653599491805)⟩,⟨1182759660400629900,1182759660401263211⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨195175793553564008,195175793553649352⟩,⟨114848635720786996,114848635720872341⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨26535237284374113,26535237284382855⟩,⟨(-28252993009844785),(-28252993009836039)⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-3056626722418851),(-3056626722417972)⟩,⟨(-6100133561473771),(-6100133561472891)⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-1319460777799425),(-1319460777799308)⟩,⟨(-79179168980944),(-79179168980828)⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-213395030511712),(-213395030511680)⟩,⟨209329274372726,209329274372756⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-16317263383522),(-16317263383503)⟩,⟨77121943930858,77121943930875⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨1619881255366,1619881255383⟩,⟨17043826685442,17043826685458⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨245985510772524720296529,245985510772524849363984⟩,⟨(-699695234712171767323806),(-699695234712171637216939)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-219111436866546908001790),(-219111436866546499850103)⟩,⟨(-1801092157472332189626591),(-1801092157472331777502523)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-1986517304180655885458809),(-1986517304180655225573084)⟩,⟨(-875025121038390420238390),(-875025121038389756125595)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-1751833655874103956765997),(-1751833655874102951024233)⟩,⟨2664740308800084264736677,2664740308800085270001316⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨2251031123304034408054391,2251031123304036488775428⟩,⟨4010934294061141165205650,4010934294061143243737938⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨4524269178295669739148100,4524269178295672466787318⟩,⟨391500181798769056100917,391500181798771784245949⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨1927581624828250847663302,1927581624828253278672343⟩,⟨(-2535799956792320452716996),(-2535799956792318021489185)⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-706033323770226257924739),(-706033323770224668973744)⟩,⟨(-1561845304060585525624392),(-1561845304060583936844127)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-758477523891792393829681),(-758477523891791586334600)⟩,⟨(-14211606806229684164792),(-14211606806228876620344)⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-126055087581321579211990),(-126055087581321232986475)⟩,⟨265206278173418558278485,265206278173418904497466⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨66030442736939350273871,66030442736939508403971⟩,⟨81963241890960817009369,81963241890960975137979⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨36491574976175560214469,36491574976175652710796⟩,⟨(-5882319616741517198697),(-5882319616741424701053)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨6164185779164270318670,6164185779164342957765⟩,⟨(-11890293004016088595533),(-11890293004016015956681)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-1417322199872453885532),(-1417322199872404084954)⟩,⟨(-4943323707314037710040),(-4943323707313987909581)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-1449143025904625997934),(-1449143025904591467883)⟩,⟨(-1375231370676528636932),(-1375231370676494106870)⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-470983981448760618205),(-470983981448749449937)⟩,⟨(-248453071668007545500),(-248453071667996377220)⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨583930479821269979934604,583930479821272121750045⟩,⟨(-16086957154842763309424),(-16086957154840620299142)⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨105389283534995678498933793,105389283534995678955047081⟩,⟨51150138295590397052764585,51150138295590397509501090⟩⟩
end hm24_1_1_9
namespace hm24_1_1_11
noncomputable def s4_0 : CBox := ⟨⟨77177069043037317516,77177069043038943135⟩,⟨(-1043985334430088336),(-1043985334428462723)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨172357655236454186524,172357655236459180608⟩,⟨(-49643844374694637329),(-49643844374689643264)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨124406355317371884061,124406355317380965384⟩,⟨(-128801540465722098496),(-128801540465713017175)⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨968553269697023132,968553269705843414⟩,⟨(-116057923215647336393),(-116057923215638516106)⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-44233936221111150880),(-44233936221102779893)⟩,⟨(-30358386526354223392),(-30358386526345852407)⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-15695983041841022549),(-15695983041836310007)⟩,⟨10080295989530193381,10080295989534905923⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨1667557552208784202,1667557552210773697⟩,⟨4854443325711300770,4854443325713290265⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨1152715001339496676,1152715001340076240⟩,⟨(-228972177026919770),(-228972177026340209)⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-24232493268352254),(-24232493268236621)⟩,⟨(-233468628799640464),(-233468628799524827)⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨(-42895048922174764),(-42895048922157780)⟩,⟨(-462220548743352),(-462220548726368)⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-1545092229871125),(-1545092229869195)⟩,⟨7409433343457142,7409433343459071⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨1180710808275418,1180710808275616⟩,⟨695796611004527,695796611004724⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨233987489935379,233987489935412⟩,⟨(-138958131042491),(-138958131042456)⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨11330475197433,11330475197453⟩,⟨(-61750014482215),(-61750014482195)⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-6806717783694),(-6806717783677)⟩,⟨(-15348148510601),(-15348148510584)⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-2441376771925),(-2441376771908)⟩,⟨(-2744289784647),(-2744289784631)⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨(-20386069610830777168126),(-20386069610830761445599)⟩,⟨85871895257191455838128,85871895257191471715612⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨49530341749243659875269,49530341749243709828950⟩,⟨211114633621430350790748,211114633621430401276271⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨250281527585740960296724,250281527585741042017932⟩,⟨76445443649793005486825,76445443649793087616771⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨169730364421502247990821,169730364421502373366530⟩,⟨(-351061526189615686677662),(-351061526189615561461864)⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-349858380391180002827382),(-349858380391179741122729)⟩,⟨(-452968917374669162706605),(-452968917374668901249774)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-574986743836338021501526),(-574986743836337676023615)⟩,⟨44878003740114562762109,44878003740114908338050⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-185760433365061029600476),(-185760433365060720338141)⟩,⟨369924343758558893934940,369924343758559203204654⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨134777122912243740788453,134777122912243942772103⟩,⟨184385952567359712048504,184385952567359914013464⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨101475612610661671736953,101475612610661773682545⟩,⟨(-21714164667119712197847),(-21714164667119610245150)⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨7841609326695144388279,7841609326695187609752⟩,⟨(-40494908310213797895125),(-40494908310213754675249)⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-12361867192143710834796),(-12361867192143690976184)⟩,⟨(-8792658767086744676604),(-8792658767086724817807)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨(-4902402762836145610838),(-4902402762836132341837)⟩,⟨2394467798775357079944,2394467798775370349031⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-334265937927996013765),(-334265937927985869925)⟩,⟨1990649557522452515987,1990649557522462659763⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨448219269657232503894,448219269657241108401⟩,⟨648261222631132064020,648261222631140668525⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨282367922957451912825,282367922957457095206⟩,⟨127434026915954904683,127434026915960087072⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨82197455130482730900,82197455130484269027⟩,⟨12021435602455745960,12021435602457284090⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
end hm24_1_1_11
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock25_0
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
open IntegerIntervals
namespace hm25_0_0_2
noncomputable def s0_0 : CBox := ⟨⟨(-8165533602199418478870379330),(-8165533602199410038238563166)⟩,⟨(-15724984100915063004620670335),(-15724984100915054563612146092)⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-33841343715112034574078299231),(-33841343715112017354359484393)⟩,⟨(-37164911708067299909005233594),(-37164911708067282687513795388)⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-71065544391337932881988150062),(-71065544391337916461389775707)⟩,⟨(-23775224951352773767580378156),(-23775224951352757344673243369)⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-81356806656804853270685364473),(-81356806656804842345625678007)⟩,⟨35895712087573772110104887450,35895712087573783034158938053⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-19900764009260380929720144192),(-19900764009260377015170218399)⟩,⟨89607818507555074612795649226,89607818507555078525147693773⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨65415067465955589970692730311,65415067465955591295447097847⟩,⟨54238081608299637126158643418,54238081608299638452783039684⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨61721885775415263339224820608,61721885775415263785646346555⟩,⟨(-35614550713316613244356899956),(-35614550713316612798427469985)⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-12982252288903578907157575781),(-12982252288903578738603049021)⟩,⟨(-52605545103683589901374120591),(-52605545103683589733074897728)⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-37140994800529931526126268975),(-37140994800529931461177853364)⟩,⟨(-501776346976188734248144835),(-501776346976188668996741404)⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-6534247831122294189131586806),(-6534247831122294165779443691)⟩,⟨21675053000129346191033306766,21675053000129346214296814803⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨9548872436329682917309193710,9548872436329682925092568172⟩,⟨7192898863243532178717729491,7192898863243532186471445580⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨4706903811726650192141120999,4706903811726650194629328122⟩,⟨(-2281275362217415602752724564),(-2281275362217415600311736163)⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨325133059819901214285018917,325133059819901214875455169⟩,⟨(-1720381723651058089758948557),(-1720381723651058089082800196)⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-199841895789294802951547378),(-199841895789294802796124827)⟩,⟨(-328440732892157052626556213),(-328440732892157052459777541)⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-34116067811144744707235149),(-34116067811144744681174597)⟩,⟨(-19203253775879519897554223),(-19203253775879519879266499)⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-628558655157985032097107),(-628558655157985030678458)⟩,⟨(-140506743556556415068312),(-140506743556556414655899)⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨22304298481887062679008431638,22304298481887106801930977397⟩,⟨(-56485289675677992823040061052),(-56485289675677948701405227858)⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨21501215646651854298710970008,21501215646652019139081662630⟩,⟨(-174459889230451432442307841352),(-174459889230451267601051672831)⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-99766761618567969931953842828),(-99766761618567630493792771378)⟩,⟨(-253765298507461996960527178748),(-253765298507461657507917170566)⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-305284194515974338470903056599),(-305284194515973490389927290100)⟩,⟨(-156689338126862493208440560670),(-156689338126861645116045315201)⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-346120678714330161398689761615),(-346120678714328541099318040893)⟩,⟨165254958298601791304404152345,165254958298603411585237621231⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-16774855109843239943783307530),(-16774855109839935346032734366)⟩,⟨394616682517095997028204097454,394616682517099301628153568598⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨350838346336186910437773380873,350838346336191740721855941636⟩,⟨151708000120779979495548883344,151708000120784809791005305404⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨226110448952728484507359651322,226110448952733915845570283313⟩,⟨(-269567974117229718549126966298),(-269567974117224287225602852947)⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-177491966486470669101429815019),(-177491966486465797659294870087)⟩,⟨(-254411550150854846596464420587),(-254411550150849975142316113699)⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-249363440334904872515356620953),(-249363440334901385535677907182)⟩,⟨82951382579512592760152839967,82951382579516079733719021579⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-8582187402947570071938435635),(-8582187402945653587465637782)⟩,⟨213768668573129774552409610184,213768668573131691035427585214⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨144730539330610658447266626032,144730539330611427348848210000⟩,⟨82945817411360655639935072196,82945817411361424547598715938⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨113174244088123058302566553507,113174244088123398384926659327⟩,⟨(-49101514423080431420564131232),(-49101514423080091340900035680)⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨35038756812072362127663653363,35038756812072479244151712293⟩,⟨(-76579113398364921779911234958),(-76579113398364804666338744396)⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-3719400065390953876984899348),(-3719400065390902462334646357)⟩,⟨(-48695800880975954341706483429),(-48695800880975902927203229485)⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-5240032580687880601781271537),(-5240032580687867607480921718)⟩,⟨(-15096551777934923004597026957),(-15096551777934910010084986365)⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨97727978032814353428529343731,97727978032814353469213327397⟩,⟨(-4571339097356717080096343029),(-4571339097356717050148333596)⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨272257070125739823882053728188,272257070125739824018437820088⟩,⟨(-86918513396329308673400720909),(-86918513396329308558800679274)⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨307435571064815216971049513123,307435571064815217228085886090⟩,⟨(-331669596487969954882009506689),(-331669596487969954624090403386)⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨1353014887132154608309256161,1353014887132155000958080506⟩,⟨(-588176581834457572699662923730),(-588176581834457572253400429273)⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-557575515615244377476772054705),(-557575515615244376710967365730)⟩,⟨(-405039302118689404765651807379),(-405039302118689404005534720969)⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-668994957864848902276832281282),(-668994957864848900869083906300)⟩,⟨346228762158144094327229993303,346228762158144095687307384095⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨101831175673975232158819911359,101831175673975234750677481077⟩,⟨773858941350344430708072807533,773858941350344433355058587899⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨765747855422440468502015084711,765747855422440473419692444867⟩,⟨110494001033237838728988596868,110494001033237843609106209036⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨282611890264745029036456017486,282611890264745037992872946165⟩,⟨(-681455714416459855198648518261),(-681455714416459846232541057643)⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-532522051891732360993172117575),(-532522051891732343508055347310)⟩,⟨(-420437464418214881439181489778),(-420437464418214863935847691470)⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-511912711940947879392323489842),(-511912711940947839997556260693)⟩,⟨315623557361037161041879653904,315623557361037200403780586712⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨40914993958782002053606481372,40914993958782094543132105677⟩,⟨509099428801112634311495931648,509099428801112726824132844459⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨347220950152586828991533735588,347220950152587041865804298602⟩,⟨216660543466155563548951674467,216660543466155776432071012137⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨294453696695377907215073550974,294453696695378188902590341596⟩,⟨(-51451425643253368473338661896),(-51451425643253086799980254631)⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨142039501673200023644474594324,142039501673200292739044273994⟩,⟨(-113703393828563768876931992713),(-113703393828563499791854023920)⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨36471769675668896914956379853,36471769675669022847024181384⟩,⟨(-48957365191894599494265293900),(-48957365191894473564053907140)⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨68558249892805540491009226067,68558249892805761060774113594⟩,⟨72322137673217220963996314773,72322137673217441526057941490⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨249209704226066379882675882073,249209704226066841964960072294⟩,⟨154555335725965169137195630687,154555335725965631181106024524⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨469350151657719029177500275849,469350151657719495769271797332⟩,⟨24311167984302301891949698444,24311167984302768429148885000⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨483255415760615587671997530491,483255415760615926392772795726⟩,⟨(-388993327387213210168021814460),(-388993327387212871418788487886)⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-25460926200027297229159514294),(-25460926200027153634133170397)⟩,⟨(-736759445515703662558712347423),(-736759445515703518891301067701)⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨(-737542645575598814837209383142),(-737542645575598753134215372548)⟩,⟨(-351779058425130578030573481657),(-351779058425130516412482638683)⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-619379921949880253677013563762),(-619379921949880225475983353193)⟩,⟨598738304307194937716072305104,598738304307194965953742946075⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨407784788959306307044238713357,407784788959306321531457442289⟩,⟨772640845830868899230696111229,772640845830868913740370547484⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨834619917528682140792915768982,834619917528682148515653198027⟩,⟨(-191820619245879468195455587851),(-191820619245879460536139380378)⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨50321395565493818263663872670,50321395565493822183019827438⟩,⟨(-809424078377812257226115932173),(-809424078377812253229722711073)⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨(-672090760993392770937080506988),(-672090760993392768901686115658)⟩,⟨(-306073123553749330795857786451),(-306073123553749328816622263326)⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨(-507908706940899334111165643419),(-507908706940899333057237020737)⟩,⟨390913921384532951701260144194,390913921384532952747556645547⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨3129317868136168242807826752,3129317868136168765776826373⟩,⟨521702023295146178029454379263,521702023295146178605635092655⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨256813802791372264786330891221,256813802791372265097555743096⟩,⟨287157468240645037727870518877,287157468240645038040428211736⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨222527466492086537463564649081,222527466492086537617255763540⟩,⟨79314744106492449165142629484,79314744106492449299684070740⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨79270284653724263762650259665,79270284653724263806628494454⟩,⟨6997298548867055634771681209,6997298548867055669408327743⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨(-77361354003838163689401817161),(-77361354003837141019314436420)⟩,⟨57882776466511245193968994720,57882776466512267868332796768⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-171647451494525795027445314115),(-171647451494521889557217869121)⟩,⟨223237476102924746231938136526,223237476102928651698886394322⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-52626457696795204173365779615),(-52626457696786897898326751881)⟩,⟨441182864045838337663438862468,441182864045846643886815962164⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨355212253921870258435029728604,355212253921892204727570544498⟩,⟨456040034906707996235779310915,456040034906729942486240335233⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨680911404176462068626524745589,680911404176506437334240888926⟩,⟨(-56188138847971478704609347065),(-56188138847927109920749206070)⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨246535824403170144231096580289,246535824403267199364396057589⟩,⟨(-721265442341994533649670826593),(-721265442341897478528648380242)⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨(-663483300334505478447878130744),(-663483300334352237778197617136)⟩,⟨(-474495558774637252365531621025),(-474495558774484011750751065643)⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨(-628453067474627666632843702416),(-628453067474440601926051468016)⟩,⟨562503326178684104877695952702,562503326178871169667892379613⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨428799181655748526960103099946,428799181655931919351404460781⟩,⟨728917483944941008504926118208,728917483945124400814635346400⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨785072246585949196025216140110,785072246586093635639896434875⟩,⟨(-246333493484939262951942689435),(-246333493484794823286036577933)⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨2938173791314331966616467886,2938173791402324785278433447⟩,⟨(-774667696231800616982457063253),(-774667696231712624152303759776)⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-632694525885436296563660091983),(-632694525885397408040187492999)⟩,⟨(-298945233114014062510758550972),(-298945233113975174053906579945)⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-516868247786865330005267504898),(-516868247786846608039566238079)⟩,⟨293541080758944713293862853628,293541080758963435294869853732⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-138081390443879219917997860556),(-138081390443872288808109821035)⟩,⟨434428588090643640094074967275,434428588090650571246400552255⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨57833698613906177438566699926,57833698613909386830551070260⟩,⟨281324759437994028677643304895,281324759437997238072267016073⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨43705264334812003673889460337,43705264334812836791117819717⟩,⟨87816650972040249842728831985,87816650972041082956562490530⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨(-2801910469337543423131547267),(-2801910469337543400068501965)⟩,⟨(-37086599087359476599690464719),(-37086599087359476572639955682)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-39879358159926313440757876807),(-39879358159926313351284081551)⟩,⟨(-101508859716879954303907251763),(-101508859716879954206344556235)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-143730048705031164971403675780),(-143730048705031164763154550881)⟩,⟨(-101118244754334292255974575332),(-101118244754334292047987800006)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-233480427134873877691346415880),(-233480427134873877299325237436)⟩,⟨51768769789182589900483927345,51768769789182590274308779052⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-96897634593951549374777243853),(-96897634593951548589657496394)⟩,⟨284690430909456477871480419968,284690430909456478658357318531⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨264736255511062789894585057636,264736255511062791498429949985⟩,⟨236972490496421795725090655957,236972490496421797342934332554⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨337546990915146623644071717335,337546990915146627025463817219⟩,⟨(-206396406594629016746737783392),(-206396406594629013379791157969)⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-136848076122072013844822058493),(-136848076122072006870049011917)⟩,⟨(-396924651499343262408607649004),(-396924651499343255425818102891)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-425764402467507725553609589450),(-425764402467507710462534612757)⟩,⟨61624177053757514077933225040,61624177053757529167995102993⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-30340365336521949039185516117),(-30340365336521907573402953837)⟩,⟨427639919313669267418173343722,427639919313669308881622231827⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨386943798863268190972776452388,386943798863268327161247313061⟩,⟨149592368277463772587725198694,149592368277463908776873096165⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨277405191488373434851180329807,277405191488373841778824511831⟩,⟨(-266818327746978489594331562657),(-266818327746978082665090301483)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-48954125517234428118331047904),(-48954125517233346120480303791)⟩,⟨(-329968870596154356812351256862),(-329968870596153274813512611446)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-200279093371542401551885708103),(-200279093371540877709487363536)⟩,⟨(-163694540026358937270284590113),(-163694540026357413430594661389)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-160992146831787294888883853233),(-160992146831785774799633941122)⟩,⟨(-29495775802616829636906787984),(-29495775802615309549876132498)⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-55802195685893373783957339769),(-55802195685892645532310241990)⟩,⟨4171289742973281432502566044,4171289742974009683658662129⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-5996234942248543189009860749),(-5996234942075575908052993610)⟩,⟨2846849828587463105488529970,2846849828760430376429489782⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-22919455250350083871355805330),(-22919455250350083594864437100)⟩,⟨3819909208391680482467038571,3819909208391680759040882075⟩⟩
end hm25_0_0_2
namespace hm25_0_0_3
noncomputable def s0_0 : CBox := ⟨⟨2731555445592569067698461104,2731555445592570534076352347⟩,⟨(-1418053352207553083088323885),(-1418053352207551616774875252)⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨6338297288183614603935886920,6338297288183617542508218018⟩,⟨(-5760506955536336203589615476),(-5760506955536333265313761418)⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨3927671260585116313720697745,3927671260585119008890315896⟩,⟨(-11639167606478044350016884371),(-11639167606478041655219394209)⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-5483652650589163515126930226),(-5483652650589161817442106628)⟩,⟨(-12599401489262885354504616863),(-12599401489262883656673198606)⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-12751782335078798042277045019),(-12751782335078797481204019330)⟩,⟨(-2940392151722931854092569136),(-2940392151722931292715122784)⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-7067963442257286753816466034),(-7067963442257286581378422802)⟩,⟨8324635937470004117557302503,8324635937470004289774488948⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨3911268788932846865059441879,3911268788932846915944677156⟩,⟨7030519487431183738071030046,7030519487431183788999966334⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨5091118799137122541838383186,5091118799137122558213091849⟩,⟨(-1149773347209800813511647248),(-1149773347209800797113571264)⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨110561509027819679878740303,110561509027819685124420661⟩,⟨(-2948036266840602084950539348),(-2948036266840602079719752916)⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-1349987643179871978912731763),(-1349987643179871977415614396)⟩,⟨(-448285383019911484650735401),(-448285383019911483157370548)⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-353289848291631082043742118),(-353289848291631081665899041)⟩,⟨439914590514852386502013152,439914590514852386885345296⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨70309502477200200898569583,70309502477200200983939522⟩,⟨158256135155117773438546651,158256135155117773526329604⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨36065396078633270725756497,36065396078633270741939350⟩,⟨8084319186496970317812249,8084319186496970331017306⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨3897865702755959761818834,3897865702755959764119533⟩,⟨(-2208353939344068739570916),(-2208353939344068737469816)⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨100573035242332580562902,100573035242332580676338⟩,⟨(-169773631956606043440450),(-169773631956606043272692)⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨180929207009033731422,180929207009033732093⟩,⟨(-786010358525861685006),(-786010358525861682649)⟩⟩
noncomputable def s1_0 : CBox := ⟨⟨19669477324929658143451918694,19669477324929673507108341069⟩,⟨7768031393963699250848774179,7768031393963714614958439711⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨60171115955722332792054090973,60171115955722389627048048578⟩,⟨7443562862415975238569936952,7443562862416032073258071716⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨85921520498929662212417068485,85921520498929777049889567903⟩,⟨(-33657870813048755617713353276),(-33657870813048640785172105260)⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨51780808728203714507449200637,51780808728203992870624782209⟩,⟨(-100317649629927442697874975178),(-100317649629927164338519957236)⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-51992358255041459528221710499),(-51992358255040946545277293044)⟩,⟨(-109903415537441081781155240609),(-109903415537440568792300706441)⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-119492630425638617824648389101),(-119492630425637618737683559698)⟩,⟨(-5665552366682059374672293926),(-5665552366681060288322118119)⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-44181925671237422839121639486),(-44181925671236040158529917748)⟩,⟨100485489759508959332438006209,100485489759510342009682049179⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨72488254987755659535228500065,72488254987757126568539136918⟩,⟨61675584168312077602237189028,61675584168313544639560986836⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨64827593468908816644542073117,64827593468910053163690064039⟩,⟨(-44508340623257460932968327205),(-44508340623256224416854043417)⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-19204590761117910262851582008),(-19204590761117081660487068166)⟩,⟨(-59191450125744169626780480001),(-59191450125743341023006930558)⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-47238496321748054153252577806),(-47238496321747629629344647913)⟩,⟨(-2214122169991502995293335521),(-2214122169991078471040336842)⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-17321580142188421133445768130),(-17321580142188261807401344703)⟩,⟨29843301860603887479888219105,29843301860604046804685004574⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨9477211766050970474234937248,9477211766051036963603205703⟩,⟨22080061665247360338830109714,22080061665247426828704931487⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨14172730087549044655830579029,14172730087549066366300917763⟩,⟨6523514414135242207573442314,6523514414135263918569567103⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨8703193557370822518796529245,8703193557370831714156672170⟩,⟨(-657000731624952343136110669),(-657000731624943147750242013)⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨2647614986961577907181618887,2647614986961580186355053142⟩,⟨(-918687143489043824390320198),(-918687143489041545252534433)⟩⟩
noncomputable def s2_0 : CBox := ⟨⟨2387927390925669500532656905,2387927390925669516200533112⟩,⟨51088587659508430307665104612,51088587659508430329095822271⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨45105273028738891569986065526,45105273028738891629648383924⟩,⟨141436836487742953346819231664,141436836487742953418111787161⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨169993900087503837873447486540,169993900087503838006253416218⟩,⟨157837670555429934740370776221,157837670555429934872740337810⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨296138567188989353663163978726,296138567188989353888767605985⟩,⟨1139614457894431906678781624,1139614457894432104548650941⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨199706155466342721031616733979,199706155466342721405783815011⟩,⟨(-273556167463185269258608182825),(-273556167463185268881687693256)⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-164250750075510630992585860000),(-164250750075510630343806973459)⟩,⟨(-319844378263915298834610331262),(-319844378263915298162283387794)⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-357395245448337236610172091772),(-357395245448337235388987912778)⟩,⟨45628940893364498710154557089,45628940893364499905132794979⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-50634318731376239811119806163),(-50634318731376237643129480857)⟩,⟨340480306630714199093339804021,340480306630714201278435998168⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨291048946804296699593244183869,291048946804296703422829116169⟩,⟨122239237442249578448683468899,122239237442249582274152730562⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨173827006123246043270809945380,173827006123246050448518239293⟩,⟨(-218225378896626669219575818330),(-218225378896626662049763807808)⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-124047721875064587541557467163),(-124047721875064572033353027091)⟩,⟨(-202912890809676037390357493377),(-202912890809676021868618824712)⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-194159089996371364025220784853),(-194159089996371328829942549522)⟩,⟨15017560278278814661826774415,15017560278278849847990802151⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-80263085952657295454897974499),(-80263085952657217041534019267)⟩,⟨128038951863075754411013549993,128038951863075832820950386003⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨18386827080746586553225663638,18386827080746687833242349360⟩,⟨105953422439559079862605815188,105953422439559181147918696461⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨40141191963514725067722281095,40141191963514820053717204522⟩,⟨50190685510711882324873965932,50190685510711977314365485447⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨17129713914484469630152333513,17129713914484513691079341328⟩,⟨12762480813824606036914688973,12762480813824650098518776002⟩⟩
noncomputable def s3_0 : CBox := ⟨⟨(-50431078532243912827495648524),(-50431078532243759025746662279)⟩,⟨47804003819018722516024698158,47804003819018876323204232469⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-107296973227237443163449144869),(-107296973227237122406046474021)⟩,⟨172920595610780349624861829769,172920595610780670409190899027⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-16909906178082185624956429833),(-16909906178081864803894686372)⟩,⟨322649783768200844272162295699,322649783768201165131234027660⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨263371611346578368149876621871,263371611346578598125097552770⟩,⟨327947368028366300560525946547,327947368028366530516291770893⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨490693259192025658912096558620,490693259192025754711634880136⟩,⟨(-16117199680241514232521731366),(-16117199680241418482035957717)⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨230399932655213218785147780656,230399932655213259033090636232⟩,⟨(-480226380734054864053140559834),(-480226380734054823749043758002)⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-379767106470316455996834737532),(-379767106470316438003092822250)⟩,⟨(-395046798471397167661314800814),(-395046798471397149691037140372)⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨(-479359505677664976129655836636),(-479359505677664967127850695404)⟩,⟨251109204485356936349569478371,251109204485356945336857181741⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨113958928739937424246100700131,113958928739937428867409405014⟩,⟨503127639639714117144400872873,503127639639714121805080615265⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨473980663783056642162885114918,473980663783056644508873213801⟩,⟨30891867019058095974685191253,30891867019058098274256561595⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨175442802346195115392834302445,175442802346195116523348972339⟩,⟨(-382609487195525582747202762159),(-382609487195525581583812708536)⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨(-216694995205871038891355778836),(-216694995205871038308127038024)⟩,⟨(-282735291941793663832958793095),(-282735291941793663245229930507)⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-283678276495543095161354009345),(-283678276495543094846442802409)⟩,⟨1307165601113807888633911400,1307165601113808173522190392⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-153530278123509694696199240145),(-153530278123509694528332574887)⟩,⟨137092228718534528891474389918,137092228718534529058578964572⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-41894185497268002522108863849),(-41894185497268002450860844444)⟩,⟨117429007322913273150209526361,117429007322913273231974601533⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-3671047195788449458526719370),(-3671047195788449440341496785)⟩,⟨41572095398707847222731702993,41572095398707847246020523123⟩⟩
noncomputable def s4_0 : CBox := ⟨⟨(-50462364461147496036776946394),(-50462364461146604461859580561)⟩,⟨(-67446924549406628418606088643),(-67446924549405736847346548737)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-193855508189082980682406723158),(-193855508189079589284185214194)⟩,⟨(-149115684215794440676218901139),(-149115684215791049275208562681)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-380277902901031815919819533760),(-380277902901024656977294241026)⟩,⟨(-45562299030929579800680203459),(-45562299030922420814430065172)⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-389086872430361865639804274162),(-389086872430343172485612718838)⟩,⟨302462789190406494214313783330,302462789190425187403879855500⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨46397955059572869705362073907,46397955059610145270818347502⟩,⟨572378904748633069687201446185,572378904748670345189656035257⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨595623674143371764231811750064,595623674143451916902601005308⟩,⟨204864732116624299928383477755,204864732116704452608981540307⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨385864747516875148532610775211,385864747516999234361981580228⟩,⟨(-536944340109104733510756500905),(-536944340108980647637084462899)⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨(-445315396247032789811281623022),(-445315396246884340639368080811)⟩,⟨(-500063184537725448982179019340),(-500063184537576999876102673971)⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-567139038977689970137244520278),(-567139038977547421733455893539)⟩,⟨331667236661008157977113666983,331667236661150706443941918792⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨576689958735558597477367586313,576689958735624151440278401902⟩,⟨3390907460773263909550627324,3390907460838817863695228762⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨219061742237089292228856185953,219061742237117708075735013525⟩,⟨(-461692083376545652533591322059),(-461692083376517236637684094009)⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-210429039637938779073315042606),(-210429039637925317082057845911)⟩,⟨(-371468976471592314274502297270),(-371468976471578852308779131646)⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-307861657723677635112290908525),(-307861657723672721393672133989)⟩,⟨(-98057041037315915397658028011),(-98057041037311001709499088323)⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-197579740177156526529059730565),(-197579740177154272155877105036)⟩,⟨40570683960462927331808216075,40570683960465181703106258440⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-61381850666240168112844714393),(-61381850666239585774317408474)⟩,⟨30547005399766474779531148568,30547005399767057120465017076⟩⟩
noncomputable def ans : CBox := ⟨⟨(-7646305692486548789305763621),(-7646305692352920645062074282)⟩,⟨(-6848400967192386790701306360),(-6848400967058758638056510636)⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-18929147600076571225011273738),(-18929147600076570991790530890)⟩,⟨(-25644013782660850817536063950),(-25644013782660850583921282414)⟩⟩
end hm25_0_0_3
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock25_1
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
open IntegerIntervals
namespace hm25_0_0_10
noncomputable def s0_0 : CBox := ⟨⟨(-24433107534994061718),(-24433107534994036380)⟩,⟨(-47149729548242057662),(-47149729548242032318)⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-86423848458472802237),(-86423848458472757384)⟩,⟨(-96366110559655458803),(-96366110559655413946)⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-133784484804928984024),(-133784484804928952597)⟩,⟨(-47866061180386190144),(-47866061180386158712)⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-98395804989390380783),(-98395804989390367190)⟩,⟨38818312436957180613,38818312436957194209⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-16101763400896711436),(-16101763400896708837)⟩,⟨55554417024303551363,55554417024303553958⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨16754661118198865051,16754661118198865473⟩,⟨16677637397537623654,16677637397537624071⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨6583859798810093234,6583859798810093301⟩,⟨(-2810060721232589824),(-2810060721232589757)⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-145593538360639875),(-145593538360639852)⟩,⟨(-1558560110199384098),(-1558560110199384074)⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-232572564544600084),(-232572564544600063)⟩,⟨(-44330433799581947),(-44330433799581923)⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-10854986329893598),(-10854986329893578)⟩,⟨20455324695975996,20455324695976015⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨869424623604522,869424623604540⟩,⟨993078024476830,993078024476847⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨36033811059470,36033811059490⟩,⟨(-9104903005149),(-9104903005130)⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨141642711072,141642711089⟩,⟨(-364791669495),(-364791669478)⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-360146449),(-360146433)⟩,⟨(-840115104),(-840115087)⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-121565),(-121548)⟩,⟨(-81834),(-81818)⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),0⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨17459342831183428779545,17459342831183463267683⟩,⟨(-44162669453502702768326),(-44162669453502668281278)⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨16042956735872346719117,16042956735872465817890⟩,⟨(-126380632860278603828763),(-126380632860278484729349)⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-60601725608834329342739),(-60601725608834118480223)⟩,⟨(-158704001472149556617639),(-158704001472149345745520)⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-150448692731604635709257),(-150448692731604221645744)⟩,⟨(-80744696878860770743057),(-80744696878860356673074)⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-129828851327643581673630),(-129828851327642987723653)⟩,⟨57510022774936408086957,57510022774937002029778⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-8277213858375575228264),(-8277213858374736519794)⟩,⟨101419959353994031500285,101419959353994870208950⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨57859602433368296390553,57859602433369089478476⟩,⟨28425921127571747619899,28425921127572540710132⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨25212961752508825215538,25212961752509387079456⟩,⟨(-26863750712527520571340),(-26863750712526958709080)⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-10107033694394587582415),(-10107033694394280738636)⟩,⟨(-16494753032365198253198),(-16494753032364891408694)⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-9180444898974652385243),(-9180444898974522889753)⟩,⟨2466859581378374454969,2466859581378503950286⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-415470472529597011838),(-415470472529556436268)⟩,⟨4440817851870511787727,4440817851870552363250⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨1725900002362167292016,1725900002362176832944⟩,⟨1091524983772200579296,1091524983772210120296⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨864933574961740065841,864933574961742708567⟩,⟨(-343737828850275745802),(-343737828850273103093)⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨183561033377389286997,183561033377389880251⟩,⟨(-382803624929481266147),(-382803624929480672907)⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-12721653506006251816),(-12721653506006056834)⟩,⟨(-183653614225961100682),(-183653614225960905702)⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-16917307769250065862),(-16917307769250023752)⟩,⟨(-48867830401193089697),(-48867830401193047586)⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨1971088455990631610067659,1971088455990631610938433⟩,⟨(-91644252955426126294900),(-91644252955426125687117)⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨5223657504563955910035053,5223657504563955912782199⟩,⟨(-1653293421394704029548308),(-1653293421394704027312031)⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨5368816559533946785784959,5368816559533946790384450⟩,⟨(-5714836344732373550963931),(-5714836344732373546355171)⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨129027014485078197685114,129027014485078203597348⟩,⟨(-8792250058265052553767496),(-8792250058265052546878841)⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-6778875901916510070285293),(-6778875901916510060735310)⟩,⟨(-5122178152739685384874720),(-5122178152739685375381606)⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-6617684057483682958572015),(-6617684057483682944760201)⟩,⟨3215710349879214398040271,3215710349879214411252634⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨583167661893586352554669,583167661893586371747511⟩,⟨5807450963267110254828291,5807450963267110274530331⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨4243850308811051464387559,4243850308811051491499008⟩,⟨762693954880488081591499,762693954880488108457758⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨1252153586855678952700746,1252153586855678988707749⟩,⟨(-2737636786245413843091448),(-2737636786245413807050511)⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-1536430929465919591478769),(-1536430929465919540758993)⟩,⟨(-1301292091896301410030905),(-1301292091896301359231682)⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-1131504680064564552277405),(-1131504680064564469265595)⟩,⟨651234175310960484132151,651234175310960567048597⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨46503793143756789803359,46503793143756936953821⟩,⟨826129083976340008858323,826129083976340156056040⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨430099960435888747712485,430099960435889009028912⟩,⟨278360728341722648962446,278360728341722910294519⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨299596727817165752816130,299596727817166037743661⟩,⟨(-49484640171330454671264),(-49484640171330169762625)⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨124897694171403903937587,124897694171404138632001⟩,⟨(-99252285360121779251527),(-99252285360121544568305)⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨29651245687678770876889,29651245687678873156299⟩,⟨(-39768085236654916974237),(-39768085236654814696847)⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨13852843170585156558132081,13852843170585201147755731⟩,⟨14619417609772871306809657,14619417609772915894739479⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨48429203109633877986014887,48429203109633968134272606⟩,⟨30157717330569484968555290,30157717330569575108685276⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨84673278688598834647028203,84673278688598919044230241⟩,⟨4800429815522838679469619,4800429815522923065780778⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨78645634385004132979797683,78645634385004188281481693⟩,⟨(-62147521679451934420090599),(-62147521679451879113521874)⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-2154847734917647064032791),(-2154847734917626751033121)⟩,⟨(-103233701368444397990043622),(-103233701368444377665460145)⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨(-86257960081507216847440287),(-86257960081507209444505810)⟩,⟨(-43095998985903252935120260),(-43095998985903245543353909)⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-61413314797369414170526908),(-61413314797369411394242899)⟩,⟨56787933633685201880305362,56787933633685204660286700⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨30509177894571322152061971,30509177894571323303109831⟩,⟨61427565538981727402430518,61427565538981728555908610⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨52721809244847078208155957,52721809244847078700429216⟩,⟨(-10721707735561288931188827),(-10721707735561288443905061)⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨3495007577523004463841410,3495007577523004663212117⟩,⟨(-40535456449616166773089534),(-40535456449616166568964625)⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨(-26850323061501166840461978),(-26850323061501166756500345)⟩,⟨(-12906763733060620436283397),(-12906763733060620355057842)⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨(-16954875366102168241336918),(-16954875366102168205651342)⟩,⟨12616356325882641743265889,12616356325882641778562307⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-73833062143056383203678),(-73833062143056368526595)⟩,⟨14430475260041702388808538,14430475260041702405401537⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨6126750143559993582599682,6126750143559993590370792⟩,⟨6936950604697830009319269,6936950604697830017143176⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨4839980224271599680425211,4839980224271599683986124⟩,⟨1738078761870273277011879,1738078761870273280021009⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨1640173027761436096809438,1640173027761436097790455⟩,⟨145228653873559254634985,145228653873559255358171⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨(-93383358448386219373670002),(-93383358448384985302180069)⟩,⟨69845107062066099249528283,69845107062067333325398519⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-201369677925345706897063646),(-201369677925341140333691843)⟩,⟨261050781614314734004205878,261050781614319300564363153⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-60049857917550006523842004),(-60049857917540859235015953)⟩,⟨486185837850384252799074818,486185837850393400039168039⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨355090267912403895286639243,355090267912425890592841908⟩,⟨463170206167078559888964791,463170206167100555157529633⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨614202135213525823585552207,614202135213565665979909410⟩,⟨(-43530577664803361423030532),(-43530577664763518968545408)⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨202654799097275837324995332,202654799097351829666721978⟩,⟨(-564496847228744283938017643),(-564496847228668291603551491)⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨(-441791694422073248241660997),(-441791694421970733714442487)⟩,⟨(-328361195523906518311334808),(-328361195523804003819679360)⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨(-365506228575673512943651531),(-365506228575566999989937032)⟩,⟨314082250460168860611005208,314082250460275373610134660⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨198747711702881815641846829,198747711702970281207934432⟩,⟨354346248898034934568699670,354346248898123400097321144⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨318811517510363201313127283,318811517510422072073812489⟩,⟨(-93291534335928107454275004),(-93291534335869236673945988)⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨5417292581825851209165784,5417292581856070658455215⟩,⟨(-264461199625427675239884944),(-264461199625397455785880826)⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-184081459744883133246092183),(-184081459744871696103192438)⟩,⟨(-89909068960814260174830952),(-89909068960802823052646504)⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-133100014903317114844796120),(-133100014903312274690016109)⟩,⟨74059473147247077931132848,74059473147251918095445118⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-32300263548113585035078799),(-32300263548111985450701199)⟩,⟨99949720399557700884450898,99949720399559300479601442⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨12266035575741538926365977,12266035575742226835458167⟩,⟨60224159650506233780218085,60224159650506921689952459⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨9000271880747787882663945,9000271880747959562190640⟩,⟨18093580172089317045224274,18093580172089488723972036⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨(-14528609280093485273400388),(-14528609280093485153208213)⟩,⟨(-192714200299630141148215304),(-192714200299630141002746408)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-201301503789295350771705553),(-201301503789295350313761084)⟩,⟨(-514532598352058948422361074),(-514532598352058947914702718)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-690721500401498930864134138),(-690721500401498929844492002)⟩,⟨(-489810922557835491829207911),(-489810922557835490810571823)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-1046884231150839194504062704),(-1046884231150839192724069985)⟩,⟨224786680298958236339287435,224786680298958238022474871⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-406084339567865390097748155),(-406084339567865386881466731)⟩,⟨1155951671832376144154113253,1155951671832376147377129169⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨953088258615293083324758218,953088258615293089156548702⟩,⟨875130559739655390227469489,875130559739655396120159174⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨1093088033451532758051536440,1093088033451532768863187171⟩,⟨(-645906979023984135690999041),(-645906979023984124931893533)⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-364513833309383801315814585),(-364513833309383781906601887)⟩,⟨(-1117339982664402823706084779),(-1117339982664402804273773007)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-1036570716467796401458813267),(-1036570716467796365106444674)⟩,⟨132101623994082073175150110,132101623994082109526559366⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-78295911888974782161019661),(-78295911888974695959517149)⟩,⟨900297412558226625942930998,900297412558226712140205878⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨708171128909444235094405219,708171128909444481676996288⟩,⟨284909981810138103188691924,284909981810138349767528980⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨455263045179060503994202365,455263045179061159900192811⟩,⟨(-428841634904989821301618728),(-428841634904989165387688430)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-68102522429911369741333671),(-68102522429909803264772540)⟩,⟨(-482169180967116211900204340),(-482169180967114645419917168)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-267640004093147430450209589),(-267640004093145391157216484)⟩,⟨(-220463459484301544288763307),(-220463459484299505003766690)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-203345646316624564041997579),(-203345646316622647740038731)⟩,⟨(-37559247121217127048434094),(-37559247121215210752359276)⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-68392018824948552420058885),(-68392018824947660046703177)⟩,⟨5101123351736763892624734,5101123351737656264765916⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-149591008845024049151798639),(-149591008844929733804121652)⟩,⟨30432949637716427755994682,30432949637810743096213157⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-489111514053367585611342415),(-489111514053367585148679134)⟩,⟨96999166175934231939508435,96999166175934232382531252⟩⟩
end hm25_0_0_10
namespace hm25_0_0_11
noncomputable def s0_0 : CBox := ⟨⟨2233851529582215566,2233851529582216783⟩,⟨(-1157289183345519176),(-1157289183345517960)⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨4484678514540858553,4484678514540860655⟩,⟨(-4014363541429821370),(-4014363541429819267)⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨2158807100276009384,2158807100276010811⟩,⟨(-5985275444222737187),(-5985275444222735760)⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-1621114956824234883),(-1621114956824234285)⟩,⟨(-4168611561009009291),(-4168611561009008698)⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-2167901788971885741),(-2167901788971885622)⟩,⟨(-646444482496568408),(-646444482496568286)⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-596401027268725367),(-596401027268725337)⟩,⟨586398285302930828,586398285302930859⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨84912543764046558,84912543764046578⟩,⟨206811261953013260,206811261953013282⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨41852536376678893,41852536376678915⟩,⟨(-3214724094311119),(-3214724094311099)⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨1083597546501092,1083597546501111⟩,⟨(-5166403264756947),(-5166403264756928)⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-361094073473354),(-361094073473335)⟩,⟨(-200568650946116),(-200568650946096)⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-13722802927189),(-13722802927169)⟩,⟨11576032530218,11576032530238⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨83141463264,83141463283⟩,⟨352481052306,352481052324⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨2323054446,2323054465⟩,⟨933702336,933702353⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨3094902,3094920⟩,⟨(-1300807),(-1300788)⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨132,148⟩,⟨(-214),(-191)⟩⟩
noncomputable def s1_0 : CBox := ⟨⟨4194189009198973947702,4194189009198977222890⟩,⟨1658385389311036533645,1658385389311039808940⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨11889429951665188808704,11889429951665200009476⟩,⟨1514756577325041233083,1514756577325052433796⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨14660412366696135749261,14660412366696155212476⟩,⟨(-5577571576136689095177),(-5577571576136669632854)⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨7281144523175442377029,7281144523175479468193⟩,⟨(-13492547929757561474923),(-13492547929757524384349)⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-4938160185829640175970),(-4938160185829588830194)⟩,⟨(-11255093504396824519261),(-11255093504396773172861)⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-8388758892589056385138),(-8388758892588987121624)⟩,⟨(-725356008029865918444),(-725356008029796654942)⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-2258670251029953962562),(-2258670251029891919246)⟩,⟨4528722845789388965027,4528722845789451008158⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨1974650222807113675446,1974650222807155179923⟩,⟨1878942422862255818566,1878942422862297323169⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨1149123039502023906388,1149123039502045213095⟩,⟨(-692643844288190570562),(-692643844288169263901)⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-155570737704097249612),(-155570737704088833322)⟩,⟨(-596018962383031424980),(-596018962383023008680)⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-268419296572974257754),(-268419296572971799518)⟩,⟨(-26879428169648744263),(-26879428169646286023)⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-62273613812661209471),(-62273613812660668796)⟩,⟨97309081932036247929,97309081932036788596⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨18120844739798606283,18120844739798747473⟩,⟨46111492161591633558,46111492161591774748⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨19345755972636211863,19345755972636241906⟩,⟨9329867655152304823,9329867655152334868⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨8956453460216438992,8956453460216448523⟩,⟨(-612480240019968970),(-612480240019959441)⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨2337517668670088135,2337517668670090161⟩,⟨(-808945932653815005),(-808945932653812975)⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨13056069242357088208643,13056069242357088295373⟩,⟨281023487962334948847219,281023487962334948972277⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨234000373646059586038464,234000373646059586355994⟩,⟨740138153811430321551983,740138153811430321943550⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨798966583874200983552209,798966583874200984199433⟩,⟨751849172006651490033301,751849172006651490679368⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨1207664955131502847070991,1207664955131502848020942⟩,⟨19588034878559053858166,19588034878559054671013⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨689030556853579976496139,689030556853579977771283⟩,⟨(-907448945410802798410293),(-907448945410802797127851)⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-416197611354655869532929),(-416197611354655867813011)⟩,⟨(-863400231002588697561875),(-863400231002588695761605)⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-732049919538531580133016),(-732049919538531577651941)⟩,⟨70681843742146191812322,70681843742146194227735⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-94855536378416359655827),(-94855536378416356397453)⟩,⟨515099538368213337231939,515099538368213340520572⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨319193919647665082300351,319193919647665086503011⟩,⟨147717188960102733241448,147717188960102737440285⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨146836416402897205620982,146836416402897211308262⟩,⟨(-171873937458757575794111),(-171873937458757570116143)⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-69849858487602057342690),(-69849858487602048424629)⟩,⟨(-122425549943958408738573),(-122425549943958399809888)⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-85993296811972687767246),(-85993296811972672482575)⟩,⟨4583440710780034428357,4583440710780049707991⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-28136641292027191206088),(-28136641292027164939323)⟩,⟨43278642295695032715993,43278642295695058981116⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨4822761279147169591801,4822761279147197540077⟩,⟨29410751669578253674737,29410751669578281624921⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨9557444654792889389223,9557444654792911985497⟩,⟨12037963940495728754894,12037963940495751352284⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨3794913769486874001668,3794913769486883761428⟩,⟨2829803917349778544663,2829803917349788304624⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨(-2780272098211022514929682),(-2780272098211014035278284)⟩,⟨2634351323655201678950227,2634351323655210158926999⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-5710112954729680636078387),(-5710112954729663569180643)⟩,⟨9164996301637114473935756,9164996301637131542387463⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-909798014149683599777281),(-909798014149667772143558)⟩,⟨15876271888014256314782493,15876271888014272144482977⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨11477441805380028502474213,11477441805380038744274364⟩,⟨14557925671787908529650639,14557925671787918770541337⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨18756164895885215589753179,18756164895885219286886943⟩,⟨(-359476900010232211964469),(-359476900010228516968710)⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨7699168712153170761316048,7699168712153172078541190⟩,⟨(-15322542517456730340660452),(-15322542517456729021424372)⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-9826971031062154930940722),(-9826971031062154447610571)⟩,⟨(-10686495263559462717680591),(-10686495263559462234993761)⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨(-10398459086838530905648986),(-10398459086838530710385791)⟩,⟨5124824898000688174583611,5124824898000688369420581⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨1735144192348321885652874,1735144192348321965876203⟩,⟨8672053208862541047553846,8672053208862541128618829⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨6476810305063708384313402,6476810305063708417009075⟩,⟨577897068490156055252618,577897068490156087170691⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨2018060225448200385420145,2018060225448200398079391⟩,⟨(-4170569149473425714783124),(-4170569149473425701689721)⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨(-1907946215061926340784673),(-1907946215061926335417454)⟩,⟨(-2574926303983326961231341),(-2574926303983326955802139)⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-2140547653897197075800772),(-2140547653897197073327265)⟩,⟨(-13921829801593448231299),(-13921829801593446050247)⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-1011658401410024562937916),(-1011658401410024561791910)⟩,⟨892104782837173699031023,892104782837173700168894⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-250392116075848558664528),(-250392116075848558229918)⟩,⟨696609360927486936157782,696609360927486936674239⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-20779870789886916033502),(-20779870789886915929936)⟩,⟨234591712889433677803398,234591712889433677945000⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨(-16606719727938688134990310),(-16606719727938394713470138)⟩,⟨(-22204306235818268006791834),(-22204306235817974586289939)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-61826393571714589971408380),(-61826393571713508455520598)⟩,⟨(-47710915046835219768737444),(-47710915046834138252106213)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-114297885182276511354238695),(-114297885182274361104672563)⟩,⟨(-14177588838017900443734759),(-14177588838015750182951527)⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-107784446931505618613193371),(-107784446931500508575242011)⟩,⟨82469226041597802501798362,82469226041602912548357186⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨9776592080248370253621158,9776592080257500764237900⟩,⟨140831997078177417514515080,140831997078186548011587359⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨127161876925417173164368133,127161876925434292575563488⟩,⟨45925841115301091189444961,45925841115318210602215253⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨72837848761804675593522756,72837848761827320637361183⟩,⟨(-97532069420468021935389452),(-97532069420445376883732728)⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨(-67828490764202137642729167),(-67828490764179077799106755)⟩,⟨(-79337836354036471709273965),(-79337836354013411875425371)⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-75212173198121894962414442),(-75212173198103135161365896)⟩,⟨41931737892877769870382779,41931737892896529679326114⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨19187939431526640612986153,19187939431538864098907084⟩,⟨66165294033375212072897137,66165294033387435554771144⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨53706890604649351938942950,53706890604655493486513860⟩,⟨1212104286367886401111891,1212104286374027947704758⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨17970370376177512568813712,17970370376179792292628195⟩,⟨(-36642597933107856594587100),(-36642597933105576866615566)⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-14480970489506080078290121),(-14480970489505130770862271)⟩,⟨(-26092281789190584748420029),(-26092281789189635442871062)⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-19318975537191036427389050),(-19318975537190727127113908)⟩,⟨(-6256082362871818006444331),(-6256082362871508708276044)⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-11535810203815504730125648),(-11535810203815372941799253)⟩,⟨2346790209086042852089982,2346790209086174640291470⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-3449195705168701867037145),(-3449195705168669139152775)⟩,⟨1715618547878871798046345,1715618547878904526081095⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨54995247968833855272039219,54995247968833855313726973⟩,⟨(-4144951825110881195507156),(-4144951825110881161195238)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨146379109117768331406366430,146379109117768331551256587⟩,⟨(-57238280965497690431134278),(-57238280965497690300697702)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨138559421114919091207109078,138559421114919091495658118⟩,⟨(-195200442795739621717081498),(-195200442795739621428260418)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-62722154492935517530929224),(-62722154492935517059102641)⟩,⟨(-293306130530902081844898762),(-293306130530902081345418820)⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-319878851429344990991767781),(-319878851429344990098913744)⟩,⟨(-112811983773102677904636526),(-112811983773102677013623646)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-239316384991508459752615487),(-239316384991508458143927906)⟩,⟨259808341032812043532737419,259808341032812045124454169⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨173011810248694880236295183,173011810248694883125896890⟩,⟨294058322188779105252757627,294058322188779108156686419⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨295368783722442346299061237,295368783722442351428687616⟩,⟨(-95679572780133097978142490),(-95679572780133092854638149)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-33713413754783305365943737),(-33713413754783295941625579)⟩,⟨(-269091413840860703643520558),(-269091413840860694219000916)⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-229506592179310860256752755),(-229506592179310838317722344)⟩,⟨(-20419338428910903731305949),(-20419338428910881791223000)⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-71719336434318968775733102),(-71719336434318907091784832)⟩,⟨177394124810389485128513465,177394124810389546813560977⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨105690489863303759031270322,105690489863303920744470266⟩,⟨112495462323695403438275447,112495462323695565149354604⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨117425533305973566422234637,117425533305973947473509460⟩,⟨(-16481078310742105779646971),(-16481078310741724729351452)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨53144827662261369052873866,53144827662261860251865421⟩,⟨(-64454384503860913090456808),(-64454384503860421889408309)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨8990600785754215121211262,8990600785754673253510617⟩,⟨(-48625913283569832303753254),(-48625913283569374169954527)⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-1214897548758402323594319),(-1214897548758189740538742)⟩,⟨(-16292931433076404122110174),(-16292931433076191538747007)⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def ans : CBox := ⟨⟨(-6829087645305715290870835),(-6829087645285167821896788)⟩,⟨(-45251851073766205763366537),(-45251851073745658292803085)⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-23687354313445332008216486),(-23687354313445331892601069)⟩,⟨(-148068244402214326996990703),(-148068244402214326875096220)⟩⟩
end hm25_0_0_11
namespace hm25_0_0_12
noncomputable def s0_0 : CBox := ⟨⟨50248123850463227,50248123850463297⟩,⟨97016182522648442,97016182522648512⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨170939128143520716,170939128143520824⟩,⟨191328369636169372,191328369636169474⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨245504480810784186,245504480810784260⟩,⟨89261757053770267,89261757053770343⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨161949291270012568,161949291270012607⟩,⟨(-62077425009709625),(-62077425009709583)⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨23783848908789639,23783848908789662⟩,⟨(-77599868029825806),(-77599868029825780)⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-18832791524403947),(-18832791524403925)⟩,⟨(-19564076453839180),(-19564076453839162)⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-5962359569514947),(-5962359569514930)⟩,⟨2354644618367716,2354644618367734⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨62775082967326,62775082967345⟩,⟨1032172200680299,1032172200680318⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨105493104485301,105493104485319⟩,⟨24063058522052,24063058522073⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨3397343865734,3397343865754⟩,⟨(-5866184658289),(-5866184658272)⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-142088320425),(-142088320403)⟩,⟨(-174313247263),(-174313247242)⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-3176165293),(-3176165274)⟩,⟨701743640,701743658⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-5651604),(-5651585)⟩,⟨13653057,13653074⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨4337,4353⟩,⟨10508,10526⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-14),16⟩,⟨0,16⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨0,16⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-144396044312653936241),(-144396044312653651094)⟩,⟨365134567300022475220,365134567300022760353⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-131103494795688691139),(-131103494795687725512)⟩,⟨1025322311404638681497,1025322311404639647128⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨470579826736824953764,470579826736826600506⟩,⟨1241468892999011824413,1241468892999013471231⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨1109300037903989697893,1109300037903992743764⟩,⟨601900340003346893384,601900340003349939302⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨894531769438966450466,894531769438970520031⟩,⟨(-388720461019983521113),(-388720461019979451599)⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨58088577884077785360,58088577884083029761⟩,⟨(-636161980644127220690),(-636161980644121976292)⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-325010202809279982512),(-325010202809275532188)⟩,⟨(-164523125199496439926),(-164523125199491989590)⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-128382746037385149755),(-128382746037382338344)⟩,⟨133091786322382617335,133091786322385428739⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨43523334144405599613,43523334144406956333⟩,⟨73405262155523792278,73405262155525149003⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨35482850324428510705,35482850324429012310⟩,⟨(-8991333473545198737),(-8991333473544697130)⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨1587328625672231303,1587328625672367886⟩,⟨(-14877572727196918362),(-14877572727196781781)⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-5030867529464535467),(-5030867529464507354)⟩,⟨(-3257432630893355802),(-3257432630893327691)⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-2253982210486672098),(-2253982210486665164)⟩,⟨875835508418689581,875835508418696512⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-434744955301550387),(-434744955301548975)⟩,⟨896342304745790107,896342304745791517⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨27027927922580379,27027927922580820⟩,⟨400416179341441984,400416179341442426⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨35458669586979981,35458669586980086⟩,⟨102494711866371602,102494711866371707⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-36727463288406925793150),(-36727463288406925776675)⟩,⟨1705026812832172948028,1705026812832172959386⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-96131473095418953737264),(-96131473095418953686091)⟩,⟨30359701240732776174996,30359701240732776216340⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-96516743386218003427017),(-96516743386218003343815)⟩,⟨102393755454437057603378,102393755454437057686709⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-2701187437294499314133),(-2701187437294499211673)⟩,⟨152061978549914198235164,152061978549914198355262⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨111358262720669963456755,111358262720669963614639⟩,⟨84967634098572386624676,84967634098572386781706⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨103267121662343720616672,103267121662343720831801⟩,⟨(-49380168919529791271544),(-49380168919529791066283)⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-7841878689791452977923),(-7841878689791452699230)⟩,⟨(-84595924987632958405600),(-84595924987632958119150)⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-57316959818085444004708),(-57316959818085443638979)⟩,⟨(-10808922098224637842364),(-10808922098224637480057)⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-15974261368553409824637),(-15974261368553409375732)⟩,⟨34119114671706340296650,34119114671706340745950⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨17626621824656683354003,17626621824656683936758⟩,⟨15189468695327518009975,15189468695327518593731⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨12143535169833132082447,12143535169833132962902⟩,⟨(-6868168745864016305830),(-6868168745864015426461)⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-412878335553475365436),(-412878335553473910906)⟩,⟨(-8206049216748955201400),(-8206049216748953746378)⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-3992264736472274470970),(-3992264736472272050856)⟩,⟨(-2607188957002022357206),(-2607188957002019936933)⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-2646697956377902722865),(-2646697956377900209438)⟩,⟨430854285570618088058,430854285570620601313⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-1063579806511970942642),(-1063579806511968948137)⟩,⟨843648436794178340558,843648436794180334965⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-247560871457957875600),(-247560871457957021860)⟩,⟨331956674902699764536,331956674902700618259⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨(-459219281543357774366836),(-459219281543356296051208)⟩,⟨(-484681202649254688760455),(-484681202649253210502117)⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-1589902653030624901605074),(-1589902653030621939201968)⟩,⟨(-991069571412157117622227),(-991069571412154155491439)⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-2728770506677849032234887),(-2728770506677846310576383)⟩,⟨(-158043399161949806407589),(-158043399161947085108572)⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨(-2470269743383742662195992),(-2470269743383740923766728)⟩,⟨1943059556107210312953781,1943059556107212051538235⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨54539340164657603143154,54539340164658219282421⟩,⟨3123861005186906662515638,3123861005186907279016577⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨2495123342860864344511884,2495123342860864560023525⟩,⟨1260870189186626139268637,1260870189186626354448427⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨1704662212517287125913436,1704662212517287202844394⟩,⟨(-1558885699432686908155907),(-1558885699432686831122386)⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨(-789132611179241703698765),(-789132611179241673465405)⟩,⟨(-1613652612883823315521239),(-1613652612883823285219395)⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨(-1307650065944294247317763),(-1307650065944294235080071)⟩,⟨257361901264412670314811,257361901264412682422411⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨(-87496955314362377114107),(-87496955314362372429735)⟩,⟨948692159357788889789193,948692159357788894590095⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨593849425166061271036130,593849425166061272907928⟩,⟨289249130915834574575894,289249130915834576384582⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨358479790615011535453739,358479790615011536210947⟩,⟨(-264500749718826762676871),(-264500749718826761928703)⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨2296717025365045669865,2296717025365045966986⟩,⟨(-291068094005232009718520),(-291068094005232009380509)⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-119075075499933436554362),(-119075075499933436401625)⟩,⟨(-135244133820736710255048),(-135244133820736710101163)⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-91907221679797979991913),(-91907221679797979923242)⟩,⟨(-33066339828947156618003),(-33066339828947156560447)⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-30757247871574524087466),(-30757247871574524068720)⟩,⟨(-2725493256761875837023),(-2725493256761875823415)⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨4839678356837389254215822,4839678356837453205926146⟩,⟨(-3619455956321589690057141),(-3619455956321525738129942)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨10362248328242527846605225,10362248328242762641971582⟩,⟨(-13422562458622394976707399),(-13422562458622160181498592)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨3068311778615853808810119,3068311778616317153761909⟩,⟨(-24631373688955179256942607),(-24631373688954715914356560)⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-17557456668141249365567576),(-17557456668140161095540574)⟩,⟨(-22992617190631841818632278),(-22992617190630753550409024)⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-29601337541440640256102615),(-29601337541438722187779350)⟩,⟨2011937849524074554496351,2011937849525992625615688⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-9540413048554121306498681),(-9540413048550585970233843)⟩,⟨26258810838369486656821087,26258810838373021992772961⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨19737930256215884283270734,19737930256220469782264151⟩,⟨14810951333411432306070862,14810951333416017803488941⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨15786663179282197595495171,15786663179286774151881898⟩,⟨(-13427793977371576927537787),(-13427793977367000369222999)⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-8109666299795334062140189),(-8109666299791687262144754)⟩,⟨(-14634396524059256269648242),(-14634396524055609471177751)⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨(-12587899341722634907316907),(-12587899341720308332366193)⟩,⟨3617538408949919277798108,3617538408952245853513067⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-246484984499947838196572),(-246484984498803658601291)⟩,⟨9998239726943698121422911,9998239726944842301204118⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨6686288304805376455424237,6686288304805793010118093⟩,⟨3292518346983429436134882,3292518346983845990064051⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨4688838364753927585311203,4688838364754098261063183⟩,⟨(-2595569553467563357125255),(-2595569553467392681033818)⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨1110742250204618190588941,1110742250204673013687453⟩,⟨(-3422966393542560819452565),(-3422966393542505995976394)⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-411582617065157542772114),(-411582617065134398942224)⟩,⟨(-2025530024199056198180961),(-2025530024199033054328803)⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-299776428726682256755826),(-299776428726676537585986)⟩,⟨(-602730001678727875806277),(-602730001678722156663047)⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨1083992881969473881821113,1083992881969473890800062⟩,⟨14386267892463748529746958,14386267892463748540697890⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨14918951771407699723601357,14918951771407699757657624⟩,⟨38173110785861057951433141,38173110785861057989339663⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨50567579368591239248646314,50567579368591239323639416⟩,⟨35929985410437497325474883,35929985410437497400400882⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨75328436061054316990928604,75328436061054317119407589⟩,⟨(-16042799703408900469002453),(-16042799703408900347761932)⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨28728053328491257541551752,28728053328491257767824249⟩,⟨(-81142543259643150200597920),(-81142543259643149973864563)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-64921931741534423034515118),(-64921931741534422636271423)⟩,⟨(-59991512977170168337307353),(-59991512977170167934729800)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-72515682485677172470239702),(-72515682485677171755247190)⟩,⟨42481336332797711281452716,42481336332797711992865013⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨23021263832868253527196721,23021263832868254766989208⟩,⟨71575666665038135607911883,71575666665038136849191634⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨64035807601920537088604632,64035807601920539328401085⟩,⟨(-7884919158632739540937145),(-7884919158632737301177391)⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨4879176714829094955592231,4879176714829100074573072⟩,⟨(-53632266947411444699270101),(-53632266947411439580529162)⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-40734347749582163562732575),(-40734347749582149417243340)⟩,⟨(-16549217537701218763508235),(-16549217537701204618308027)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨(-25481543198159166912862429),(-25481543198159130365427394)⟩,⟨23877727053471785495352926,23877727053471822043304056⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨3656017224509308456930812,3656017224509393425266418⟩,⟨26214540906304568429180507,26214540906304653397750898⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨14228799183408555129528596,14228799183408663585466066⟩,⟨11743556156137413293413506,11743556156137521748867949⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨10658921240290364505443105,10658921240290464905346120⟩,⟨1972752994117917124094382,1972752994118017523648485⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨3557989051319058807331985,3557989051319105229297390⟩,⟨(-265231453863917402888097),(-265231453863870980993849)⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨12399506034243386440320264,12399506034247497325893865⟩,⟨(-1331037742652041146673605),(-1331037742647930261399377)⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨40616493024030407610642001,40616493024030407640380084⟩,⟨(-5267581095613204345776719),(-5267581095613204317856050)⟩⟩
end hm25_0_0_12
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock28_1
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
open IntegerIntervals
namespace hm28_0_0_10
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),0⟩⟩
end hm28_0_0_10
end SharpPlanar.CachedData

end OAI
end


