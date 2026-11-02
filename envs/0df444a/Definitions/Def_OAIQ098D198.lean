-- Prove2me | Definitions.Def_OAIQ098D198
-- name    : OAIQ098D198
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T15:51:04.176197+00:00
-- url     : https://prove2.me/theorems/8e9d2b27-b845-4301-9002-fa0efb874ab7
-- title:
--   Definitions bundle OAIQ098D198 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1426 declarations of OpenAI's Lean: 1426 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.hm25_1_0_9.s5_15`, `OAI.SharpPlanar.CachedData.hm25_1_0_9.s5_2`, `OAI.SharpPlanar.CachedData.hm25_1_0_9.s5_3`, `OAI.SharpPlanar.CachedData.hm25_1_0_9.s5_4`, `OAI.SharpPlanar.CachedData.hm25_1_0_9.s5_5`, `OAI.SharpPlanar.CachedData.hm25_1_0_9.s5_6`, `OAI.SharpPlanar.CachedData.hm25_1_0_9.s5_7`, `OAI.SharpPlanar.CachedData.hm25_1_0_9.s5_8`, `OAI.SharpPlanar.CachedData.hm25_1_0_9.s5_9`, `OAI.SharpPlanar.CachedData.hm25_1_1_2.ans`, `OAI.SharpPlanar.CachedData.hm25_1_1_2.atomAnswer`, `OAI.SharpPlanar.CachedData.hm25_1_1_2.s0`, `OAI.SharpPlanar.CachedData.hm25_1_1_2.s0_0`, `OAI.SharpPlanar.CachedData.hm25_1_1_2.s0_1`, `OAI.SharpPlanar.CachedData.hm25_1_1_2.s0_10`, `OAI.SharpPlanar.CachedData.hm25_1_1_2.s0_11`, `OAI.SharpPlanar.CachedData.hm25_1_1_2.s0_12`, `OAI.SharpPlanar.CachedData.hm25_1_1_2.s0_13`, `OAI.SharpPlanar.CachedData.hm25_1_1_2.s0_14`, `OAI.SharpPlanar.CachedData.hm25_1_1_2.s0_15`, `OAI.SharpPlanar.CachedData.hm25_1_1_2.s0_2`, `OAI.SharpPlanar.CachedData.hm25_1_1_2.s0_3`, `OAI.SharpPlanar.CachedData.hm25_1_1_2.s0_4`, `OAI.SharpPlanar.CachedData.hm25_1_1_2.s0_5`, `OAI.SharpPlanar.CachedData.hm25_1_1_2.s0_6`, `OAI.SharpPlanar.CachedData.hm25_1_1_2.s0_7`, `OAI.SharpPlanar.CachedData.hm25_1_1_2.s0_8`, `OAI.SharpPlanar.CachedData.hm25_1_1_2.s0_9`, `OAI.SharpPlanar.CachedData.hm25_1_1_2.s1`, `OAI.SharpPlanar.CachedData.hm25_1_1_2.s1_0`, `OAI.SharpPlanar.CachedData.hm25_1_1_2.s1_1`, `OAI.SharpPlanar.CachedData.hm25_1_1_2.s1_10`, `OAI.SharpPlanar.CachedData.hm25_1_1_2.s1_11`, `OAI.SharpPlanar.CachedData.hm25_1_1_2.s1_12`, `OAI.SharpPlanar.CachedData.hm25_1_1_2.s1_13`, `OAI.SharpPlanar.CachedData.hm25_1_1_2.s1_14`, `OAI.SharpPlanar.CachedData.hm25_1_1_2.s1_15`, `OAI.SharpPlanar.CachedData.hm25_1_1_2.s1_2`, `OAI.SharpPlanar.CachedData.hm25_1_1_2.s1_3`, `OAI.SharpPlanar.CachedData.hm25_1_1_2.s1_4` and 1386 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_LowBlock25_1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/LowBlock25_1.lean), [`PlanarPacking_Certificate_LowBlock25_10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/LowBlock25_10.lean), [`PlanarPacking_Certificate_LowBlock25_11`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/LowBlock25_11.lean), [`PlanarPacking_Certificate_LowBlock27_0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/LowBlock27_0.lean), [`PlanarPacking_Certificate_LowBlock27_1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/LowBlock27_1.lean), [`PlanarPacking_Certificate_WUCert15`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/WUCert15.lean), [`PlanarPacking_Certificate_WUCert19`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/WUCert19.lean).
--
--   **Imports.** It imports the bundles `OAIQ098D003`, `OAIQ098D004` and `OAIQ098D005` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098D272`, `OAIQ098D407`, `OAIQ098D408`, `OAIQ098D561` and `OAIQ098D692`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098D003
import Definitions.Def_OAIQ098D004
import Definitions.Def_OAIQ098D005

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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm25_1_0_9
noncomputable def s5_2 : CBox := ⟨⟨13720479564484561251868152,13720479564484562184932741⟩,⟨79062685538821604534023798,79062685538821605470103582⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨179854817579642529141683077,179854817579642530246601938⟩,⟨(-17376623285842621698332677),(-17376623285842620397522812)⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨128001325441184802010455568,128001325441184804400547482⟩,⟨(-424335861070872823781000919),(-424335861070872821409786489)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-583167133826249102691184896),(-583167133826249097757388282)⟩,⟨(-590048001051310980281610072),(-590048001051310975493655587)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-1164685544127327841539138891),(-1164685544127327830645493848)⟩,⟨376946136147777385861355517,376946136147777396903789717⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-151200235527371948405165607),(-151200235527371924037334091)⟩,⟨1505770901039000233792619911,1505770901039000258076774099⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨1453330350953398585152457697,1453330350953398643592601614⟩,⟨760949310032393625736776700,760949310032393684190862187⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨1230570643623899814653366437,1230570643623900002137765660⟩,⟨(-1032848889554485086794492498),(-1032848889554484899282476342)⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨72610364094870502477801391,72610364094873270119031512⟩,⟨120770637063199725532428106,120770637063202493173347811⟩⟩
end hm25_1_0_9
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock25_10
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm25_1_1_2
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
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-7383405695323),(-7383405695305)⟩,⟨(-3960649538705),(-3960649538687)⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-15034492394589),(-15034492394564)⟩,⟨(-3709401245479),(-3709401245460)⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-9532386331818),(-9532386331796)⟩,⟨2464752550622,2464752550641⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨(-1839998024465),(-1839998024441)⟩,⟨2741673509345,2741673509371⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨221482647230,221482647260⟩,⟨615569693336,615569693360⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨81583855890,81583855917⟩,⟨9464785487,9464785514⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨3041420775,3041420806⟩,⟨(-6236936292),(-6236936259)⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨(-313905747),(-313905714)⟩,⟨(-278672070),(-278672039)⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨(-16396586),(-16396555)⟩,⟨10809867,10809900⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨215943,215977⟩,⟨756300,756333⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨30355,30387⟩,⟨3636,3671⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨798,829⟩,⟨(-1072),(-1040)⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-29),1⟩,⟨(-88),(-60)⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-17),11⟩,⟨(-18),11⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨1148331872726287734993,1148331872726344730479⟩,⟨(-1742820115491557482211),(-1742820115491500486720)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨1514857766876173069026,1514857766876323545003⟩,⟨(-4429800031329510970181),(-4429800031329360494032)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-719095334285807072590),(-719095334285625034375)⟩,⟨(-4298630049757078244972),(-4298630049756896206418)⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-1974233809562530449554),(-1974233809562309979114)⟩,⟨(-1611761346857921288257),(-1611761346857700817769)⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-1000580453359058658133),(-1000580453358917089363)⟩,⟨247781736659721375644,247781736659862944342⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-65146927388155182844),(-65146927388076080853)⟩,⟨298000676394208276866,298000676394287378865⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨60459751314025199630,60459751314053768604⟩,⟨34786470384151931451,34786470384180500425⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨8675904036630832722,8675904036637051871⟩,⟨(-9716765051212828580),(-9716765051206609427)⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-1309229123891384633),(-1309229123890435282)⟩,⟨(-1637124254461054325),(-1637124254460104976)⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨(-271811646587945107),(-271811646587833088)⟩,⟨143377113113430335,143377113113542355⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨9449804669559554,9449804669570218⟩,⟨42651355455118230,42651355455128895⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨6363168872684223,6363168872685165⟩,⟨1132157771199212,1132157771200153⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨721927676555969,721927676556063⟩,⟨(-795177378576593),(-795177378576497)⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-14826523055913),(-14826523055881)⟩,⟨(-213916956726236),(-213916956726203)⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-30726439259922),(-30726439259900)⟩,⟨(-41677184882521),(-41677184882500)⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-8600418002564),(-8600418002547)⟩,⟨(-6439250193952),(-6439250193935)⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨13342287251400248348476678,13342287251400250975729076⟩,⟨3181299639258600529760049,3181299639258603132856389⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨32005041978348267252345195,32005041978348275379999501⟩,⟨(-7059235171070743938877772),(-7059235171070735891383260)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨12319340696478077682218251,12319340696478090214174918⟩,⟨(-35298145607872603817717055),(-35298145607872591348343030)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-44187073407972462312358804),(-44187073407972444670986316)⟩,⟨(-25456571775484403661447295),(-25456571775484386005968887)⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-57309653743262452117037291),(-57309653743262418521547831)⟩,⟨34992976114799490187644321,34992976114799523814768973⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-4587557783977847436072831),(-4587557783977807305643597)⟩,⟨59367271789240027499213550,59367271789240067622827362⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨28915947151616000483518107,28915947151616032776944442⟩,⟨23014217375112450745255566,23014217375112483036080144⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨16226713737927185071651248,16226713737927204069351045⟩,⟨(-6265534079255856837082102),(-6265534079255837837691827)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨730191312620121049644224,730191312620129748435363⟩,⟨(-6644834510115059985141334),(-6644834510115051286745169)⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-1889199289576624993630386),(-1889199289576621638427093)⟩,⟨(-1206963206631171172668441),(-1206963206631167817425455)⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-605919306991009310447142),(-605919306991007987856485)⟩,⟨347819612983329156083928,347819612983330478688421⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨(-5659078901738093782373),(-5659078901737459214371)⟩,⟨215318070743546334851495,215318070743546969410784⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨53738826483814883687956,53738826483815312961109⟩,⟨44261774126498799755124,44261774126499229029327⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨24350458793423528994863,24350458793423767284913⟩,⟨(-1202623587957632593076),(-1202623587957394302118)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨7481747003511977720036,7481747003512131296092⟩,⟨(-4781062346913451544198),(-4781062346913297968092)⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨1534975639860855967106,1534975639860906618537⟩,⟨(-1698153273806630962754),(-1698153273806580311346)⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-826577128365795451509921),(-826577128365765169053208)⟩,⟨6535447429362948823221192,6535447429362979084139278⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-739460342890099024508442752),(-739460342890099015814343771)⟩,⟨2050452042450765419815473375,2050452042450765428513894950⟩⟩
end hm25_1_1_2
namespace hm25_1_1_3
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
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-28),29⟩,⟨(-28),28⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-2361337535038),(-2361337535021)⟩,⟨13383178980371,13383178980390⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨1984239325098,1984239325118⟩,⟨25110735329277,25110735329301⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨8823774942398,8823774942421⟩,⟨13475313296514,13475313296538⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨5270456040213,5270456040240⟩,⟨1377283791279,1377283791308⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨840143849379,840143849413⟩,⟨(-696452157193),(-696452157163)⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨(-33658622028),(-33658621992)⟩,⟨(-134707927188),(-134707927151)⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-11876587394),(-11876587357)⟩,⟨(-926759125),(-926759084)⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨(-239678797),(-239678754)⟩,⟨692586535,692586576⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨29252171,29252216⟩,⟨19042798,19042841⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨1081743,1081785⟩,⟨(-924962),(-924921)⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨(-18146),(-18104)⟩,⟨(-53357),(-53315)⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨(-2469),(-2431)⟩,⟨(-497),(-456)⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-130),(-94)⟩,⟨72,108⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-19),15⟩,⟨(-5),28⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨(-2645421748438370295409),(-2645421748438293734703)⟩,⟨(-1153721132674595010293),(-1153721132674518449663)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-6411993625297344132967),(-6411993625297150905982)⟩,⟨(-1006183699070959783225),(-1006183699070766556620)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-5716246590183573903781),(-5716246590183308695934)⟩,⟨2051134269298844337983,2051134269299109545389⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-1711379577579766642053),(-1711379577579459906444)⟩,⟨3142176572658729426282,3142176572659036161915⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨619627436869930203297,619627436870134761077⟩,⟨1323375143146030647187,1323375143146235205057⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨437476912966901902128,437476912967012250702⟩,⟨3981336445845914116,3981336445956262668⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨30306341455216848136,30306341455258234606⟩,⟨(-96750484461884640472),(-96750484461843253998)⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨(-16889830993238366030),(-16889830993228674565)⟩,⟨(-9158052472787015928),(-9158052472777324467)⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-1900571480115695537),(-1900571480114230410)⟩,⟨2499292244363952982,2499292244365418109⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨317205156665083781,317205156665250426⟩,⟨343487778990925801,343487778991092444⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨59478759330897453,59478759330913027⟩,⟨(-31878580429058868),(-31878580429043288)⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-1117534216776418),(-1117534216774999)⟩,⟨(-10063865444736952),(-10063865444735536)⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-1541754823423825),(-1541754823423672)⟩,⟨(-724668285263738),(-724668285263582)⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-319553726464957),(-319553726464918)⟩,⟨126112133821677,126112133821715⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-48715585759290),(-48715585759266)⟩,⟨67867522710371,67867522710394⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-5580510182950),(-5580510182929)⟩,⟨16478344430554,16478344430571⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨2987172142835603025719277,2987172142835606283373486⟩,⟨(-16269880772456467799612333),(-16269880772456464510004105)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-10633104230839766953696197),(-10633104230839756830834826)⟩,⟨(-38157412793287855080032598),(-38157412793287844857661856)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-43656087018371883707767905),(-43656087018371867889654583)⟩,⟨(-12392711933477879067475933),(-12392711933477863182390619)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-27514113160647051682506986),(-27514113160647029068166507)⟩,⟨55937778459081872279109569,55937778459081894868047436⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨48193046432099186163180888,48193046432099229790034056⟩,⟨67336029812926711990794768,67336029812926755580544271⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨74178047798887131787536186,74178047798887184566541070⟩,⟨(-359199780272197015066557),(-359199780272144225194009)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨25526918914129103556611544,25526918914129146680786612⟩,⟨(-38952464551180164085981318),(-38952464551180120959736040)⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-10083957735101180209660700),(-10083957735101154439400353)⟩,⟨(-19772816358324480997132046),(-19772816358324455228932149)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-8642617198098531028657466),(-8642617198098519049862564)⟩,⟨44185289352265207232869,44185289352277186603796⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-1257689293572788690834512),(-1257689293572784016907038)⟩,⟨2654241622873432671917123,2654241622873437345755453⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨567112684910341311575981,567112684910343170681927⟩,⟨733542908214843880444651,733542908214845739543181⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨287174985111953253561914,287174985111954144158386⟩,⟨(-34874599655979419753354),(-34874599655978529145141)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨48020388776624948909547,48020388776625529868348⟩,⟨(-81372085909228266913389),(-81372085909227685956915)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-7025846843104780821477),(-7025846843104442043849)⟩,⟨(-32618233340490989460842),(-32618233340490650684361)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-8208106910919630794294),(-8208106910919411533988)⟩,⟨(-9057299208655351269664),(-9057299208655132009311)⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-2669824438063604754584),(-2669824438063535094952)⟩,⟨(-1692026209330061484074),(-1692026209329991824379)⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨8327767480723210343822668,8327767480723250166108745⟩,⟨107655885575858241862517,107655885575898088697520⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨2514360048090380976736222752,2514360048090380987758511224⟩,⟨761726924345491413794105544,761726924345491424806699939⟩⟩
end hm25_1_1_3
namespace hm25_1_1_4
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
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-20),16⟩,⟨(-20),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-32),30⟩,⟨(-32),29⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-44),44⟩,⟨(-44),44⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-51),51⟩,⟨(-51),51⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨16362906668302,16362906668320⟩,⟨(-2357244119795),(-2357244119777)⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨28308887492585,28308887492608⟩,⟨(-11955798062468),(-11955798062442)⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨12184119996069,12184119996096⟩,⟨(-15560063890623),(-15560063890595)⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨(-537896092426),(-537896092394)⟩,⟨(-6718895457642),(-6718895457611)⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-1176691566119),(-1176691566085)⟩,⟨(-692353556185),(-692353556152)⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨(-144779377029),(-144779376992)⟩,⟨100163903662,100163903699⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨4503493503,4503493544⟩,⟨14662365996,14662366038⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨957981852,957981894⟩,⟨(-57276601),(-57276557)⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨7695912,7695958⟩,⟨(-45884649),(-45884606)⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨(-1752459),(-1752409)⟩,⟨(-812422),(-812372)⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨(-55610),(-55555)⟩,⟨54408,54463⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨916,966⟩,⟨3350,3401⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨165,209⟩,⟨58,105⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-6),38⟩,⟨(-30),16⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨(-711183400665625208230),(-711183400665550469434)⟩,⟨2907393513498344743677,2907393513498419482626⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨122818527473377620592,122818527473560518049⟩,⟨6747465625576065265824,6747465625576248163805⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨3171727776490814270784,3171727776491115401190⟩,⟨5497543423015732583227,5497543423016033713970⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨3584605507108748879074,3584605507109057727928⟩,⟨1159231011260688259407,1159231011260997108134⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨1252530414580991111862,1252530414581219748052⟩,⟨(-919130918443447595774),(-919130918443218959653)⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-92133616653549386162),(-92133616653433109228)⟩,⟨(-461492990051204988800),(-461492990051088711834)⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨(-110124279005028570062),(-110124279004984302927)⟩,⟨(-9381247217115634134),(-9381247217071367006)⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨(-5562376545067412504),(-5562376545056574020)⟩,⟨20512268103475712177,20512268103486550661⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨3243212021891946097,3243212021893693062⟩,⟨1386676767253314858,1386676767255061825⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨285594886523833506,285594886524033261⟩,⟨(-450627960749643112),(-450627960749443357)⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-54200763292496125),(-54200763292478563)⟩,⟨(-56345414293918819),(-56345414293901257)⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-10971249010200351),(-10971249010198793)⟩,⟨4603509672852628,4603509672854186⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-286010652741031),(-286010652740847)⟩,⟨2006347635735895,2006347635736081⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨260386308339259,260386308339298⟩,⟨320300837188704,320300837188744⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨96283059367364,96283059367390⟩,⟨30803974165214,30803974165239⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨21127937294647,21127937294666⟩,⟨219547955315,219547955337⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨(-14837554085131103442795441),(-14837554085131100365954041)⟩,⟨(-1926105926929283051476017),(-1926105926929280006007728)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-34009510584549321164106091),(-34009510584549311559445116)⟩,⟨11514390554251491890772079,11514390554251501404967046⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-8910840247382739456288324),(-8910840247382724430656305)⟩,⟨40341695394156507416550282,40341695394156522389613143⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨52827371886289742391073123,52827371886289763954246966⟩,⟨21811830043904752174854555,21811830043904773768699545⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨58859245690270933610730196,58859245690270975719683468⟩,⟨(-48998149281568730462682098),(-48998149281568688322010810)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-6010097915182963314169800),(-6010097915182911697193350)⟩,⟨(-69046906766369665505862385),(-69046906766369613900977352)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-38878943616250330974850002),(-38878943616250288251533140)⟩,⟨(-20636488257610240752597216),(-20636488257610198030086686)⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-17828843723028063358588294),(-17828843723028037489795720)⟩,⟨11547689099878619646786230,11547689099878645517376539⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨1000763958197641340145056,1000763958197653520305583⟩,⟨8320587894439068892133053,8320587894439081071694332⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨2742747303551845573137796,2742747303551850373082236⟩,⟨898169582073919448576516,898169582073924248639250⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨646167455946017852682987,646167455946019772226758⟩,⟨(-658926505753607797912402),(-658926505753605878371745)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨(-77159765460165316505405),(-77159765460164386449414)⟩,⟨(-280993825384623140067315),(-280993825384622210022187)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-89409268419432783518720),(-89409268419432207607444)⟩,⟨(-35427484745334320237152),(-35427484745333744322687)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-31868925669975366663165),(-31868925669974994616925)⟩,⟨12543296885479722755025,12543296885480094802158⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-7806536058494641034150),(-7806536058494412907136)⟩,⟨9916326202833099173252,9916326202833327300115⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-1258974795926228563006),(-1258974795926158795688)⟩,⟨3021667832835979473640,3021667832836049240872⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-766630200889644306364368),(-766630200889605317444442)⟩,⟨(-7851368526903804996083991),(-7851368526903766027765625)⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨569618625565372476408085417,569618625565372486869807861⟩,⟨(-2305610127080045448605608405),(-2305610127080045438130815367)⟩⟩
end hm25_1_1_4
namespace hm25_1_1_5
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
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-22),21⟩,⟨(-18),21⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-32),32⟩,⟨(-32),35⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-46),44⟩,⟨(-44),48⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-62),62⟩,⟨(-62),62⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-7153921737272),(-7153921737254)⟩,⟨(-14410451000630),(-14410451000612)⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-19784532065806),(-19784532065786)⟩,⟨(-22540830726257),(-22540830726231)⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-18303608045483),(-18303608045456)⟩,⟨(-6424618596976),(-6424618596952)⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨(-6104742599986),(-6104742599956)⟩,⟨2692570197281,2692570197313⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-251369142916),(-251369142881)⟩,⟨1343113275616,1343113275650⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨146861167402,146861167440⟩,⟨101590083133,101590083170⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨12345321652,12345321696⟩,⟨(-9859414732),(-9859414682)⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨(-439670308),(-439670256)⟩,⟨(-904099248),(-904099194)⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨(-48133476),(-48133418)⟩,⟨12021648,12021705⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨(-10010),(-9948)⟩,⟨2097056,2097118⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨80759,80826⟩,⟨29312,29376⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨2886,2945⟩,⟨(-2671),(-2614)⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-44),11⟩,⟨(-259),(-205)⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-39),13⟩,⟨(-40),11⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-20),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨2477477356181187485193,2477477356181243809997⟩,⟨170099256316288386587,170099256316344711209⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨5510367704046854719148,5510367704047006317277⟩,⟨(-1071504473680008899327),(-1071504473679857301657)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨4051478624335940076754,4051478624336205713482⟩,⟨(-3426853298130876907131),(-3426853298130611270567)⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨401362667179834347336,401362667180080457676⟩,⟨(-3147957080458798270136),(-3147957080458552159623)⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-973542912816519823964),(-973542912816316294541)⟩,⟨(-893490196682637945143),(-893490196682434415690)⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-372488328839166484967),(-372488328839066734929)⟩,⟨158905443677476939163,158905443677576689178⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨12841454691587636536,12841454691625290876⟩,⟨95527339299345174611,95527339299382828957⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨18797726615504076947,18797726615513545845⟩,⟨615357965968631166,615357965978100064⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨498427744891641886,498427744893229575⟩,⟨(-3130463191481647736),(-3130463191480060048)⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨(-464597926947969972),(-464597926947777211)⟩,⟨(-146048541388053150),(-146048541387860387)⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-36680570737322895),(-36680570737305518)⟩,⟨62492963030519703,62492963030537078⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨7067310296996392,7067310296997791⟩,⟨8668312488732011,8668312488733407⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨1905280203481098,1905280203481262⟩,⟨(-300053587535978),(-300053587535813)⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨217953759067213,217953759067252⟩,⟨(-331577236344624),(-331577236344583)⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-322705651169),(-322705651143)⟩,⟨(-97860228386510),(-97860228386488)⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-6179357552552),(-6179357552535)⟩,⟨(-19576558146650),(-19576558146632)⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨(-828529530223537501847119),(-828529530223535232626573)⟩,⟨10794761170087731505825421,10794761170087733799471440⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨9685289192693775851605115,9685289192693782980045874⟩,⟨24169253810319916628465507,24169253810319923821183118⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨29713697340913422992012262,29713697340913434277099066⟩,⟨4739904214091145285817487,4739904214091156602937706⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨13425143496085220145530514,13425143496085236549399099⟩,⟨(-39711674462879797417635366),(-39711674462879781041581511)⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-39335649778645314145249305),(-39335649778645281799259461)⟩,⟨(-40788177063100549055603979),(-40788177063100516730506957)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-51069086654357029507776245),(-51069086654356989471973415)⟩,⟨8704678478107639710388006,8704678478107679756429082⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-12831620232203156837981254),(-12831620232203123315710226)⟩,⟨30707918686786812622953598,30707918686786846144965176⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨10199949682301407029403979,10199949682301427557174004⟩,⟨12667005733248417684087060,12667005733248438210679262⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨6323420011797487038359580,6323420011797496804580868⟩,⟨(-1509399034708344197196073),(-1509399034708334430500225)⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨429361683010853289145968,429361683010857170859524⟩,⟨(-2227705063588321526720515),(-2227705063588317645118566)⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-590069715384911886015688),(-590069715384910330898708)⟩,⟨(-438010829104253182673292),(-438010829104251627545888)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨(-214870591441807249451848),(-214870591441806479536742)⟩,⟨94708000101088206833550,94708000101088976755727⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-17195151902292409294994),(-17195151902291952433978)⟩,⟨76401019821314081836119,76401019821314538694082⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨14405820230246225944859,14405820230246548053258⟩,⟨24153499796197274697830,24153499796197596805775⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨9151907201733408716449,9151907201733593299000⟩,⟨4991144597967698853594,4991144597967883436350⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨2643896211843323461391,2643896211843377628046⟩,⟨604227965286023165641,604227965286077332379⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-5845472053856469177259678),(-5845472053856438913754194)⟩,⟨1216882611291963960532103,1216882611291994237571881⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-1686512807538474739289684408),(-1686512807538474731326437251)⟩,⟨(-324793163840305165203557535),(-324793163840305157253042315)⟩⟩
end hm25_1_1_5
namespace hm25_1_1_6
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
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-16),19⟩,⟨(-16),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-20),32⟩,⟨(-31),28⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-40),40⟩,⟨(-40),40⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-52),52⟩,⟨(-52),52⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-9289288664993),(-9289288664974)⟩,⟨9162288346002,9162288346020⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-12324444781414),(-12324444781387)⟩,⟨21050567140339,21050567140360⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-171582718939),(-171582718912)⟩,⟨15866323837957,15866323837983⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨3755352383809,3755352383839⟩,⟨4023641695782,4023641695814⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨1124769108067,1124769108099⟩,⟨(-183633865699),(-183633865665)⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨36572146061,36572146101⟩,⟨(-146446088513),(-146446088474)⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-11762469132),(-11762469087)⟩,⟨(-6749522459),(-6749522416)⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨(-582118573),(-582118523)⟩,⟨656773610,656773661⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨26879889,26879941⟩,⟨34942676,34942727⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨1728817,1728874⟩,⟨(-781655),(-781600)⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨(-7855),(-7798)⟩,⟨(-78781),(-78722)⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨(-3460),(-3408)⟩,⟨(-1356),(-1306)⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-212),(-165)⟩,⟨91,137⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-31),15⟩,⟨(-4),42⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨(-176192064413407201614),(-176192064413372370911)⟩,⟨(-1707885684813602226751),(-1707885684813567395892)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-1392290303610924286139),(-1392290303610809159632)⟩,⟨(-3633611988082690848193),(-3633611988082575721414)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-2851484435476318551058),(-2851484435476129722691)⟩,⟨(-2353160515296279988062),(-2353160515296091159666)⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-2223713967773657095281),(-2223713967773489797969)⟩,⟨131706105522701436096,131706105522868733253⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-487426828813461010631),(-487426828813315829953)⟩,⟨799772732740359579579,799772732740504760259⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨166229166487831941030,166229166487905079448⟩,⟨238125194223238487857,238125194223311626290⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨65746828456135839138,65746828456162692330⟩,⟨(-24168361203320982155),(-24168361203294128965)⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨(-2747215134983260193),(-2747215134976461684)⟩,⟨(-13595016620250023951),(-13595016620243225444)⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-2364711778743719721),(-2364711778742551031)⟩,⟨209317019227925401,209317019229094092⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨(-16382003107441623),(-16382003107294412)⟩,⟨370110767114827565,370110767114974773⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨54133193804564136,54133193804578334⟩,⟨14210669724721527,14210669724735723⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨4947252408665728,4947252408666886⟩,⟨(-7230557633940022),(-7230557633938862)⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-670890233222747),(-670890233222622)⟩,⟨(-1374711900320971),(-1374711900320844)⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-305928347038506),(-305928347038468)⟩,⟨(-86248346540231),(-86248346540192)⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-75030327311365),(-75030327311339)⟩,⟨24551516767299,24551516767322⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-13509206023758),(-13509206023739)⟩,⟨9683085935583,9683085935602⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨6526471273185250821823306,6526471273185252241635908⟩,⟨157411561951918931816784,157411561951920335902671⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨14263834386942104097027037,14263834386942108570135300⟩,⟨(-6642412602384930239018067),(-6642412602384925803018442)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨1804504093552175035919898,1804504093552182108165171⟩,⟨(-18172572299039787559147097),(-18172572299039780502479829)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-24758018250943562588005599),(-24758018250943552277692122)⟩,⟨(-6597544173511234755915852),(-6597544173511224425422530)⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-23311965114081023427155026),(-23311965114081002877429847)⟩,⟨26025023709836483669139399,26025023709836504229802405⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨8010063588848148298131150,8010063588848173991930015⟩,⟨31259401136036721558792995,31259401136036747245631629⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨20010884604029552318014686,20010884604029574033299197⟩,⟨6269517717922245802587197,6269517717922267518578110⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨7368386881031419907333064,7368386881031433328328094⟩,⟨(-7305670186990060822476282),(-7305670186990047400905565)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-1436934500444401912261950),(-1436934500444395473301478)⟩,⟨(-3949291454990690845881559),(-3949291454990684407220489)⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-1483098298302785439600626),(-1483098298302782863096939)⟩,⟨(-95516949380089077924743),(-95516949380086501339839)⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-234413082507646084727558),(-234413082507645053227878)⟩,⟨427594829973851435198146,427594829973852466686097⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨84071623736552333860924,84071623736552858592082⟩,⟨133405718930078573807384,133405718930079098535470⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨53026759309830194699594,53026759309830499889100⟩,⟨3477122387475517967215,3477122387475823158909⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨14711449376661497617727,14711449376661723555362⟩,⟨(-12406776721759550991071),(-12406776721759325053315)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨2336307581729171246339,2336307581729292084103⟩,⟨(-6784459437570053695813),(-6784459437569932858230)⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨102148814818905053665,102148814818938861664⟩,⟨(-1869668406212460395982),(-1869668406212426588048)⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨1151176611368828275881510,1151176611368847721243318⟩,⟨3580866832278974958509034,3580866832278994396670102⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-142691390608142652445763017),(-142691390608142647410804152)⟩,⟨1025169478974946686344314059,1025169478974946691389009962⟩⟩
end hm25_1_1_6
namespace hm25_1_1_7
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
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-18),16⟩,⟨(-19),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-32),29⟩,⟨(-32),28⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-44),44⟩,⟨(-44),44⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-56),56⟩,⟨(-56),56⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨8067485042905,8067485042924⟩,⟨4144400812731,4144400812749⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨16635391668593,16635391668618⟩,⟨3526588624644,3526588624667⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨10574101333139,10574101333163⟩,⟨(-3456680662540),(-3456680662517)⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨1811948267694,1811948267722⟩,⟨(-3443940211768),(-3443940211739)⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-396815155288),(-396815155260)⟩,⟨(-711564245320),(-711564245293)⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨(-108628823040),(-108628823008)⟩,⟨12629290878,12629290911⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-1441381484),(-1441381449)⟩,⟨9872853995,9872854033⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨620761570,620761608⟩,⟨214170668,214170710⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨16218269,16218308⟩,⟨(-29401127),(-29401089)⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨(-1109287),(-1109243)⟩,⟨(-966641),(-966602)⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨(-53378),(-53334)⟩,⟨32438,32480⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨258,301⟩,⟨2918,2961⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨134,175⟩,⟨72,113⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-6),35⟩,⟨(-21),17⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨(-979508923485924037456),(-979508923485901121570)⟩,⟨275469853160539038403,275469853160561954206⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-1983279429720223649522),(-1983279429720149599002)⟩,⟨1188229158125792137678,1188229158125866188078⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-1080036781592686194500),(-1080036781592574790733)⟩,⟨1925647813656495436022,1925647813656606839824⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨325287591442316799709,325287591442417473620⟩,⟨1300226579616002457097,1300226579616103131108⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨534105364521355641428,534105364521441222392⟩,⟨196248465431433045877,196248465431518626826⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨122343226130673527667,122343226130720662968⟩,⟨(-129981732429278610950),(-129981732429231475656)⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨(-23580856860831289804),(-23580856860814611009)⟩,⟨(-36713851812756254165),(-36713851812739575367)⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨(-7963330857658478586),(-7963330857654292648)⟩,⟨3666982626409998185,3666982626414184118⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨500287653058361826,500287653059088099⟩,⟨1439421468423753939,1439421468424480212⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨235939011839182471,235939011839275820⟩,⟨(-51804807323414311),(-51804807323320962)⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-643177755902582),(-643177755893225)⟩,⟨(-37046012724404378),(-37046012724395017)⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-5596152093632659),(-5596152093631812)⟩,⟨(-1812923280263308),(-1812923280262462)⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-759541369682313),(-759541369682222)⟩,⟨710219849137914,710219849138006⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨6968084068101,6968084068132⟩,⟨218131495404303,218131495404332⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨32124119199311,32124119199331⟩,⟨44134557018901,44134557018923⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨9301717642700,9301717642718⟩,⟨6821341912452,6821341912469⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨(-95728867598089545211268),(-95728867598088802856398)⟩,⟨(-3372867643280906390804871),(-3372867643280905639881209)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-3839299595575333433206770),(-3839299595575331074659026)⟩,⟨(-7189199524935931565790894),(-7189199524935929189356890)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-9492729103661997843019604),(-9492729103661994076518682)⟩,⟨(-377588006672423667064537),(-377588006672419894498498)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-2598970915886054975943824),(-2598970915886049426594536)⟩,⟨13169420671497839385454612,13169420671497844922728602⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨14617189008975498219228578,14617189008975509355195625⟩,⟨11283398058985444667835998,11283398058985455799132080⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨16283086765381597682631623,16283086765381611707329170⟩,⟨(-5629954131845507556972308),(-5629954131845493528336006)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨2376471439768057994193275,2376471439768069946187965⟩,⟨(-11073312306393060058763206),(-11073312306393048107429679)⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-4389217565402058133229501),(-4389217565402050692099908)⟩,⟨(-3596449481615236142506043),(-3596449481615228701580335)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-2082815565673255390334112),(-2082815565673251798774903)⟩,⟨1041345995609197317055875,1041345995609200908768052⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨51535995078419008744889,51535995078420452988220⟩,⟨832881281819831712230960,832881281819833156426552⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨259143432841956608736120,259143432841957187291853⟩,⟨98834831890990848600877,98834831890991427165395⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨68860509656123611846391,68860509656123912007173⟩,⟨(-59130159772189471366762),(-59130159772189171205211)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-2791225017149315092621),(-2791225017149138535032)⟩,⟨(-30782218164023604483338),(-30782218164023427926956)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-8579651762719170300895),(-8579651762719038055301)⟩,⟨(-7334966409922020871003),(-7334966409921888625367)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-4176697505796331926566),(-4176697505796266302137)⟩,⟨(-691205287979761097533),(-691205287979695472974)⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-1100710477123555562724),(-1100710477123536985340)⟩,⟨127720243667521117512,127720243667539694931⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨1856297558219070454976346,1856297558219081078570157⟩,⟨(-817762823554120053458476),(-817762823554109426704450)⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨532671177676222560712788927,532671177676222563451932631⟩,⟨46108590124212731184257821,46108590124212733917266079⟩⟩
end hm25_1_1_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock25_11
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm25_1_1_8
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
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-24),21⟩,⟨(-16),27⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-43),43⟩,⟨(-43),43⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨861676183919,861676183936⟩,⟨(-5448869053761),(-5448869053744)⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-1157989798948),(-1157989798927)⟩,⟨(-10308074515190),(-10308074515171)⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-4090609945207),(-4090609945188)⟩,⟨(-5462989756003),(-5462989755985)⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨(-2380970497123),(-2380970497099)⟩,⟨(-356850528185),(-356850528162)⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-334197316792),(-334197316768)⟩,⟨384758286092,384758286118⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨31782844958,31782844987⟩,⟨61613856966,61613856994⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨6252411133,6252411162⟩,⟨(-1470817209),(-1470817180)⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨(-26121805),(-26121777)⟩,⟨(-429127623),(-429127594)⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨(-22280499),(-22280469)⟩,⟨(-2079341),(-2079307)⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨(-282969),(-282936)⟩,⟨957397,957431⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨36128,36170⟩,⟨23496,23536⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨1738,1779⟩,⟨(-1117),(-1084)⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-11),26⟩,⟨(-146),(-109)⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-25),12⟩,⟨(-27),11⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨227359884076426880794,227359884076439950272⟩,⟨476125968365471891230,476125968365484960739⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨786794745958991330976,786794745959031603344⟩,⟨908670678829485118849,908670678829525391256⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨1090559076453108451211,1090559076453164090330⟩,⟨376408882170586664842,376408882170642303915⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨641048964971322172596,641048964971376968481⟩,⟨(-294887916103751527527),(-294887916103696731693)⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨47259258197446015781,47259258197489898396⟩,⟨(-298771883119306298232),(-298771883119262415604)⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-81901946142870778962),(-81901946142844906881)⟩,⟨(-50088433228463265640),(-50088433228437393555)⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨(-16745772686414216410),(-16745772686404873583)⟩,⟨16888263636004630280,16888263636013973103⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨2987169462382624136,2987169462384920903⟩,⟨3819512908793402683,3819512908795699451⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨715598521914763594,715598521915159944⟩,⟨(-469604156360907440),(-469604156360511089)⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨(-63217265707900152),(-63217265707849029)⟩,⟨(-122460556759833334),(-122460556759782209)⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-20557504048847648),(-20557504048842429)⟩,⟨6167518816445238,6167518816450454⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-91587075485558),(-91587075485054)⟩,⟨3454767487686541,3454767487687045⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨536433423945462,536433423945526⟩,⟨307920572529349,307920572529416⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨123669722671570,123669722671595⟩,⟨(-43561267662115),(-43561267662089)⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨19422109662551,19422109662568⟩,⟨(-26712964295246),(-26712964295225)⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨2180799719891,2180799719910⟩,⟨(-6656272720241),(-6656272720223)⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨(-1521003464240919405131984),(-1521003464240919058377116)⟩,⟨123262173642242573139752,123262173642242916002173⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-3158360230645504660084094),(-3158360230645503559198189)⟩,⟨1915582437373322800699405,1915582437373323894133462⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨84183593999868541896134,84183593999870295836785⟩,⟨4323622728685922334296666,4323622728685924086414540⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨6102174534539146150962910,6102174534539148741314601⟩,⟨793135977881053378530836,793135977881055974988923⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨4710376108348077888264080,4710376108348083134201821⟩,⟨(-7122614559022398685570274),(-7122614559022393437995466)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-3244831077766239683271314),(-3244831077766233027392998)⟩,⟨(-7365811607238131853343417),(-7365811607238125199365834)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-5314098728522780194677406),(-5314098728522774488129488)⟩,⟨(-636294730838900363116319),(-636294730838894656138017)⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-1495318061555654459556207),(-1495318061555650887620278)⟩,⟨2266491511725308264850597,2266491511725311836830549⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨617129341274432708905877,617129341274434439560126⟩,⟨945404910029166974567871,945404910029168705158451⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨402763465965768049069643,402763465965768746815402⟩,⟨(-76597696184578994796343),(-76597696184578297027428)⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨31095479164993499429333,31095479164993779469186⟩,⟨(-134482011362263582567804),(-134482011362263302533014)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨(-34545803995592339570281),(-34545803995592192614915)⟩,⟨(-29938136619997791240533),(-29938136619997644285059)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-15255410870042103634844),(-15255410870042013470482)⟩,⟨3836082697331024013341,3836082697331114178210⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-3000796403209440189027),(-3000796403209374260240)⟩,⟨4955309569413451460012,4955309569413517388725⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨7948080068034709121,7948080068065947923⟩,⟨2185524982807686161775,2185524982807717400505⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨161663849647828891046,161663849647839607630⟩,⟨550541955916711797137,550541955916722513710⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-472637240831807026294180),(-472637240831801981069773)⟩,⟨(-830928993313816052005850),(-830928993313811007930622)⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨8309651589987752599623134,8309651589987753897659360⟩,⟨(-241517735999194315801273015),(-241517735999194314499948664)⟩⟩
end hm25_1_1_8
namespace hm25_1_1_9
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
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-18),18⟩,⟨(-18),18⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-2944064042679),(-2944064042662)⟩,⟨477774669954,477774669970⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-5106101999692),(-5106101999675)⟩,⟨2358115565822,2358115565839⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-2105340048474),(-2105340048456)⟩,⟨3068869587140,3068869587160⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨245897132160,245897132182⟩,⟨1300951563079,1300951563097⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨264367445120,264367445137⟩,⟨102011124260,102011124277⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨26169388869,26169388887⟩,⟨(-29006141380),(-29006141357)⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-2096730455),(-2096730433)⟩,⟨(-3018677205),(-3018677180)⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨(-224864049),(-224864025)⟩,⟨109692604,109692628⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨4144801,4144829⟩,⟨12591147,12591173⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨596053,596079⟩,⟨(-85295),(-85267)⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨3392,3425⟩,⟨(-26264),(-26231)⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨(-1121),(-1089)⟩,⟨(-687),(-659)⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-89),(-59)⟩,⟨19,46⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-16),14⟩,⟨(-6),19⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨198377623305587919107,198377623305594313717⟩,⟨(-140683659786474947227),(-140683659786468552632)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨350685798399569333426,350685798399588203534⟩,⟨(-430753932295538632171),(-430753932295519762070)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨81955362353255776957,81955362353279719707⟩,⟨(-529563047315878459536),(-529563047315854516755)⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-191099273780070464776),(-191099273780043133903)⟩,⟨(-269295036560884515008),(-269295036560857184116)⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-142827852729996046894),(-142827852729975822463)⟩,⟨5484894091724748171,5484894091744972597⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-15418421626896351917),(-15418421626884150163)⟩,⟨43229410001970271292,43229410001982473046⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨9747715152581982791,9747715152586702813⟩,⟨6144383356685550036,6144383356690270055⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨1489402151403464918,1489402151404623166⟩,⟨(-1861289367885666783),(-1861289367884508536)⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-314484302321943496),(-314484302321745296)⟩,⟨(-289330774894520015),(-289330774894321817)⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨(-51753589176059638),(-51753589176034352)⟩,⟨46969934205428946,46969934205454233⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨5922639711030221,5922639711032787⟩,⟨9330120968098603,9330120968101169⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨1743996421669560,1743996421669822⟩,⟨(-464509582009339),(-464509582009078)⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨72397403025472,72397403025515⟩,⟨(-318916341898380),(-318916341898336)⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-42119556424453),(-42119556424431)⟩,⟨(-55936457464350),(-55936457464329)⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-16884383534821),(-16884383534803)⟩,⟨(-5515002542421),(-5515002542403)⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-3780764428865),(-3780764428849)⟩,⟨(-1754152301),(-1754152285)⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨81562333434599196285690,81562333434599336835312⟩,⟨608000093598605699712418,608000093598605841755030⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨840129750240621015954059,840129750240621465020058⟩,⟨1228319141465078976463171,1228319141465079428258352⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨1744324775574823320000172,1744324775574824041748315⟩,⟨(-137558044308561280080994),(-137558044308560557977591)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨159485028645015311622135,159485028645016386719623⟩,⟨(-2502359152008130456031763),(-2502359152008129383610034)⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-3061436979009555014913064),(-3061436979009552828892329)⟩,⟨(-1717234739732084041803594),(-1717234739732081856237883)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-2937988925688314462908446),(-2937988925688311675519281)⟩,⟨1593705062802402484920137,1593705062802405273104859⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-60492324885329956907556),(-60492324885327554855504)⟩,⟨2247382139570685894547750,2247382139570688296376742⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨1024477782254277617325723,1024477782254279125555676⟩,⟨533254435400563074360018,533254435400564582593991⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨374312715445455012592076,374312715445455744198155⟩,⟨(-310851007226989010413653),(-310851007226988278786489)⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-55318136232184336296528),(-55318136232184041298758)⟩,⟨(-170286437072436972671545),(-170286437072436677683133)⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-60813742544122928118295),(-60813742544122809427094)⟩,⟨(-5492832871199879389029),(-5492832871199760695454)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨(-10989161723053665880465),(-10989161723053603409510)⟩,⟨17264599544554267176898,17264599544554329647587⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨2786109433081478704283,2786109433081519892343⟩,⟨6548066672165112870027,6548066672165154057937⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨2452635289558503008083,2452635289558531399521⟩,⟨984335785808601460573,984335785808629852066⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨988241195664510796610,988241195664525153705⟩,⟨(-170941220315577646550),(-170941220315563289430)⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨237149538982605449453,237149538982610770307⟩,⟨(-116232526820481102421),(-116232526820475781566)⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-325998366208086735556053),(-325998366208084621841141)⟩,⟨231678492621187848583747,231678492621189962638151⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-97076029236493680513749456),(-97076029236493679964222654)⟩,⟨1704896704569563678869169,1704896704569564226862943⟩⟩
end hm25_1_1_9
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock27_0
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm27_0_0_2
noncomputable def s0_0 : CBox := ⟨⟨9459503815930741469036459558,9459503815930748439498591679⟩,⟨(-14979897689072733592590476858),(-14979897689072726622899291693)⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨14058311195589649001050736905,14058311195589667742097333719⟩,⟨(-48205346387407624349368048722),(-48205346387407605609741046360)⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-19531691652678861235747851489),(-19531691652678841480015848443)⟩,⟨(-72140640015633226364456212823),(-72140640015633206608370216872)⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-77163162399331656476895904184),(-77163162399331646138227089355)⟩,⟨(-43326359567728824330576944935),(-43326359567728813989035848017)⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-80113105818364274289549152860),(-80113105818364269368930479855)⟩,⟨43441506049588295314102542528,43441506049588300233587847247⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨9033094055066197170117313388,9033094055066198864109686401⟩,⟨83697230565303854460225590602,83697230565303856153408611037⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨69643543770766536380118696221,69643543770766537006309986302⟩,⟨10809674378485232694670815489,10809674378485233322029453408⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨17649021197712637634866328934,17649021197712637882368139283⟩,⟨(-50548393483003144865909160962),(-50548393483003144619177615802)⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-32387313625324351865640737462),(-32387313625324351774359598053)⟩,⟨(-17272382226273066942130828860),(-17272382226273066850509385625)⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-13900196983148493523549093832),(-13900196983148493492992319229)⟩,⟨17556380491190362717679813919,17556380491190362748165075784⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨7094756083743671498815502203,7094756083743671508234415189⟩,⟨9486546750964759199626852408,9486546750964759209051217553⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨5029790617789301302930725802,5029790617789301305663087055⟩,⟨(-1299047974844567150194202740),(-1299047974844567147540673214)⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨537365616860002233338191729,537365616860002233983963664⟩,⟨(-1658182184839834165302831637),(-1658182184839834164580151274)⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-176019558336642850814067106),(-176019558336642850657352595)⟩,⟨(-340822386112029129298418159),(-340822386112029129125552503)⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-33496625414393631337874607),(-33496625414393631311625371)⟩,⟨(-20211818316523875548852461),(-20211818316523875529723392)⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-627454236073399737626237),(-627454236073399736205412)⟩,⟨(-145218330248603786516399),(-145218330248603786090282)⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨37999358800577271910557916491,37999358800577308534701877266⟩,⟨47363491238475006897023201667,47363491238475043525417380803⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨142786321851478673282402725693,142786321851478830102803397860⟩,⟨102226097278040457289926512007,102226097278040614118432324887⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨270980513060209627306949197960,270980513060210033197816033570⟩,⟨23132350493686726928682820042,23132350493687132817431681175⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨262654254389826965419952900226,262654254389827750969445343345⟩,⟨(-218300501754725700496280617826),(-218300501754724914965991066728)⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-43437977771861170086227669490),(-43437977771859411485555622832)⟩,⟨(-378362050735945948082285989396),(-378362050735944189472547293643)⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-375113869098416133744290294798),(-375113869098412834312753420483)⟩,⟨(-111493964576887396790412814152),(-111493964576884097351679835022)⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-200948649986605849382568352461),(-200948649986601055661078012122)⟩,⟨320241894434380466847806888556,320241894434385260555164627902⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨254358832788174387117169016896,254358832788179894175824323834⟩,⟨237037275746324150963387029645,237037275746329658036192352603⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨242352275036563233145184308725,242352275036568166384089768226⟩,⟨(-187708140118799854497780329815),(-187708140118794921270549952756)⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-118000068684829926033208965753),(-118000068684826467132960564282)⟩,⟨(-231607988903481463168544290363),(-231607988903478004260378771808)⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-207553800601700878236382008384),(-207553800601698955258541582965)⟩,⟨43031393228634754409171305508,43031393228636677384442458553⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-31397994153829345698702381679),(-31397994153828511657032484880)⟩,⟨162633076120914632395126602369,162633076120915466433607311248⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨89059595838049087766059013713,89059595838049402307549865716⟩,⟨84521169790939628396475205086,84521169790939942942670162002⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨83956758269835232410769261036,83956758269835372866049412450⟩,⟨(-2527286981066614102365945737),(-2527286981066473646629076976)⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨40950474901425581729256721675,40950474901425630733823244680⟩,⟨(-26523035217726097563977073582),(-26523035217726048560805006835)⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨10513561175864433638863276308,10513561175864444439798208785⟩,⟨(-12032113196644394676132387743),(-12032113196644383875876081194)⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-97692620641729719082413448970),(-97692620641729719040212442828)⟩,⟨5061176294888637656983412381,5061176294888637688510475482⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-269734144320417258324324466275),(-269734144320417258181365346127)⟩,⟨93580611422657796885167309872,93580611422657797007420048437⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-284842830588321436502829350672),(-284842830588321436230613716504)⟩,⟨349706744840503416874031761994,349706744840503417151905125515⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨69121372237381796080327962738,69121372237381796520813845305⟩,⟨581231502218457995775388956822,581231502218457996268277504896⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨620364053782600457222096722953,620364053782600458121296158670⟩,⟨288581083416702570865985212529,288581083416702571738612958151⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨543306459598226271949939372688,543306459598226273702930733409⟩,⟨(-511521407018499641321212922174),(-511521407018499639589590073650)⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-371981487232311187318813661024),(-371981487232311183811781454675)⟩,⟨(-676365543922389004059634054682),(-676365543922389000507816081312)⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-723483449924906606828034612739),(-723483449924906599766393160453)⟩,⟨246834226648705073914319917295,246834226648705080927812743556⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨131273920670699813067567795721,131273920670699826433672726026⟩,⟨717004544153078638532695630796,717004544153078651941372517503⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨671000428851742506770872638969,671000428851742531857330606497⟩,⟨(-4087910570374819941347478553),(-4087910570374794885900294534)⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨147078295105686507102041792924,147078295105686558670123062788⟩,⟨(-577346734633564967226123211791),(-577346734633564915647057210893)⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-407736934569488420664563920048),(-407736934569488303527236466270)⟩,⟨(-301506407389055772783134827699),(-301506407389055655631422225217)⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-380004736449555136695851692202),(-380004736449554931554292527907)⟩,⟨146664708043846514332710686728,146664708043846719451455850632⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-120139834959833076285902208212),(-120139834959832736233598723438)⟩,⟨272858054297154011526462765549,272858054297154351576184291860⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨22924627421235753533585724000,22924627421236049014981794580⟩,⟨180314040636132570533224005189,180314040636132866022071936008⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨23877631465380035979312596761,23877631465380140961919140044⟩,⟨56178677049169419323246129316,56178677049169524309607446144⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨27870437942136419702126242595,27870437942136605233043782280⟩,⟨(-95664706966796786436414209019),(-95664706966796600889557711659)⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨1928712353812952365022429444,1928712353813462830568580523⟩,⟨(-292949035416609369724645711789),(-292949035416608859228343886236)⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-239339750669532394606968074882),(-239339750669531825794156928757)⟩,⟨(-403043670452975931930703566743),(-403043670452975363126453063847)⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨(-598422036104869848180599788464),(-598422036104869514156083925198)⟩,⟨(-151975286571478017006071448868),(-151975286571477683060313168604)⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-535041784643218331476816649865),(-535041784643218144564298385903)⟩,⟨499519139110930582585520485645,499519139110930769538662833510⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨282436244587015808036495148720,282436244587015891805596957706⟩,⟨758696061033069997136515070661,758696061033070080938050558152⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨848303440384832590771193759045,848303440384832632340127597730⟩,⟨(-79479536700679668191585504365),(-79479536700679626694732059562)⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨76933537566082654758635199225,76933537566082676536119104505⟩,⟨(-859845368206205565174525283530),(-859845368206205543315579263261)⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨(-820595548381164991216991349948),(-820595548381164980100732086659)⟩,⟨(-206744843233219340357452686665),(-206744843233219329317959458814)⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨(-337756335796058648281595486050),(-337756335796058642961121991066)⟩,⟨727574267735444487223141670089,727574267735444492603815440975⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨557046995078958416250894066175,557046995078958418802266526267⟩,⟨474442125827076063865543524570,474442125827076066393585174568⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨569480832489463313291134277208,569480832489463314539353408616⟩,⟨(-284119326730960650644320130394),(-284119326730960649426275913459)⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨59538773279998709766408009370,59538773279998710358585663942⟩,⟨(-515830798193175501006036785604),(-515830798193175500362165780311)⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-237273262720962920034570364727),(-237273262720962919699792519739)⟩,⟨(-302236753928081837062400107832),(-302236753928081836721859739354)⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-220261618639807087977264150792),(-220261618639807087814276829720)⟩,⟨(-84764508724594577464119231199),(-84764508724594577319313636666)⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-79225334991342860856274258734),(-79225334991342860810213934906)⟩,⟨(-7394763773859068552870090528),(-7394763773859068516096182251)⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨11927124282486538780368518024,11927124282487336587919952269⟩,⟨95868241442095346626557275802,95868241442096144419761115793⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨113835946287619453225285401127,113835946287623026523220549835⟩,⟨257240386447052820802328175553,257240386447056394072726995993⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨371010060798028288720812096064,371010060798038033458120804512⟩,⟨242205849593629763419551794269,242205849593639508164948567417⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨555961319137756797424424282915,555961319137776693955021011858⟩,⟨(-147208500012224439227740680557),(-147208500012204542625052608376)⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨166651401258819692433131383935,166651401258867335670975285278⟩,⟨(-657268630059388950416784988857),(-657268630059341307217109926533)⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-633369186313929419645878898961),(-633369186313833079061687022293)⟩,⟨(-410486558723592494566228732475),(-410486558723496154011894209697)⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨(-562501372042097916079299587829),(-562501372041946722566938263216)⟩,⟨577662761433286794321951929685,577662761433437987903639428384⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨523102515440603263708470042835,523102515440791959281036893366⟩,⟨648179628449183571338848744404,648179628449372266830748422712⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨697300401622893112306251531940,697300401623078077414911290070⟩,⟨(-459704305032393770772349839394),(-459704305032208805584714930646)⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨(-357737031105662499728982337102),(-357737031105519957663933763991)⟩,⟨(-730523045338725032940426310053),(-730523045338582490940315156227)⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-744856051493223014869900401672),(-744856051493135534983490897635)⟩,⟨183818701421178840226223882447,183818701421266320139244501053⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-76741131898948974199527481127),(-76741131898907166817190106308)⟩,⟨690376958359685284366043217547,690376958359727091782131776022⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨470391996604356583326994225331,470391996604373606841012463897⟩,⟨358622659153248142700357714002,358622659153265166153637232276⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨449399266862661328922404440462,449399266862669493159573760181⟩,⟨(-68781296789942246078826831522),(-68781296789934081848356217156)⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨219185827638528954276881799797,219185827638531914497616934622⟩,⟨(-185151879526150700299381258657),(-185151879526147740056516064216)⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨54602384314748587048738754612,54602384314749245609061974419⟩,⟨(-81475898690570414247823765179),(-81475898690569755676129274590)⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨(-2987667664646483631153557623),(-2987667664646483606907948400)⟩,⟨(-37067251228523226082444597680),(-37067251228523226054234732101)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-42350346828814319995558071149),(-42350346828814319900184898785)⟩,⟨(-100367565350156709712859706359),(-100367565350156709609796524121)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-149462502267987135000966320244),(-149462502267987134776173670389)⟩,⟨(-91428466663495570189493054232),(-91428466663495569966672018298)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-224322950445875793727656081572),(-224322950445875793289522351859)⟩,⟨79153182879028300983030017288,79153182879028301403335484312⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-40066904352592649446702976446),(-40066904352592648529397663585)⟩,⟨295715682587544795668524441469,295715682587544796594111073874⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨316513078838297827242977040312,316513078838297829277309152744⟩,⟨153595183588450272082802398836,153595183588450274123713225044⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨236487937003084197893665969606,236487937003084202453944189923⟩,⟨(-311482337273125039502406920776),(-311482337273125034954123427456)⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-298788421292394790572799521830),(-298788421292394780615958538183)⟩,⟨(-287437844683427903862239085378),(-287437844683427893894432890469)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-319752789174506133613300208915),(-319752789174506111993521420333)⟩,⟨279687465448060773839680733592,279687465448060795452497315157⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨240790851152752903243971522405,240790851152752955292249903707⟩,⟨348712546719025612557702674290,348712546719025664608483434767⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨378293605063366080974941476562,378293605063366236900671262016⟩,⟨(-160236951831281549114995406901),(-160236951831281393189032334686)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨(-18949830043353334202890305273),(-18949830043352853517378574294)⟩,⟨(-381607238573679602361392508566),(-381607238573679121675418833662)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-291817885577943998025575887151),(-291817885577943022843311836380)⟩,⟨(-158252540368580411563677444129),(-158252540368579436384337837054)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-246612192140940539224338840142),(-246612192140938742876782573682)⟩,⟨75753839365069690004287298694,75753839365071486351396543449⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-109006230707936452076679425845),(-109006230707934822189579692506)⟩,⟨121873964895952893206734498408,121873964895954523095579970573⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-24538654056572578510670414254),(-24538654056571989915441784098)⟩,⟨50283600824324321749648647692,50283600824324910345851715615⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-6849003478050526790989210528),(-6849003477877060615363642557)⟩,⟨78713147824242811750806318,78713147997708987571132856⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-22919455250350083972510157251),(-22919455250350083488872272744)⟩,⟨(-3819909208391680864530283927),(-3819909208391680382533144364)⟩⟩
end hm27_0_0_2
namespace hm27_0_0_3
noncomputable def s0_0 : CBox := ⟨⟨2601799532195123657278799807,2601799532195124867909840880⟩,⟨1643396448725580920766859458,1643396448725582131529828837⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨8211664074113644681830213114,8211664074113647876242302232⟩,⟨2403888648050531799577091745,2403888648050534994227492396⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨11834556528888181783598797757,11834556528888185030307839106⟩,⟨(-3168513042209966077260043342),(-3168513042209962830605561876)⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨6759527315411059074250007481,6759527315411060679546158912⟩,⟨(-11887361422163943850875491195),(-11887361422163942246010769716)⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-6093481735326700752422913912),(-6093481735326700045133334467)⟩,⟨(-11475346257079215217325534550),(-11475346257079214509887859403)⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-10770313329976418418654003542),(-10770313329976418199433921524)⟩,⟨1024978965740490341019796211,1024978965740490560343990018⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-1353556151929150354276284706),(-1353556151929150282865643651)⟩,⟨7841508419764124146348929058,7841508419764124217638557916⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨4832087509668128882644623330,4832087509668128906656008064⟩,⟨1804418316322860930323999498,1804418316322860954395318738⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨1438333879978137015736184612,1438333879978137023106869795⟩,⟨(-2536264143649297530986702337),(-2536264143649297523630877700)⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-1076619362313643758587707063),(-1076619362313643756628043709)⟩,⟨(-906390056945110592268028121),(-906390056945110590310905414)⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-458823353160560802617519244),(-458823353160560802157982583)⟩,⟨319734098153075146380774009,319734098153075146841256000⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨37022211447070299883768475,37022211447070299975359336⟩,⟨168012330981178116233865102,168012330981178116330004646⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨34580321722943129105617061,34580321722943129122842215⟩,⟨12613459463099724299809187,12613459463099724314372671⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨4039266368874184608360714,4039266368874184610743879⟩,⟨(-1917192890968498233605086),(-1917192890968498231511297)⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨105888656703067445962575,105888656703067446081394⟩,⟨(-166385371098305008397082),(-166385371098305008228737)⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨187208378827852541030,187208378827852541725⟩,⟨(-784509830461172031563),(-784509830461172029205)⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-16494118972688540893261492950),(-16494118972688528139204545483)⟩,⟨13231609152450906686590363769,13231609152450919439151505199⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-35283885195874608388488395641),(-35283885195874554327867854245)⟩,⟨49232370247933500883477423217,49232370247933554941270132372⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-7950147262930390347514412562),(-7950147262930253106702412307)⟩,⟨91695707249672190469796721447,91695707249672327711320412898⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨71604484183129296763672167480,71604484183129554687112235799⟩,⟨86590017012632188912244522236,86590017012632446842071881404⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨119990038515793334464800152296,119990038515793891316685624255⟩,⟨(-13306419667935188467521796837),(-13306419667934631618493033049)⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨34370138429257224085812163448,34370138429258220429742171486⟩,⟨(-113432360391951988095421079459),(-113432360391950991753750917010)⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-91584076175946408705746922721),(-91584076175945036283216276229)⟩,⟨(-58315955177572515538059243244),(-58315955177571143111396075302)⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-64643372783057198545321526990),(-64643372783055710526010117915)⟩,⟨68316512113142894718679267125,68316512113144382734130346842⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨47083071119364028993238095616,47083071119365280738527642315⟩,⟨61820624059308808772812315584,61820624059310060521055212105⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨55066442511201814509297045249,55066442511202636338154705008⟩,⟨(-27501412954750560585795023573),(-27501412954749738758780377323)⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-9178496233264029395072428193),(-9178496233263602755569860011)⟩,⟨(-45947016925301738235409827978),(-45947016925301311595371317076)⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-33602263440455434437008425089),(-33602263440455261663726635315)⟩,⟨(-6694272931780834990037520101),(-6694272931780662216090078296)⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-16535271503463487530596415835),(-16535271503463426067202164048)⟩,⟨17276476644224126220627098292,17276476644224187683127237304⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨430281592565799296255233474,430281592565825358637359137⟩,⟨15555379809588072714865088361,15555379809588098777162494237⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨4733041908318034362392099450,4733041908318043130121454209⟩,⟨7322936541228960640308293687,7322936541228969408277149969⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨2109899289673592517870504084,2109899289673594412293217226⟩,⟨1844022811428862380460821853,1844022811428864274997683629⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-2643860139016029567841799570),(-2643860139016029551347713562)⟩,⟨(-51070120149891558946459674024),(-51070120149891558924236031410)⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-48562940153157653269576885142),(-48562940153157653205930000178)⟩,⟨(-140128553106338752579817272813),(-140128553106338752505114725654)⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-179246108481746988027639494225),(-179246108481746987884572833534)⟩,⟨(-146268328982036769579889809901),(-146268328982036769439774171546)⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-292701003496136799745862352333),(-292701003496136799496826897026)⟩,⟨34313298703986407685499722074,34313298703986407907400506048⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-142601863219519793282146561856),(-142601863219519792852943452063)⟩,⟨304522555455629633690641498372,304522555455629634133147629584⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨243270971488083304483924014382,243270971488083305309878381251⟩,⟨260163604271316792256308547396,260163604271316793092935337756⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨312927536712930087627456819279,312927536712930089265144748576⟩,⟨(-170405541416714191767075118138),(-170405541416714190150830195145)⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-108313009935884794141494997105),(-108313009935884791027201121719)⟩,⟨(-322403995497380571165824615085),(-322403995497380568029373148883)⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-307077880256196361586601656659),(-307077880256196355860666658488)⟩,⟨54678771738282441952594741729,54678771738282447659729537887⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨392740488992244201802328276,392740488992254480772821110⟩,⟨275921542683110806114617770370,275921542683110816406704618715⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨228077678736267884010097981553,228077678736267904357006691554⟩,⟨59099834206353470519244813830,59099834206353490861748909903⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨115464508642828769221084525251,115464508642828813747792980388⟩,⟨(-155091450911978150428003476232),(-155091450911978105907055059690)⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-53839482056223406187080913986),(-53839482056223330594336798105)⟩,⟨(-140430461885061830759252005540),(-140430461885061755157749274143)⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-98108480058457005267010223201),(-98108480058456883073664204771)⟩,⟨(-43344394104795733344823041492),(-43344394104795611150499024460)⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-63696424349612687267915586888),(-63696424349612582911092645699)⟩,⟨8067046903988840963872415585,8067046903988945317953205481⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-19657587204233221851381278245),(-19657587204233185116099176984)⟩,⟨8353792036297173849286919240,8353792036297210583198800952⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨66705954264450733694023748764,66705954264450863075224018294⟩,⟨19435764454937426345479296936,19435764454937555715442444695⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨203298760903118336875629293989,203298760903118691183561285911⟩,⟨1388590614452385759735901192,1388590614452740046070915641⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨277185188235181208728680892251,277185188235181599999844798528⟩,⟨(-164354338078366541542538209373),(-164354338078366150265461976495)⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨103533308092664967423046765698,103533308092665194071180716952⟩,⟨(-405609235995317652366758071485),(-405609235995317425664495631525)⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-332009156072833831775802596211),(-332009156072833707055470778655)⟩,⟨(-356940174343749663528487722092),(-356940174343749538835431552864)⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨(-494995684489658528984460505767),(-494995684489658474282683043777)⟩,⟨182875384751155502948735501013,182875384751155557628763398110⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨48936670077570133608384184629,48936670077570160043030867233⟩,⟨539761680920409784286475356999,539761680920409810768043467603⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨532436788634831760625457657315,532436788634831774187281435415⟩,⟨49432779647933927624147038204,49432779647933941134351035989⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨126234388272348225089075772343,126234388272348231750629053812⟩,⟨(-493887437612183561384402786305),(-493887437612183554675526700155)⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨(-425489423622356458177390167617),(-425489423622356455019123381347)⟩,⟨(-199201319018663228854226872030),(-199201319018663225732037800145)⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨(-271303714730186467057578176489),(-271303714730186465613342672289)⟩,⟨316732733585869283478407272426,316732733585869284936164548551⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨157217014767846627245453181304,157217014767846627923997444357⟩,⟨316862584936547086154065628654,316862584936547086850077144107⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨280434861384636274861136017884,280434861384636275212902015210⟩,⟨32795649754052878205956280212,32795649754052878528579538103⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨161586643465983784241230020581,161586643465983784424097764798⟩,⟨(-126635789048419452052661536666),(-126635789048419451873018014523)⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨44772732966315322426963497179,44772732966315322503646235987⟩,⟨(-116231278588720707624300170144),(-116231278588720707537632534972)⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨3879602163057615588436932366,3879602163057615607744227574⟩,⟨(-41548504839412947425015529303),(-41548504839412947400634778214)⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨(-83580891159175618484469276003),(-83580891159174922972303635311)⟩,⟨10396438519977371839361049016,10396438519978067363800165041⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-223437129691579375296748375896),(-223437129691576272669816243818)⟩,⟨98821262485929239725405841557,98821262485932342375819618853⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-208961365660629309145551491986),(-208961365660620912199550537108)⟩,⟨319695508263994855350855909442,319695508264003252290042546567⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨125013655697458635495685127318,125013655697475584976377987269⟩,⟨474113586218316187415896490695,474113586218333136836102825880⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨552220392997941865366755094095,552220392997981894063673185310⟩,⟨140932494291338769516731030440,140932494291378798245114056792⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨340283554109861949196748240321,340283554109941476615212783917⟩,⟨(-522681073646224222980764349824),(-522681073646144695537704403762)⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨(-467130845179201473425559961405),(-467130845179079039789938898967)⟩,⟨(-457128647826958500187665579051),(-457128647826836066607870253303)⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨(-515729075301895654137916627228),(-515729075301745893293274544038)⟩,⟨413891168650451193979703031349,413891168650600954887993119502⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨355628232350719742609953146456,355628232350863496416814260991⟩,⟨542711810607553552501639007356,542711810607697306247454725923⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨556037675690209862616919017058,556037675690318346791436020239⟩,⟨(-270490606875524361352202401062),(-270490606875415877128521630918)⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-135593293305708516102254059685),(-135593293305643312544796868852)⟩,⟨(-554809570396367202034628701205),(-554809570396301998496841386149)⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-504071802666170127099669895810),(-504071802666139580428089832021)⟩,⟨(-56922224813827110390671323678),(-56922224813796563744025458457)⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-257977217099629248109051142810),(-257977217099617009291478878873)⟩,⟨337553763413603615927131896068,337553763413615854788729076422⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨48544856015016627686371682592,48544856015022417084121794587⟩,⟨318563479389895223335080989232,318563479389901012737665039258⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨129991723902439782550970353018,129991723902441862155493758507⟩,⟨153963143796586034588187907181,153963143796588114176966228291⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨56948008612333859668976429956,56948008612334320012099299403⟩,⟨38166927685247962412280873431,38166927685248422747342617554⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨38785787423207466576523513534,38785787423207466606164637305⟩,⟨(-3125350255301300808381192962),(-3125350255301300783002136483)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨104695728499208767379209029620,104695728499208767487049042951⟩,⟨(-44153324552755829659003249526),(-44153324552755829559397850289)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨94844216320722990581790065303,94844216320722990813160144210⟩,⟨(-154872661100525916443686569712),(-154872661100525916210234335978)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-81086101522309129109525219160),(-81086101522309128677632982021)⟩,⟨(-230458701632778590742793430752),(-230458701632778590292148949875)⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-300087777599493311504311979593),(-300087777599493310564394444053)⟩,⟨(-41060527889666385760936465243),(-41060527889666384829564763577)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-154260237847440237187482534767),(-154260237847440235145347697739)⟩,⟨316507305187140030193944288717,316507305187140032229300232946⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨306365315508790330328662646757,306365315508790334805926760017⟩,⟨233588405589111722509007439134,233588405589111726998339198992⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨279007218523329120725133598363,279007218523329130369311584080⟩,⟨(-288722388939702121274358321359),(-288722388939702111640926770042)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-265391005988353031437509999359),(-265391005988353010897956351906)⟩,⟨(-304815435381971289169968284611),(-304815435381971268623838689541)⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-326414681911336089349240472294),(-326414681911336040761943020397)⟩,⟨224360042371459766422198432036,224360042371459815007346224349⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨146609839600179347976749606880,146609839600179491073411550480⟩,⟨347897722250300943729417990964,347897722250301086825714284579⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨345297105880960978117854635864,345297105880961412366845773674⟩,⟨(-16660239070362822398892598299),(-16660239070362388150514191150)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨141527065126210738840368976075,141527065126211608716920944824⟩,⟨(-260391783909282006221281774549),(-260391783909281136341641580111)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-66802780815711764009728452406),(-66802780815710178029825051983)⟩,⟨(-217872627815408324225642401902),(-217872627815406738245286592086)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-106842682199726262527230710167),(-106842682199724833516567264179)⟩,⟨(-95599444874027416423226830936),(-95599444874025987414307032654)⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-43922313099838179783275595180),(-43922313099837665643230636471)⟩,⟨(-21435514304768358000554779831),(-21435514304767843861473478091)⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨3789432501142798339874949299,3789432501276786979106492379⟩,⟨(-7708594080758927177140761487),(-7708594080624938538113964403)⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨18929147600076570912115992736,18929147600076571313427972415⟩,⟨(-25644013782660850899004792954),(-25644013782660850495284814838)⟩⟩
end hm27_0_0_3
namespace hm27_0_0_4
noncomputable def s0_0 : CBox := ⟨⟨(-214131679704663900635526865),(-214131679704663742902988926)⟩,⟨338924854950500302367425088,338924854950500460083034590⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-308305693700729164725162984),(-308305693700728756269987137)⟩,⟨1049201313413350583510556113,1049201313413350991935733821⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨385544411161332891444561400,385544411161333291687480559⟩,⟨1456366110553077721866162953,1456366110553078122115376244⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨1374019930750824243266110974,1374019930750824430184295706⟩,⟨791165957867379458305720949,791165957867379645272483400⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨1233587178607391544681181195,1233587178607391621010583837⟩,⟨(-641341943753232114926995967),(-641341943753232038612056591)⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-85853609117718412095219191),(-85853609117718390775737957)⟩,⟨(-1040568804152325328569399482),(-1040568804152325307259891919)⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-663268967490448386801370338),(-663268967490448380704311501)⟩,⟨(-126001412440354333729692839),(-126001412440354327623345087)⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-138138397562659690880014662),(-138138397562659689119959853)⟩,⟨347274910415290706995899733,347274910415290708752658029⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨149489956389180819239552651,149489956389180819685630553⟩,⟨89883220311468073063351701,89883220311468073509618656⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨44456842753986233893574613,44456842753986233988070135⟩,⟨(-49773904684134311527168257),(-49773904684134311432261371)⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-10886987420266667056078206),(-10886987420266667039101342)⟩,⟨(-16747912876949692936764821),(-16747912876949692919836601)⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-4257519193459294999387054),(-4257519193459294996829228)⟩,⟨788666618280321695566974,788666618280321697953730⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-222232441073217929109118),(-222232441073217928858690)⟩,⟨552056026692323507383502,552056026692323507692180⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨16299946594938569335770,16299946594938569356832⟩,⟨37004194496793142441700,37004194496793142466488⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨657225892550928246215,657225892550928247039⟩,⟨434432516511971119352,434432516511971119931⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨784100940711032185,784100940711032205⟩,⟨190830501827620774,190830501827620791⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-3455502025359832479879113811),(-3455502025359829149532478901)⟩,⟨(-4308009304121396558901857607),(-4308009304121393228160443896)⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-12731615962833357390722982592),(-12731615962833343414730294850)⟩,⟨(-9133968110253210190156277058),(-9133968110253196213423697721)⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-23272411080065687697727733224),(-23272411080065652892612743482)⟩,⟨(-2048845146937747192288507381),(-2048845146937712387352810687)⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-21411566736305643884138409932),(-21411566736305580361060576775)⟩,⟨17616584859637079948623900583,17616584859637143470108364093⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨3053923159889487558217481365,3053923159889619818321470684⟩,⟨28543291145084933321549219517,28543291145085065582328147692⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨25730976608137681812574760698,25730976608137907507589372756⟩,⟨7945423738206762404475412454,7945423738206988100021944452⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨12694274840906666178743840457,12694274840906960949126190477⟩,⟨(-19648407842742133337040936322),(-19648407842741838567564907883)⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-13765154932369034368583404787),(-13765154932368732715182303543)⟩,⟨(-13224880181102034805353402705),(-13224880181101733151162289919)⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-11830704744961962268204304444),(-11830704744961723962652422140)⟩,⟨8859679882510757162649410030,8859679882510995467640837947⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨4807860025368096067240874688,4807860025368242571830314011⟩,⟨9822738640523384399161302412,9822738640523530904072557194⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨7631358194340666357081947809,7631358194340737374064975908⟩,⟨(-1467012055750715521922918420),(-1467012055750644505023550429)⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨1069797946161134461642306365,1069797946161161313176588608⟩,⟨(-5208717572827645019093713979),(-5208717572827618167663597474)⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-2514170382826954777986390990),(-2514170382826945768145530373)⟩,⟨(-2426701888957211584680526915),(-2426701888957202574712241844)⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-2161892296031488519408096692),(-2161892296031484891847441166)⟩,⟨54528171173729142135148023,54528171173732769707570893⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-982200774060199288832599679),(-982200774060198112175714986)⟩,⟨633498597528833973914543333,633498597528835150540620008⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-242575683321891309855729271),(-242575683321891060620576978)⟩,⟨277489199215745261184929380,277489199215745510405707190⟩⟩
noncomputable def s2_0 : CBox := ⟨⟨20023206751188431361600157709,20023206751188431370377157410⟩,⟨(-1035826187302124753404098709),(-1035826187302124746932164921)⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨54598647092804224691263798904,54598647092804224720539596471⟩,⟨(-18901148833730836088171890100),(-18901148833730836063320190171)⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨56333246864803780427081353626,56333246864803780481172705163⟩,⟨(-68907307649162530270983850979),(-68907307649162530215739070852)⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-12773291502661473910863387606),(-12773291502661473827021196090)⟩,⟨(-110554592915927017800767314144),(-110554592915927017706394583300)⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-112118699684516487359604990049),(-112118699684516487196274788047)⟩,⟨(-52851280951665871925953034686),(-52851280951665871767613854732)⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-93441258852847035021135791391),(-93441258852847034721645105969)⟩,⟨86777415480455720227780676603,86777415480455720523277415569⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨58549821580433519103127434646,58549821580433519661828376210⟩,⟨108594325943096482291906756349,108594325943096482858301272194⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨107765853700978036016265178833,107765853700978037061191103565⟩,⟨(-35643854013316914436446984346),(-35643854013316913399161697724)⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-17070851788599208744638949941),(-17070851788599206916751168883)⟩,⟨(-98648153899449983142326684925),(-98648153899449981308218500867)⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-85106577856908486066480582701),(-85106577856908482899206764237)⟩,⟨(-276001233421496087047533677),(-276001233421492923929489339)⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-17808312220381769919025980128),(-17808312220381763899812628134)⟩,⟨67583310130326901808790794014,67583310130326907829326290392⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨44248277069433374185422401922,44248277069433386877570300799⟩,⟨33166095687013289339970269202,33166095687013302033845628437⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨38924654992668738662332991917,38924654992668759560130218909⟩,⟨(-14823596906932642351091115376),(-14823596906932621455812133455)⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨11728817935265249141374800173,11728817935265282074671311736⟩,⟨(-26457897324830063518150565193),(-26457897324830030585131489172)⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-2129065773934632410488141383),(-2129065773934604769277152172)⟩,⟨(-16875976180552824200450334150),(-16875976180552796558483809592)⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-2191987914417106470086729634),(-2191987914417096830040982166)⟩,⟨(-5158827433369365537974245544),(-5158827433369355897554111808)⟩⟩
noncomputable def s3_0 : CBox := ⟨⟨(-10165317046329692587074766543),(-10165317046329624930175952581)⟩,⟨34885016113725944142260807642,34885016113726011805100627460⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-748821068718886621458006502),(-748821068718702202543275854)⟩,⟨105813356089071347007760954973,105813356089071531438048517548⟩⟩
noncomputable def ans : CBox := ⟨⟨8446563302696182830293286891,8446563302774909761865188978⟩,⟨4805734864269861334107714412,4805734864348588265836427623⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨29247805196765215054915670378,29247805196765215314867447283⟩,⟨21985530137787495860073934538,21985530137787496117698093681⟩⟩
end hm27_0_0_4
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock27_1
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm27_0_0_10
noncomputable def s0_0 : CBox := ⟨⟨28391636001935962396,28391636001935983303⟩,⟨(-44870329342058474557),(-44870329342058453650)⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨37214057885117568034,37214057885117616460⟩,⟨(-123843029403372826400),(-123843029403372777980)⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-33969053357519976299),(-33969053357519938072)⟩,⟨(-137585058782628280906),(-137585058782628242679)⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-89504000965394118660),(-89504000965394105896)⟩,⟨(-55431181282335686359),(-55431181282335673589)⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-52257111855261599887),(-52257111855261596565)⟩,⟨23854940102226951748,23854940102226955071⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨218826268226096556,218826268226097071⟩,⟨23434221514608286960,23434221514608287478⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨6804876974183601198,6804876974183601284⟩,⟨1983904217780011713,1983904217780011799⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨738573390612123695,738573390612123722⟩,⟨(-1362263544927947140),(-1362263544927947114)⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-182545725871182537),(-182545725871182517)⟩,⟨(-147278537180727753),(-147278537180727735)⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-17713984806212749),(-17713984806212730)⟩,⟨14634435556331746,14634435556331767⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨534952901288097,534952901288118⟩,⟨1198403602703888,1198403602703907⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨37015140698846,37015140698865⟩,⟨(-1226274065821),(-1226274065803)⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨191090224712,191090224731⟩,⟨(-340724181916),(-340724181896)⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-290987828),(-290987811)⟩,⟨(-865926978),(-865926961)⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-118493),(-118477)⟩,⟨(-86192),(-86175)⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),0⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨29698030967012071565138,29698030967012100184991⟩,⟨37049921864087455985378,37049921864087484608839⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨103191416904459817865287,103191416904459930972812⟩,⟨74493296392529702652551,74493296392529815766496⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨168665835460071866892102,168665835460072117975457⟩,⟨16200539215473269686224,16200539215473520768342⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨132828116225956247647424,132828116225956632397272⟩,⟨(-106011715895144241231386),(-106011715895143856491936)⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-11765315251562700246382),(-11765315251562055120623)⟩,⟨(-140514068848745756196128),(-140514068848745111067201)⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-95356459585786053884260),(-95356459585785224473672)⟩,⟨(-32775221704663516737767),(-32775221704662687324752)⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-36687716880879831417978),(-36687716880879043038670)⟩,⟨52165820661491412278235,52165820661492200654808⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨25094240926809705639736,25094240926810276989867⟩,⟨26390190431760024888092,26390190431760596239798⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨15839706732364911595495,15839706732365221476754⟩,⟨(-10712679815919388533470),(-10712679815919078652927)⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-3729328452367552199729),(-3729328452367423811666)⟩,⟨(-8634259129919210064665),(-8634259129919081676354)⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-4372497182610517971843),(-4372497182610476751607)⟩,⟨647018876655367769905,647018876655408990108⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-477648499118901676877),(-477648499118891358458)⟩,⟨1970939845653712806726,1970939845653723125099⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨650183976600284967489,650183976600287402553⟩,⟨659900378039599252811,659900378039601687910⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨423418493718370261476,423418493718370978317⟩,⟨(-4513125278341962248),(-4513125278341245408)⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨155121571339194127986,155121571339194314439⟩,⟨(-98799064081664077487),(-98799064081663891037)⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨34057270997799709139,34057270997799744161⟩,⟨(-38907131993335253100),(-38907131993335218081)⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-1970380272407600648551998),(-1970380272407600647650666)⟩,⟨101481835737132908543044,101481835737132909182901⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-5175950204922932239114460),(-5175950204922932236242836)⟩,⟨1780148424014112498375419,1780148424014112500761164⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-4982320846431012361803556),(-4982320846431012356951565)⟩,⟨6027632059590822997428389,6027632059590823002389998⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨917335435365172194025661,917335435365172200639079⟩,⟨8702443886488630131565346,8702443886488630139140893⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨7574487632804099743123609,7574487632804099754324090⟩,⟨3712707762171513847778494,3712707762171513858607521⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨5441357083355995635021924,5441357083355995652126325⟩,⟨(-4849764801209739420183302),(-4849764801209739403370922)⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-2611956650732636914278624),(-2611956650732636888400013)⟩,⟨(-5147831619972290213345049),(-5147831619972290187028487)⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-4081021456577769422035671),(-4081021456577769383230542)⟩,⟨1224176982183703974396818,1224176982183704012859493⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨421788703133794214364551,421788703133794267962373⟩,⟨2944679311048581998094557,2944679311048582051909527⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨1990473249068701970053259,1990473249068702043131188⟩,⟨62010520271965466629459,62010520271965539595879⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨360145976190543998503769,360145976190544108209561⟩,⟨(-1242296065993858789227460),(-1242296065993858679496392)⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-647721496661531493899181),(-647721496661531308962797)⟩,⟨(-505422043490672904011682),(-505422043490672719042051)⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-478893022714152496525958),(-478893022714152243592998)⟩,⟨175073520546628922200132,175073520546629175095509⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-124820183860271098048724),(-124820183860270755817968)⟩,⟨275949253853666513679191,275949253853666855906131⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨19492298918852957686125,19492298918853216387990⟩,⟨158178969373571885754965,158178969373572144465532⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨19381637500567453307076,19381637500567538612395⟩,⟨45656348987126423797090,45656348987126509106507⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨5637014748908720329423542,5637014748908757826412392⟩,⟨(-19332917536301357022445497),(-19332917536301319521950137)⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨487623470768739451402899,487623470768838844996602⟩,⟨(-56993026724706204121305373),(-56993026724706104721158129)⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-42806023996468331255030451),(-42806023996468228107079428)⟩,⟨(-72957029102007116337826945),(-72957029102007013191469036)⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨(-96448914663109127812124000),(-96448914663109073399724545)⟩,⟨(-25494265809674422389204181),(-25494265809674367990923589)⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-75967710085657762874860582),(-75967710085657736336524393)⟩,⟨68850916725817197755664050,68850916725817224300027172⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨31550463737671862455427670,31550463737671872450669734⟩,⟨90172118294745349482854568,90172118294745359482850336⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨82531272991419566608178485,82531272991419570691892964⟩,⟨(-5738545647386569181238648),(-5738545647386565105859996)⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨7839637233178911724702429,7839637233178913455380587⟩,⟨(-67320675278266021273834712),(-67320675278266019535579830)⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨(-51180129485506896247483299),(-51180129485506895538738743)⟩,⟨(-14395824237577030896122176),(-14395824237577030193085222)⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨(-17885164094402562799618440),(-17885164094402562528576839)⟩,⟨36051424592694189606096558,36051424592694189880691273⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨22036645135863559566439149,22036645135863559671366821⟩,⟨19639383392820839529808822,19639383392820839633695592⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨18940047017193992455277820,18940047017193992497508608⟩,⟨(-9037496108262465518712172),(-9037496108262465477822064)⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨1818109779017585314096159,1818109779017585330731711⟩,⟨(-14247323910195042533110339),(-14247323910195042514626030)⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-5651466293403718400550530),(-5651466293403718392229993)⟩,⟨(-7299112116210135711029374),(-7299112116210135702515099)⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-4790028140997537000842667),(-4790028140997536997080606)⟩,⟨(-1857493798212718789501250),(-1857493798212718786262817)⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-1639237486391259243157306),(-1639237486391259242133206)⟩,⟨(-153487400134913297152123),(-153487400134913296384328)⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨14373640321694313183128409,14373640321695275798647538⟩,⟨115710659160254411119896932,115710659160255373720704203⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨132774406746465436065863076,132774406746469610979182915⟩,⟨301396592401091470433867476,301396592401095645319642253⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨407863541469577878685291942,407863541469588591417450637⟩,⟨268874804000784958908023661,268874804000795671647542277⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨562524634413079848788099311,562524634413099810754268558⟩,⟨(-143992429736228617700325766),(-143992429736208655670638032)⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨157562175306719065006452187,157562175306761864659165914⟩,⟨(-590436395504062551948152284),(-590436395504019752324700935)⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-492979577987570665414660047),(-492979577987495499844651848)⟩,⟨(-331179312495327677940841826),(-331179312495252512393558407)⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨(-387240591532602375208305552),(-387240591532501189791517945)⟩,⟨382243120475503596964792762,382243120475604782425770336⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨290744594644714064507245614,290744594644821608285730425⟩,⟨376798709874339393676824443,376798709874446937411541780⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨339825897838443134634494744,339825897838532274824744294⟩,⟨(-213349039813509646210501882),(-213349039813420505983857257)⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨(-138227240311573839106278377),(-138227240311515759088368652)⟩,⟨(-297884083959375176442865652),(-297884083959317096450308932)⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-255427846476827492192459539),(-255427846476797332482715121)⟩,⟨58176413614374083073734596,58176413614404242792028484⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-25284822071078912652494187),(-25284822071066624460333604)⟩,⟨201784823228071465354660458,201784823228083753557639247⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨119667362433638922088192545,119667362433643318075336291⟩,⟨93028892031231167786210634,93028892031235563756656825⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨103635091054360144584840465,103635091054362032683076664⟩,⟨(-15310725372875543573953175),(-15310725372873655477491722)⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨46982212259492450029225425,46982212259493085122210240⟩,⟨(-39528919779654813621476002),(-39528919779654178523261471)⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨11252761600933824971942275,11252761600933960698944127⟩,⟨(-16782899656306637238824161),(-16782899656306501509213325)⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨(-15491813654294581647329627),(-15491813654294581520970239)⟩,⟨(-192613982661223593774218433),(-192613982661223593622728957)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-213779350337517563915193190),(-213779350337517563427098533)⟩,⟨(-508788876618840963593158787),(-508788876618840963057785148)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-718403011764029492004027899),(-718403011764029490904146143)⟩,⟨(-443410172620099213926853745),(-443410172620099212837829678)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-1006870759394872689025707345),(-1006870759394872687040755637)⟩,⟨347182872817208530419723963,347182872817208532309395664⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-175881723241718519200483039),(-175881723241718515452385155)⟩,⟨1202999948823628320923590823,1202999948823628324709748755⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨1144912390052488598516064177,1144912390052488605905750305⟩,⟨575035136844408972133887870,575035136844408979553429927⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨775097395217489641444863679,775097395217489656000403800⟩,⟨(-987074687358412762179411108),(-987074687358412747669042654)⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-821800016292945713353424681),(-821800016292945685687683258)⟩,⟨(-819547365729768391833056186),(-819547365729768364133641947)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-789007864874388195271175767),(-789007864874388143218923944)⟩,⟨665014170579625167909802392,665014170579625219946099109⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨494869407106369979578975250,494869407106370088152907177⟩,⟨743673592897003894095669186,743673592897004002671543235⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨700318327907466477927761247,700318327907466761779317969⟩,⟨(-284594209183942682179069227),(-284594209183942398324796631)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨(-23818357630109800370190873),(-23818357630109028920918243)⟩,⟨(-620398108872938593386987706),(-620398108872937821934061694)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-424242012727653993030655879),(-424242012727652578987644495)⟩,⟨(-234210732564411103105734441),(-234210732564409689073218463)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-331008445908118217761953064),(-331008445908115819105424717)⟩,⟨100186518545658646885656427,100186518545661045540855879⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-137959712671817792643333407),(-137959712671815734640520982)⟩,⟨153762528572019010311580828,153762528572021068319046546⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-30085467890576874402980679),(-30085467890576153015708216)⟩,⟨61622276457520278130423492,61622276457520999520152601⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-135606191673975596441477146),(-135606191673881023397306858)⟩,⟨(-26391489735133994414220357),(-26391489735039421368691112)⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-489111514053367585708881489),(-489111514053367585030510153)⟩,⟨(-96999166175934232550611785),(-96999166175934231897999081)⟩⟩
end hm27_0_0_10
namespace hm27_0_0_11
noncomputable def s0_0 : CBox := ⟨⟨2125590193956936259,2125590193956937267⟩,⟨1345301365857793135,1345301365857794142⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨5756776095045215200,5756776095045217470⟩,⟨1736248909246031750,1736248909246034019⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨6165221767748837398,6165221767748839131⟩,⟨(-1504063526451410899),(-1504063526451409168)⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨2363835246958442111,2363835246958442670⟩,⟨(-3772381574383086823),(-3772381574383086265)⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-916068511167607085),(-916068511167606937)⟩,⟨(-2051649304537131624),(-2051649304537131474)⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-829249029709834598),(-829249029709834560)⟩,⟨(-1893722617368822),(-1893722617368789)⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-65136013671232716),(-65136013671232695)⟩,⟨211621412867958915,211621412867958939⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨36183811900250919,36183811900250936⟩,⟨20458843149858637,20458843149858657⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨3365202680466097,3365202680466116⟩,⟨(-4005832618767758),(-4005832618767739)⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-254591617405691),(-254591617405672)⟩,⟨(-321429225770537),(-321429225770518)⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-16448700633665),(-16448700633647)⟩,⟨6956298106174,6956298106193⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨5800899582,5800899601⟩,⟨360959276334,360959276350⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨2164688454,2164688471⟩,⟨1250419902,1250419920⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨3188726,3188744⟩,⟨(-1044483),(-1044466)⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨140,157⟩,⟨(-209),(-187)⟩⟩
noncomputable def s1_0 : CBox := ⟨⟨(-3518908125618183811972),(-3518908125618181093718)⟩,⟨2820325648082583601141,2820325648082586319047⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-7013226409808726208545),(-7013226409808715572989)⟩,⟨9704997150549402969899,9704997150549413604845⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-1516429475739468489141),(-1516429475739445326847)⟩,⟨15571407134087726065783,15571407134087749228188⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨9489612536243124335352,9489612536243158814062⟩,⟨11950520260121059976197,11950520260121094455852⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨12166428860234014494985,12166428860234070268109⟩,⟨(-971918606751839926201),(-971918606751784153349)⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨2753230510010579381803,2753230510010647794858⟩,⟨(-7876379105478037254360),(-7876379105477968841516)⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-4076600584304078579336),(-4076600584304016888205)⟩,⟨(-2906697451694960445339),(-2906697451694898753990)⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-1966294227412960797597),(-1966294227412918576475)⟩,⟨1842123628675106483948,1842123628675148704951⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨734358790327093688467,734358790327115199127⟩,⟨1104510133030895465736,1104510133030916976447⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨561389890762807537254,561389890762815881713⟩,⟨(-237311516317521526454),(-237311516317513182009)⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-37268130631463677926),(-37268130631461176913)⟩,⟨(-264739147296849770298),(-264739147296847269280)⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-111349292203367182798),(-111349292203366598356)⟩,⟨(-27667971344321261410),(-27667971344320676968)⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-35271098647016123284),(-35271098647015993231)⟩,⟨34464921399926904338,34464921399927034389⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨176669520548848217,176669520548884554⟩,⟨21421928583193756040,21421928583193792375⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨4810772064635893829,4810772064635902947⟩,⟨7569120253700715877,7569120253700724997⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨1860817691125601886,1860817691125603576⟩,⟨1629224668695610803,1629224668695612494⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-14457891743294731304192),(-14457891743294731212882)⟩,⟨(-280922608305774306239561),(-280922608305774306110147)⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-251957294604855120398740),(-251957294604855120059987)⟩,⟨(-733390865773067222472584),(-733390865773067222063411)⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-842732317737629618234882),(-842732317737629617538171)⟩,⟨(-697863778806898161627516),(-697863778806898160946301)⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-1195568983764816529443864),(-1195568983764816528399733)⟩,⟨124013712203261024697946,124013712203261025606843⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-500460691837251161450412),(-500460691837251159996966)⟩,⟨1014498002063868406709801,1014498002063868408213687⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨629372292845306966430132,629372292845306968618531⟩,⟨710997704813332878387588,710997704813332880615505⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨650025123868855219476733,650025123868855222788898⟩,⟨(-326438868811573161587432),(-326438868811573158332141)⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-146400109209357822902999),(-146400109209357818240546)⟩,⟨(-496417915544724912734840),(-496417915544724908029652)⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-344279265232469952356417),(-344279265232469946082331)⟩,⟨47620763146611546389902,47620763146611552638006⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-7996045616656140271101),(-7996045616656132098516)⟩,⟨223446696739776718955647,223446696739776727140995⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨133966121761786169227111,133966121761786181043656⟩,⟨39428755083275231325740,39428755083275243139557⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨52819159249939399575749,52819159249939418763684⟩,⟨(-67242273229650993560845),(-67242273229650974376508)⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-17532947520270665390975),(-17532947520270639957692)⟩,⟨(-48292214225951870701556),(-48292214225951845264374)⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-27068844153323419957372),(-27068844153323386407616)⟩,⟨(-12284888546752817193815),(-12284888546752783643671)⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-15241208672233466626522),(-15241208672233441704726)⟩,⟨1870729549730759863499,1870729549730784784429⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-4357075000985504406383),(-4357075000985496265275)⟩,⟨1849345249448070196729,1849345249448078337433⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨3676550051546104509546408,3676550051546111641110805⟩,⟨1072104711211845780711379,1072104711211852911602156⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨10787172619367600892870576,10787172619367619708489381⟩,⟨94952243422436824627209,94952243422455638992074⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨13685229525988974106952179,13685229525988993459391482⟩,⟨(-8017423353495194254476158),(-8017423353495174901737268)⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨4736654782701194318507107,4736654782701204389326495⟩,⟨(-17831908420428435104939781),(-17831908420428425031476953)⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-12483398227774623054946689),(-12483398227774618224249968)⟩,⟨(-13824928526285827540429270),(-13824928526285822710834162)⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨(-16050059681818995230707011),(-16050059681818993449868253)⟩,⟨5571330994923020326943724,5571330994923022106915202⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨953149395896172543228178,953149395896173251564927⟩,⟨14327682982307464287524666,14327682982307464997338047⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨11374371774595270059749397,11374371774595270354015724⟩,⟨1362949219789581206578953,1362949219789581499539597⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨2395148614197358967519339,2395148614197359083278547⟩,⟨(-8405076715648000105019204),(-8405076715647999988304024)⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨(-5752644561143942807813064),(-5752644561143942763834766)⟩,⟨(-2877080613916927845914306),(-2877080613916927802513791)⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨(-3063930611311265446744487),(-3063930611311265430550841)⟩,⟨3418608299888186932568187,3418608299888186948924975⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨1364166022563897143566383,1364166022563897149780459⟩,⟨2875097558676239911274969,2875097558676239917699271⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨2112994434287977341819086,2112994434287977344573480⟩,⟨272860318014101543169347,272860318014101545641791⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨1064436211552750602081444,1064436211552750603328392⟩,⟨(-822732457194634930667107),(-822732457194634929449470)⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨267595179578970797029178,267595179578970797496904⟩,⟨(-689407774808625368118735),(-689407774808625367573349)⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨21961730776134296172478,21961730776134296282432⟩,⟨(-234457805409802069297526),(-234457805409802069149764)⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨(-27512828115478585396626735),(-27512828115478356525900868)⟩,⟨3417001123995835532053059,3417001123996064406199554⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-71399049076449462378860048),(-71399049076448473720877025)⟩,⟨31435656402399354902508601,31435656402400343566876771⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-63267716753788489597678595),(-63267716753785971894064550)⟩,⟨95855871804306058733536179,95855871804308576435463548⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨33349154577352343959097358,33349154577356982261867242⟩,⟨130843718017884603833153639,130843718017889242121423474⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨135312821713672810965937517,135312821713682619565783103⟩,⟨36334895303194772062429840,36334895303204580668842728⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨74883863126670875617723949,74883863126687801216906243⟩,⟨(-110974230440595893026264542),(-110974230440578967421987856)⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨(-84318460073874391202142250),(-84318460073852038447708501)⟩,⟨(-85844036497455763010715732),(-85844036497433410265978187)⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨(-81784076697894167310716563),(-81784076697870881507829369)⟩,⟨62751418748150798620134433,62751418748174084432436699⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨45019826212032828580335539,45019826212051729272547328⟩,⟨72152216887355978437183031,72152216887374879121722317⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨61853485381362081406500126,61853485381374140349886270⟩,⟨(-28505892846163894574564490),(-28505892846151835625943121)⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-11698392706601210147460922),(-11698392706595077801525488)⟩,⟨(-51901343492401549161884045),(-51901343492395416817670608)⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-40189588686547222014834019),(-40189588686544772855795425)⟩,⟨(-5107138069578821904531269),(-5107138069576372747671749)⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-18253466956504422396273480),(-18253466956503560326656465)⟩,⟨23423333606640485773418098,23423333606641347846333953⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨2946928892872702442946536,2946928892873067623039369⟩,⟨20037139544689002372061657,20037139544689367552503418⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨7569115922570084084688423,7569115922570205769658283⟩,⟨9000787209517378994648180,9000787209517500678604575⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨3199238377124785314242039,3199238377124811189424190⟩,⟨2145185860907306235502708,2145185860907332110181170⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨54966660072458413781522625,54966660072458413824928345⟩,⟨(-4419750266833653619579224),(-4419750266833653583506567)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨144746548089210592725491733,144746548089210592878260732⟩,⟨(-60786418788714820176961237),(-60786418788714820037938506)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨125452246725928412201791035,125452246725928412510200326⟩,⟨(-203028045785186653447575541),(-203028045785186653136052282)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-97000290303877434678390434),(-97000290303877434148782678)⟩,⟨(-282132088369311886298735634),(-282132088369311885741895034)⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-332977288836069237219782024),(-332977288836069236171093162)⟩,⟨(-49128675729890747287405116),(-49128675729890746249393819)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-157513951324524635800216959),(-157513951324524633775181128)⟩,⟨312285710843127527201960099,312285710843127529218634280⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨264819935498074666554163332,264819935498074670450443380⟩,⟨208821947096713396719628015,208821947096713400628276008⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨216988704869915148268362450,216988704869915155578965718⟩,⟨(-216609657687370901760323369),(-216609657687370894458714903)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-172121195518665011528386470),(-172121195518664998038556948)⟩,⟨(-205165097055830122515407483),(-205165097055830109021467359)⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-189883578938399800201588023),(-189883578938399772554794749)⟩,⟨125768881158651110646091971,125768881158651138292492911⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨71016823882449316678922752,71016823882449387735957423⟩,⟨175678105011222081369810229,175678105011222152426097967⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨153120827708107705167940437,153120827708107895262802141⟩,⟨(-5663182200363542847509374),(-5663182200363352753642994)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨57128804207373647485328700,57128804207373991522075165⟩,⟨(-103251926370663943732392620),(-103251926370663599692901680)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-24095815209986341767718981),(-24095815209985764167920612)⟩,⟨(-79758933595944649766703205),(-79758933595944072166561506)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-36763937768983547173480470),(-36763937768983055063502991)⟩,⟨(-32998478542898023572718826),(-32998478542897531463927018)⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-14680004821318868976174616),(-14680004821318697120627065)⟩,⟨(-7167530645126543320077132),(-7167530645126371465152407)⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def ans : CBox := ⟨⟨7018386985600021693763773,7018386985620626544108843⟩,⟨(-41111057429042058208009115),(-41111057429021453358090921)⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨23687354313445331886430521,23687354313445332052293981⟩,⟨(-148068244402214327020389190),(-148068244402214326846695628)⟩⟩
end hm27_0_0_11
namespace hm27_0_0_12
noncomputable def s0_0 : CBox := ⟨⟨(-58433716462409219),(-58433716462409159)⟩,⟨92302741250453053,92302741250453111⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-74259552880190093),(-74259552880189980)⟩,⟨245317709721109214,245317709721109325⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨61052433199573096,61052433199573184⟩,⟨253291750526084916,253291750526085003⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨145804454274644777,145804454274644815⟩,⟨92428722094754119,92428722094754156⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨73880352151559994,73880352151560017⟩,⟨(-32262817876291080),(-32262817876291057)⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨369290678490076,369290678490100⟩,⟨(-26924914778873086),(-26924914778873064)⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-6041625287422116),(-6041625287422097)⟩,⟨(-1956245607172626),(-1956245607172607)⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-519412602619369),(-519412602619352)⟩,⟨882906930003789,882906930003808⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨80827067532121,80827067532139⟩,⟨70545929925861,70545929925878⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨5357229353248,5357229353266⟩,⟨(-4077598926645),(-4077598926627)⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-83425894380),(-83425894362)⟩,⟨(-207672198164),(-207672198145)⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-3243480024),(-3243480007)⟩,⟨2632740,2632758⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-7522367),(-7522348)⟩,⟨12695605,12695622⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨3462,3478⟩,⟨10822,10840⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-14),16⟩,⟨0,16⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨0,16⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-245517880895420268895),(-245517880895420032280)⟩,⟨(-306366185639321359060),(-306366185639321122415)⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-836692906954928304798),(-836692906954927388147)⟩,⟨(-605253234617842519458),(-605253234617841602753)⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-1317832331143429392180),(-1317832331143427433406)⟩,⟨(-130095605557579903133),(-130095605557577944366)⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-985666845238128336349),(-985666845238125503640)⟩,⟨778735517393421017967,778735517393423850601⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨73447997220332012640,73447997220336433170⟩,⟨965777263593625610485,965777263593630031037⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨596483820965809180642,596483820965814354360⟩,⟨211990938509447943094,211990938509453116828⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨211127683162087761986,211127683162092188325⟩,⟨(-292097451878741293097),(-292097451878736866768)⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-123992127474414515748),(-123992127474411654744)⟩,⟨(-134325468957294903809),(-134325468957292042796)⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-70619491945849604392),(-70619491945848235106)⟩,⟨46157778170026007121,46157778170027376405⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨13844465010972942121,13844465010973439461⟩,⟨33470139008317216071,33470139008317713410⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨14698349908398117442,14698349908398256606⟩,⟨(-1964106334156899455),(-1964106334156760291)⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨1468619461018604394,1468619461018634764⟩,⟨(-5768359158417804369),(-5768359158417774001)⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-1675079340730723829),(-1675079340730717442)⟩,⟨(-1728477533362586048),(-1728477533362579663)⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-993630945419351552),(-993630945419349847)⟩,⟨5803886093288192,5803886093289895⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-338576774724416919),(-338576774724416495)⟩,⟨214741175142469099,214741175142469522⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-71444172353142575),(-71444172353142484)⟩,⟨81581775169750319,81581775169750409⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨36714290645896046400122,36714290645896046417163⟩,⟨(-1888135664004206393350),(-1888135664004206381395)⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨95256716079283305846097,95256716079283305899552⟩,⟨(-32689779655640417583990),(-32689779655640417539888)⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨89604368751569121896060,89604368751569121983745⟩,⟨(-108007174734622807836023),(-108007174734622807746328)⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-15364930246282288989320),(-15364930246282288874801)⟩,⟨(-150569034500417630400286),(-150569034500417630268353)⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-124561899823729967582544),(-124561899823729967397421)⟩,⟨(-61840387968243770029522),(-61840387968243769850676)⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-85166532482741364273044),(-85166532482741364006994)⟩,⟨74874745583363189261292,74874745583363189522442⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨37399618070169790439569,37399618070169790814982⟩,⟨75246478866990282116410,75246478866990282498589⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨55358477796339753874308,55358477796339754397356⟩,⟨(-16047350096222056783607),(-16047350096222056265446)⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-4923389078884923538348),(-4923389078884922870577)⟩,⟨(-36901742219033534029475),(-36901742219033533358856)⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-22996193028462310119708),(-22996193028462309279158)⟩,⟨(-929251524601026900254),(-929251524601026061039)⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-3956532586930044510298),(-3956532586930043343973)⟩,⟨13244199309570892673653,13244199309570893840251⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨6399527679745564575006,6399527679745566399439⟩,⟨5060246193447886503472,5060246193447888328260⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨4464333769853281672341,4464333769853284017536⟩,⟨(-1609597609943948791304),(-1609597609943946446476)⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨1108365142390858361131,1108365142390861376227⟩,⟨(-2434105653876610927513),(-2434105653876607912453)⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-164577781704922102648),(-164577781704919902001)⟩,⟨(-1346196885895662343620),(-1346196885895660142896)⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-161755025764731126286),(-161755025764730414141)⟩,⟨(-381154590110389604914),(-381154590110388892736)⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨(-186911869146182315121085),(-186911869146181072030364)⟩,⟨640907292850315227502695,640907292850316470712028⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-16935499505058462078889),(-16935499505055197448650)⟩,⟨1871573162527612962322429,1871573162527616227172577⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨1376513837939493160220991,1376513837939496488658981⟩,⟨2353169797145845895313320,2353169797145849223699676⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨3022168732514175955590509,3022168732514177665135105⟩,⟨806699478458582744362730,806699478458584453453703⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨2306323770106409967776407,2306323770106410773474137⟩,⟨(-2074815741775920105497780),(-2074815741775919299615517)⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨(-901823915991697695817391),(-901823915991697405239646)⟩,⟨(-2618847066406782254252365),(-2618847066406781963529618)⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-2280168793471669131756203),(-2280168793471669018654947)⟩,⟨144840382418156170302896,144840382418156283164431⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨(-217047394180507382507448),(-217047394180507337046364)⟩,⟨1761745315561862036995510,1761745315561862082662796⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨1265377419160270218850332,1265377419160270236470237⟩,⟨365257695024184811834239,365257695024184829307432⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨424256173167348760045628,424256173167348766416422⟩,⟨(-841491728613204731313388),(-841491728613204724856515)⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨(-486168273984772419760297),(-486168273984772417422855)⟩,⟨(-438187426430534625384177),(-438187426430534623070153)⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨(-400086877696410001505306),(-400086877696410000609410)⟩,⟨188759729744349491090866,188759729744349491956565⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-37534031871488494585391),(-37534031871488494248525)⟩,⟨287269030517228355556477,287269030517228355932731⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨109793151734368083860785,109793151734368084024138⟩,⟨142294629285807923567176,142294629285807923734590⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨90955485857360007419944,90955485857360007492429⟩,⟨35338122676457891036618,35338122676457891098553⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨30739678416300288550238,30739678416300288569791⟩,⟨2880528207533958554715,2880528207533958569159⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨(-744620564571407718741937),(-744620564571357835785181)⟩,⟨(-5996649620193717443337987),(-5996649620193667561109903)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-6822494836790399990323805),(-6822494836790185373928420)⟩,⟨(-15504548438329963808998266),(-15504548438329749193958991)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-20650808207499207505920457),(-20650808207498665101899778)⟩,⟨(-13646723981677617528375457),(-13646723981677075124000587)⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-27898525587497549720169832),(-27898525587496561782224045)⟩,⟨7080115102193341652491670,7080115102194329593470632⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-7680695166665656978523483),(-7680695166663596375574181)⟩,⟨28426585430938071972500051,28426585430940132574098627⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨22900103843192724022783486,22900103843196217774285022⟩,⟨15521420692191541423609525,15521420692195035174064488⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨17444617070713917974946580,17444617070718444552141768⟩,⟨(-17050160579304966553460966),(-17050160579300439974315768)⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨(-12415307489343427141421700),(-12415307489338805177593543)⟩,⟨(-16272432374245163396927055),(-16272432374240541434955364)⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-14043281483517902682992584),(-14043281483514228920102798)⟩,⟨8708367823542764827419375,8708367823546438591791824⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨5388773231256119128767489,5388773231258414324708261⟩,⟨11773542014411063105782575,11773542014413358300732389⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨9667498615529781667269891,9667498615530924679067244⟩,⟨(-2156201806028498497892369),(-2156201806027355485777118)⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨945441211752764105923522,945441211753211579908524⟩,⟨(-7337723828581178501058198),(-7337723828580731026670864)⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-4202820400950155419478783),(-4202820400950000448143788)⟩,⟨(-3283153440069326194644676),(-3283153440069171223907065)⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-3551244988659587345638547),(-3551244988659522600616031)⟩,⟨519937729624780680974532,519937729624845425934169⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-1580668262803273346865283),(-1580668262803251974995351)⟩,⟨1328582617826427453753511,1328582617826448825803452⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-374871460374743873604523),(-374871460374739351971489)⟩,⟨559033519886157125738183,559033519886161647460341⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨1155858569604759458837560,1155858569604759468277312⟩,⟨14378792539323824343247251,14378792539323824354647556⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨15843806437773361371747560,15843806437773361408045226⟩,⟨37747749967685019881114051,37747749967685019921073708⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨52596575390761579786853319,52596575390761579867734313⟩,⟨32536026799306518660995901,32536026799306518741058599⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨72468040553327222100286608,72468040553327222243481142⟩,⟨(-24842781320273409563196107),(-24842781320273409427133923)⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨12578589686599503808999641,12578589686599504072518307⟩,⟨(-84485245562895854858777061),(-84485245562895854592513403)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-78081983662770240553921348),(-78081983662770240049417135)⟩,⟨(-39551011637608402203640208),(-39551011637608401696990105)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-51571946099078037310893506),(-51571946099078036348735944)⟩,⟨65128498724081810370800442,65128498724081811329854586⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨52337056172054975465586431,52337056172054977232101288⟩,⟨52664678997112611597538356,52664678997112613366255560⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨48904166427089861758691826,48904166427089864965411739⟩,⟨(-40837300001892088634894245),(-40837300001892085429145136)⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-29300384854190585368382632),(-29300384854190578915198469)⟩,⟨(-44443998612698653250465872),(-44443998612698646797213875)⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-40398018069795319920254906),(-40398018069795303614749890)⟩,⟨16244580760266475322024013,16244580760266491627715584⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨1232547129418846567529361,1232547129418889506062059⟩,⟨34643109524972201718666578,34643109524972244657445856⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨23035581036444892554864683,23035581036444969285872511⟩,⟨12773760138022477846401226,12773760138022554576754339⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨17617082329223322372874664,17617082329223449870139084⟩,⟨(-5312355671000275675685566),(-5312355671000148178502145)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨7235159613661389831919024,7235159613661497698986080⟩,⟨(-8057607526495079397835835),(-8057607526494971530492901)⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨1565286779089246308741582,1565286779089283837747379⟩,⟨(-3205724745872079448479581),(-3205724745872041919329567)⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨11294050376079104171946052,11294050376083226830893576⟩,⟨1738816275380169404425524,1738816275384292063495755⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨40616493024030407604361353,40616493024030407645553996⟩,⟨5267581095613204317463873,5267581095613204356480425⟩⟩
end hm27_0_0_12
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert15
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

namespace SharpPlanar.Numerical.U15
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def wuplusBox := matrixMulBox WplusBox entries
end SharpPlanar.Numerical.U15

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert19
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

namespace SharpPlanar.Numerical.U19
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def wuplusBox := matrixMulBox WplusBox entries
end SharpPlanar.Numerical.U19

end OAI
end


