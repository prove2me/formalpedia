-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0060GraphCenterB__11_q01_q01_q01
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0060GraphCenterB__11_q01_q01_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T07:27:53.424982+00:00
-- url     : https://prove2.me/theorems/d056665d-c646-49d8-a43e-a7a5b74602ae
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0060GraphCenterB (+10 modules: GeneralCK.Certificates.E8TAxisZero0061GraphCenterB, GeneralCK.Certificates.E8TAxisZero0062Gra…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0060GraphCenterB (+10 modules: GeneralCK.Certificates.E8TAxisZero0061GraphCenterB, GeneralCK.Certificates.E8TAxisZero0062GraphCenterB, GeneralCK.Certificates.E8TAxisZero0063GraphCenterB, GeneralCK.Certificates.E8TAxisZero0064GraphCenterB, GeneralCK.Certificates.E8TAxisZero0065GraphCenterB, GeneralCK.Certificates.E8TAxisZero0066GraphCenterB, GeneralCK.Certificates.E8TAxisZero0067GraphCenterB, GeneralCK.Certificates.E8TAxisZero0068GraphCenterB, GeneralCK.Certificates.E8TAxisZero0069GraphCenterB, GeneralCK.Certificates.E8TAxisZero0070GraphCenterB) (piece 2 of 11) (piece 2 of 3) (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0060GraphCenterB (+10 modules: GeneralCK.Certificates.E8TAxisZero0061GraphCenterB, GeneralCK.Certificates.E8TAxisZero0062GraphCenterB, GeneralCK.Certificates.E8TAxisZero0063GraphCenterB, GeneralCK.Certificates.E8TAxisZero0064GraphCenterB, GeneralCK.Certificates.E8TAxisZero0065GraphCenterB, GeneralCK.Certificates.E8TAxisZero0066GraphCenterB, GeneralCK.Certificates.E8TAxisZero0067GraphCenterB, GeneralCK.Certificates.E8TAxisZero0068GraphCenterB, GeneralCK.Certificates.E8TAxisZero0069GraphCenterB, GeneralCK.Certificates.E8TAxisZero0070GraphCenterB) (piece 2 of 11) (piece 2 of 3) (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0060GraphCenterB (+10 modules: GeneralCK.Certificates.E8TAxisZero0061GraphCenterB, GeneralCK.Certificates.E8TAxisZero0062GraphCenterB, GeneralCK.Certificates.E8TAxisZero0063GraphCenterB, GeneralCK.Certificates.E8TAxisZero0064GraphCenterB, GeneralCK.Certificates.E8TAxisZero0065GraphCenterB, GeneralCK.Certificates.E8TAxisZero0066GraphCenterB, GeneralCK.Certificates.E8TAxisZero0067GraphCenterB, GeneralCK.Certificates.E8TAxisZero0068GraphCenterB, GeneralCK.Certificates.E8TAxisZero0069GraphCenterB, GeneralCK.Certificates.E8TAxisZero0070GraphCenterB) (piece 2 of 11) (piece 2 of 3) (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0060GraphCenterB (+10 modules: GeneralCK/Certificates/E8TAxisZero0061GraphCenterB, GeneralCK/Certificates/E8TAxisZero0062GraphCenterB, GeneralCK/Certificates/E8TAxisZero0063GraphCenterB, GeneralCK/Certificates/E8TAxisZero0064GraphCenterB, GeneralCK/Certificates/E8TAxisZero0065GraphCenterB, GeneralCK/Certificates/E8TAxisZero0066GraphCenterB, GeneralCK/Certificates/E8TAxisZero0067GraphCenterB, GeneralCK/Certificates/E8TAxisZero0068GraphCenterB, GeneralCK/Certificates/E8TAxisZero0069GraphCenterB, GeneralCK/Certificates/E8TAxisZero0070GraphCenterB) (piece 2 of 11) (piece 2 of 3) (piece 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0060GraphCenterB__11_q01_q01_q00

namespace GeneralCK.Certificates.E8TAxisZero0061GraphCenterB
open DyadicInterval E8TAxisStableInterval E8TAxisZero0061PaddedInputs
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem twiceAlphaZ_checked : twiceAlpha.mul zData = twiceAlphaZ := by decide

def hCorrection : DyadicJet5Enclosure precision :=
  ⟨⟨260358196003689953659638723299182834147480659593, 260358196003689953659638723299182839874502536730⟩,
   ⟨-286248625466237997755063824811651410067446486211, -286248625466237997755063824811651393234145231691⟩,
   ⟨96510654745806490559581950438166177053873254096, 96510654745806490559581950438166224685879320235⟩,
   ⟨720420152542458999920967129949594853085591034783, 720420152542458999920967129949594989655961671375⟩,
   ⟨-2875321244118696177703214937981140046217756301862, -2875321244118696177703214937981139632653801959429⟩,
   ⟨6322090166666809304063892618733651043612853495605, 6322090166666809304063892618733652419684364820676⟩⟩

theorem hCorrection_checked : twiceAlphaZ.mul onePlusZInv = hCorrection := by decide

def hData : DyadicJet5Enclosure precision :=
  ⟨⟨363415002696627064391777385443573646278824022321, 363415002696627064391777385443573654204869155011⟩,
   ⟨-485263096950578601044031587366129873673150662708, -485263096950578601044031587366129852462190704812⟩,
   ⟨467439552905421270331616691450674579650239603987, 467439552905421270331616691450674637229785392526⟩,
   ⟨79582042742801475231045384783520695212585450032, 79582042742801475231045384783520856629968860091⟩,
   ⟨-1956455846548834616840721779534144892168444462708, -1956455846548834616840721779534144407739183999582⟩,
   ⟨5710473130795881028184541887491090082198572256686, 5710473130795881028184541887491091695102341721503⟩⟩

theorem hData_checked : l1Data.add hCorrection = hData := by decide

def xNumerator : DyadicJet5Enclosure precision :=
  ⟨⟨875089419499660747992645858213075521577811108283, 875089419499660747992645858213075526124898852836⟩,
   ⟨257108319947544071137085403864549487427468998878, 257108319947544071137085403864549494001626019524⟩,
   ⟨-444195129002997271882723036902175294346863137528, -444195129002997271882723036902175278277237618270⟩,
   ⟨636908959639642763257279640493783089685802065580, 636908959639642763257279640493783134867990121335⟩,
   ⟨-423940623996364868803631270542208393492318913072, -423940623996364868803631270542208241474581544671⟩,
   ⟨-1729376999532492016151766028934432112302510509251, -1729376999532492016151766028934431482999903938100⟩⟩

theorem xNumerator_checked : logtwo.mul rData = xNumerator := by decide

def xDenominator : DyadicJet5Enclosure precision :=
  ⟨⟨726830005393254128783554770887147292557648044642, 726830005393254128783554770887147308409738310022⟩,
   ⟨-970526193901157202088063174732259747346301325416, -970526193901157202088063174732259704924381409624⟩,
   ⟨934879105810842540663233382901349159300479207974, 934879105810842540663233382901349274459570785052⟩,
   ⟨159164085485602950462090769567041390425170900064, 159164085485602950462090769567041713259937720182⟩,
   ⟨-3912911693097669233681443559068289784336888925416, -3912911693097669233681443559068288815478367999164⟩,
   ⟨11420946261591762056369083774982180164397144513372, 11420946261591762056369083774982183390204683443006⟩⟩

theorem xDenominator_checked : two.mul hData = xDenominator := by decide

end GeneralCK.Certificates.E8TAxisZero0061GraphCenterB


