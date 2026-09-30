-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0060GraphCenterB__11_q01_q01_q02
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0060GraphCenterB__11_q01_q01_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T07:36:06.288969+00:00
-- url     : https://prove2.me/theorems/167d4843-2419-4266-8527-f9b7f7a4075b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0060GraphCenterB (+10 modules: GeneralCK.Certificates.E8TAxisZero0061GraphCenterB, GeneralCK.Certificates.E8TAxisZero0062Gra…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0060GraphCenterB (+10 modules: GeneralCK.Certificates.E8TAxisZero0061GraphCenterB, GeneralCK.Certificates.E8TAxisZero0062GraphCenterB, GeneralCK.Certificates.E8TAxisZero0063GraphCenterB, GeneralCK.Certificates.E8TAxisZero0064GraphCenterB, GeneralCK.Certificates.E8TAxisZero0065GraphCenterB, GeneralCK.Certificates.E8TAxisZero0066GraphCenterB, GeneralCK.Certificates.E8TAxisZero0067GraphCenterB, GeneralCK.Certificates.E8TAxisZero0068GraphCenterB, GeneralCK.Certificates.E8TAxisZero0069GraphCenterB, GeneralCK.Certificates.E8TAxisZero0070GraphCenterB) (piece 2 of 11) (piece 2 of 3) (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0060GraphCenterB (+10 modules: GeneralCK.Certificates.E8TAxisZero0061GraphCenterB, GeneralCK.Certificates.E8TAxisZero0062GraphCenterB, GeneralCK.Certificates.E8TAxisZero0063GraphCenterB, GeneralCK.Certificates.E8TAxisZero0064GraphCenterB, GeneralCK.Certificates.E8TAxisZero0065GraphCenterB, GeneralCK.Certificates.E8TAxisZero0066GraphCenterB, GeneralCK.Certificates.E8TAxisZero0067GraphCenterB, GeneralCK.Certificates.E8TAxisZero0068GraphCenterB, GeneralCK.Certificates.E8TAxisZero0069GraphCenterB, GeneralCK.Certificates.E8TAxisZero0070GraphCenterB) (piece 2 of 11) (piece 2 of 3) (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0060GraphCenterB (+10 modules: GeneralCK.Certificates.E8TAxisZero0061GraphCenterB, GeneralCK.Certificates.E8TAxisZero0062GraphCenterB, GeneralCK.Certificates.E8TAxisZero0063GraphCenterB, GeneralCK.Certificates.E8TAxisZero0064GraphCenterB, GeneralCK.Certificates.E8TAxisZero0065GraphCenterB, GeneralCK.Certificates.E8TAxisZero0066GraphCenterB, GeneralCK.Certificates.E8TAxisZero0067GraphCenterB, GeneralCK.Certificates.E8TAxisZero0068GraphCenterB, GeneralCK.Certificates.E8TAxisZero0069GraphCenterB, GeneralCK.Certificates.E8TAxisZero0070GraphCenterB) (piece 2 of 11) (piece 2 of 3) (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0060GraphCenterB (+10 modules: GeneralCK/Certificates/E8TAxisZero0061GraphCenterB, GeneralCK/Certificates/E8TAxisZero0062GraphCenterB, GeneralCK/Certificates/E8TAxisZero0063GraphCenterB, GeneralCK/Certificates/E8TAxisZero0064GraphCenterB, GeneralCK/Certificates/E8TAxisZero0065GraphCenterB, GeneralCK/Certificates/E8TAxisZero0066GraphCenterB, GeneralCK/Certificates/E8TAxisZero0067GraphCenterB, GeneralCK/Certificates/E8TAxisZero0068GraphCenterB, GeneralCK/Certificates/E8TAxisZero0069GraphCenterB, GeneralCK/Certificates/E8TAxisZero0070GraphCenterB) (piece 2 of 11) (piece 2 of 3) (piece 3 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0060GraphCenterB__11_q01_q01_q01

namespace GeneralCK.Certificates.E8TAxisZero0061GraphCenterB
open DyadicInterval E8TAxisStableInterval E8TAxisZero0061PaddedInputs
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def xDenominatorInv : DyadicJet5Enclosure precision :=
  ⟨⟨2938771129523231779843898984002198229320177405428, 2938771129523231779843898984002198293414484009199⟩,
   ⟨3924101011129305109819351542177671723889624462264, 3924101011129305109819351542177672066581476115383⟩,
   ⟨6699626977072801764086952925828166478431650929126, 6699626977072801764086952925828168710740735464944⟩,
   ⟨11052190195466138622962276360036702508705248971329, 11052190195466138622962276360036720044835395866138⟩,
   ⟨19711020029088362441562976901520732442683483184989, 19711020029088362441562976901520896757873836011128⟩,
   ⟨34219894169989398098490131222126952626801783043249, 34219894169989398098490131222128759742228260462110⟩⟩

theorem xDenominatorInv_checked : xDenominator.inv = xDenominatorInv := by decide

def xJetBox : DyadicJet5Enclosure precision :=
  ⟨⟨1759620007318940711272892992776945386425224575758, 1759620007318940711272892992776945433945595386335⟩,
   ⟨2866587129769104662926223766218605334426240641430, 2866587129769104662926223766218605576320165669425⟩,
   ⟨4498950072886687120560416889760073673043718633859, 4498950072886687120560416889760075238175285682476⟩,
   ⟨7856148714630221992060928519919707541583011499202, 7856148714630221992060928519919719905134775452098⟩,
   ⟨13349975583844745108237209156258818465665536884118, 13349975583844745108237209156258935370840626621883⟩,
   ⟨24263992778192763810389770809634004834615800978029, 24263992778192763810389770809635302137237147021534⟩⟩

theorem xJetBox_checked : xNumerator.mul xDenominatorInv = xJetBox := by decide

def logtwoInv : DyadicJet5Enclosure precision :=
  ⟨⟨2108501164428393954197770173035669512474567507196, 2108501164428393954197770173035669517051546299815⟩,
   ⟨0, 0⟩,
   ⟨0, 0⟩,
   ⟨0, 0⟩,
   ⟨0, 0⟩,
   ⟨0, 0⟩⟩

theorem logtwoInv_checked : logtwo.inv = logtwoInv := by decide

def yConstant : DyadicJet5Enclosure precision :=
  ⟨⟨4217002328856787908395540346071339024949135014392, 4217002328856787908395540346071339034103092599630⟩,
   ⟨0, 0⟩,
   ⟨0, 0⟩,
   ⟨0, 0⟩,
   ⟨0, 0⟩,
   ⟨0, 0⟩⟩

theorem yConstant_checked : two.mul logtwoInv = yConstant := by decide

def yNumerator : DyadicJet5Enclosure precision :=
  ⟨⟨313928335802955861567617133380568281099629627373, 313928335802955861567617133380568288896138794459⟩,
   ⟨-326949551905250245077204169208463815046947605833, -326949551905250245077204169208463791286287472604⟩,
   ⟨-1881598157233311186045847541315176898248491338, -1881598157233311186045847541315100513185425699⟩,
   ⟨1291470705663861926036639392172229872144596445819, 1291470705663861926036639392172230134263284400542⟩,
   ⟨-4211475567199486385471583510478292248548298713843, -4211475567199486385471583510478291271118147564845⟩,
   ⟨5435016766252930995025005564279630993204348427341, 5435016766252930995025005564279635002209542090259⟩⟩

end GeneralCK.Certificates.E8TAxisZero0061GraphCenterB


