-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0060GraphCenterB__11_q01_q00_q02
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0060GraphCenterB__11_q01_q00_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T06:03:49.20517+00:00
-- url     : https://prove2.me/theorems/d1daa781-0738-4846-819f-2437d1517b6f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0060GraphCenterB (+10 modules: GeneralCK.Certificates.E8TAxisZero0061GraphCenterB, GeneralCK.Certificates.E8TAxisZero0062Gra…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0060GraphCenterB (+10 modules: GeneralCK.Certificates.E8TAxisZero0061GraphCenterB, GeneralCK.Certificates.E8TAxisZero0062GraphCenterB, GeneralCK.Certificates.E8TAxisZero0063GraphCenterB, GeneralCK.Certificates.E8TAxisZero0064GraphCenterB, GeneralCK.Certificates.E8TAxisZero0065GraphCenterB, GeneralCK.Certificates.E8TAxisZero0066GraphCenterB, GeneralCK.Certificates.E8TAxisZero0067GraphCenterB, GeneralCK.Certificates.E8TAxisZero0068GraphCenterB, GeneralCK.Certificates.E8TAxisZero0069GraphCenterB, GeneralCK.Certificates.E8TAxisZero0070GraphCenterB) (piece 2 of 11) (piece 1 of 3) (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0060GraphCenterB (+10 modules: GeneralCK.Certificates.E8TAxisZero0061GraphCenterB, GeneralCK.Certificates.E8TAxisZero0062GraphCenterB, GeneralCK.Certificates.E8TAxisZero0063GraphCenterB, GeneralCK.Certificates.E8TAxisZero0064GraphCenterB, GeneralCK.Certificates.E8TAxisZero0065GraphCenterB, GeneralCK.Certificates.E8TAxisZero0066GraphCenterB, GeneralCK.Certificates.E8TAxisZero0067GraphCenterB, GeneralCK.Certificates.E8TAxisZero0068GraphCenterB, GeneralCK.Certificates.E8TAxisZero0069GraphCenterB, GeneralCK.Certificates.E8TAxisZero0070GraphCenterB) (piece 2 of 11) (piece 1 of 3) (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0060GraphCenterB (+10 modules: GeneralCK.Certificates.E8TAxisZero0061GraphCenterB, GeneralCK.Certificates.E8TAxisZero0062GraphCenterB, GeneralCK.Certificates.E8TAxisZero0063GraphCenterB, GeneralCK.Certificates.E8TAxisZero0064GraphCenterB, GeneralCK.Certificates.E8TAxisZero0065GraphCenterB, GeneralCK.Certificates.E8TAxisZero0066GraphCenterB, GeneralCK.Certificates.E8TAxisZero0067GraphCenterB, GeneralCK.Certificates.E8TAxisZero0068GraphCenterB, GeneralCK.Certificates.E8TAxisZero0069GraphCenterB, GeneralCK.Certificates.E8TAxisZero0070GraphCenterB) (piece 2 of 11) (piece 1 of 3) (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0060GraphCenterB (+10 modules: GeneralCK/Certificates/E8TAxisZero0061GraphCenterB, GeneralCK/Certificates/E8TAxisZero0062GraphCenterB, GeneralCK/Certificates/E8TAxisZero0063GraphCenterB, GeneralCK/Certificates/E8TAxisZero0064GraphCenterB, GeneralCK/Certificates/E8TAxisZero0065GraphCenterB, GeneralCK/Certificates/E8TAxisZero0066GraphCenterB, GeneralCK/Certificates/E8TAxisZero0067GraphCenterB, GeneralCK/Certificates/E8TAxisZero0068GraphCenterB, GeneralCK/Certificates/E8TAxisZero0069GraphCenterB, GeneralCK/Certificates/E8TAxisZero0070GraphCenterB) (piece 2 of 11) (piece 1 of 3) (piece 3 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0060GraphCenterB__11_q01_q00_q01

namespace GeneralCK.Certificates.E8TAxisZero0061GraphCenterB
open DyadicInterval E8TAxisStableInterval E8TAxisZero0061PaddedInputs
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def onePlusZInv : DyadicJet5Enclosure precision :=
  ⟨⟨1361994401588732616559200951439043787992608398517, 1361994401588732616559200951439043789902381862626⟩,
   ⟨185464449079807389886017370506254201615238445189, 185464449079807389886017370506254205954897765901⟩,
   ⟨-320419054899828762344960872583037078210870218850, -320419054899828762344960872583037067238628979166⟩,
   ⟨459432698784930780431246579223497578487611502707, 459432698784930780431246579223497610994353396793⟩,
   ⟨-305808517935464137939675365621280479804365311476, -305808517935464137939675365621280363193786857573⟩,
   ⟨-1247481810526480710328019855975758129709760250009, -1247481810526480710328019855975757625122400478528⟩⟩

theorem onePlusZInv_checked : onePlusZ.inv = onePlusZInv := by decide

def rData : DyadicJet5Enclosure precision :=
  ⟨⟨1262487165846562314914717070161804556329284254059, 1262487165846562314914717070161804560148831182276⟩,
   ⟨370928898159614779772034741012508403230476890378, 370928898159614779772034741012508411909795531803⟩,
   ⟨-640838109799657524689921745166074156345741672373, -640838109799657524689921745166074134553256723661⟩,
   ⟨918865397569861560862493158446995157887208189361, 918865397569861560862493158446995221076721609641⟩,
   ⟨-611617035870928275879350731242560951991943510777, -611617035870928275879350731242560734004360827318⟩,
   ⟨-2494963621052961420656039711951516206070094094971, -2494963621052961420656039711951515303594227362049⟩⟩

theorem rData_checked : rNumerator.mul onePlusZInv = rData := by decide

def qNumerator : DyadicJet5Enclosure precision :=
  ⟨⟨427108915554465052821101558688646341000047632684, 427108915554465052821101558688646349796140654896⟩,
   ⟨-854217831108930105642203117377292699592281309792, -854217831108930105642203117377292682000095265368⟩,
   ⟨1708435662217860211284406234754585364000190530736, 1708435662217860211284406234754585399184562619584⟩,
   ⟨-3416871324435720422568812469509170798369125239168, -3416871324435720422568812469509170728000381061472⟩,
   ⟨6833742648871440845137624939018341456000762122944, 6833742648871440845137624939018341596738250478336⟩,
   ⟨-13667485297742881690275249878036683193476500956672, -13667485297742881690275249878036682912001524245888⟩⟩

theorem qNumerator_checked : four.mul zData = qNumerator := by decide

def qDenominator : DyadicJet5Enclosure precision :=
  ⟨⟨1682857233552259218110031398995202659728723265711, 1682857233552259218110031398995202664448090811967⟩,
   ⟨-458313469330960146804284706427032229372492421066, -458313469330960146804284706427032219291115258256⟩,
   ⟨979036046214910481574935708330836195164365767656, 979036046214910481574935708330836217897688374467⟩,
   ⟨-2207708522641781715015336598568759472406190878278, -2207708522641781715015336598568759416657272539890⟩,
   ⟨5413962766131406437492533924765866938628709098090, 5413962766131406437492533924765867091255638273941⟩,
   ⟨-14822108415654184904832510760045126768284302617416, -14822108415654184904832510760045126298514074269426⟩⟩

theorem qDenominator_checked : onePlusZ.mul onePlusZ = qDenominator := by decide

def qDenominatorInv : DyadicJet5Enclosure precision :=
  ⟨⟨1269262177048828921616192266185916685275215711814, 1269262177048828921616192266185916688834706443783⟩,
   ⟨345673976529721771058497806797772735376201620291, 345673976529721771058497806797772744918684189809⟩,
   ⟨-550135404292294152560584162194785885672765635213, -550135404292294152560584162194785854517716012552⟩,
   ⟨612336957752662849401084262034137741503218652029, 612336957752662849401084262034137869477822331991⟩,
   ⟨317932387327776217224334562366598190672016128631, 317932387327776217224334562366598843745912066578⟩,
   ⟨-4727680225102833415201114623729471799755329163532, -4727680225102833415201114623729467795474352191302⟩⟩

end GeneralCK.Certificates.E8TAxisZero0061GraphCenterB


