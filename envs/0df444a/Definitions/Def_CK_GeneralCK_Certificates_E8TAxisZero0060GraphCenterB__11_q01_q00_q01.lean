-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0060GraphCenterB__11_q01_q00_q01
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0060GraphCenterB__11_q01_q00_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T05:57:42.140623+00:00
-- url     : https://prove2.me/theorems/faad7320-dc12-4b87-be43-1e64eaa7c22c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0060GraphCenterB (+10 modules: GeneralCK.Certificates.E8TAxisZero0061GraphCenterB, GeneralCK.Certificates.E8TAxisZero0062Gra…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0060GraphCenterB (+10 modules: GeneralCK.Certificates.E8TAxisZero0061GraphCenterB, GeneralCK.Certificates.E8TAxisZero0062GraphCenterB, GeneralCK.Certificates.E8TAxisZero0063GraphCenterB, GeneralCK.Certificates.E8TAxisZero0064GraphCenterB, GeneralCK.Certificates.E8TAxisZero0065GraphCenterB, GeneralCK.Certificates.E8TAxisZero0066GraphCenterB, GeneralCK.Certificates.E8TAxisZero0067GraphCenterB, GeneralCK.Certificates.E8TAxisZero0068GraphCenterB, GeneralCK.Certificates.E8TAxisZero0069GraphCenterB, GeneralCK.Certificates.E8TAxisZero0070GraphCenterB) (piece 2 of 11) (piece 1 of 3) (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0060GraphCenterB (+10 modules: GeneralCK.Certificates.E8TAxisZero0061GraphCenterB, GeneralCK.Certificates.E8TAxisZero0062GraphCenterB, GeneralCK.Certificates.E8TAxisZero0063GraphCenterB, GeneralCK.Certificates.E8TAxisZero0064GraphCenterB, GeneralCK.Certificates.E8TAxisZero0065GraphCenterB, GeneralCK.Certificates.E8TAxisZero0066GraphCenterB, GeneralCK.Certificates.E8TAxisZero0067GraphCenterB, GeneralCK.Certificates.E8TAxisZero0068GraphCenterB, GeneralCK.Certificates.E8TAxisZero0069GraphCenterB, GeneralCK.Certificates.E8TAxisZero0070GraphCenterB) (piece 2 of 11) (piece 1 of 3) (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0060GraphCenterB (+10 modules: GeneralCK.Certificates.E8TAxisZero0061GraphCenterB, GeneralCK.Certificates.E8TAxisZero0062GraphCenterB, GeneralCK.Certificates.E8TAxisZero0063GraphCenterB, GeneralCK.Certificates.E8TAxisZero0064GraphCenterB, GeneralCK.Certificates.E8TAxisZero0065GraphCenterB, GeneralCK.Certificates.E8TAxisZero0066GraphCenterB, GeneralCK.Certificates.E8TAxisZero0067GraphCenterB, GeneralCK.Certificates.E8TAxisZero0068GraphCenterB, GeneralCK.Certificates.E8TAxisZero0069GraphCenterB, GeneralCK.Certificates.E8TAxisZero0070GraphCenterB) (piece 2 of 11) (piece 1 of 3) (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0060GraphCenterB (+10 modules: GeneralCK/Certificates/E8TAxisZero0061GraphCenterB, GeneralCK/Certificates/E8TAxisZero0062GraphCenterB, GeneralCK/Certificates/E8TAxisZero0063GraphCenterB, GeneralCK/Certificates/E8TAxisZero0064GraphCenterB, GeneralCK/Certificates/E8TAxisZero0065GraphCenterB, GeneralCK/Certificates/E8TAxisZero0066GraphCenterB, GeneralCK/Certificates/E8TAxisZero0067GraphCenterB, GeneralCK/Certificates/E8TAxisZero0068GraphCenterB, GeneralCK/Certificates/E8TAxisZero0069GraphCenterB, GeneralCK/Certificates/E8TAxisZero0070GraphCenterB) (piece 2 of 11) (piece 1 of 3) (piece 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0060GraphCenterB__11_q01_q00_q00

namespace GeneralCK.Certificates.E8TAxisZero0061GraphCenterB
open DyadicInterval E8TAxisStableInterval E8TAxisZero0061PaddedInputs
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem logtwo_checked : constant centerBInput.logTwo = logtwo := by decide

def zData : DyadicJet5Enclosure precision :=
  ⟨⟨106777228888616263205275389672161585250011908171, 106777228888616263205275389672161587449035163724⟩,
   ⟨-213554457777232526410550779344323174898070327448, -213554457777232526410550779344323170500023816342⟩,
   ⟨427108915554465052821101558688646341000047632684, 427108915554465052821101558688646349796140654896⟩,
   ⟨-854217831108930105642203117377292699592281309792, -854217831108930105642203117377292682000095265368⟩,
   ⟨1708435662217860211284406234754585364000190530736, 1708435662217860211284406234754585399184562619584⟩,
   ⟨-3416871324435720422568812469509170798369125239168, -3416871324435720422568812469509170728000381061472⟩⟩

theorem zData_checked : zBox centerBInput = zData := by decide

def onePlusZ : DyadicJet5Enclosure precision :=
  ⟨⟨1568278866219519181408960222388444604905944451147, 1568278866219519181408960222388444607104967706700⟩,
   ⟨-213554457777232526410550779344323174898070327448, -213554457777232526410550779344323170500023816342⟩,
   ⟨427108915554465052821101558688646341000047632684, 427108915554465052821101558688646349796140654896⟩,
   ⟨-854217831108930105642203117377292699592281309792, -854217831108930105642203117377292682000095265368⟩,
   ⟨1708435662217860211284406234754585364000190530736, 1708435662217860211284406234754585399184562619584⟩,
   ⟨-3416871324435720422568812469509170798369125239168, -3416871324435720422568812469509170728000381061472⟩⟩

theorem onePlusZ_checked : one.add zData = onePlusZ := by decide

def negativeZ : DyadicJet5Enclosure precision :=
  ⟨⟨-106777228888616263205275389672161587449035163724, -106777228888616263205275389672161585250011908171⟩,
   ⟨213554457777232526410550779344323170500023816342, 213554457777232526410550779344323174898070327448⟩,
   ⟨-427108915554465052821101558688646349796140654896, -427108915554465052821101558688646341000047632684⟩,
   ⟨854217831108930105642203117377292682000095265368, 854217831108930105642203117377292699592281309792⟩,
   ⟨-1708435662217860211284406234754585399184562619584, -1708435662217860211284406234754585364000190530736⟩,
   ⟨3416871324435720422568812469509170728000381061472, 3416871324435720422568812469509170798369125239168⟩⟩

theorem negativeZ_checked : negative zData = negativeZ := by decide

def rNumerator : DyadicJet5Enclosure precision :=
  ⟨⟨1354724408442286654998409443044121432206897379252, 1354724408442286654998409443044121434405920634805⟩,
   ⟨213554457777232526410550779344323170500023816342, 213554457777232526410550779344323174898070327448⟩,
   ⟨-427108915554465052821101558688646349796140654896, -427108915554465052821101558688646341000047632684⟩,
   ⟨854217831108930105642203117377292682000095265368, 854217831108930105642203117377292699592281309792⟩,
   ⟨-1708435662217860211284406234754585399184562619584, -1708435662217860211284406234754585364000190530736⟩,
   ⟨3416871324435720422568812469509170728000381061472, 3416871324435720422568812469509170798369125239168⟩⟩

theorem rNumerator_checked : one.add negativeZ = rNumerator := by decide

end GeneralCK.Certificates.E8TAxisZero0061GraphCenterB


