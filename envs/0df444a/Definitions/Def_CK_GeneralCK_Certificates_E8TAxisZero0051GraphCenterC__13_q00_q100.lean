-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0051GraphCenterC__13_q00_q100
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0051GraphCenterC__13_q00_q100
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T05:50:26.700432+00:00
-- url     : https://prove2.me/theorems/8bc54869-3694-42d6-ba7e-e5067f568b57
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0051GraphCenterC (+12 modules: GeneralCK.Certificates.E8TAxisZero0052GraphCenterC, GeneralCK.Certificates.E8TAxisZero0053Gra…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0051GraphCenterC (+12 modules: GeneralCK.Certificates.E8TAxisZero0052GraphCenterC, GeneralCK.Certificates.E8TAxisZero0053GraphCenterC, GeneralCK.Certificates.E8TAxisZero0054GraphCenterC, GeneralCK.Certificates.E8TAxisZero0055GraphCenterC, GeneralCK.Certificates.E8TAxisZero0056GraphCenterC, GeneralCK.Certificates.E8TAxisZero0057GraphCenterC, GeneralCK.Certificates.E8TAxisZero0058GraphCenterC, GeneralCK.Certificates.E8TAxisZero0059GraphCenterC, GeneralCK.Certificates.E8TAxisZero0060GraphCenterC, GeneralCK.Certificates.E8TAxisZero0061GraphCenterC, GeneralCK.Certificates.E8TAxisZero0062GraphCenterC, GeneralCK.Certificates.E8TAxisZero0063GraphCenterC) (piece 1 of 13) (piece 1 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0051GraphCenterC (+12 modules: GeneralCK.Certificates.E8TAxisZero0052GraphCenterC, GeneralCK.Certificates.E8TAxisZero0053GraphCenterC, GeneralCK.Certificates.E8TAxisZero0054GraphCenterC, GeneralCK.Certificates.E8TAxisZero0055GraphCenterC, GeneralCK.Certificates.E8TAxisZero0056GraphCenterC, GeneralCK.Certificates.E8TAxisZero0057GraphCenterC, GeneralCK.Certificates.E8TAxisZero0058GraphCenterC, GeneralCK.Certificates.E8TAxisZero0059GraphCenterC, GeneralCK.Certificates.E8TAxisZero0060GraphCenterC, GeneralCK.Certificates.E8TAxisZero0061GraphCenterC, GeneralCK.Certificates.E8TAxisZero0062GraphCenterC, GeneralCK.Certificates.E8TAxisZero0063GraphCenterC) (piece 1 of 13) (piece 1 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0051GraphCenterC (+12 modules: GeneralCK.Certificates.E8TAxisZero0052GraphCenterC, GeneralCK.Certificates.E8TAxisZero0053GraphCenterC, GeneralCK.Certificates.E8TAxisZero0054GraphCenterC, GeneralCK.Certificates.E8TAxisZero0055GraphCenterC, GeneralCK.Certificates.E8TAxisZero0056GraphCenterC, GeneralCK.Certificates.E8TAxisZero0057GraphCenterC, GeneralCK.Certificates.E8TAxisZero0058GraphCenterC, GeneralCK.Certificates.E8TAxisZero0059GraphCenterC, GeneralCK.Certificates.E8TAxisZero0060GraphCenterC, GeneralCK.Certificates.E8TAxisZero0061GraphCenterC, GeneralCK.Certificates.E8TAxisZero0062GraphCenterC, GeneralCK.Certificates.E8TAxisZero0063GraphCenterC) (piece 1 of 13) (piece 1 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0051GraphCenterC (+12 modules: GeneralCK/Certificates/E8TAxisZero0052GraphCenterC, GeneralCK/Certificates/E8TAxisZero0053GraphCenterC, GeneralCK/Certificates/E8TAxisZero0054GraphCenterC, GeneralCK/Certificates/E8TAxisZero0055GraphCenterC, GeneralCK/Certificates/E8TAxisZero0056GraphCenterC, GeneralCK/Certificates/E8TAxisZero0057GraphCenterC, GeneralCK/Certificates/E8TAxisZero0058GraphCenterC, GeneralCK/Certificates/E8TAxisZero0059GraphCenterC, GeneralCK/Certificates/E8TAxisZero0060GraphCenterC, GeneralCK/Certificates/E8TAxisZero0061GraphCenterC, GeneralCK/Certificates/E8TAxisZero0062GraphCenterC, GeneralCK/Certificates/E8TAxisZero0063GraphCenterC) (piece 1 of 13) (piece 1 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0051GraphCenterC__13_q00_q01


namespace GeneralCK.Certificates.E8TAxisZero0051GraphCenterC
open DyadicInterval E8TAxisStableInterval E8TAxisZero0051PaddedInputs
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def yDenominator : DyadicJet5Enclosure precision :=
  ⟨⟨894246106779736018692617332419250704310064996512, 894246106779736018692617332419250712482032893532⟩,
   ⟨-411852022332323673112867049695174949999090743014, -411852022332323673112867049695174914940725951979⟩,
   ⟨-695048194442017661084911952340172873881391719455, -695048194442017661084911952340172686639464685759⟩,
   ⟨790495469467110544689628712081504946426365362784, 790495469467110544689628712081506286240233370569⟩,
   ⟨5093630097065026876168313702618739705537379042000, 5093630097065026876168313702618752259424711448655⟩,
   ⟨-8629761220025045612698057398917952777791307847933, -8629761220025045612698057398917806256452528474396⟩⟩

theorem yDenominator_checked : qData.mul ellData = yDenominator := by decide

def yDenominatorInv : DyadicJet5Enclosure precision :=
  ⟨⟨2388589695528895781306437673831299309467781438312, 2388589695528895781306437673831299331295640864289⟩,
   ⟨1100083622581578413980056779075173488046613939550, 1100083622581578413980056779075173601795775614753⟩,
   ⟨2869823267972101931271006251806948582569511660371, 2869823267972101931271006251806949316928387628355⟩,
   ⟨4418796564048748559535977688622752744397913410792, 4418796564048748559535977688622758729824712793117⟩,
   ⟨4028552342139249841316258703325521656078008067517, 4028552342139249841316258703325582147147890808436⟩,
   ⟨9973365694771603878364541068064093249336708266874, 9973365694771603878364541068064830189390691780493⟩⟩

theorem yDenominatorInv_checked : yDenominator.inv = yDenominatorInv := by decide

def yCorrection : DyadicJet5Enclosure precision :=
  ⟨⟨697177791009908701049878872983800809011829722792, 697177791009908701049878872983800821887099970219⟩,
   ⟨669174289088382107300186825939940270051082967867, 669174289088382107300186825939940336009499298235⟩,
   ⟨-1579507292210039293930202654226004996859113728481, -1579507292210039293930202654226004574658429092632⟩,
   ⟨1817389176227994304701152671137974361829755169678, 1817389176227994304701152671137977682989175929676⟩,
   ⟨6226188179226378773871995596409205975144571393761, 6226188179226378773871995596409238059029296563811⟩,
   ⟨-50556800634334221519208717335925044342379191552941, -50556800634334221519208717335924666582034419034542⟩⟩

theorem yCorrection_checked : yNumerator.mul yDenominatorInv = yCorrection := by decide

def ySum : DyadicJet5Enclosure precision :=
  ⟨⟨1586746370095223806031220417861130006121604215898, 1586746370095223806031220417861130018996908017758⟩,
   ⟨2130675926419285025503871658656223289707015510843, 2130675926419285025503871658656223355665431841211⟩,
   ⟨-1579507292210039293930202654226004996859113728481, -1579507292210039293930202654226004574658429092632⟩,
   ⟨1817389176227994304701152671137974361829755169678, 1817389176227994304701152671137977682989175929676⟩,
   ⟨6226188179226378773871995596409205975144571393761, 6226188179226378773871995596409238059029296563811⟩,
   ⟨-50556800634334221519208717335925044342379191552941, -50556800634334221519208717335924666582034419034542⟩⟩

theorem ySum_checked : alphaJet.add yCorrection = ySum := by decide

def yJetBox : DyadicJet5Enclosure precision :=
  ⟨⟨4578382238569886344854012064238868454749685767553, 4578382238569886344854012064238868501838374093110⟩,
   ⟨6147831185573200796340321845301564419886492719601, 6147831185573200796340321845301564623547511447428⟩,
   ⟨-4557494675038757023982180448143241289773727735564, -4557494675038757023982180448143240061666986513770⟩,
   ⟨5243876703818811534278572172654783886887327208044, 5243876703818811534278572172654793481110800602538⟩,
   ⟨17964981619622762305791153470401882117706801853070, 17964981619622762305791153470401974731226629664999⟩,
   ⟨-145876091116731961690275664608997150826149823017854, -145876091116731961690275664608996060523540669442934⟩⟩

end GeneralCK.Certificates.E8TAxisZero0051GraphCenterC


