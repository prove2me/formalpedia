-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0060GraphWholeC__12_q05_q00_q02
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0060GraphWholeC__12_q05_q00_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T07:45:42.024279+00:00
-- url     : https://prove2.me/theorems/8c731244-efea-4e30-ad74-e8f3a4323962
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0060GraphWholeC (+11 modules: GeneralCK.Certificates.E8TAxisZero0061GraphWholeC, GeneralCK.Certificates.E8TAxisZero0062Graph…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0060GraphWholeC (+11 modules: GeneralCK.Certificates.E8TAxisZero0061GraphWholeC, GeneralCK.Certificates.E8TAxisZero0062GraphWholeC, GeneralCK.Certificates.E8TAxisZero0063GraphWholeC, GeneralCK.Certificates.E8TAxisZero0064GraphWholeC, GeneralCK.Certificates.E8TAxisZero0065GraphWholeC, GeneralCK.Certificates.E8TAxisZero0066GraphWholeC, GeneralCK.Certificates.E8TAxisZero0067GraphWholeC, GeneralCK.Certificates.E8TAxisZero0068GraphWholeC, GeneralCK.Certificates.E8TAxisZero0069GraphWholeC, GeneralCK.Certificates.E8TAxisZero0070GraphWholeC, GeneralCK.Certificates.E8TAxisZero0071GraphWholeC) (piece 6 of 12) (piece 1 of 3) (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0060GraphWholeC (+11 modules: GeneralCK.Certificates.E8TAxisZero0061GraphWholeC, GeneralCK.Certificates.E8TAxisZero0062GraphWholeC, GeneralCK.Certificates.E8TAxisZero0063GraphWholeC, GeneralCK.Certificates.E8TAxisZero0064GraphWholeC, GeneralCK.Certificates.E8TAxisZero0065GraphWholeC, GeneralCK.Certificates.E8TAxisZero0066GraphWholeC, GeneralCK.Certificates.E8TAxisZero0067GraphWholeC, GeneralCK.Certificates.E8TAxisZero0068GraphWholeC, GeneralCK.Certificates.E8TAxisZero0069GraphWholeC, GeneralCK.Certificates.E8TAxisZero0070GraphWholeC, GeneralCK.Certificates.E8TAxisZero0071GraphWholeC) (piece 6 of 12) (piece 1 of 3) (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0060GraphWholeC (+11 modules: GeneralCK.Certificates.E8TAxisZero0061GraphWholeC, GeneralCK.Certificates.E8TAxisZero0062GraphWholeC, GeneralCK.Certificates.E8TAxisZero0063GraphWholeC, GeneralCK.Certificates.E8TAxisZero0064GraphWholeC, GeneralCK.Certificates.E8TAxisZero0065GraphWholeC, GeneralCK.Certificates.E8TAxisZero0066GraphWholeC, GeneralCK.Certificates.E8TAxisZero0067GraphWholeC, GeneralCK.Certificates.E8TAxisZero0068GraphWholeC, GeneralCK.Certificates.E8TAxisZero0069GraphWholeC, GeneralCK.Certificates.E8TAxisZero0070GraphWholeC, GeneralCK.Certificates.E8TAxisZero0071GraphWholeC) (piece 6 of 12) (piece 1 of 3) (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0060GraphWholeC (+11 modules: GeneralCK/Certificates/E8TAxisZero0061GraphWholeC, GeneralCK/Certificates/E8TAxisZero0062GraphWholeC, GeneralCK/Certificates/E8TAxisZero0063GraphWholeC, GeneralCK/Certificates/E8TAxisZero0064GraphWholeC, GeneralCK/Certificates/E8TAxisZero0065GraphWholeC, GeneralCK/Certificates/E8TAxisZero0066GraphWholeC, GeneralCK/Certificates/E8TAxisZero0067GraphWholeC, GeneralCK/Certificates/E8TAxisZero0068GraphWholeC, GeneralCK/Certificates/E8TAxisZero0069GraphWholeC, GeneralCK/Certificates/E8TAxisZero0070GraphWholeC, GeneralCK/Certificates/E8TAxisZero0071GraphWholeC) (piece 6 of 12) (piece 1 of 3) (piece 3 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0060GraphWholeC__12_q05_q00_q01

namespace GeneralCK.Certificates.E8TAxisZero0065GraphWholeC
open DyadicInterval E8TAxisStableInterval E8TAxisZero0065PaddedInputs
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def onePlusZInv : DyadicJet5Enclosure precision :=
  ⟨⟨1062706665216651286304614466603231177233158783097, 1067394723526269079855381710620158306367570101758⟩,
   ⟨570619357532906087426709443165040075757590252740, 585082438041437214578275280674891926631466559595⟩,
   ⟨-557377807273277843371701542064437990998260416030, -499823778755069718818972890543230441089631795594⟩,
   ⟨-578905844222736473252439051652701201948372520099, -281635859497150945474139783285533451825462442081⟩,
   ⟨1940400147846218481190986038445537673437405244646, 3862007550613425796173759780287025104008106770207⟩,
   ⟨-9689717008953453911308785524052037236250429401043, 5238690096179865870154564825172531247569878035053⟩⟩

theorem onePlusZInv_checked : onePlusZ.inv = onePlusZInv := by decide

def rData : DyadicJet5Enclosure precision :=
  ⟨⟨663911693102399654405544100490179334810385023219, 673287809721635241507078588524033593079207660540⟩,
   ⟨1141238715065812174853418886330080151515180505481, 1170164876082874429156550561349783853262933119189⟩,
   ⟨-1111054236480507078295287065927494056866334258189, -1003521854631174520496592684760374242814171570394⟩,
   ⟨-1115854364821277683089672427530447230084500208260, -607024623264961108745231503785705069644548242394⟩,
   ⟨4236499903828319849496493464117649400063527700327, 7372003399316781782500619487075098868834539772764⟩,
   ⟨-16530035656662734891707008096688977313309377996529, 7685973826552533978589698709222016687604702577924⟩⟩

theorem rData_checked : rNumerator.mul onePlusZInv = rData := by decide

def qNumerator : DyadicJet5Enclosure precision :=
  ⟨⟨2158481345705194695333040682616957047326607745324, 2193792600653308347825990444006390815547165536516⟩,
   ⟨-4387585201306616695651980888012781631094331073032, -4316962691410389390666081365233914094653215490648⟩,
   ⟨8633925382820778781332162730467828189306430981296, 8775170402613233391303961776025563262188662146064⟩,
   ⟨-17550340805226466782607923552051126524377324292128, -17267850765641557562664325460935656378612861962592⟩,
   ⟨34535701531283115125328650921871312757225723925184, 35100681610452933565215847104102253048754648584256⟩,
   ⟨-70201363220905867130431694208204506097509297168512, -69071403062566230250657301843742625514451447850368⟩⟩

theorem qNumerator_checked : four.mul zData = qNumerator := by decide

def qDenominator : DyadicJet5Enclosure precision :=
  ⟨⟨2739982666846133650220385491117941065827508261745, 2764210483969108986205740643894384255701131030519⟩,
   ⟨-3017042785899515924182232800706014128633628413654, -2955442772355728232733761950989675137359695129752⟩,
   ⟨7504808398012523540268966438724786454785565028365, 7680585942291447001076950314811274883440182581583⟩,
   ⟨-21947173366552554613003839483219536271572068180264, -21385308209229315379743703024431317629835829132168⟩,
   ⟨68273382071275703956310486636789614140730454566087, 70238352660983751669407434380827018561910948428924⟩,
   ⟨-245852729033482073112413890419205821198889145131430, -238557826753819700699913295625287143805696094339176⟩⟩

theorem qDenominator_checked : onePlusZ.mul onePlusZ = qDenominator := by decide

def qDenominatorInv : DyadicJet5Enclosure precision :=
  ⟨⟨772729518359203387134641678164967058852611355744, 779562243866142850780563272529018521679914298046⟩,
   ⟨826188122527268601742908414787174633223656635354, 858389606793838423015755951479280829153176016094⟩,
   ⟨-418540759556620740405389758057978747743688371341, -207578607619494271707847969311856596853954834375⟩,
   ⟨-2792218021050213143535706046142976788164428088500, -969717798439079381527753622519895401297523341161⟩,
   ⟨-5820849147437974441410136995217831217527409805989, 13839063496598247750057266180928398277355654911940⟩,
   ⟨-115912033951793292064591427630606095915407256564535, 138590843530285164897940457041508629777427701094424⟩⟩

end GeneralCK.Certificates.E8TAxisZero0065GraphWholeC


