-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0060GraphWholeC__12_q05_q00_q01
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0060GraphWholeC__12_q05_q00_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T07:40:24.410583+00:00
-- url     : https://prove2.me/theorems/fe18ac0c-0fba-4a2e-9177-2bc7453e31b1
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0060GraphWholeC (+11 modules: GeneralCK.Certificates.E8TAxisZero0061GraphWholeC, GeneralCK.Certificates.E8TAxisZero0062Graph…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0060GraphWholeC (+11 modules: GeneralCK.Certificates.E8TAxisZero0061GraphWholeC, GeneralCK.Certificates.E8TAxisZero0062GraphWholeC, GeneralCK.Certificates.E8TAxisZero0063GraphWholeC, GeneralCK.Certificates.E8TAxisZero0064GraphWholeC, GeneralCK.Certificates.E8TAxisZero0065GraphWholeC, GeneralCK.Certificates.E8TAxisZero0066GraphWholeC, GeneralCK.Certificates.E8TAxisZero0067GraphWholeC, GeneralCK.Certificates.E8TAxisZero0068GraphWholeC, GeneralCK.Certificates.E8TAxisZero0069GraphWholeC, GeneralCK.Certificates.E8TAxisZero0070GraphWholeC, GeneralCK.Certificates.E8TAxisZero0071GraphWholeC) (piece 6 of 12) (piece 1 of 3) (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0060GraphWholeC (+11 modules: GeneralCK.Certificates.E8TAxisZero0061GraphWholeC, GeneralCK.Certificates.E8TAxisZero0062GraphWholeC, GeneralCK.Certificates.E8TAxisZero0063GraphWholeC, GeneralCK.Certificates.E8TAxisZero0064GraphWholeC, GeneralCK.Certificates.E8TAxisZero0065GraphWholeC, GeneralCK.Certificates.E8TAxisZero0066GraphWholeC, GeneralCK.Certificates.E8TAxisZero0067GraphWholeC, GeneralCK.Certificates.E8TAxisZero0068GraphWholeC, GeneralCK.Certificates.E8TAxisZero0069GraphWholeC, GeneralCK.Certificates.E8TAxisZero0070GraphWholeC, GeneralCK.Certificates.E8TAxisZero0071GraphWholeC) (piece 6 of 12) (piece 1 of 3) (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0060GraphWholeC (+11 modules: GeneralCK.Certificates.E8TAxisZero0061GraphWholeC, GeneralCK.Certificates.E8TAxisZero0062GraphWholeC, GeneralCK.Certificates.E8TAxisZero0063GraphWholeC, GeneralCK.Certificates.E8TAxisZero0064GraphWholeC, GeneralCK.Certificates.E8TAxisZero0065GraphWholeC, GeneralCK.Certificates.E8TAxisZero0066GraphWholeC, GeneralCK.Certificates.E8TAxisZero0067GraphWholeC, GeneralCK.Certificates.E8TAxisZero0068GraphWholeC, GeneralCK.Certificates.E8TAxisZero0069GraphWholeC, GeneralCK.Certificates.E8TAxisZero0070GraphWholeC, GeneralCK.Certificates.E8TAxisZero0071GraphWholeC) (piece 6 of 12) (piece 1 of 3) (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0060GraphWholeC (+11 modules: GeneralCK/Certificates/E8TAxisZero0061GraphWholeC, GeneralCK/Certificates/E8TAxisZero0062GraphWholeC, GeneralCK/Certificates/E8TAxisZero0063GraphWholeC, GeneralCK/Certificates/E8TAxisZero0064GraphWholeC, GeneralCK/Certificates/E8TAxisZero0065GraphWholeC, GeneralCK/Certificates/E8TAxisZero0066GraphWholeC, GeneralCK/Certificates/E8TAxisZero0067GraphWholeC, GeneralCK/Certificates/E8TAxisZero0068GraphWholeC, GeneralCK/Certificates/E8TAxisZero0069GraphWholeC, GeneralCK/Certificates/E8TAxisZero0070GraphWholeC, GeneralCK/Certificates/E8TAxisZero0071GraphWholeC) (piece 6 of 12) (piece 1 of 3) (piece 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0060GraphWholeC__12_q05_q00_q00

namespace GeneralCK.Certificates.E8TAxisZero0065GraphWholeC
open DyadicInterval E8TAxisStableInterval E8TAxisZero0065PaddedInputs
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem logtwo_checked : constant wholeCInput.logTwo = logtwo := by decide

def zData : DyadicJet5Enclosure precision :=
  ⟨⟨539620336426298673833260170654239261831651936331, 548448150163327086956497611001597703886791384129⟩,
   ⟨-1096896300326654173912995222003195407773582768258, -1079240672852597347666520341308478523663303872662⟩,
   ⟨2158481345705194695333040682616957047326607745324, 2193792600653308347825990444006390815547165536516⟩,
   ⟨-4387585201306616695651980888012781631094331073032, -4316962691410389390666081365233914094653215490648⟩,
   ⟨8633925382820778781332162730467828189306430981296, 8775170402613233391303961776025563262188662146064⟩,
   ⟨-17550340805226466782607923552051126524377324292128, -17267850765641557562664325460935656378612861962592⟩⟩

theorem zData_checked : zBox wholeCInput = zData := by decide

def onePlusZ : DyadicJet5Enclosure precision :=
  ⟨⟨2001121973757201592036945003370522281487584479307, 2009949787494230005160182443717880723542723927105⟩,
   ⟨-1096896300326654173912995222003195407773582768258, -1079240672852597347666520341308478523663303872662⟩,
   ⟨2158481345705194695333040682616957047326607745324, 2193792600653308347825990444006390815547165536516⟩,
   ⟨-4387585201306616695651980888012781631094331073032, -4316962691410389390666081365233914094653215490648⟩,
   ⟨8633925382820778781332162730467828189306430981296, 8775170402613233391303961776025563262188662146064⟩,
   ⟨-17550340805226466782607923552051126524377324292128, -17267850765641557562664325460935656378612861962592⟩⟩

theorem onePlusZ_checked : one.add zData = onePlusZ := by decide

def negativeZ : DyadicJet5Enclosure precision :=
  ⟨⟨-548448150163327086956497611001597703886791384129, -539620336426298673833260170654239261831651936331⟩,
   ⟨1079240672852597347666520341308478523663303872662, 1096896300326654173912995222003195407773582768258⟩,
   ⟨-2193792600653308347825990444006390815547165536516, -2158481345705194695333040682616957047326607745324⟩,
   ⟨4316962691410389390666081365233914094653215490648, 4387585201306616695651980888012781631094331073032⟩,
   ⟨-8775170402613233391303961776025563262188662146064, -8633925382820778781332162730467828189306430981296⟩,
   ⟨17267850765641557562664325460935656378612861962592, 17550340805226466782607923552051126524377324292128⟩⟩

theorem negativeZ_checked : negative zData = negativeZ := by decide

def rNumerator : DyadicJet5Enclosure precision :=
  ⟨⟨913053487167575831247187221714685315769141158847, 921881300904604244370424662062043757824280606645⟩,
   ⟨1079240672852597347666520341308478523663303872662, 1096896300326654173912995222003195407773582768258⟩,
   ⟨-2193792600653308347825990444006390815547165536516, -2158481345705194695333040682616957047326607745324⟩,
   ⟨4316962691410389390666081365233914094653215490648, 4387585201306616695651980888012781631094331073032⟩,
   ⟨-8775170402613233391303961776025563262188662146064, -8633925382820778781332162730467828189306430981296⟩,
   ⟨17267850765641557562664325460935656378612861962592, 17550340805226466782607923552051126524377324292128⟩⟩

theorem rNumerator_checked : one.add negativeZ = rNumerator := by decide

end GeneralCK.Certificates.E8TAxisZero0065GraphWholeC


