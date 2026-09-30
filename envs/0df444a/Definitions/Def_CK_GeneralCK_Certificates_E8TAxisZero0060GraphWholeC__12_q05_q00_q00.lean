-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0060GraphWholeC__12_q05_q00_q00
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0060GraphWholeC__12_q05_q00_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T07:30:42.472709+00:00
-- url     : https://prove2.me/theorems/c59e2630-a2c2-4e1f-9144-577c1691b9a8
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0060GraphWholeC (+11 modules: GeneralCK.Certificates.E8TAxisZero0061GraphWholeC, GeneralCK.Certificates.E8TAxisZero0062Graph…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0060GraphWholeC (+11 modules: GeneralCK.Certificates.E8TAxisZero0061GraphWholeC, GeneralCK.Certificates.E8TAxisZero0062GraphWholeC, GeneralCK.Certificates.E8TAxisZero0063GraphWholeC, GeneralCK.Certificates.E8TAxisZero0064GraphWholeC, GeneralCK.Certificates.E8TAxisZero0065GraphWholeC, GeneralCK.Certificates.E8TAxisZero0066GraphWholeC, GeneralCK.Certificates.E8TAxisZero0067GraphWholeC, GeneralCK.Certificates.E8TAxisZero0068GraphWholeC, GeneralCK.Certificates.E8TAxisZero0069GraphWholeC, GeneralCK.Certificates.E8TAxisZero0070GraphWholeC, GeneralCK.Certificates.E8TAxisZero0071GraphWholeC) (piece 6 of 12) (piece 1 of 3) (piece 1 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0060GraphWholeC (+11 modules: GeneralCK.Certificates.E8TAxisZero0061GraphWholeC, GeneralCK.Certificates.E8TAxisZero0062GraphWholeC, GeneralCK.Certificates.E8TAxisZero0063GraphWholeC, GeneralCK.Certificates.E8TAxisZero0064GraphWholeC, GeneralCK.Certificates.E8TAxisZero0065GraphWholeC, GeneralCK.Certificates.E8TAxisZero0066GraphWholeC, GeneralCK.Certificates.E8TAxisZero0067GraphWholeC, GeneralCK.Certificates.E8TAxisZero0068GraphWholeC, GeneralCK.Certificates.E8TAxisZero0069GraphWholeC, GeneralCK.Certificates.E8TAxisZero0070GraphWholeC, GeneralCK.Certificates.E8TAxisZero0071GraphWholeC) (piece 6 of 12) (piece 1 of 3) (piece 1 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0060GraphWholeC (+11 modules: GeneralCK.Certificates.E8TAxisZero0061GraphWholeC, GeneralCK.Certificates.E8TAxisZero0062GraphWholeC, GeneralCK.Certificates.E8TAxisZero0063GraphWholeC, GeneralCK.Certificates.E8TAxisZero0064GraphWholeC, GeneralCK.Certificates.E8TAxisZero0065GraphWholeC, GeneralCK.Certificates.E8TAxisZero0066GraphWholeC, GeneralCK.Certificates.E8TAxisZero0067GraphWholeC, GeneralCK.Certificates.E8TAxisZero0068GraphWholeC, GeneralCK.Certificates.E8TAxisZero0069GraphWholeC, GeneralCK.Certificates.E8TAxisZero0070GraphWholeC, GeneralCK.Certificates.E8TAxisZero0071GraphWholeC) (piece 6 of 12) (piece 1 of 3) (piece 1 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0060GraphWholeC (+11 modules: GeneralCK/Certificates/E8TAxisZero0061GraphWholeC, GeneralCK/Certificates/E8TAxisZero0062GraphWholeC, GeneralCK/Certificates/E8TAxisZero0063GraphWholeC, GeneralCK/Certificates/E8TAxisZero0064GraphWholeC, GeneralCK/Certificates/E8TAxisZero0065GraphWholeC, GeneralCK/Certificates/E8TAxisZero0066GraphWholeC, GeneralCK/Certificates/E8TAxisZero0067GraphWholeC, GeneralCK/Certificates/E8TAxisZero0068GraphWholeC, GeneralCK/Certificates/E8TAxisZero0069GraphWholeC, GeneralCK/Certificates/E8TAxisZero0070GraphWholeC, GeneralCK/Certificates/E8TAxisZero0071GraphWholeC) (piece 6 of 12) (piece 1 of 3) (piece 1 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0060GraphWholeC__12_q05_q00_q00_q01

namespace GeneralCK.Certificates.E8TAxisZero0065GraphWholeC
open DyadicInterval E8TAxisStableInterval E8TAxisZero0065PaddedInputs
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def alphaJet : DyadicJet5Enclosure precision :=
  ⟨⟨716228578308099727358082939138935890959882435278, 728086423187601485414030335955879143113117579333⟩,
   ⟨1461501637330902918203684832716283019655932542976, 1461501637330902918203684832716283019655932542976⟩,
   ⟨0, 0⟩,
   ⟨0, 0⟩,
   ⟨0, 0⟩,
   ⟨0, 0⟩⟩

theorem alphaJet_checked : DyadicJet5Enclosure.variableJet wholeCInput.alpha = alphaJet := by decide

def logtwo : DyadicJet5Enclosure precision :=
  ⟨⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩,
   ⟨0, 0⟩,
   ⟨0, 0⟩,
   ⟨0, 0⟩,
   ⟨0, 0⟩,
   ⟨0, 0⟩⟩

end GeneralCK.Certificates.E8TAxisZero0065GraphWholeC


