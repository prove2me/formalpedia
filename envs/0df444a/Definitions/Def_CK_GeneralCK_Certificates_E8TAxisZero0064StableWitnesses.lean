-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0064StableWitnesses
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0064StableWitnesses
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:23:09.170968+00:00
-- url     : https://prove2.me/theorems/f3cb197c-395f-4dd9-8c25-5783d645c7dc
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0064StableWitnesses` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0064StableWitnesses` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0064StableWitnesses` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0064StableWitnesses (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0064StableWitnesses.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0064StableWitnesses_part00

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0064StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def wholeBAlpha : DyadicInterval precision := ⟨1789978720893028890625892399751465273863386640085, 1825097555394958903314865090464227326945826578248⟩
def wholeBExp : DyadicInterval precision := ⟨120259854956637015564404235031998631226646285344, 126180500168779842375710971896999472838971255025⟩
def wholeBLog : DyadicInterval precision := ⟨115567757767424937209215292873304311654880829801, 121028049066139339503431943155376669191007343175⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨120259854956637015564404235031998631776402099232, scale precision, 126180500168779842375710971896999472289215441137, scale precision,
    0, 512, 0, 512, ⟨-3650195110789917806629730180928454660572761731930, -3650195110789917806629730180928454660572759634777⟩, ⟨-3579957441786057781251784799502930541359157929571, -3579957441786057781251784799502930541359155832418⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0064StableWitnesses


