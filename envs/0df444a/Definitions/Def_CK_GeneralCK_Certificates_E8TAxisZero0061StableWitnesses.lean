-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0061StableWitnesses
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0061StableWitnesses
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:24:30.034165+00:00
-- url     : https://prove2.me/theorems/07d49902-401a-4517-962b-6757c91be480
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0061StableWitnesses` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0061StableWitnesses` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0061StableWitnesses` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0061StableWitnesses (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0061StableWitnesses.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0061StableWitnesses_part00

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0061StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def wholeBAlpha : DyadicInterval precision := ⟨1894150053562829778049475167569232974415525819984, 1929880448118816680501041306907956802475255432287⟩
def wholeBExp : DyadicInterval precision := ⟨104194998629268025762902089605650127034512182044, 109416268601682423356072899456224122272510714408⟩
def wholeBLog : DyadicInterval precision := ⟨100648405859295802650490660502936119530128169474, 105514098828591461453288669743455509484089557200⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨104194998629268025762902089605650127584267995932, scale precision, 109416268601682423356072899456224121722754900520, scale precision,
    0, 512, 0, 512, ⟨-3859760896237633361002082613815913612661717179235, -3859760896237633361002082613815913612661715082082⟩, ⟨-3788300107125659556098950335138465941487820896799, -3788300107125659556098950335138465941487818799646⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0061StableWitnesses


