-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0060StableWitnesses
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0060StableWitnesses
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:37:34.119535+00:00
-- url     : https://prove2.me/theorems/507f6859-7307-467a-ad6f-ac5f9ba581ae
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0060StableWitnesses` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0060StableWitnesses` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0060StableWitnesses` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0060StableWitnesses (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0060StableWitnesses.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0060StableWitnesses_part00

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0060StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def wholeBAlpha : DyadicInterval precision := ⟨1929268073660617791113193735762571654657675834636, 1965182150578005651608976553331225664541740519026⟩
def wholeBExp : DyadicInterval precision := ⟨99281109903711221103981782405705202513284928938, 104282351385864462439714513796768580427663099554⟩
def wholeBLog : DyadicInterval precision := ⟨96054316820902904302303053035131400119643182109, 100729943133272929411895507856675174660813256268⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨99281109903711221103981782405705203063040742826, scale precision, 104282351385864462439714513796768579877907285666, scale precision,
    0, 512, 0, 512, ⟨-3930364301156011303217953106662451337176351142082, -3930364301156011303217953106662451337176349044929⟩, ⟨-3858536147321235582226387471525143301610606790537, -3858536147321235582226387471525143301610604693384⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0060StableWitnesses


