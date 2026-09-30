-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0070StableWitnesses_q01
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0070StableWitnesses_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:53:49.939761+00:00
-- url     : https://prove2.me/theorems/a12ed454-2933-4b90-a866-0c572964b809
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0070StableWitnesses (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0070StableWitnesses (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0070StableWitnesses (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0070StableWitnesses (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0070StableWitnesses (piece 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0070StableWitnesses_q00

namespace GeneralCK.Certificates.E8TAxisZero0070StableWitnesses
open DyadicInterval E8TAxisStableInterval
set_option maxRecDepth 100000
def centerCExpWitness : ExpWitness precision :=
  ⟨587736430517897015450132223503546876166180188718, scale precision, 587736430517897015450132223503546877265691816495, scale precision,
    0, 512, 0, 512, ⟨-1331341916282471653733957403251310220663854849935, -1331341916282471653733957403251310220663852752782⟩, ⟨-1331341916282471653733957403251310217929741460291, -1331341916282471653733957403251310217929739363138⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1604634301185043853054582563588557416108331639096, 1604634301185043853054582563588557416108331639097⟩
def centerBExp : DyadicInterval precision := ⟨162609076934338712823362391470194993576288496561, 162609076934338712823362391470194995775311752114⟩
def centerBLog : DyadicInterval precision := ⟨154182558239988409834444008722814290362342682877, 154182558239988409834444008722814292561365938430⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨162609076934338712823362391470194994126044310449, scale precision, 162609076934338712823362391470194995225555938226, scale precision,
    0, 512, 0, 512, ⟨-3209268602370087706109165127177114837157772395757, -3209268602370087706109165127177114837157770298604⟩, ⟨-3209268602370087706109165127177114827275556257790, -3209268602370087706109165127177114827275554160637⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨659917674403335303398947154306570012946022027567, 671052481512572809340093335645151882932874114538⟩
def wholeDExp : DyadicInterval precision := ⟨583424017396714902499808941799093863591730436308, 592382009410612930615839145836493983293758080466⟩
def wholeDLog : DyadicInterval precision := ⟨490914027605645316992013980560028280616805628608, 497302293015079090720897450218278679747777485235⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨583424017396714902499808941799093864141486250196, scale precision, 592382009410612930615839145836493982744002266578, scale precision,
    0, 512, 0, 512, ⟨-1342104963025145618680186671290303767242910652864, -1342104963025145618680186671290303767242908555711⟩, ⟨-1319835348806670606797894308613140024535709142512, -1319835348806670606797894308613140024535707045359⟩⟩
end GeneralCK.Certificates.E8TAxisZero0070StableWitnesses


