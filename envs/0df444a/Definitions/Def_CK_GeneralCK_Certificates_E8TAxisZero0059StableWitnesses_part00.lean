-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0059StableWitnesses_part00
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0059StableWitnesses_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:14:53.015435+00:00
-- url     : https://prove2.me/theorems/36a8ffc0-a863-400c-9f25-a3b6bccfe6cd
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0059StableWitnesses (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0059StableWitnesses (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0059StableWitnesses (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0059StableWitnesses (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0059StableWitnesses (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0059StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨791938512842554261609794269869582385953292906566, 791938512842554261609794269869582385953292906567⟩
def centerDExp : DyadicInterval precision := ⟨494470288976765335249663465240012275930998297549, 494470288976765335249663465240012278130021553102⟩
def centerDLog : DyadicInterval precision := ⟨425914889167615021373493039688154777291425506011, 425914889167615021373493039688154779490448761564⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨494470288976765335249663465240012276480754111437, scale precision, 494470288976765335249663465240012277580265739214, scale precision,
    0, 512, 0, 512, ⟨-1583877025685108523219588539739164773531495455899, -1583877025685108523219588539739164773531493358746⟩, ⟨-1583877025685108523219588539739164770281678267518, -1583877025685108523219588539739164770281676170365⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨792145084263579129855347152782070571944246668003, 792145084263579129855347152782070571944246668004⟩
def centerCExp : DyadicInterval precision := ⟨494330529989360281010626056455807423152987657283, 494330529989360281010626056455807425352010912836⟩
def centerCLog : DyadicInterval precision := ⟨425810457563106080269545911733543628076876504486, 425810457563106080269545911733543630275899760039⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨494330529989360281010626056455807423702743471171, scale precision, 494330529989360281010626056455807424802255098948, scale precision,
    0, 512, 0, 512, ⟨-1584290168527158259710694305564141145513862379046, -1584290168527158259710694305564141145513860281893⟩, ⟨-1584290168527158259710694305564141142263126390121, -1584290168527158259710694305564141142263124292968⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1982589189183638945330647538915323850639132229579, 1982589189183638945330647538915323850639132229580⟩
def centerBExp : DyadicInterval precision := ⟨96944103719750023189320879521753127156758176926, 96944103719750023189320879521753129355781432479⟩
def centerBLog : DyadicInterval precision := ⟨93864327202488387280529556228457210331662488266, 93864327202488387280529556228457212530685743819⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨96944103719750023189320879521753127706513990814, scale precision, 96944103719750023189320879521753128806025618591, scale precision,
    0, 512, 0, 512, ⟨-3965178378367277890661295077830647709566227243425, -3965178378367277890661295077830647709566225146272⟩, ⟨-3965178378367277890661295077830647692990303772041, -3965178378367277890661295077830647692990301674888⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨786008954924549138888839394711577924172029077196, 797886217135535601213561462349015058648188303748⟩
def wholeDExp : DyadicInterval precision := ⟨490462045819898463991457369988920386537963137363, 498498909896069833132911032342083545771079714894⟩
def wholeDLog : DyadicInterval precision := ⟨422916858198723400101802834922666846616439225893, 428921977795889549222947679819138374779521683823⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨490462045819898463991457369988920387087718951251, scale precision, 498498909896069833132911032342083545221323901006, scale precision,
    0, 512, 0, 512, ⟨-1595772434271071202427122924698030118934565623881, -1595772434271071202427122924698030118934563526728⟩, ⟨-1572017909849098277777678789423155846732282314032, -1572017909849098277777678789423155846732280216879⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨786008954924549138888839394711577924172029077196, 798300648385302148205461270420216151660336045968⟩
def wholeCExp : DyadicInterval precision := ⟨490183968579304193759503934602799356857076074920, 498498909896069833132911032342083545771079714894⟩
def wholeCLog : DyadicInterval precision := ⟨422708637473434740293082936311178331559771632167, 428921977795889549222947679819138374779521683823⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨490183968579304193759503934602799357406831888808, scale precision, 498498909896069833132911032342083545221323901006, scale precision,
    0, 512, 0, 512, ⟨-1596601296770604296410922540840432304959790438571, -1596601296770604296410922540840432304959788341418⟩, ⟨-1572017909849098277777678789423155846732282314032, -1572017909849098277777678789423155846732280216879⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩


end GeneralCK.Certificates.E8TAxisZero0059StableWitnesses


