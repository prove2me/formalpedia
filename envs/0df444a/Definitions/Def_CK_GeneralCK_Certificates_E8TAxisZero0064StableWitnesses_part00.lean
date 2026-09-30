-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0064StableWitnesses_part00
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0064StableWitnesses_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:16:01.405958+00:00
-- url     : https://prove2.me/theorems/7a2a6fad-7012-41b5-8a04-eee6779eb9d2
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0064StableWitnesses (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0064StableWitnesses (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0064StableWitnesses (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0064StableWitnesses (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0064StableWitnesses (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0064StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨733440986312093234127888410179197994001522319513, 733440986312093234127888410179197994001522319514⟩
def centerDExp : DyadicInterval precision := ⟨535680729704461451649291949156588179014765393299, 535680729704461451649291949156588181213788648852⟩
def centerDLog : DyadicInterval precision := ⟨456387420244430310281539606035895557724605706337, 456387420244430310281539606035895559923628961890⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨535680729704461451649291949156588179564521207187, scale precision, 535680729704461451649291949156588180664032834964, scale precision,
    0, 512, 0, 512, ⟨-1466881972624186468255776820358395989502948479653, -1466881972624186468255776820358395989502946382500⟩, ⟨-1466881972624186468255776820358395986503142895557, -1466881972624186468255776820358395986503140798404⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨733641441738596835016932155157256171325286618123, 733641441738596835016932155157256171325286618124⟩
def centerCExp : DyadicInterval precision := ⟨535533804952829131515095509521001953628692003467, 535533804952829131515095509521001955827715259020⟩
def centerCLog : DyadicInterval precision := ⟨456279899435389339257259731675659462614159022194, 456279899435389339257259731675659464813182277747⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨535533804952829131515095509521001954178447817355, scale precision, 535533804952829131515095509521001955277959445132, scale precision,
    0, 512, 0, 512, ⟨-1467282883477193670033864310314512344150888578150, -1467282883477193670033864310314512344150886480997⟩, ⟨-1467282883477193670033864310314512341150259991497, -1467282883477193670033864310314512341150257894344⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1807510265814388899917913864384531510832208921847, 1807510265814388899917913864384531510832208921848⟩
def centerBExp : DyadicInterval precision := ⟨123189310663593082674715100817111290985692568729, 123189310663593082674715100817111293184715824282⟩
def centerBLog : DyadicInterval precision := ⟨118271986309902198059449429769155279183978891872, 118271986309902198059449429769155281383002147425⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨123189310663593082674715100817111291535448382617, scale precision, 123189310663593082674715100817111292634960010394, scale precision,
    0, 512, 0, 512, ⟨-3615020531628777799835827728769063028186648928319, -3615020531628777799835827728769063028186646831166⟩, ⟨-3615020531628777799835827728769063015142188856222, -3615020531628777799835827728769063015142186759069⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨727686670816724440524685346233204921246428500688, 739212305620516788391447838602016614455786978946⟩
def wholeDExp : DyadicInterval precision := ⟨531466696428681553786643034174516969558482716148, 539915612896337333160506278237532713275465316046⟩
def wholeDLog : DyadicInterval precision := ⟨453300409610535438784277685833236607008526820688, 459483149562382791203438629890379328233241384504⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨531466696428681553786643034174516970108238530036, scale precision, 539915612896337333160506278237532712725709502158, scale precision,
    0, 512, 0, 512, ⟨-1478424611241033576782895677204033230423370623258, -1478424611241033576782895677204033230423368526105⟩, ⟨-1455373341633448881049370692466409841004719898474, -1455373341633448881049370692466409841004717801321⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨727686670816724440524685346233204921246428500688, 739614424302254009127841865748253801302561896296⟩
def wholeCExp : DyadicInterval precision := ⟨531174320571399858154369459977994794021567605654, 539915612896337333160506278237532713275465316046⟩
def wholeCLog : DyadicInterval precision := ⟨453085986162967046262311852959200128247975144533, 459483149562382791203438629890379328233241384504⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨531174320571399858154369459977994794571323419542, scale precision, 539915612896337333160506278237532712725709502158, scale precision,
    0, 512, 0, 512, ⟨-1479228848604508018255683731496507604117752600103, -1479228848604508018255683731496507604117750502950⟩, ⟨-1455373341633448881049370692466409841004719898474, -1455373341633448881049370692466409841004717801321⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide


end GeneralCK.Certificates.E8TAxisZero0064StableWitnesses


