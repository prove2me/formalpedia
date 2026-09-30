-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0302StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0302StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T00:34:18.941747+00:00
-- url     : https://prove2.me/theorems/79a07479-dfbb-44f7-bdb1-622328caee5e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0302StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0303StableWitnesses, GeneralCK.Certificates.E8TAxisProd03…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0302StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0303StableWitnesses, GeneralCK.Certificates.E8TAxisProd0304StableWitnesses, GeneralCK.Certificates.E8TAxisProd0305StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0302StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0303StableWitnesses, GeneralCK.Certificates.E8TAxisProd0304StableWitnesses, GeneralCK.Certificates.E8TAxisProd0305StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0302StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0303StableWitnesses, GeneralCK.Certificates.E8TAxisProd0304StableWitnesses, GeneralCK.Certificates.E8TAxisProd0305StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0302StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0303StableWitnesses, GeneralCK/Certificates/E8TAxisProd0304StableWitnesses, GeneralCK/Certificates/E8TAxisProd0305StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0302StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0302StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3957182113162240766624229437560720104187299711, 3957182113162240766624229437560720104187299712⟩
def centerAExp : DyadicInterval precision := ⟨1453608663518239684990297266292415545523124059933, 1453608663518239684990297266292415547722147315486⟩
def centerALog : DyadicInterval precision := ⟨1009083914440550911538268226967653949061006604559, 1009083914440550911538268226967653951260029860112⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1453608663518239684990297266292415546072879873821, scale precision, 1453608663518239684990297266292415547172391501598, scale precision,
    0, 128, 0, 128, ⟨-7914364226324481533248458875121440761116590109, -7914364226324481533248458875121440761114492956⟩, ⟨-7914364226324481533248458875121439655634705892, -7914364226324481533248458875121439655632608739⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨721949241039261777105100229686264310385356161447, 721949241039261777105100229686264310385356161448⟩
def centerDExp : DyadicInterval precision := ⟨544171400918647169539408046331758482200227109223, 544171400918647169539408046331758484399250364776⟩
def centerDLog : DyadicInterval precision := ⟨462587568506596564045749998967475930132416323351, 462587568506596564045749998967475932331439578904⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨544171400918647169539408046331758482749982923111, scale precision, 544171400918647169539408046331758483849494550888, scale precision,
    1, 128, 1, 128, ⟨-1443898482078523554210200459372528622247213277149, -1443898482078523554210200459372528622247211179996⟩, ⟨-1443898482078523554210200459372528619294213465789, -1443898482078523554210200459372528619294211368636⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨726937355339110808496584129880967661640406540425, 726937355339110808496584129880967661640406540426⟩
def centerCExp : DyadicInterval precision := ⟨540469528962502920101262101257262982068936306670, 540469528962502920101262101257262984267959562223⟩
def centerCLog : DyadicInterval precision := ⟨459887581587749183276995695242290245015071883287, 459887581587749183276995695242290247214095138840⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨540469528962502920101262101257262982618692120558, scale precision, 540469528962502920101262101257262983718203748335, scale precision,
    1, 128, 1, 128, ⟨-1453874710678221616993168259761935324767427118826, -1453874710678221616993168259761935324767425021673⟩, ⟨-1453874710678221616993168259761935321794201140027, -1453874710678221616993168259761935321794199042874⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1780263549478751735100373076112162112657476038749, 1780263549478751735100373076112162112657476038750⟩
def centerBExp : DyadicInterval precision := ⟨127869243025197133412165489029911405371306975932, 127869243025197133412165489029911407570330231485⟩
def centerBLog : DyadicInterval precision := ⟨122581753501197993100763077713888656827819326716, 122581753501197993100763077713888659026842582269⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨127869243025197133412165489029911405921062789820, scale precision, 127869243025197133412165489029911407020574417597, scale precision,
    3, 128, 3, 128, ⟨-3560527098957503470200746152224324231598473721968, -3560527098957503470200746152224324231598471624815⟩, ⟨-3560527098957503470200746152224324219031432530179, -3560527098957503470200746152224324219031430433026⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3798893981423257492988718450954299577395465180, 4115470352964345628383522602588716836376905847⟩
def wholeAExp : DyadicInterval precision := ⟨1453293830838237185210198542808669482340765754580, 1453923564186661310665317018859587709527417053272⟩
def wholeALog : DyadicInterval precision := ⟨1008926063354791867585944205900164500105846572497, 1009241782561842849966002591658486094460586802138⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1453293830838237185210198542808669482890521568468, scale precision, 1453923564186661310665317018859587708977661239384, scale precision,
    0, 128, 0, 128, ⟨-8230940705928691256767045205177434225615544793, -8230940705928691256767045205177434225613447640⟩, ⟨-7597787962846514985977436901908598602170753227, -7597787962846514985977436901908598602168656074⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨716228578308099727358082939138935890959899212494, 727686670816724440524685346233204921246428500689⟩
def wholeDExp : DyadicInterval precision := ⟨539915612896337333160506278237532711076442060493, 548448150163327086956497611001597703886791384129⟩
def wholeDLog : DyadicInterval precision := ⟨459483149562382791203438629890379326034218128951, 465700648921796470149242465934935277251827483709⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨539915612896337333160506278237532711626197874381, scale precision, 548448150163327086956497611001597703337035570241, scale precision,
    1, 128, 1, 128, ⟨-1455373341633448881049370692466409843980996201432, -1455373341633448881049370692466409843980994104279⟩, ⟨-1432457156616199454716165878277871780454813181077, -1432457156616199454716165878277871780454811083924⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨721002934992365362306809053633544693986704408117, 732889839947546691460260588396435987553242433634⟩
def wholeCExp : DyadicInterval precision := ⟨536084902843194212169358813657498766123996067406, 544876547247851763273770634032890870042508742728⟩
def wholeCLog : DyadicInterval precision := ⟨456683156853861016051201860833528286575440973708, 463101306975057858506244255700798472122118125960⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨536084902843194212169358813657498766673751881294, scale precision, 544876547247851763273770634032890869492752928840, scale precision,
    1, 128, 1, 128, ⟨-1465779679895093382920521176792871976605257878770, -1465779679895093382920521176792871976605255781617⟩, ⟨-1442005869984730724613618107267089386498820756163, -1442005869984730724613618107267089386498818659010⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1762821356311411369254373393413045567533624830831, 1797763551611072325103375238645418346330265467743⟩
def wholeBExp : DyadicInterval precision := ⟨124843409527397051882333196081094800582470897052, 130958053370962518886081223346872129661887049698⟩
def wholeBLog : DyadicInterval precision := ⟨119796704680138984193280885336255417622023386911, 125419304209820776284899920330798766398190557809⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨124843409527397051882333196081094801132226710940, scale precision, 130958053370962518886081223346872129112131235810, scale precision,
    3, 128, 3, 128, ⟨-3595527103222144650206750477290836699096346458945, -3595527103222144650206750477290836699096344361792⟩, ⟨-3525642712622822738508746786826091128931934848033, -3525642712622822738508746786826091128931932750880⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0302StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0303StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0303StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3957182113162240766624229437560720104187299711, 3957182113162240766624229437560720104187299712⟩
def centerAExp : DyadicInterval precision := ⟨1453608663518239684990297266292415545523124059933, 1453608663518239684990297266292415547722147315486⟩
def centerALog : DyadicInterval precision := ⟨1009083914440550911538268226967653949061006604559, 1009083914440550911538268226967653951260029860112⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1453608663518239684990297266292415546072879873821, scale precision, 1453608663518239684990297266292415547172391501598, scale precision,
    0, 128, 0, 128, ⟨-7914364226324481533248458875121440761116590109, -7914364226324481533248458875121440761114492956⟩, ⟨-7914364226324481533248458875121439655634705892, -7914364226324481533248458875121439655632608739⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨710524563403850356500890582610538039823374015368, 710524563403850356500890582610538039823374015369⟩
def centerDExp : DyadicInterval precision := ⟨552745918518612785766768712299414359359889019406, 552745918518612785766768712299414361558912274959⟩
def centerDLog : DyadicInterval precision := ⟨468822363559667384554973018042110607773397723001, 468822363559667384554973018042110609972420978554⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨552745918518612785766768712299414359909644833294, scale precision, 552745918518612785766768712299414361009156461071, scale precision,
    1, 128, 1, 128, ⟨-1421049126807700713001781165221076081100344655889, -1421049126807700713001781165221076081100342558736⟩, ⟨-1421049126807700713001781165221076078193153502733, -1421049126807700713001781165221076078193151405580⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨715483634806565196274885924788400619681502334758, 715483634806565196274885924788400619681502334759⟩
def centerCExp : DyadicInterval precision := ⟨549007535380205945691925135601039294494050677240, 549007535380205945691925135601039296693073932793⟩
def centerCLog : DyadicInterval precision := ⟨466107340010418278821772650395181728569650240412, 466107340010418278821772650395181730768673495965⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨549007535380205945691925135601039295043806491128, scale precision, 549007535380205945691925135601039296143318118905, scale precision,
    1, 128, 1, 128, ⟨-1430967269613130392549771849576801240826499332208, -1430967269613130392549771849576801240826497235055⟩, ⟨-1430967269613130392549771849576801237899512103977, -1430967269613130392549771849576801237899510006824⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1746031599061665853373289899508459765536974787060, 1746031599061665853373289899508459765536974787061⟩
def centerBExp : DyadicInterval precision := ⟨134001782865943180682009177149061815941181347913, 134001782865943180682009177149061818140204603466⟩
def centerBLog : DyadicInterval precision := ⟨128210062344358951545914099604064514606615446134, 128210062344358951545914099604064516805638701687⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨134001782865943180682009177149061816490937161801, scale precision, 134001782865943180682009177149061817590448789578, scale precision,
    3, 128, 3, 128, ⟨-3492063198123331706746579799016919537069908325245, -3492063198123331706746579799016919537069906228092⟩, ⟨-3492063198123331706746579799016919525077992920149, -3492063198123331706746579799016919525077990822996⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3798893981423257492988718450954299577395465180, 4115470352964345628383522602588716836376905847⟩
def wholeAExp : DyadicInterval precision := ⟨1453293830838237185210198542808669482340765754580, 1453923564186661310665317018859587709527417053272⟩
def wholeALog : DyadicInterval precision := ⟨1008926063354791867585944205900164500105846572497, 1009241782561842849966002591658486094460586802138⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1453293830838237185210198542808669482890521568468, scale precision, 1453923564186661310665317018859587708977661239384, scale precision,
    0, 128, 0, 128, ⟨-8230940705928691256767045205177434225615544793, -8230940705928691256767045205177434225613447640⟩, ⟨-7597787962846514985977436901908598602170753227, -7597787962846514985977436901908598602168656074⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨704837076587479092158941059188951191105662022838, 716228578308099727358082939138935890959899212495⟩
def wholeDExp : DyadicInterval precision := ⟨548448150163327086956497611001597701687768128576, 557064765387537285209117120927584104924255812884⟩
def wholeDLog : DyadicInterval precision := ⟨465700648921796470149242465934935275052804228156, 471952686082951260798866870121334520250908543212⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨548448150163327086956497611001597702237523942464, scale precision, 557064765387537285209117120927584104374499998996, scale precision,
    1, 128, 1, 128, ⟨-1432457156616199454716165878277871783384785766055, -1432457156616199454716165878277871783384783668902⟩, ⟨-1409674153174958184317882118377902380768999045198, -1409674153174958184317882118377902380768996948045⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨709583755101471771314445841827351929448758849319, 721401323893458199929402962689149867770160190844⟩
def wholeCExp : DyadicInterval precision := ⟨544579573775494981561336767580803246329969406976, 553458011937847212937185909447477859863711232762⟩
def wholeCLog : DyadicInterval precision := ⟨462884967232229539459504051870060081850619733606, 469338954370711885916159094166887894104553817075⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨544579573775494981561336767580803246879725220864, scale precision, 553458011937847212937185909447477859313955418874, scale precision,
    1, 128, 1, 128, ⟨-1442802647786916399858805925378299737015714670887, -1442802647786916399858805925378299737015712573734⟩, ⟨-1419167510202943542628891683654703857445793404370, -1419167510202943542628891683654703857445791307217⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1728706906144776675316046217570130326927040384722, 1763416701862672344166815790275025717092770960273⟩
def wholeBExp : DyadicInterval precision := ⟨130851404781876642602235800128568495397277620450, 137216665515504062256314755504270669513529064762⟩
def wholeBLog : DyadicInterval precision := ⟨125321422732507949334238435847320915213973182618, 131151973238507038651663181484985596611352446222⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨130851404781876642602235800128568495947033434338, scale precision, 137216665515504062256314755504270668963773250874, scale precision,
    3, 128, 3, 128, ⟨-3526833403725344688333631580550051440325859333857, -3526833403725344688333631580550051440325857236704⟩, ⟨-3457413812289553350632092435140260647998604867667, -3457413812289553350632092435140260647998602770514⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0303StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0304StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0304StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3640605953424817106904235978836837760282897367, 3640605953424817106904235978836837760282897368⟩
def centerAExp : DyadicInterval precision := ⟨1454238532866739696576544033316540574868034513622, 1454238532866739696576544033316540577067057769175⟩
def centerALog : DyadicInterval precision := ⟨1009399667722954236284698895375438337347134637797, 1009399667722954236284698895375438339546157893350⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1454238532866739696576544033316540575417790327510, scale precision, 1454238532866739696576544033316540576517301955287, scale precision,
    0, 128, 0, 128, ⟨-7281211906849634213808471957673676073068378631, -7281211906849634213808471957673676073066281478⟩, ⟨-7281211906849634213808471957673674968065307991, -7281211906849634213808471957673674968063210838⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨791938512842554261609794269869582385953292906566, 791938512842554261609794269869582385953292906567⟩
def centerDExp : DyadicInterval precision := ⟨494470288976765335249663465240012275930998297549, 494470288976765335249663465240012278130021553102⟩
def centerDLog : DyadicInterval precision := ⟨425914889167615021373493039688154777291425506011, 425914889167615021373493039688154779490448761564⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨494470288976765335249663465240012276480754111437, scale precision, 494470288976765335249663465240012277580265739214, scale precision,
    1, 128, 1, 128, ⟨-1583877025685108523219588539739164773531495455899, -1583877025685108523219588539739164773531493358746⟩, ⟨-1583877025685108523219588539739164770281678267518, -1583877025685108523219588539739164770281676170365⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨796695219287132433919189915902081306577842894742, 796695219287132433919189915902081306577842894743⟩
def centerCExp : DyadicInterval precision := ⟨491262066166378384739115475957570631032899462220, 491262066166378384739115475957570633231922717773⟩
def centerCLog : DyadicInterval precision := ⟨423515737939540726040060991779894181197444704036, 423515737939540726040060991779894183396467959589⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨491262066166378384739115475957570631582655276108, scale precision, 491262066166378384739115475957570632682166903885, scale precision,
    1, 128, 1, 128, ⟨-1593390438574264867838379831804162614791207016528, -1593390438574264867838379831804162614791204919375⟩, ⟨-1593390438574264867838379831804162611520166659596, -1593390438574264867838379831804162611520164562443⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1989378057241897896538194971289463906631191259942, 1989378057241897896538194971289463906631191259943⟩
def centerBExp : DyadicInterval precision := ⟨96047638047502716025027232923478815716002620208, 96047638047502716025027232923478817915025875761⟩
def centerBLog : DyadicInterval precision := ⟨93023384853710196544381024217744464609577290734, 93023384853710196544381024217744466808600546287⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨96047638047502716025027232923478816265758434096, scale precision, 96047638047502716025027232923478817365270061873, scale precision,
    3, 128, 3, 128, ⟨-3978756114483795793076389942578927821627701430140, -3978756114483795793076389942578927821627699332987⟩, ⟨-3978756114483795793076389942578927804897065706795, -3978756114483795793076389942578927804897063609642⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3482318024844347500022322904444928295572395252, 3798893981423257492988718450954299577395465181⟩
def wholeAExp : DyadicInterval precision := ⟨1453923564186661310665317018859587707328393797719, 1454553569581723058392238696431353226318692924653⟩
def wholeALog : DyadicInterval precision := ⟨1009241782561842849966002591658486092261563546585, 1009557569928173087760872372803888452026676915366⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1453923564186661310665317018859587707878149611607, scale precision, 1454553569581723058392238696431353225768937110765, scale precision,
    0, 128, 0, 128, ⟨-7597787962846514985977436901908599707413204648, -7597787962846514985977436901908599707411107495⟩, ⟨-6964636049688695000044645808889856038763968154, -6964636049688695000044645808889856038761871001⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨786008954924549138888839394711577924172029077196, 797886217135535601213561462349015058648188303748⟩
def wholeDExp : DyadicInterval precision := ⟨490462045819898463991457369988920386537963137363, 498498909896069833132911032342083545771079714894⟩
def wholeDLog : DyadicInterval precision := ⟨422916858198723400101802834922666846616439225893, 428921977795889549222947679819138374779521683823⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨490462045819898463991457369988920387087718951251, scale precision, 498498909896069833132911032342083545221323901006, scale precision,
    1, 128, 1, 128, ⟨-1595772434271071202427122924698030118934565623881, -1595772434271071202427122924698030118934563526728⟩, ⟨-1572017909849098277777678789423155846732282314032, -1572017909849098277777678789423155846732280216879⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨790544729755515845959006727606100906630576870317, 802865233561216913142342731263416338063221001902⟩
def wholeCExp : DyadicInterval precision := ⟨487131610930505629454859937688780156030152787852, 495414307070612103505849426500932784144559077899⟩
def wholeCLog : DyadicInterval precision := ⟨420421118540265489243162511406115268459587697128, 426620089041561576829752774202709547012917206308⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨487131610930505629454859937688780156579908601740, scale precision, 495414307070612103505849426500932783594803264011, scale precision,
    1, 128, 1, 128, ⟨-1605730467122433826284685462526832677775831029061, -1605730467122433826284685462526832677775828931908⟩, ⟨-1581089459511031691918013455212201811639342478459, -1581089459511031691918013455212201811639340381306⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1971339279621247086412252159443639087270337031534, 2007459344838015109981333409805805952774581623362⟩
def wholeBExp : DyadicInterval precision := ⟨93700250251947919493499046556195183093183315378, 98448105641421299325358424932461888596849880900⟩
def wholeBLog : DyadicInterval precision := ⟨90819089311026764918018830305296807976909967983, 95274091584696573089005939062121999060099133195⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨93700250251947919493499046556195183642939129266, scale precision, 98448105641421299325358424932461888047094067012, scale precision,
    3, 128, 3, 128, ⟨-4014918689676030219962666819611611914124050914813, -4014918689676030219962666819611611914124048817660⟩, ⟨-3942678559242494172824504318887278166379329427083, -3942678559242494172824504318887278166379327329930⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0304StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0305StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0305StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3640605953424817106904235978836837760282897367, 3640605953424817106904235978836837760282897368⟩
def centerAExp : DyadicInterval precision := ⟨1454238532866739696576544033316540574868034513622, 1454238532866739696576544033316540577067057769175⟩
def centerALog : DyadicInterval precision := ⟨1009399667722954236284698895375438337347134637797, 1009399667722954236284698895375438339546157893350⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1454238532866739696576544033316540575417790327510, scale precision, 1454238532866739696576544033316540576517301955287, scale precision,
    0, 128, 0, 128, ⟨-7281211906849634213808471957673676073068378631, -7281211906849634213808471957673676073066281478⟩, ⟨-7281211906849634213808471957673674968065307991, -7281211906849634213808471957673674968063210838⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨780097432743148472065827322615976914715321380242, 780097432743148472065827322615976914715321380243⟩
def centerDExp : DyadicInterval precision := ⟨502547949796029941349747428157944022560728851116, 502547949796029941349747428157944024759752106669⟩
def centerDLog : DyadicInterval precision := ⟨431938086327136521229594192068681255335127784667, 431938086327136521229594192068681257534151040220⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨502547949796029941349747428157944023110484665004, scale precision, 502547949796029941349747428157944024209996292781, scale precision,
    1, 128, 1, 128, ⟨-1560194865486296944131654645231953831029434576104, -1560194865486296944131654645231953831029432478951⟩, ⟨-1560194865486296944131654645231953827831853042018, -1560194865486296944131654645231953827831850944865⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨784825211185677980683167040598723030858575088283, 784825211185677980683167040598723030858575088284⟩
def centerCExp : DyadicInterval precision := ⟨499307083016279393342551516198154804948247354869, 499307083016279393342551516198154807147270610422⟩
def centerCLog : DyadicInterval precision := ⟨429524479103427889687004539144190826927825526591, 429524479103427889687004539144190829126848782144⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨499307083016279393342551516198154805498003168757, scale precision, 499307083016279393342551516198154806597514796534, scale precision,
    1, 128, 1, 128, ⟨-1569650422371355961366334081197446063326319309195, -1569650422371355961366334081197446063326317212042⟩, ⟨-1569650422371355961366334081197446060107983141094, -1569650422371355961366334081197446060107981043941⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1953958740204174710150636495801291571113209226401, 1953958740204174710150636495801291571113209226402⟩
def centerBExp : DyadicInterval precision := ⟨100817712391744321217605918939660102162922604611, 100817712391744321217605918939660104361945860164⟩
def centerBLog : DyadicInterval precision := ⟨97492468481451235812912162439992340125411717669, 97492468481451235812912162439992342324434973222⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨100817712391744321217605918939660102712678418499, scale precision, 100817712391744321217605918939660103812190046276, scale precision,
    3, 128, 3, 128, ⟨-3907917480408349420301272991602583150195941950053, -3907917480408349420301272991602583150195939852900⟩, ⟨-3907917480408349420301272991602583134256897052699, -3907917480408349420301272991602583134256894955546⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3482318024844347500022322904444928295572395252, 3798893981423257492988718450954299577395465181⟩
def wholeAExp : DyadicInterval precision := ⟨1453923564186661310665317018859587707328393797719, 1454553569581723058392238696431353226318692924653⟩
def wholeALog : DyadicInterval precision := ⟨1009241782561842849966002591658486092261563546585, 1009557569928173087760872372803888452026676915366⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1453923564186661310665317018859587707878149611607, scale precision, 1454553569581723058392238696431353225768937110765, scale precision,
    0, 128, 0, 128, ⟨-7597787962846514985977436901908599707413204648, -7597787962846514985977436901908599707411107495⟩, ⟨-6964636049688695000044645808889856038763968154, -6964636049688695000044645808889856038761871001⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨774203834768265108571628471566363912561698867070, 786008954924549138888839394711577924172029077197⟩
def wholeDExp : DyadicInterval precision := ⟨498498909896069833132911032342083543572056459341, 506617451172271417683927781753795731632056364141⟩
def wholeDLog : DyadicInterval precision := ⟨428921977795889549222947679819138372580498428270, 434963177842048586751554818318029033914423871208⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨498498909896069833132911032342083544121812273229, scale precision, 506617451172271417683927781753795731082300550253, scale precision,
    1, 128, 1, 128, ⟨-1572017909849098277777678789423155849955836091904, -1572017909849098277777678789423155849955833994751⟩, ⟨-1548407669536530217143256943132727823537450607677, -1548407669536530217143256943132727823537448510524⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨778712112448521877793443428117797062747093418422, 790957598324456230108653058298177011882814344824⟩
def wholeCExp : DyadicInterval precision := ⟨495134480870478184263686628454033306932376277427, 503501558295645583797981801823466970464949412236⟩
def wholeCLog : DyadicInterval precision := ⟨426411088908782582191496763088995507057195567839, 432647519611944829173698619020478877983072844004⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨495134480870478184263686628454033307482132091315, scale precision, 503501558295645583797981801823466969915193598348, scale precision,
    1, 128, 1, 128, ⟨-1581915196648912460217306116596354025388358619309, -1581915196648912460217306116596354025388356522156⟩, ⟨-1557424224897043755586886856235594123898425153623, -1557424224897043755586886856235594123898423056470⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1936007185943845989390045675498262083038031684068, 1971955274660056362478541973922469047330392798993⟩
def wholeBExp : DyadicInterval precision := ⟨98365152615312884351162488128478604176924688800, 103325062170948613155723074595141225275025077459⟩
def wholeBLog : DyadicInterval precision := ⟨95196371640444493842545809205936191958093681696, 99836136820102029132063017789269588023863318907⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨98365152615312884351162488128478604726680502688, scale precision, 103325062170948613155723074595141224725269263571, scale precision,
    3, 128, 3, 128, ⟨-3943910549320112724957083947844938102829014934402, -3943910549320112724957083947844938102829012837249⟩, ⟨-3872014371887691978780091350996524158299935322289, -3872014371887691978780091350996524158299933225136⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0305StableWitnesses

end


