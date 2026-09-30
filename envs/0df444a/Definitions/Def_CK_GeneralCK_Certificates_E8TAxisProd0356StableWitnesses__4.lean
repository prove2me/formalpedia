-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0356StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0356StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T21:48:22.255296+00:00
-- url     : https://prove2.me/theorems/58110fa5-cd44-484c-b6b7-1ed7c0ce0b03
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0356StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0357StableWitnesses, GeneralCK.Certificates.E8TAxisProd03…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0356StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0357StableWitnesses, GeneralCK.Certificates.E8TAxisProd0358StableWitnesses, GeneralCK.Certificates.E8TAxisProd0359StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0356StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0357StableWitnesses, GeneralCK.Certificates.E8TAxisProd0358StableWitnesses, GeneralCK.Certificates.E8TAxisProd0359StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0356StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0357StableWitnesses, GeneralCK.Certificates.E8TAxisProd0358StableWitnesses, GeneralCK.Certificates.E8TAxisProd0359StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0356StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0357StableWitnesses, GeneralCK/Certificates/E8TAxisProd0358StableWitnesses, GeneralCK/Certificates/E8TAxisProd0359StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0356StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0356StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨2374304945389442440708671056104672722900487814, 2374304945389442440708671056104672722900487815⟩
def centerAExp : DyadicInterval precision := ⟨1456760733519020528598233539146530576837684754745, 1456760733519020528598233539146530579036708010298⟩
def centerALog : DyadicInterval precision := ⟨1010663362960215057194405650418097343575557659645, 1010663362960215057194405650418097345774580915198⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1456760733519020528598233539146530577387440568633, scale precision, 1456760733519020528598233539146530578486952196410, scale precision,
    0, 128, 0, 128, ⟨-4748609890778884881417342112209345997346971596, -4748609890778884881417342112209345997344874443⟩, ⟨-4748609890778884881417342112209344894257076814, -4748609890778884881417342112209344894254979661⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨815839300550668055994007428828159575323513310288, 815839300550668055994007428828159575323513310289⟩
def centerDExp : DyadicInterval precision := ⟨478559189448815119699945348173357163995361504812, 478559189448815119699945348173357166194384760365⟩
def centerDLog : DyadicInterval precision := ⟨413977501179630865966571380465000387295391805362, 413977501179630865966571380465000389494415060915⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨478559189448815119699945348173357164545117318700, scale precision, 478559189448815119699945348173357165644628946477, scale precision,
    1, 128, 1, 128, ⟨-1631678601101336111988014857656319152325961100681, -1631678601101336111988014857656319152325959003528⟩, ⟨-1631678601101336111988014857656319148968094237626, -1631678601101336111988014857656319148968092140473⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨818978563884435740175057798713757616973376630757, 818978563884435740175057798713757616973376630758⟩
def centerCExp : DyadicInterval precision := ⟨476507736413076731141348392715651555724428392569, 476507736413076731141348392715651557923451648122⟩
def centerCLog : DyadicInterval precision := ⟨412431267050142965773379360948926733291126520866, 412431267050142965773379360948926735490149776419⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨476507736413076731141348392715651556274184206457, scale precision, 476507736413076731141348392715651557373695834234, scale precision,
    1, 128, 1, 128, ⟨-1637957127768871480350115597427515235632915857392, -1637957127768871480350115597427515235632913760239⟩, ⟨-1637957127768871480350115597427515232260592762794, -1637957127768871480350115597427515232260590665641⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2058209247542355460825555848556854960599597284991, 2058209247542355460825555848556854960599597284992⟩
def centerBExp : DyadicInterval precision := ⟨87413687236516754917243304126105348261997421984, 87413687236516754917243304126105350461020677537⟩
def centerBLog : DyadicInterval precision := ⟨84899316265209926894096488083535812005071931484, 84899316265209926894096488083535814204095187037⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨87413687236516754917243304126105348811753235872, scale precision, 87413687236516754917243304126105349911264863649, scale precision,
    4, 128, 4, 128, ⟨-4116418495084710921651111697113709930390765583535, -4116418495084710921651111697113709930390763486382⟩, ⟨-4116418495084710921651111697113709912007625653600, -4116418495084710921651111697113709912007623556447⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨2216017656540843594568486214625237657012954244, 2532592299075639559542598685704412299858871782⟩
def wholeAExp : DyadicInterval precision := ⟨1456445219907862366338488118605723266224391715309, 1457076315351450948047082186788007227169797069041⟩
def wholeALog : DyadicInterval precision := ⟨1010505341326056445575717809135292020753352555862, 1010821401672838003372446069258059723988541223816⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1456445219907862366338488118605723266774147529197, scale precision, 1457076315351450948047082186788007226620041255153, scale precision,
    0, 128, 0, 128, ⟨-5065184598151279119085197371408825151383222183, -5065184598151279119085197371408825151381125030⟩, ⟨-4432035313081687189136972429250474762601466399, -4432035313081687189136972429250474762599369246⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨809836502735595761416983074307699172577520882055, 821860677686075647293949968540300351172223479072⟩
def wholeDExp : DyadicInterval precision := ⟨474632069948069015840646238761706422401368339240, 482506534178222248007502303634473308617104830159⟩
def wholeDLog : DyadicInterval precision := ⟨411016094834480306545789264008568523645402888608, 416948124396604742320674577430730287178108048617⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨474632069948069015840646238761706422951124153128, scale precision, 482506534178222248007502303634473308067349016271, scale precision,
    1, 128, 1, 128, ⟨-1643721355372151294587899937080600704037272982110, -1643721355372151294587899937080600704037270884957⟩, ⟨-1619673005471191522833966148615398343489844592111, -1619673005471191522833966148615398343489842494958⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨812757290144920169154832965114479480152479331254, 825219791062042057707057241973156007939515701940⟩
def wholeCExp : DyadicInterval precision := ⟨472455289482000898876960528037276779108850909287, 480581820224566243808937463873283693971918038704⟩
def wholeCLog : DyadicInterval precision := ⟨409372015224181913641688137692764937871844639207, 415500411324872022765153541641004627508758625923⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨472455289482000898876960528037276779658606723175, scale precision, 480581820224566243808937463873283693422162224816, scale precision,
    1, 128, 1, 128, ⟨-1650439582124084115414114483946312017579656913683, -1650439582124084115414114483946312017579654816530⟩, ⟨-1625514580289840338309665930228958958633092427894, -1625514580289840338309665930228958958633090330741⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2040015652096749340747538885957826284237421440827, 2076440749492529141244564795139839378229334519701⟩
def wholeBExp : DyadicInterval precision := ⟨85259783773029908574969626493086830274978155378, 89617355523607815553902329988002365491894953461⟩
def wholeBLog : DyadicInterval precision := ⟨82865554858487248229283242619003903081053960988, 86977141877718825502824807495140297403911493039⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨85259783773029908574969626493086830824733969266, scale precision, 89617355523607815553902329988002364942139139573, scale precision,
    4, 128, 4, 128, ⟨-4152881498985058282489129590279678765882445126733, -4152881498985058282489129590279678765882443029580⟩, ⟨-4080031304193498681495077771915652559509292364522, -4080031304193498681495077771915652559509290267369⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0356StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0357StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0357StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨2374304945389442440708671056104672722900487814, 2374304945389442440708671056104672722900487815⟩
def centerAExp : DyadicInterval precision := ⟨1456760733519020528598233539146530576837684754745, 1456760733519020528598233539146530579036708010298⟩
def centerALog : DyadicInterval precision := ⟨1010663362960215057194405650418097343575557659645, 1010663362960215057194405650418097345774580915198⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1456760733519020528598233539146530577387440568633, scale precision, 1456760733519020528598233539146530578486952196410, scale precision,
    0, 128, 0, 128, ⟨-4748609890778884881417342112209345997346971596, -4748609890778884881417342112209345997344874443⟩, ⟨-4748609890778884881417342112209344894257076814, -4748609890778884881417342112209344894254979661⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨803852177515934255585547919467375235228063974291, 803852177515934255585547919467375235228063974292⟩
def centerDExp : DyadicInterval precision := ⟨486474140463139135434442039725801311744313926422, 486474140463139135434442039725801313943337181975⟩
def centerDLog : DyadicInterval precision := ⟨419927923473864759956554512738531498009528841884, 419927923473864759956554512738531500208552097437⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨486474140463139135434442039725801312294069740310, scale precision, 486474140463139135434442039725801313393581368087, scale precision,
    1, 128, 1, 128, ⟨-1607704355031868511171095838934750472107746123950, -1607704355031868511171095838934750472107744026797⟩, ⟨-1607704355031868511171095838934750468804511870366, -1607704355031868511171095838934750468804509773213⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨806972136043735805908404043955502647134998074473, 806972136043735805908404043955502647134998074474⟩
def centerCExp : DyadicInterval precision := ⟨484401554825063838092901836096288571011561928205, 484401554825063838092901836096288573210585183758⟩
def centerCLog : DyadicInterval precision := ⟨418372103371089352179299088932707772552161052984, 418372103371089352179299088932707774751184308537⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨484401554825063838092901836096288571561317742093, scale precision, 484401554825063838092901836096288572660829369870, scale precision,
    1, 128, 1, 128, ⟨-1613944272087471611816808087911005295928681019090, -1613944272087471611816808087911005295928678921937⟩, ⟨-1613944272087471611816808087911005292611313375956, -1613944272087471611816808087911005292611311278803⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2022481161272149986210325820347176970448321703217, 2022481161272149986210325820347176970448321703218⟩
def centerBExp : DyadicInterval precision := ⟨91793746301246357221388696376825054599512666628, 91793746301246357221388696376825056798535922181⟩
def centerBLog : DyadicInterval precision := ⟨89026352337631995739303539556555613080243208138, 89026352337631995739303539556555615279266463691⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨91793746301246357221388696376825055149268480516, scale precision, 91793746301246357221388696376825056248780108293, scale precision,
    3, 128, 3, 128, ⟨-4044962322544299972420651640694353949649626597105, -4044962322544299972420651640694353949649624499952⟩, ⟨-4044962322544299972420651640694353932143662312928, -4044962322544299972420651640694353932143660215775⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨2216017656540843594568486214625237657012954244, 2532592299075639559542598685704412299858871782⟩
def wholeAExp : DyadicInterval precision := ⟨1456445219907862366338488118605723266224391715309, 1457076315351450948047082186788007227169797069041⟩
def wholeALog : DyadicInterval precision := ⟨1010505341326056445575717809135292020753352555862, 1010821401672838003372446069258059723988541223816⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1456445219907862366338488118605723266774147529197, scale precision, 1457076315351450948047082186788007226620041255153, scale precision,
    0, 128, 0, 128, ⟨-5065184598151279119085197371408825151383222183, -5065184598151279119085197371408825151381125030⟩, ⟨-4432035313081687189136972429250474762601466399, -4432035313081687189136972429250474762599369246⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨797886217135535601213561462349015058648188303747, 809836502735595761416983074307699172577520882056⟩
def wholeDExp : DyadicInterval precision := ⟨482506534178222248007502303634473306418081574606, 490462045819898463991457369988920388736986392916⟩
def wholeDLog : DyadicInterval precision := ⟨416948124396604742320674577430730284979084793064, 422916858198723400101802834922666848815462481446⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨482506534178222248007502303634473306967837388494, scale precision, 490462045819898463991457369988920388187230579028, scale precision,
    1, 128, 1, 128, ⟨-1619673005471191522833966148615398346820241033264, -1619673005471191522833966148615398346820238936111⟩, ⟨-1595772434271071202427122924698030115658189688259, -1595772434271071202427122924698030115658187591106⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨800789093237051640993320341704292036401494085946, 813174903790675435270300547776661299147946415525⟩
def wholeCExp : DyadicInterval precision := ⟨480307253047982564333142441600660834371045844021, 488517571229872190688465166626124637206480275502⟩
def wholeCLog : DyadicInterval precision := ⟨415293773064665725797602136077825513974232856391, 421460238264099943405098418906670737104853105916⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨480307253047982564333142441600660834920801657909, scale precision, 488517571229872190688465166626124636656724461614, scale precision,
    1, 128, 1, 128, ⟨-1626349807581350870540601095553322599968716884133, -1626349807581350870540601095553322599968714786980⟩, ⟨-1601578186474103281986640683408584071158280678857, -1601578186474103281986640683408584071158278581704⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2004365567763319348475137471186043242245625164304, 2040637016713598987314498814201704474493346432168⟩
def wholeBExp : DyadicInterval precision := ⟨89541185392435401307712788335794414943354403287, 94097789596194195580133878013038692076100927646⟩
def wholeBLog : DyadicInterval precision := ⟨86905370785129428414758254738294237828172597778, 91192629339425350376404722326798074650774359668⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨89541185392435401307712788335794415493110217175, scale precision, 94097789596194195580133878013038691526345113758, scale precision,
    4, 128, 3, 128, ⟨-4081274033427197974628997628403408957959872217500, -4081274033427197974628997628403408957959870120347⟩, ⟨-4008731135526638696950274942372086475952591483282, -4008731135526638696950274942372086475952589386129⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0357StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0358StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0358StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨2057730428207317882804005838293844500353867260, 2057730428207317882804005838293844500353867261⟩
def centerAExp : DyadicInterval precision := ⟨1457391965428497307986584889920415113297923882582, 1457391965428497307986584889920415115496947138135⟩
def centerALog : DyadicInterval precision := ⟨1010979457468226488278372104764954114338219249334, 1010979457468226488278372104764954116537242504887⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1457391965428497307986584889920415113847679696470, scale precision, 1457391965428497307986584889920415114947191324247, scale precision,
    0, 128, 0, 128, ⟨-4115460856414635765608011676587689552014842957, -4115460856414635765608011676587689552012745804⟩, ⟨-4115460856414635765608011676587688449402723240, -4115460856414635765608011676587688449400626087⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨815839300550668055994007428828159575323513310288, 815839300550668055994007428828159575323513310289⟩
def centerDExp : DyadicInterval precision := ⟨478559189448815119699945348173357163995361504812, 478559189448815119699945348173357166194384760365⟩
def centerDLog : DyadicInterval precision := ⟨413977501179630865966571380465000387295391805362, 413977501179630865966571380465000389494415060915⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨478559189448815119699945348173357164545117318700, scale precision, 478559189448815119699945348173357165644628946477, scale precision,
    1, 128, 1, 128, ⟨-1631678601101336111988014857656319152325961100681, -1631678601101336111988014857656319152325959003528⟩, ⟨-1631678601101336111988014857656319148968094237626, -1631678601101336111988014857656319148968092140473⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨818559702685677814014491793413379769409227428091, 818559702685677814014491793413379769409227428092⟩
def centerCExp : DyadicInterval precision := ⟨476780945569307538301744817634721060175485069309, 476780945569307538301744817634721062374508324862⟩
def centerCLog : DyadicInterval precision := ⟨412637286428606912543839036826155862301247166851, 412637286428606912543839036826155864500270422404⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨476780945569307538301744817634721060725240883197, scale precision, 476780945569307538301744817634721061824752510974, scale precision,
    1, 128, 1, 128, ⟨-1637119405371355628028983586826759540503651233132, -1637119405371355628028983586826759540503649135979⟩, ⟨-1637119405371355628028983586826759537133260576388, -1637119405371355628028983586826759537133258479235⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2057586611734240405477546620197086850428495401697, 2057586611734240405477546620197086850428495401698⟩
def centerBExp : DyadicInterval precision := ⟨87488199757323632559168566247557989823914395031, 87488199757323632559168566247557992022937650584⟩
def centerBLog : DyadicInterval precision := ⟨84969621949534817248219165110662975550394196861, 84969621949534817248219165110662977749417452414⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨87488199757323632559168566247557990373670208919, scale precision, 87488199757323632559168566247557991473181836696, scale precision,
    4, 128, 4, 128, ⟨-4115173223468480810955093240394173710040733480653, -4115173223468480810955093240394173710040731383500⟩, ⟨-4115173223468480810955093240394173691673250223279, -4115173223468480810955093240394173691673248126126⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨1899443256066344012630337314537754309230277491, 2216017656540843594568486214625237657012954245⟩
def wholeAExp : DyadicInterval precision := ⟨1457076315351450948047082186788007224970773813488, 1457707683773513925477741956702213446679176875042⟩
def wholeALog : DyadicInterval precision := ⟨1010821401672838003372446069258059721789517968263, 1011137530350683182654731711817158199758569694808⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1457076315351450948047082186788007225520529627376, scale precision, 1457707683773513925477741956702213446129421061154, scale precision,
    0, 128, 0, 128, ⟨-4432035313081687189136972429250475865452447731, -4432035313081687189136972429250475865450350578⟩, ⟨-3798886512132688025260674629075508067274948598, -3798886512132688025260674629075508067272851445⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨809836502735595761416983074307699172577520882055, 821860677686075647293949968540300351172223479072⟩
def wholeDExp : DyadicInterval precision := ⟨474632069948069015840646238761706422401368339240, 482506534178222248007502303634473308617104830159⟩
def wholeDLog : DyadicInterval precision := ⟨411016094834480306545789264008568523645402888608, 416948124396604742320674577430730287178108048617⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨474632069948069015840646238761706422951124153128, scale precision, 482506534178222248007502303634473308067349016271, scale precision,
    1, 128, 1, 128, ⟨-1643721355372151294587899937080600704037272982110, -1643721355372151294587899937080600704037270884957⟩, ⟨-1619673005471191522833966148615398343489844592111, -1619673005471191522833966148615398343489842494958⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨812339766146511844184428068343129811018114065952, 824799584791474591413561683701499840812608011110⟩
def wholeCExp : DyadicInterval precision := ⟨472727045272623653146355127550296920422604261269, 480856485366499187837718609340004723128518380372⟩
def wholeCLog : DyadicInterval precision := ⟨409577368107267924317318484841993276008476648264, 415707094085844630193733036331847104803127407762⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨472727045272623653146355127550296920972360075157, scale precision, 480856485366499187837718609340004722578762566484, scale precision,
    1, 128, 1, 128, ⟨-1649599169582949182827123367402999683324863896941, -1649599169582949182827123367402999683324861799788⟩, ⟨-1624679532293023688368856136686259620365316867595, -1624679532293023688368856136686259620365314770442⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2039394333175040441223149727295267501036078561804, 2075816837190912669673294626669910010883702970855⟩
def wholeBExp : DyadicInterval precision := ⟨85332609340543131702483700267096396419450414148, 89693584841838522997392694309462357283049762821⟩
def wholeBLog : DyadicInterval precision := ⟨82934364552842895181596773560555599682660344536, 87048965210693651596988431642737587680838372443⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨85332609340543131702483700267096396969206228036, scale precision, 89693584841838522997392694309462356733293948933, scale precision,
    4, 128, 4, 128, ⟨-4151633674381825339346589253339820031183139479180, -4151633674381825339346589253339820031183137382027⟩, ⟨-4078788666350080882446299454590534993114226302839, -4078788666350080882446299454590534993114224205686⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0358StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0359StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0359StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨2057730428207317882804005838293844500353867260, 2057730428207317882804005838293844500353867261⟩
def centerAExp : DyadicInterval precision := ⟨1457391965428497307986584889920415113297923882582, 1457391965428497307986584889920415115496947138135⟩
def centerALog : DyadicInterval precision := ⟨1010979457468226488278372104764954114338219249334, 1010979457468226488278372104764954116537242504887⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1457391965428497307986584889920415113847679696470, scale precision, 1457391965428497307986584889920415114947191324247, scale precision,
    0, 128, 0, 128, ⟨-4115460856414635765608011676587689552014842957, -4115460856414635765608011676587689552012745804⟩, ⟨-4115460856414635765608011676587688449402723240, -4115460856414635765608011676587688449400626087⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨803852177515934255585547919467375235228063974291, 803852177515934255585547919467375235228063974292⟩
def centerDExp : DyadicInterval precision := ⟨486474140463139135434442039725801311744313926422, 486474140463139135434442039725801313943337181975⟩
def centerDLog : DyadicInterval precision := ⟨419927923473864759956554512738531498009528841884, 419927923473864759956554512738531500208552097437⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨486474140463139135434442039725801312294069740310, scale precision, 486474140463139135434442039725801313393581368087, scale precision,
    1, 128, 1, 128, ⟨-1607704355031868511171095838934750472107746123950, -1607704355031868511171095838934750472107744026797⟩, ⟨-1607704355031868511171095838934750468804511870366, -1607704355031868511171095838934750468804509773213⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨806555852181915906583656308962756915150699062248, 806555852181915906583656308962756915150699062249⟩
def centerCExp : DyadicInterval precision := ⟨484677580512379876898139795518180291572231872897, 484677580512379876898139795518180293771255128450⟩
def centerCLog : DyadicInterval precision := ⟨418579402164967764599087159908475398981033882941, 418579402164967764599087159908475401180057138494⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨484677580512379876898139795518180292121987686785, scale precision, 484677580512379876898139795518180293221499314562, scale precision,
    1, 128, 1, 128, ⟨-1613111704363831813167312617925513831959138368024, -1613111704363831813167312617925513831959136270871⟩, ⟨-1613111704363831813167312617925513828643659978119, -1613111704363831813167312617925513828643657880966⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨2021861153119052157905761445778254113319598645639, 2021861153119052157905761445778254113319598645640⟩
def centerBExp : DyadicInterval precision := ⟨91871662083822904963811869589589269714311158737, 91871662083822904963811869589589271913334414290⟩
def centerBLog : DyadicInterval precision := ⟨89099661760329582529350004074096256346012282870, 89099661760329582529350004074096258545035538423⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨91871662083822904963811869589589270264066972625, scale precision, 91871662083822904963811869589589271363578600402, scale precision,
    3, 128, 3, 128, ⟨-4043722306238104315811522891556508235384757132482, -4043722306238104315811522891556508235384755035329⟩, ⟨-4043722306238104315811522891556508217893639547232, -4043722306238104315811522891556508217893637450079⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨1899443256066344012630337314537754309230277491, 2216017656540843594568486214625237657012954245⟩
def wholeAExp : DyadicInterval precision := ⟨1457076315351450948047082186788007224970773813488, 1457707683773513925477741956702213446679176875042⟩
def wholeALog : DyadicInterval precision := ⟨1010821401672838003372446069258059721789517968263, 1011137530350683182654731711817158199758569694808⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1457076315351450948047082186788007225520529627376, scale precision, 1457707683773513925477741956702213446129421061154, scale precision,
    0, 128, 0, 128, ⟨-4432035313081687189136972429250475865452447731, -4432035313081687189136972429250475865450350578⟩, ⟨-3798886512132688025260674629075508067274948598, -3798886512132688025260674629075508067272851445⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨797886217135535601213561462349015058648188303747, 809836502735595761416983074307699172577520882056⟩
def wholeDExp : DyadicInterval precision := ⟨482506534178222248007502303634473306418081574606, 490462045819898463991457369988920388736986392916⟩
def wholeDLog : DyadicInterval precision := ⟨416948124396604742320674577430730284979084793064, 422916858198723400101802834922666848815462481446⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨482506534178222248007502303634473306967837388494, scale precision, 490462045819898463991457369988920388187230579028, scale precision,
    1, 128, 1, 128, ⟨-1619673005471191522833966148615398346820241033264, -1619673005471191522833966148615398346820238936111⟩, ⟨-1595772434271071202427122924698030115658189688259, -1595772434271071202427122924698030115658187591106⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨800374131131473358676725125655331826574114410763, 812757290144920169154832965114479480152479331255⟩
def wholeCExp : DyadicInterval precision := ⟨480581820224566243808937463873283691772894783151, 488795058223570730217557954856221029119672186420⟩
def wholeCLog : DyadicInterval precision := ⟨415500411324872022765153541641004625309735370370, 421668194597013790802451617468815400241405085372⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨480581820224566243808937463873283692322650597039, scale precision, 488795058223570730217557954856221028569916372532, scale precision,
    1, 128, 1, 128, ⟨-1625514580289840338309665930228958961976826994278, -1625514580289840338309665930228958961976824897125⟩, ⟨-1600748262262946717353450251310663651504455022930, -1600748262262946717353450251310663651504452925777⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨2003746957611652394521442014905389668010256066022, 2040015652096749340747538885957826284237421440828⟩
def wholeBExp : DyadicInterval precision := ⟨89617355523607815553902329988002363292871697908, 94177480910738800564198543877444271062001742711⟩
def wholeBLog : DyadicInterval precision := ⟨86977141877718825502824807495140295204888237486, 91267498230154737506412165824082495989440312834⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨89617355523607815553902329988002363842627511796, scale precision, 94177480910738800564198543877444270512245928823, scale precision,
    4, 128, 3, 128, ⟨-4080031304193498681495077771915652577440395495959, -4080031304193498681495077771915652577440393398806⟩, ⟨-4007493915223304789042884029810779327489078549319, -4007493915223304789042884029810779327489076452166⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0359StableWitnesses

end


