-- Prove2me | Definitions.Def_GeneralCK_E8_first_cell_inputs
-- name    : GeneralCK_E8_first_cell_inputs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-24T21:33:45.31123+00:00
-- url     : https://prove2.me/theorems/8ef4db1c-18a7-493b-aec3-0bcff018bf7e
-- title:
--   Exact E8 first-cell coordinates and padded inverse input intervals
-- statement:
--   The first positive-axis E8 cell has center $(s_c,t_c)=(57/800,3/200)$ and the exact rational lower coordinates sLower and tLower. At precision $160$, eight Inputs records specify four center and four whole-cell inverse brackets together with their saved exponential and logarithm interval data. Each padded alpha interval widens its historical bracket by $4096$ units of $2^{-160}$ at either end. The lower and upper functions convert integer interval endpoints to real numbers by dividing by $2^p$. This bundle records the exact source data; inverse coverage and successful checker evaluation are proved separately.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/tree/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates

import Definitions.Def_GeneralCK_E8_semantic_core

open GeneralCK.Certificates.DyadicInterval
open GeneralCK.Certificates.E8TAxisStableInterval

namespace GeneralCK.Certificates.E8TAxisOneCellGeometry



noncomputable def sLower : ℝ :=
  13500000000000000000000000000000000000000000000000000000000637236764453 /
  200000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def tLower : ℝ :=
  24999999999999999999999999999999999999999999999999999999997261873277741 /
  2500000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def centerS : ℝ := 57 / 800
noncomputable def centerT : ℝ := 3 / 200


















end GeneralCK.Certificates.E8TAxisOneCellGeometry

namespace GeneralCK.Certificates.E8TAxisFirstCellInverseCoverage



noncomputable def lower {p : ℕ} (alpha : DyadicInterval p) : ℝ :=
  (alpha.lo : ℝ) / (scale p : ℝ)

noncomputable def upper {p : ℕ} (alpha : DyadicInterval p) : ℝ :=
  (alpha.hi : ℝ) / (scale p : ℝ)
















end GeneralCK.Certificates.E8TAxisFirstCellInverseCoverage

namespace GeneralCK.Certificates.E8TAxisOneCellStableWitnesses



set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩




def centerAAlpha : DyadicInterval precision := ⟨3798893981423257492988718450954299577395465180, 3798893981423257492988718450954299577395465181⟩
def centerAExp : DyadicInterval precision := ⟨1453923564186661310665317018859587707328393797719, 1453923564186661310665317018859587709527417053272⟩
def centerALog : DyadicInterval precision := ⟨1009241782561842849966002591658486092261563546585, 1009241782561842849966002591658486094460586802138⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩





def centerDAlpha : DyadicInterval precision := ⟨18045766478403223402692576908062521137160327707, 18045766478403223402692576908062521137160327708⟩
def centerDExp : DyadicInterval precision := ⟨1425852095715601701956974364377367523056145335983, 1425852095715601701956974364377367525255168591536⟩
def centerDLog : DyadicInterval precision := ⟨995101379269639710001049868967429114998909539386, 995101379269639710001049868967429117197932794939⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩





def centerCAlpha : DyadicInterval precision := ⟨21845476548415638059588891295986117678146826431, 21845476548415638059588891295986117678146826432⟩
def centerCExp : DyadicInterval precision := ⟨1418457285902836992172107953103186432852933275179, 1418457285902836992172107953103186435051956530732⟩
def centerCLog : DyadicInterval precision := ⟨991353521917068733163410400456957416268130316904, 991353521917068733163410400456957418467153572457⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩





def centerBAlpha : DyadicInterval precision := ⟨39899813383783773507048465821561279311279824193, 39899813383783773507048465821561279311279824194⟩
def centerBExp : DyadicInterval precision := ⟨1383841469593821749822064582626245044018339086770, 1383841469593821749822064582626245046217362342323⟩
def centerBLog : DyadicInterval precision := ⟨973680501901597785353360659766093915976436771482, 973680501901597785353360659766093918175460027035⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩





def wholeAAlpha : DyadicInterval precision := ⟨2532592299075639559542598685704412299858871781, 5065202303167835215808940955361609459283110735⟩
def wholeAExp : DyadicInterval precision := ⟨1451406261215048238048665418490328880814971300707, 1456445219907862366338488118605723268423414970862⟩
def wholeALog : DyadicInterval precision := ⟨1007979314346565773386485143059333172819831600857, 1010505341326056445575717809135292022952375811415⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩





def wholeDAlpha : DyadicInterval precision := ⟨17095885651040514825842973106213884464633028208, 18995665047735116218618892934888584156033732658⟩
def wholeDExp : DyadicInterval precision := ⟨1423999843327116683343282796578766319521637719281, 1427706722737910795912950268245206061292909357824⟩
def wholeDLog : DyadicInterval precision := ⟨994163517538761546318115582447098111973928863644, 996039840755618551298709894112357435963326953459⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩





def wholeCAlpha : DyadicInterval precision := ⟨19628941078537730196812941240615820545473948721, 24062128956868075075081587276944356176509367033⟩
def wholeCExp : DyadicInterval precision := ⟨1414161070744739559008334114269995750326367851507, 1422766325265285935775877612508304622625767981585⟩
def wholeCLog : DyadicInterval precision := ⟨989171680560481932248136251716810558925788983103, 993538609139131549366545609183574419997889925501⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩





def wholeBAlpha : DyadicInterval precision := ⟨36731543043628067898155960956801315285829304373, 43068519725266230484044453709715361187247552415⟩
def wholeBExp : DyadicInterval precision := ⟨1377853800896563995864571507763643413726591103949, 1389854329341637920452395630847774507071942206260⟩
def wholeBLog : DyadicInterval precision := ⟨970601713898490641027456271028022370013574565707, 976765729861290771806028354487818357028767967502⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩









end GeneralCK.Certificates.E8TAxisOneCellStableWitnesses

namespace GeneralCK.Certificates.E8TAxisFirstCellPaddedInputs

abbrev precision := E8TAxisOneCellStableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerAAlpha : DyadicInterval precision := ⟨3798893981423257492988718450954299577395461084, 3798893981423257492988718450954299577395469277⟩
def centerAInput : Inputs precision :=
  { E8TAxisOneCellStableWitnesses.centerAInput with alpha := centerAAlpha }



def centerBAlpha : DyadicInterval precision := ⟨39899813383783773507048465821561279311279820097, 39899813383783773507048465821561279311279828290⟩
def centerBInput : Inputs precision :=
  { E8TAxisOneCellStableWitnesses.centerBInput with alpha := centerBAlpha }



def centerCAlpha : DyadicInterval precision := ⟨21845476548415638059588891295986117678146822335, 21845476548415638059588891295986117678146830528⟩
def centerCInput : Inputs precision :=
  { E8TAxisOneCellStableWitnesses.centerCInput with alpha := centerCAlpha }



def centerDAlpha : DyadicInterval precision := ⟨18045766478403223402692576908062521137160323611, 18045766478403223402692576908062521137160331804⟩
def centerDInput : Inputs precision :=
  { E8TAxisOneCellStableWitnesses.centerDInput with alpha := centerDAlpha }



def wholeAAlpha : DyadicInterval precision := ⟨2532592299075639559542598685704412299858867685, 5065202303167835215808940955361609459283114831⟩
def wholeAInput : Inputs precision :=
  { E8TAxisOneCellStableWitnesses.wholeAInput with alpha := wholeAAlpha }



def wholeBAlpha : DyadicInterval precision := ⟨36731543043628067898155960956801315285829300277, 43068519725266230484044453709715361187247556511⟩
def wholeBInput : Inputs precision :=
  { E8TAxisOneCellStableWitnesses.wholeBInput with alpha := wholeBAlpha }



def wholeCAlpha : DyadicInterval precision := ⟨19628941078537730196812941240615820545473944625, 24062128956868075075081587276944356176509371129⟩
def wholeCInput : Inputs precision :=
  { E8TAxisOneCellStableWitnesses.wholeCInput with alpha := wholeCAlpha }



def wholeDAlpha : DyadicInterval precision := ⟨17095885651040514825842973106213884464633024112, 18995665047735116218618892934888584156033736754⟩
def wholeDInput : Inputs precision :=
  { E8TAxisOneCellStableWitnesses.wholeDInput with alpha := wholeDAlpha }





end GeneralCK.Certificates.E8TAxisFirstCellPaddedInputs


