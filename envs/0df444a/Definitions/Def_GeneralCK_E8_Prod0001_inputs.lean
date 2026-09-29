-- Prove2me | Definitions.Def_GeneralCK_E8_Prod0001_inputs
-- name    : GeneralCK_E8_Prod0001_inputs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-25T02:02:37.122697+00:00
-- url     : https://prove2.me/theorems/9c674c05-4e9d-4f8e-a2ce-94301fad60a3
-- title:
--   Exact numerical inputs and rectangle for E8 production cell 0001
-- statement:
--   At dyadic precision $160$, these exact integer records supply exponential/logarithm witnesses and eight center/whole-cell inputs for E8 production cell 0001. Each padded alpha interval extends the original interval by $65536$ units of $2^{-160}$ on both sides. Exact rational constants specify the rectangle, its center and displacement intervals. The bundle records source definitions only; separate checker and enclosure theorems prove the numerical and analytic claims.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/tree/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK

import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.DivMod
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.MonotoneContinuity
import Definitions.Def_GeneralCK_E8_first_cell_Taylor_interface
import Definitions.Def_GeneralCK_E8_interval_checkers
import Definitions.Def_GeneralCK_E8_semantic_core

open GeneralCK GeneralCK.Certificates Set GeneralCK.Certificates.DyadicInterval

section
namespace GeneralCK.Certificates.E8TAxisProd0001Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (81250000000000000000000000000000000000000000000000000000011948189333493 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (3500000000000000000000000000000000000000000000000000000000637236764453 / 40000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (1 / 50 : ℝ)
noncomputable def centerS : ℝ := (84375000000000000000000000000000000000000000000000000000013939554222409 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (74999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-4567192616659071619386515102238384436424789197, 4567192616659071619386515102238384436424789197⟩
def dt : DyadicInterval 160 := ⟨-7307508186654514591018424163581415098279662715, 7307508186654514591018424163581415098279662715⟩
def InCell (s t : ℝ) : Prop :=
  sLower ≤ s ∧ s ≤ sUpper ∧ tLower ≤ t ∧ t ≤ tUpper
noncomputable def rectangle : Rect := ⟨sLower, sUpper, tLower, tUpper⟩





end GeneralCK.Certificates.E8TAxisProd0001Geometry
end

section
namespace GeneralCK.Certificates.E8TAxisProd0001StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩



def centerAAlpha : DyadicInterval precision := ⟨3798893981423257492988718450954299577395465180, 3798893981423257492988718450954299577395465181⟩
def centerAExp : DyadicInterval precision := ⟨1453923564186661310665317018859587707328393797719, 1453923564186661310665317018859587709527417053272⟩
def centerALog : DyadicInterval precision := ⟨1009241782561842849966002591658486092261563546585, 1009241782561842849966002591658486094460586802138⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1453923564186661310665317018859587707878149611607, scale precision, 1453923564186661310665317018859587708977661239384, scale precision,
    0, 128, 0, 128, ⟨-7597787962846514985977436901908599707413204648, -7597787962846514985977436901908599707411107495⟩, ⟨-7597787962846514985977436901908598602170753227, -7597787962846514985977436901908598602168656074⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩



def centerDAlpha : DyadicInterval precision := ⟨21370495222089901813019887143702178164829792486, 21370495222089901813019887143702178164829792487⟩
def centerDExp : DyadicInterval precision := ⟨1419379569827633630618157326958425743127605926610, 1419379569827633630618157326958425745326629182163⟩
def centerDLog : DyadicInterval precision := ⟨991821481258824824738644685212964217149601286016, 991821481258824824738644685212964219348624541569⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1419379569827633630618157326958425743677361740498, scale precision, 1419379569827633630618157326958425744776873368275, scale precision,
    0, 128, 0, 128, ⟨-42740990444179803626039774287404356895731217634, -42740990444179803626039774287404356895729120481⟩, ⟨-42740990444179803626039774287404355763590049465, -42740990444179803626039774287404355763587952312⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩



def centerCAlpha : DyadicInterval precision := ⟨25170502722020047716414005663968337407731604898, 25170502722020047716414005663968337407731604899⟩
def centerCExp : DyadicInterval precision := ⟨1412017753362315034386201743905428381145819411709, 1412017753362315034386201743905428383344842667262⟩
def centerCLog : DyadicInterval precision := ⟨988081973553454480706754000816220316853591331265, 988081973553454480706754000816220319052614586818⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1412017753362315034386201743905428381695575225597, scale precision, 1412017753362315034386201743905428382795086853374, scale precision,
    0, 128, 0, 128, ⟨-50341005444040095432828011327936675384486156445, -50341005444040095432828011327936675384484059292⟩, ⟨-50341005444040095432828011327936674246442360300, -50341005444040095432828011327936674246440263147⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩



def centerBAlpha : DyadicInterval precision := ⟨46554641643973243399019820135420218326683268885, 46554641643973243399019820135420218326683268886⟩
def centerBExp : DyadicInterval precision := ⟨1371296261807782342538601000242932136151713753186, 1371296261807782342538601000242932138350737008739⟩
def centerBLog : DyadicInterval precision := ⟨967222447572329409765356335126531330148706287834, 967222447572329409765356335126531332347729543387⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1371296261807782342538601000242932136701469567074, scale precision, 1371296261807782342538601000242932137800981194851, scale precision,
    0, 128, 0, 128, ⟨-93109283287946486798039640270840437239286942002, -93109283287946486798039640270840437239284844849⟩, ⟨-93109283287946486798039640270840436067448230692, -93109283287946486798039640270840436067446133539⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩



def wholeAAlpha : DyadicInterval precision := ⟨2532592299075639559542598685704412299858871781, 5065202303167835215808940955361609459283110735⟩
def wholeAExp : DyadicInterval precision := ⟨1451406261215048238048665418490328880814971300707, 1456445219907862366338488118605723268423414970862⟩
def wholeALog : DyadicInterval precision := ⟨1007979314346565773386485143059333172819831600857, 1010505341326056445575717809135292022952375811415⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1451406261215048238048665418490328881364727114595, scale precision, 1456445219907862366338488118605723267873659156974, scale precision,
    0, 128, 0, 128, ⟨-10130404606335670431617881910723219472146955901, -10130404606335670431617881910723219472144858748⟩, ⟨-5065184598151279119085197371408824048054362095, -5065184598151279119085197371408824048052264942⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩



def wholeDAlpha : DyadicInterval precision := ⟨20578871293540181087774692060534010761932455778, 22162133741881529770516429908069211989432986974⟩
def wholeDExp : DyadicInterval precision := ⟨1417842757137037989742285799922994927468086581895, 1420918019911383254566844357126927031797158658050⟩
def wholeDLog : DyadicInterval precision := ⟨991041631832012714857158240438297378656595154964, 992601745007901601457433275450218203485852649055⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1417842757137037989742285799922994928017842395783, scale precision, 1420918019911383254566844357126927031247402844162, scale precision,
    0, 128, 0, 128, ⟨-44324267483763059541032859816138424545551175676, -44324267483763059541032859816138424545549078523⟩, ⟨-41157742587080362175549384121068020958408269492, -41157742587080362175549384121068020958406172339⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩



def wholeCAlpha : DyadicInterval precision := ⟨23112119987288769110966614346048366509737452059, 27229001637740082023660026865057311811959644990⟩
def wholeCExp : DyadicInterval precision := ⟨1408045746988392385501324593993414677796734509450, 1416000739382545652019056606267271858666372732018⟩
def wholeCLog : DyadicInterval precision := ⟨986060372561514944316941668173754764663771995451, 990106358699667674089767031322997502108730900682⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1408045746988392385501324593993414678346490323338, scale precision, 1416000739382545652019056606267271858116616918130, scale precision,
    0, 128, 0, 128, ⟨-54458003275480164047320053730114624194547410758, -54458003275480164047320053730114624194545313605⟩, ⟨-46224239974577538221933228692096732452054623183, -46224239974577538221933228692096732452052526030⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩



def wholeBAlpha : DyadicInterval precision := ⟨43702316363191017940573234188486312291623637586, 49407379045633827464414075058902870336018902476⟩
def wholeBExp : DyadicInterval precision := ⟨1365953370436910710094213347852217826469402750154, 1376659275366914708624851436993480765599208656981⟩
def wholeBLog : DyadicInterval precision := ⟨964463331704461220929462846819637724445475614936, 969986726310514225814593545165102081001021017685⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1365953370436910710094213347852217827019158564042, scale precision, 1376659275366914708624851436993480765049452843093, scale precision,
    0, 128, 0, 128, ⟨-98814758091267654928828150117805741260250017627, -98814758091267654928828150117805741260247920474⟩, ⟨-87404632726382035881146468376972623999611517965, -87404632726382035881146468376972623999609420812⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩







end GeneralCK.Certificates.E8TAxisProd0001StableWitnesses
end

section
namespace GeneralCK.Certificates.E8TAxisProd0001PaddedInputs
open DyadicInterval E8TAxisStableInterval
abbrev precision := E8TAxisProd0001StableWitnesses.precision
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def centerAAlpha : DyadicInterval precision := ⟨3798893981423257492988718450954299577395399644, 3798893981423257492988718450954299577395530717⟩
def centerAInput : Inputs precision :=
  { E8TAxisProd0001StableWitnesses.centerAInput with alpha := centerAAlpha }



def centerBAlpha : DyadicInterval precision := ⟨46554641643973243399019820135420218326683203349, 46554641643973243399019820135420218326683334422⟩
def centerBInput : Inputs precision :=
  { E8TAxisProd0001StableWitnesses.centerBInput with alpha := centerBAlpha }



def centerCAlpha : DyadicInterval precision := ⟨25170502722020047716414005663968337407731539362, 25170502722020047716414005663968337407731670435⟩
def centerCInput : Inputs precision :=
  { E8TAxisProd0001StableWitnesses.centerCInput with alpha := centerCAlpha }



def centerDAlpha : DyadicInterval precision := ⟨21370495222089901813019887143702178164829726950, 21370495222089901813019887143702178164829858023⟩
def centerDInput : Inputs precision :=
  { E8TAxisProd0001StableWitnesses.centerDInput with alpha := centerDAlpha }



def wholeAAlpha : DyadicInterval precision := ⟨2532592299075639559542598685704412299858806245, 5065202303167835215808940955361609459283176271⟩
def wholeAInput : Inputs precision :=
  { E8TAxisProd0001StableWitnesses.wholeAInput with alpha := wholeAAlpha }



def wholeBAlpha : DyadicInterval precision := ⟨43702316363191017940573234188486312291623572050, 49407379045633827464414075058902870336018968012⟩
def wholeBInput : Inputs precision :=
  { E8TAxisProd0001StableWitnesses.wholeBInput with alpha := wholeBAlpha }



def wholeCAlpha : DyadicInterval precision := ⟨23112119987288769110966614346048366509737386523, 27229001637740082023660026865057311811959710526⟩
def wholeCInput : Inputs precision :=
  { E8TAxisProd0001StableWitnesses.wholeCInput with alpha := wholeCAlpha }



def wholeDAlpha : DyadicInterval precision := ⟨20578871293540181087774692060534010761932390242, 22162133741881529770516429908069211989433052510⟩
def wholeDInput : Inputs precision :=
  { E8TAxisProd0001StableWitnesses.wholeDInput with alpha := wholeDAlpha }





end GeneralCK.Certificates.E8TAxisProd0001PaddedInputs
end


