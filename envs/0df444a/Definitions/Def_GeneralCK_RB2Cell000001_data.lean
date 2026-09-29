-- Prove2me | Definitions.Def_GeneralCK_RB2Cell000001_data
-- name    : GeneralCK_RB2Cell000001_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-24T23:15:36.60506+00:00
-- url     : https://prove2.me/theorems/d5d2a59b-f189-4322-b080-f72598c8d193
-- title:
--   Exact certificate data for the second RB2 cell
-- statement:
--   For the second RB2 cell, the entropy coordinates are $e=H(u)$ and $f=H(u+\rho(1/2-u))$, with $$\frac1{10}\le u\le\frac{257}{2560},\qquad \frac{53}{512}\le\rho\le\frac{137}{1280}.$$ This bundle stores the source's exact dyadic endpoints, proposed logarithm enclosures, input and register jet records, center and whole-cell instruction lists, and their affine-coordinate real semantics. Endpoint intervals at precision $40$ are lifted exactly to precision $64$ for logarithm checks. All integer data and program definitions are preserved from the release source. Separate theorem proofs check these proposals and use them to establish positivity of the correction matrix's first diagonal entry and determinant. The data bundle itself introduces no positivity assumption.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/releases/tag/v1.0

import Definitions.Def_GeneralCK_RB2_program_data

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell000001Endpoints
open GeneralCK.Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

noncomputable def lift40 (a : DyadicInterval 40) : DyadicInterval 64 :=
  ⟨a.lo*16777216, a.hi*16777216⟩







noncomputable def sharedTwo : DyadicInterval 64 := ⟨12786308645202655420,12786308645202662926⟩

noncomputable def out_w0 : DyadicInterval 40 := ⟨-2529573748800,-2529573690944⟩



noncomputable def out_w1 : DyadicInterval 40 := ⟨-2529573748800,-2529573690944⟩



noncomputable def out_w2 : DyadicInterval 40 := ⟨-116083747264,-116083747200⟩



noncomputable def out_w3 : DyadicInterval 40 := ⟨-116083747264,-116083747200⟩



noncomputable def out_w4 : DyadicInterval 40 := ⟨-2143970009856,-2143969970560⟩



noncomputable def out_w5 : DyadicInterval 40 := ⟨-2143970009856,-2143969970560⟩



noncomputable def out_w6 : DyadicInterval 40 := ⟨-168755665728,-168755665664⟩



noncomputable def out_w7 : DyadicInterval 40 := ⟨-168755665728,-168755665664⟩



noncomputable def out_w8 : DyadicInterval 40 := ⟨762123383616,762123402880⟩



noncomputable def out_w9 : DyadicInterval 40 := ⟨83671233088,83671233152⟩



noncomputable def out_w10 : DyadicInterval 40 := ⟨-90566838400,-90566838336⟩



noncomputable def out_w11 : DyadicInterval 40 := ⟨83671356160,83671356224⟩



noncomputable def out_w12 : DyadicInterval 40 := ⟨-90566982656,-90566982592⟩



noncomputable def out_w13 : DyadicInterval 40 := ⟨-6895626432,-6895626368⟩



noncomputable def out_w14 : DyadicInterval 40 := ⟨-6895605312,-6895605248⟩



noncomputable def out_w15 : DyadicInterval 40 := ⟨174238071424,174238071488⟩



noncomputable def out_w16 : DyadicInterval 40 := ⟨174238338816,174238338880⟩



noncomputable def out_w17 : DyadicInterval 40 := ⟨2413489943680,2413490001536⟩



noncomputable def out_w18 : DyadicInterval 40 := ⟨2413489943680,2413490001536⟩



noncomputable def out_w19 : DyadicInterval 40 := ⟨1975214304896,1975214343488⟩



noncomputable def out_w20 : DyadicInterval 40 := ⟨1975214304896,1975214343488⟩



noncomputable def out_w21 : DyadicInterval 40 := ⟨-2531719137984,-2531719080128⟩



noncomputable def out_w22 : DyadicInterval 40 := ⟨-2527432537536,-2527432479680⟩



noncomputable def out_w23 : DyadicInterval 40 := ⟨-116322434304,-116322434240⟩



noncomputable def out_w24 : DyadicInterval 40 := ⟨-115845112128,-115845112064⟩



noncomputable def out_w25 : DyadicInterval 40 := ⟨-2151089336896,-2151089297472⟩



noncomputable def out_w26 : DyadicInterval 40 := ⟨-2136891211904,-2136891172736⟩



noncomputable def out_w27 : DyadicInterval 40 := ⟨-169934367808,-169934367744⟩



noncomputable def out_w28 : DyadicInterval 40 := ⟨-167579105152,-167579105088⟩



noncomputable def out_w29 : DyadicInterval 40 := ⟨81066406144,81066406208⟩



noncomputable def out_w30 : DyadicInterval 40 := ⟨-87522554112,-87522554048⟩



noncomputable def out_w31 : DyadicInterval 40 := ⟨86299405248,86299405312⟩



noncomputable def out_w32 : DyadicInterval 40 := ⟨-93654321728,-93654321664⟩



noncomputable def out_w33 : DyadicInterval 40 := ⟨-7354916480,-7354916416⟩



noncomputable def out_w34 : DyadicInterval 40 := ⟨-6456147904,-6456147840⟩



noncomputable def out_w35 : DyadicInterval 40 := ⟨168588960256,168588960320⟩



noncomputable def out_w36 : DyadicInterval 40 := ⟨179953726976,179953727040⟩



noncomputable def out_w37 : DyadicInterval 40 := ⟨2411110045440,2411110103296⟩



noncomputable def out_w38 : DyadicInterval 40 := ⟨2415873968064,2415874025920⟩



noncomputable def out_w39 : DyadicInterval 40 := ⟨1966956804992,1966956843584⟩



noncomputable def out_w40 : DyadicInterval 40 := ⟨1983510192384,1983510230976⟩



end LaneCBRB2Cell000001Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000001
open Set LaneCBRB2Cell000001Endpoints
open BivariateJetProgram (zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
















































noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨110165911142,110165911143⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨115749368627,115749368628⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0

noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1

noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-110165911143,-110165911142⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2

noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨439589902745,439589902746⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3

noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨46277140152,46277140153⟩,⟨-115749368628,-115749368627⟩,⟨439589902745,439589902746⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4

noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨156443051294,156443051296⟩,⟨983762259148,983762259149⟩,⟨439589902745,439589902746⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5

noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨46277140151,46277140154⟩,⟨-115749368628,-115749368627⟩,⟨439589902745,439589902746⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes7 := centerStep6.proposed :: centerBoxes6

noncomputable def centerStep7 : Instruction 40 := ⟨.log 7,⟨⟨-2529573748800,-2529573690944⟩,⟨10973683302499,10973683302600⟩,⟨0,0⟩,⟨-109522921071186,-109522921069169⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes8 := centerStep7.proposed :: centerBoxes7

noncomputable def centerStep8 : Instruction 40 := ⟨.mul 8 0,⟨⟨-253451432255,-253451426454⟩,⟨-1430062121035,-1430062063157⟩,⟨0,0⟩,⟨10973683302297,10973683302802⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes9 := centerStep8.proposed :: centerBoxes8

noncomputable def centerStep9 : Instruction 40 := ⟨.neg 0,⟨⟨253451426454,253451432255⟩,⟨1430062063157,1430062121035⟩,⟨0,0⟩,⟨-10973683302802,-10973683302297⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes10 := centerStep9.proposed :: centerBoxes9

noncomputable def centerStep10 : Instruction 40 := ⟨.add 12 7,⟨⟨989345716633,989345716634⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes11 := centerStep10.proposed :: centerBoxes10

noncomputable def centerStep11 : Instruction 40 := ⟨.log 0,⟨⟨-116083747264,-116083747200⟩,⟨-1221944765405,-1221944765402⟩,⟨0,0⟩,⟨-1358011113281,-1358011113273⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes12 := centerStep11.proposed :: centerBoxes11

noncomputable def centerStep12 : Instruction 40 := ⟨.mul 1 0,⟨⟨-104452699931,-104452699873⟩,⟨-983427880578,-983427880510⟩,⟨0,0⟩,⟨1221944765396,1221944765411⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes13 := centerStep12.proposed :: centerBoxes12

noncomputable def centerStep13 : Instruction 40 := ⟨.neg 0,⟨⟨104452699873,104452699931⟩,⟨983427880510,983427880578⟩,⟨0,0⟩,⟨-1221944765411,-1221944765396⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes14 := centerStep13.proposed :: centerBoxes13

noncomputable def centerStep14 : Instruction 40 := ⟨.add 4 0,⟨⟨357904126327,357904132186⟩,⟨2413489943667,2413490001613⟩,⟨0,0⟩,⟨-12195628068213,-12195628067693⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes15 := centerStep14.proposed :: centerBoxes14

noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2143970009856,-2143969970560⟩,⟨6914068946748,6914068946846⟩,⟨3089521749396,3089521749444⟩,⟨-43477802502577,-43477802501361⟩,⟨-27155445258826,-27155445258157⟩,⟨-8681258477998,-8681258477732⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15

noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-305052899630,-305052894034⟩,⟨-934504657887,-934504622698⟩,⟨-417579357062,-417579341335⟩,⟨6186201141433,6186201141875⟩,⟨3808735517291,3808735556826⟩,⟨1235205277502,1235205277601⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16

noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨305052894034,305052899630⟩,⟨934504622698,934504657887⟩,⟨417579341335,417579357062⟩,⟨-6186201141875,-6186201141433⟩,⟨-3808735556826,-3808735517291⟩,⟨-1235205277601,-1235205277502⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17

noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-156443051296,-156443051294⟩,⟨-983762259149,-983762259148⟩,⟨-439589902746,-439589902745⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18

noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨943068576480,943068576482⟩,⟨-983762259149,-983762259148⟩,⟨-439589902746,-439589902745⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19

noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-168755665728,-168755665664⟩,⟨-1146955873495,-1146955873490⟩,⟨-512512262180,-512512262177⟩,⟨-1196447352180,-1196447352170⟩,⟨747279271417,747279271425⟩,⟨-238895899097,-238895899093⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20

noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-144744413275,-144744413219⟩,⟨-832772082511,-832772082445⟩,⟨-372120596574,-372120596542⟩,⟨1026211886018,1026211886042⟩,⟨1389314296618,1389314296699⟩,⟨204904804816,204904804825⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21

noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨144744413219,144744413275⟩,⟨832772082445,832772082511⟩,⟨372120596542,372120596574⟩,⟨-1026211886042,-1026211886018⟩,⟨-1389314296699,-1389314296618⟩,⟨-204904804825,-204904804816⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22

noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨449797307253,449797312905⟩,⟨1767276705143,1767276740398⟩,⟨789699937877,789699953636⟩,⟨-7212413027917,-7212413027451⟩,⟨-5198049853525,-5198049813909⟩,⟨-1440110082426,-1440110082318⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23

noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨807701433580,807701445091⟩,⟨4180766648810,4180766742011⟩,⟨789699937877,789699953636⟩,⟨-19408041096130,-19408041095144⟩,⟨-5198049853525,-5198049813909⟩,⟨-1440110082426,-1440110082318⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24

noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨92554280302,92554280308⟩,⟨-231498737256,-231498737254⟩,⟨879179805490,879179805492⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25

noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨13061803469181,13061803470029⟩,⟨32670461045266,32670461049792⟩,⟨-124075016268129,-124075016251734⟩,⟨163432106053148,163432106087805⟩,⟨-310339073483627,-310339073315660⟩,⟨2357195113858734,2357195114328581⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26

noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨9595203107162,9595203244533⟩,⟨73665733488490,73665734944269⟩,⟨-81764178095258,-81764176596427⟩,⟨137948041533325,137948048869566⟩,⟨-738042275957464,-738042261059270⟩,⟨1536259668347118,1536259696952815⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27

noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨86937179136,86937312000⟩,⟨-661443170025,-661441109275⟩,⟨734156643880,734158930129⟩,⟨8780735360802,8780787009715⟩,⟨-4494054185350,-4493980554465⟩,⟨-1450627331606,-1450525582787⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28

noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29

noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1186448806912,1186448939776⟩,⟨-661443170025,-661441109275⟩,⟨734156643880,734158930129⟩,⟨8780735360802,8780787009715⟩,⟨-4494054185350,-4493980554465⟩,⟨-1450627331606,-1450525582787⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30

noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨83671233088,83671356224⟩,⟨-612975842126,-612973863733⟩,⟨680361151241,680363346156⟩,⟨7795592030954,7795643012449⟩,⟨-3785452876094,-3785381726273⟩,⟨-1765332336957,-1765235176893⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31

noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨90287025768,90287168752⟩,⟨-711778179813,-711775740021⟩,⟨790024812733,790027519614⟩,⟨9817684298580,9817749844969⟩,⟨-5245341105318,-5245252574673⟩,⟨-1106736196474,-1106617474810⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32

noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-86937312000,-86937179136⟩,⟨661441109275,661443170025⟩,⟨-734158930129,-734156643880⟩,⟨-8780787009715,-8780735360802⟩,⟨4493980554465,4494054185350⟩,⟨1450525582787,1450627331606⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33

noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1012574315776,1012574448640⟩,⟨661441109275,661443170025⟩,⟨-734158930129,-734156643880⟩,⟨-8780787009715,-8780735360802⟩,⟨4493980554465,4494054185350⟩,⟨1450525582787,1450627331606⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34

noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-90566982656,-90566838336⟩,⟨718230834002,718233165927⟩,⟨-797192134678,-797189547533⟩,⟨-10003856193544,-10003795812530⟩,⟨5400568640259,5400652613967⟩,⟨997066383136,997180826121⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35

noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-83405950616,-83405806763⟩,⟨606957822310,606960313209⟩,⟨-673686499935,-673683736336⟩,⟨-7625449989468,-7625382269037⟩,⟨3644226656333,3644317398794⟩,⟨1863326247812,1863447104053⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36

noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨6881075152,6881361989⟩,⟨-104820357503,-104815426812⟩,⟨116338312798,116343783278⟩,⟨2192234309112,2192367575932⟩,⟨-1601114448985,-1600935175879⟩,⟨756590051338,756829629243⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37

noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨3440537576,3440680995⟩,⟨-52410178752,-52407713406⟩,⟨58169156399,58171891639⟩,⟨1096117154556,1096183787966⟩,⟨-800557224493,-800467587939⟩,⟨378295025669,378414814622⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38

noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-3440680995,-3440537576⟩,⟨52407713406,52410178752⟩,⟨-58171891639,-58169156399⟩,⟨-1096183787966,-1096117154556⟩,⟨800467587939,800557224493⟩,⟨-378414814622,-378295025669⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39

noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨758682702621,758682865304⟩,⟨52407713406,52410178752⟩,⟨-58171891639,-58169156399⟩,⟨-1096183787966,-1096117154556⟩,⟨800467587939,800557224493⟩,⟨-378414814622,-378295025669⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40

noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨6874027454,6874048466⟩,⟨-104599332632,-104598846892⟩,⟨116097922114,116098461088⟩,⟨2184381999625,2184397248206⟩,⟨-1593990238516,-1593972005876⟩,⟨751010405708,751032952860⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41

noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-6874048466,-6874027454⟩,⟨104598846892,104599332632⟩,⟨-116098461088,-116097922114⟩,⟨-2184397248206,-2184381999625⟩,⟨1593972005876,1593990238516⟩,⟨-751032952860,-751010405708⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42

noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1092637579310,1092637600322⟩,⟨104598846892,104599332632⟩,⟨-116098461088,-116097922114⟩,⟨-2184397248206,-2184381999625⟩,⟨1593972005876,1593990238516⟩,⟨-751032952860,-751010405708⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43

noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-6895626432,-6895605248⟩,⟨105256901625,105257392446⟩,⟨-116828864713,-116828320101⟩,⟨-2208216221717,-2208200740956⟩,⟨1615184084691,1615202567173⟩,⟨-768171561926,-768148742653⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44

noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3447813216,-3447802624⟩,⟨52628450812,52628696223⟩,⟨-58414432357,-58414160050⟩,⟨-1104108110859,-1104100370478⟩,⟨807592042345,807601283587⟩,⟨-384085780963,-384074371326⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45

noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3447802624,3447813216⟩,⟨-52628696223,-52628450812⟩,⟨58414160050,58414432357⟩,⟨1104100370478,1104108110859⟩,⟨-807601283587,-807592042345⟩,⟨384074371326,384085780963⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46

noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765571186240,765571216096⟩,⟨-52628696223,-52628450812⟩,⟨58414160050,58414432357⟩,⟨1104100370478,1104108110859⟩,⟨-807601283587,-807592042345⟩,⟨384074371326,384085780963⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47

noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48

noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49

noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨273159394827,273159400081⟩,⟨26149711723,26149833158⟩,⟨-29024615272,-29024480528⟩,⟨-546099312052,-546095499906⟩,⟨398493001469,398497559629⟩,⟨-187758238215,-187752601427⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50

noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1531142372480,1531142432192⟩,⟨-105257392446,-105256901624⟩,⟨116828320100,116828864714⟩,⟨2208200740956,2208216221718⟩,⟨-1615202567174,-1615184084690⟩,⟨768148742652,768171561926⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51

noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1193913021643,1193913178302⟩,⟨-779899020830,-779896386357⟩,⟨865634302969,865637225825⟩,⟨11372146871907,11372217237429⟩,⟨-6429799843768,-6429704145595⟩,⟨-455177361521,-455048629927⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52

noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1288314415510,1288314728828⟩,⟨-1559798041660,-1559792772714⟩,⟨1731268605939,1731274451651⟩,⟨22744293743823,22744434474851⟩,⟨-12859599687534,-12859408291194⟩,⟨-910354571358,-910097411538⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53

noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨174238071424,174238338880⟩,⟨-1331209263159,-1331204442628⟩,⟨1477550415622,1477555763986⟩,⟨17799375274578,17799511774918⟩,⟨-9186117413116,-9185938443502⟩,⟨-2762524379796,-2762290343359⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54

noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨59988209636,59988314179⟩,⟨-452263903483,-452262182395⟩,⟨501981629743,501983539224⟩,⟨5909132644771,5909178146391⟩,⟨-2967699919980,-2967637754604⟩,⟨-1108564260627,-1108480425554⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55

noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380392451789,380392473941⟩,⟨10265362536,10265655506⟩,⟨-11394210382,-11393885304⟩,⟨-216887180906,-216877939438⟩,⟨159208693010,159219713358⟩,⟨-76797173777,-76783583768⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56

noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3178101309654,3178101494730⟩,⟨-85767461880,-85765004185⟩,⟨95193581070,95196308119⟩,⟨1816599771087,1816677457741⟩,⟨-1335386419037,-1335293897227⟩,⟨647213797557,647327740439⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57

noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨173393898519,173394210796⟩,⟨-1311933040708,-1311927847588⟩,⟨1456154648080,1456160409706⟩,⟨17249816029187,17249955246346⟩,⟨-8729209038964,-8729021135892⟩,⟨-3082035326592,-3081783718668⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58

noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨347631969943,347632549676⟩,⟨-2643142303867,-2643132290216⟩,⟨2933705063702,2933716173692⟩,⟨35049191303765,35049467021264⟩,⟨-17915326452080,-17914959579394⟩,⟨-5844559706388,-5844074062027⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59

noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨523504643985,523504868494⟩,⟨72324520524,72327938300⟩,⟨-80279310040,-80275518094⟩,⟨-1507777212700,-1507684461776⟩,⟨1099128191960,1099252652132⟩,⟨-516071277298,-515905273433⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60

noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨361227574224,361227806598⟩,⟨74857820477,74861374021⟩,⟨-83091259011,-83087316428⟩,⟨-1555419258011,-1555322435315⟩,⟨1131887202854,1132016808382⟩,⟨-527777333257,-527604798871⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61

noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨722455148448,722455613196⟩,⟨149715640954,149722748042⟩,⟨-166182518022,-166174632856⟩,⟨-3110838516022,-3110644870630⟩,⟨2263774405708,2264033616764⟩,⟨-1055554666514,-1055209597742⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62

noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524268324014,1524268404738⟩,⟨-658545554,-657568992⟩,⟨729859012,730942600⟩,⟨23803492750,23834222093⟩,⟨-21230561298,-21193846174⟩,⟨17115789792,17161156218⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63

noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨1001549661214,1001550358543⟩,⟨207120173566,207130679162⟩,⟨-229901589811,-229889933990⟩,⟨-4297137916026,-4296848758481⟩,⟨3124550879645,3124934831711⟩,⟨-1452304947589,-1451796342281⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64

noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67862906673,67862909285⟩,⟨12993113030,12993173620⟩,⟨-14421578264,-14421511034⟩,⟨-270098740734,-270096829804⟩,⟨196620236742,196622518206⟩,⟨-91759843130,-91757026332⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65

noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨49852103081,49852105711⟩,⟨267585649389,267585709722⟩,⟨38146939531,38146991920⟩,⟨-1297487804801,-1297485889058⟩,⟨-221895727740,-221893734361⟩,⟨-177007729831,-177005559233⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66

noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2132216618341,2132216784648⟩,⟨-293155717148,-293154338710⟩,⟨325382263710,325383793222⟩,⟨6170282607414,6170326151174⟩,⟨-4520920426964,-4520868566794⟩,⟨2164222577664,2164286447259⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67

noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2969252101727,2969252449118⟩,⟨-612357995713,-612355092482⟩,⟨679674355368,679677576795⟩,⟨12930883259893,12930975113106⟩,⟨-9490243630228,-9490134496380⟩,⟨4572593873579,4572727949347⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68

noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨134626554289,134626577143⟩,⟨694855695023,694856075597⟩,⟨133833124347,133833425565⟩,⟨-3215658229856,-3215646970526⟩,⟨-885358143460,-885346768146⟩,⟨-223528532945,-223516237011⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69

noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8979845178196,8979846702602⟩,⟨-46348219132451,-46348178011436⟩,⟨-8926943511293,-8926920388637⟩,⟨692928579282975,692930170866504⟩,⟨151204318501445,151205402109164⟩,⟨32657567244823,32658481401440⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70

noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨8179777883903,8179784967663⟩,⟨-40527237068121,-40527084128333⟩,⟨-10009229761287,-10009107523891⟩,⟨578633687716139,578638845693544⟩,⟨171260174130196,171264986787369⟩,⟨21619705778995,21624913992062⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71

noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨16359555767806,16359569935326⟩,⟨-81054474136242,-81054168256666⟩,⟨-20018459522574,-20018215047782⟩,⟨1157267375432278,1157277691387088⟩,⟨342520348260392,342529973574738⟩,⟨43239411557990,43249827984124⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72

noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10973683302499,10973683302600⟩,⟨-109522921071186,-109522921069169⟩,⟨0,0⟩,⟨2186188521914400,2186188521974786⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73

noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9874171674723,9874171674824⟩,⟨-109522921071186,-109522921069170⟩,⟨0,0⟩,⟨2186188521914418,2186188521974777⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74

noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2413489943680,2413490001536⟩,⟨-12195628068220,-12195628067696⟩,⟨0,0⟩,⟨108164909937337,108164909975027⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75

noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7727577604755,7727577604855⟩,⟨-48593396379207,-48593396377898⟩,⟨-21713748611288,-21713748610675⟩,⟨611140590833168,611140590858156⟩,⟨327396415387436,327396415400353⟩,⟨122027083477617,122027083482914⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76

noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6628065976979,6628065977079⟩,⟨-48593396379208,-48593396377898⟩,⟨-21713748611288,-21713748610674⟩,⟨611140590833175,611140590858153⟩,⟨327396415387439,327396415400353⟩,⟨122027083477618,122027083482914⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77

noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1975214304896,1975214343488⟩,⟨-8061024820462,-8061024820111⟩,⟨-3602034011678,-3602034011516⟩,⟨42281355143300,42281355156274⟩,⟨27902724526770,27902724533043⟩,⟨8442362577422,8442362580115⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78

noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨99127803248,99127803250⟩,⟨879179805490,879179805492⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79

noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨134183688427,134183688430⟩,⟨703814752121,703814752127⟩,⟨314496572274,314496572278⟩,⟨-1760396448892,-1760396448888⟩,⟨-1573251050376,-1573251050368⟩,⟨-351500207392,-351500207389⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80

noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4388704248576,4388704345024⟩,⟨-20256652888682,-20256652887807⟩,⟨-3602034011678,-3602034011516⟩,⟨150446265080637,150446265131301⟩,⟨27902724526770,27902724533043⟩,⟨8442362577422,8442362580115⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81

noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨695263939886,695265099352⟩,⟨-5286284607734,-5286264580432⟩,⟨5867410127404,5867432347384⟩,⟨70098382607530,70098934042528⟩,⟨-35830652904160,-35829919158788⟩,⟨-11689119412776,-11688148124054⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82

noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5083968188462,5083969444376⟩,⟨-25542937496416,-25542917468239⟩,⟨2265376115726,2265398335868⟩,⟨220544647688167,220545199173829⟩,⟨-7927928377390,-7927194625745⟩,⟨-3246756835354,-3245785543939⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83

noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨458351313050,458351426288⟩,⟨1762334141382,1762336951345⟩,⟨204237729014,204239732303⟩,⟨-31133213483239,-31133129221621⟩,⟨1096663989675,1096747909398⟩,⟨-292715297088,-292627729126⟩⟩⟩
noncomputable def centerBoxes85 := centerStep84.proposed :: centerBoxes84

noncomputable def centerStep85 : Instruction 40 := ⟨.mul 88 85,⟨⟨220331822284,220331822286⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes86 := centerStep85.proposed :: centerBoxes85

noncomputable def centerStep86 : Instruction 40 := ⟨.neg 0,⟨⟨-220331822286,-220331822284⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes87 := centerStep86.proposed :: centerBoxes86

noncomputable def centerStep87 : Instruction 40 := ⟨.add 89 0,⟨⟨879179805490,879179805492⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes88 := centerStep87.proposed :: centerBoxes87

noncomputable def centerStep88 : Instruction 40 := ⟨.mul 12 0,⟨⟨1929849185432,1929849231699⟩,⟨-14578718540443,-14578718424289⟩,⟨0,0⟩,⟨135272188302591,135272188335022⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes89 := centerStep88.proposed :: centerBoxes88

noncomputable def centerStep89 : Instruction 40 := ⟨.neg 91,⟨⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes90 := centerStep89.proposed :: centerBoxes89

noncomputable def centerStep90 : Instruction 40 := ⟨.add 1 0,⟨⟨830337557656,830337603923⟩,⟨-14578718540443,-14578718424289⟩,⟨0,0⟩,⟨135272188302591,135272188335022⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes91 := centerStep90.proposed :: centerBoxes90

noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨34947922839,34947924789⟩,⟨-701013463700,-701013453897⟩,⟨331972847757,331972866257⟩,⟨8762949548886,8762949575105⟩,⟨-6658977614141,-6658977521421⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91

noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨493299235889,493299351077⟩,⟨1061320677682,1061323497448⟩,⟨536210576771,536212598560⟩,⟨-22370263934353,-22370179646516⟩,⟨-5562313624466,-5562229612023⟩,⟨-292715297088,-292627729126⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92

noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨500903595558,500903607567⟩,⟨2531120470889,2531120592376⟩,⟨0,0⟩,⟨3131155626176,3131158552760⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93

noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨224731921610,224731979475⟩,⟨1619099873754,1619101489619⟩,⟨244281005398,244281932321⟩,⟨-3899993537002,-3899940035712⟩,⟨-1299640092241,-1299597044521⟩,⟨-133352067043,-133312170582⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94

noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-695265099352,-695263939886⟩,⟨5286264580432,5286284607734⟩,⟨-5867432347384,-5867410127404⟩,⟨-70098934042528,-70098382607530⟩,⟨35829919158788,35830652904160⟩,⟨11688148124054,11689119412776⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95

noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3693439149224,3693440405138⟩,⟨-14970388308250,-14970368280073⟩,⟨-9469466359062,-9469444138920⟩,⟨80347331038109,80347882523771⟩,⟨63732643685558,63733377437203⟩,⟨20130510701476,20131481992891⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96

noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨450744926659,450745079941⟩,⟨537252198095,537255446314⟩,⟨-99202198899,-99199127893⟩,⟨-15273488690831,-15273393735966⟩,⟨-7850497896331,-7850386600221⟩,⟨-4141191598144,-4141059949344⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97

noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨312886102588,312886102592⟩,⟨1967524518296,1967524518298⟩,⟨879179805490,879179805492⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98

noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-312886102592,-312886102588⟩,⟨-1967524518298,-1967524518296⟩,⟨-879179805492,-879179805490⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99

noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨786625525184,786625525188⟩,⟨-1967524518298,-1967524518296⟩,⟨-879179805492,-879179805490⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100

noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1413131021708,1413131049326⟩,⟨-9301666552944,-9301666483599⟩,⟨-4156409393995,-4156409363002⟩,⟨59099075904132,59099075914856⟩,⟨36804265612671,36804265695038⟩,⟨11800374540584,11800374542815⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101

noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1413131049326,-1413131021708⟩,⟨9301666483599,9301666552944⟩,⟨4156409363002,4156409393995⟩,⟨-59099075914856,-59099075904132⟩,⟨-36804265695038,-36804265612671⟩,⟨-11800374542815,-11800374540584⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102

noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-313619421550,-313619393932⟩,⟨9301666483599,9301666552944⟩,⟨4156409363002,4156409393995⟩,⟨-59099075914856,-59099075904132⟩,⟨-36804265695038,-36804265612671⟩,⟨-11800374542815,-11800374540584⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103

noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-13199869433,-13199868269⟩,⟨424511900141,424511905995⟩,⟨49551824848,49551837207⟩,⟨-4445846825972,-4445846810740⟩,⟨2045861865795,2045861927983⟩,⟨2826840126283,2826840151201⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104

noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨437545057226,437545211672⟩,⟨961764098236,961767352309⟩,⟨-49650374051,-49647290686⟩,⟨-19719335516803,-19719240546706⟩,⟨-5804636030536,-5804524672238⟩,⟨-1314351471861,-1314219798143⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105

noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-99127803250,-99127803248⟩,⟨-879179805492,-879179805490⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106

noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4172171651,4172171652⟩,⟨26568110511,26568110517⟩,⟨39631760400,39631760401⟩,⟨-277662840919,-277662840910⟩,⟨252372404139,252372404144⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107

noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨9158151736,9158151959⟩,⟨12041358637,12041360063⟩,⟨86993946002,86993948090⟩,⟨-788425957731,-788425942698⟩,⟨114381737068,114381750391⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108

noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1496748367806,1496748389138⟩,⟨-7747362609890,-7747362216340⟩,⟨-1463389916580,-1463389845662⟩,⟨116167652716663,116167660748858⟩,⟨24781874067821,24781875703603⟩,⟨5530211915226,5530212228060⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109

noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨12466851933,12466852416⟩,⟨-48138317813,-48138310788⟩,⟨106234528589,106234534009⟩,⟨-275369400010,-275369245067⟩,⟨-266880328436,-266880240902⟩,⟨-185505644391,-185505623882⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110

noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-12466852416,-12466851933⟩,⟨48138310788,48138317813⟩,⟨-106234534009,-106234528589⟩,⟨275369245067,275369400010⟩,⟨266880240902,266880328436⟩,⟨185505623882,185505644391⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111

noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-111594655666,-111594655181⟩,⟨-831041494704,-831041487677⟩,⟨-106234534009,-106234528589⟩,⟨2474392500619,2474392655562⟩,⟨266880240902,266880328436⟩,⟨185505623882,185505644391⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112

noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨83134427055,83134428686⟩,⟨-547216576311,-547216572208⟩,⟨638094599154,638094614604⟩,⟨3476795668183,3476795668935⟩,⟨-3644458773807,-3644458734703⟩,⟨-2524891138422,-2524891138147⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113

noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨113169624458,113169628292⟩,⟨-1330698154107,-1330698096654⟩,⟨757981038195,757981079142⟩,⟨21227960572859,21227961870532⟩,⟨-6855198153615,-6855197491215⟩,⟨-4717492806584,-4717492601925⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114

noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-113169628292,-113169624458⟩,⟨1330698096654,1330698154107⟩,⟨-757981079142,-757981038195⟩,⟨-21227961870532,-21227960572859⟩,⟨6855197491215,6855198153615⟩,⟨4717492601925,4717492806584⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115

noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨986341999484,986342003318⟩,⟨1330698096654,1330698154107⟩,⟨-757981079142,-757981038195⟩,⟨-21227961870532,-21227960572859⟩,⟨6855197491215,6855198153615⟩,⟨4717492601925,4717492806584⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116

noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨120372540133,120372540604⟩,⟨793770621989,793770631466⟩,⟨189622806799,189622812901⟩,⟨-2466248842744,-2466248604607⟩,⟨-679289026893,-679288897886⟩,⟨-173216689070,-173216639420⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117

noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11326271364,11326271464⟩,⟨168692692128,168692694290⟩,⟨21564493338,21564494534⟩,⟨753972850106,753972904988⟩,⟨106416123026,106416150584⟩,⟨-17126992035,-17126985612⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118

noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨168522790791,168522938222⟩,⟨1675009595647,1675014959763⟩,⟨114642738956,114645554818⟩,⟨-1732050831410,-1731839749892⟩,⟨450683978178,450828577957⟩,⟨-594650225104,-594532970177⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119

noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-168522938222,-168522790791⟩,⟨-1675014959763,-1675009595647⟩,⟨-114645554818,-114642738956⟩,⟨1731839749892,1732050831410⟩,⟨-450828577957,-450683978178⟩,⟨594532970177,594650225104⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120

noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨56208983388,56209188684⟩,⟨-55915086009,-55908106028⟩,⟨129635450580,129639193365⟩,⟨-2168153787110,-2167889204302⟩,⟨-1750468670198,-1750281022699⟩,⟨461180903134,461338054522⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121

noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨29389073983397,29389100008804⟩,⟨-265549587510150,-265548931294949⟩,⟨-89556556947165,-89556070642896⟩,⟨3896561416813152,3896585019637644⟩,⟨1442780984472345,1442801441935576⟩,⟨334451204749624,334471629466701⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122

noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13178167517,13178167621⟩,⟨173801137956,173801140712⟩,⟨41519122390,41519123890⟩,⟨606093019758,606093101384⟩,⟨125054188762,125054229676⟩,⟨27478155824,27478171057⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123

noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨352241968469,352242283176⟩,⟨1462829028142,1462841105845⟩,⟨36395468337,36402328247⟩,⟨-21048973176403,-21048464600097⟩,⟨-3548831654600,-3548480035034⟩,⟨-2020540713795,-2020257853241⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124

noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-352242283176,-352241968469⟩,⟨-1462841105845,-1462829028142⟩,⟨-36402328247,-36395468337⟩,⟨21048464600097,21048973176403⟩,⟨3548480035034,3548831654600⟩,⟨2020257853241,2020540713795⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125

noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨85302774050,85303243203⟩,⟨-501077007609,-501061675833⟩,⟨-86052702298,-86042759023⟩,⟨1329129083294,1329732629697⟩,⟨-2256155995502,-2255693017638⟩,⟨705906381380,706320915652⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126

noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨233311491675,233311491680⟩,⟨1582994557611,1582994557619⟩,⟨314496572274,314496572278⟩,⟨-3959419704444,-3959419704440⟩,⟨-1573251050376,-1573251050368⟩,⟨-351500207392,-351500207389⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127

noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1660410429192,-1660408984046⟩,⟨-4138445996599,-4138404102913⟩,⟨451086195360,451112466606⟩,⟨41884695534385,41886240669372⟩,⟨-7832344365970,-7831147692433⟩,⟨2238804168177,2239911534787⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128

noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-181778724989,-181778566065⟩,⟨-1651769974739,-1651764328913⟩,⟨-236971850427,-236968715657⟩,⟨2334486225785,2334719563421⟩,⟨-219721734956,-219563416419⟩,⟨662269912760,662400515393⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129

noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨51532766686,51532925615⟩,⟨-68775417128,-68769771294⟩,⟨77524721847,77527856621⟩,⟨-1624933478659,-1624700141019⟩,⟨-1792972785332,-1792814466787⟩,⟨310769705368,310900308004⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130

noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4360829015,4360868928⟩,⟨-29954089994,-29952647263⟩,⟨5658249364,5659119441⟩,⟨-49308015735,-49247539866⟩,⟨-305850411798,-305806452000⟩,⟨51574429211,51611072390⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131

noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2415277815,2415292714⟩,⟨-6446859434,-6446310324⟩,⟨7266977996,7267294256⟩,⟨-143715250746,-143691495941⟩,⟨-177768277090,-177751730040⟩,⟨40063069203,40076285584⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132

noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4338918452,4338945303⟩,⟨-29289061551,-29287965644⟩,⟨5142166980,5142784190⟩,⟨-70776396159,-70725092339⟩,⟨-290219422403,-290185194599⟩,⟨42900607022,42926537521⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133

noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4338945303,-4338918452⟩,⟨29287965644,29289061551⟩,⟨-5142784190,-5142166980⟩,⟨70725092339,70776396159⟩,⟨290185194599,290219422403⟩,⟨-42926537521,-42900607022⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134

noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨21883712,21950476⟩,⟨-666124350,-663585712⟩,⟨515465174,516952461⟩,⟨21417076604,21528856293⟩,⟨-15665217199,-15587029597⟩,⟨8647891690,8710465368⟩⟩⟩


noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]

noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨56208983388,56209188684⟩,⟨-55915086009,-55908106028⟩,⟨129635450580,129639193365⟩,⟨-2168153787110,-2167889204302⟩,⟨-1750468670198,-1750281022699⟩,⟨461180903134,461338054522⟩⟩

noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨21883712,21950476⟩,⟨-666124350,-663585712⟩,⟨515465174,516952461⟩,⟨21417076604,21528856293⟩,⟨-15665217199,-15587029597⟩,⟨8647891690,8710465368⟩⟩

noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨109951162777,110380659508⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨113816633344,117682103911⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0

noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1

noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-110380659508,-109951162777⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2

noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨439375154380,439804651111⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3

noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨45482193715,47072841565⟩,⟨-117682103911,-113816633344⟩,⟨439375154380,439804651111⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4

noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨155433356492,157453501073⟩,⟨981829523865,985694994432⟩,⟨439375154380,439804651111⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5

noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨45052696984,47502338296⟩,⟨-117682103911,-113816633344⟩,⟨439375154380,439804651111⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes7 := wholeStep6.proposed :: wholeBoxes6

noncomputable def wholeStep7 : Instruction 40 := ⟨.log 7,⟨⟨-2531719137984,-2527432479680⟩,⟨10952333724070,10995116277821⟩,⟨0,0⟩,⟨-109951162778821,-109097176394608⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes8 := wholeStep7.proposed :: wholeBoxes7

noncomputable def wholeStep8 : Instruction 40 := ⟨.mul 8 0,⟨⟨-254160866589,-252743247966⟩,⟨-1436485765583,-1423625884593⟩,⟨0,0⟩,⟨10866601497217,11080514916241⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes9 := wholeStep8.proposed :: wholeBoxes8

noncomputable def wholeStep9 : Instruction 40 := ⟨.neg 0,⟨⟨252743247966,254160866589⟩,⟨1423625884593,1436485765583⟩,⟨0,0⟩,⟨-11080514916241,-10866601497217⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes10 := wholeStep9.proposed :: wholeBoxes9

noncomputable def wholeStep10 : Instruction 40 := ⟨.add 12 7,⟨⟨989130968268,989560464999⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes11 := wholeStep10.proposed :: wholeBoxes10

noncomputable def wholeStep11 : Instruction 40 := ⟨.log 0,⟨⟨-116322434304,-115845112064⟩,⟨-1222210059535,-1221679586417⟩,⟨0,0⟩,⟨-1358600847770,-1357421762684⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes12 := wholeStep11.proposed :: wholeBoxes11

noncomputable def wholeStep12 : Instruction 40 := ⟨.mul 1 0,⟨⟨-104690190874,-104215348860⟩,⟨-984143941519,-982711974881⟩,⟨0,0⟩,⟨1220618409840,1223270775532⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes13 := wholeStep12.proposed :: wholeBoxes12

noncomputable def wholeStep13 : Instruction 40 := ⟨.neg 0,⟨⟨104215348860,104690190874⟩,⟨982711974881,984143941519⟩,⟨0,0⟩,⟨-1223270775532,-1220618409840⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes14 := wholeStep13.proposed :: wholeBoxes13

noncomputable def wholeStep14 : Instruction 40 := ⟨.add 4 0,⟨⟨356958596826,358851057463⟩,⟨2406337859474,2420629707102⟩,⟨0,0⟩,⟨-12303785691773,-12087219907057⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes15 := wholeStep14.proposed :: wholeBoxes14

noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2151089336896,-2136891172736⟩,⟨6856201803240,6972654597950⟩,⟨3068195295147,3111110373992⟩,⟨-44217733504695,-42753075073738⟩,⟨-27507169882188,-26810267898813⟩,⟨-8803006275373,-8561821568185⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15

noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-308042715201,-302083360508⟩,⟨-959185429466,-909671111419⟩,⟨-426697808712,-408401018197⟩,⟨5912630289610,6457928530964⟩,⟨3677383520581,3939157664608⟩,⟨1191541200496,1278539422105⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16

noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨302083360508,308042715201⟩,⟨909671111419,959185429466⟩,⟨408401018197,426697808712⟩,⟨-6457928530964,-5912630289610⟩,⟨-3939157664608,-3677383520581⟩,⟨-1278539422105,-1191541200496⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17

noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-157453501073,-155433356492⟩,⟨-985694994432,-981829523865⟩,⟨-439804651111,-439375154380⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18

noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨942058126703,944078271284⟩,⟨-985694994432,-981829523865⟩,⟨-439804651111,-439375154380⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19

noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-169934367808,-167579105088⟩,⟨-1150441864572,-1143478258974⟩,⟨-513312622799,-511714024028⟩,⟨-1203731229689,-1189203002236⟩,⟨743445918963,751105410326⟩,⟨-239642621387,-238152317603⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20

noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-145911457541,-143581253554⟩,⟨-838165809692,-827385093401⟩,⟨-373781584487,-370461229556⟩,⟨1008615918818,1043800895816⟩,⟨1380937037075,1397699169012⟩,⟨203206095544,206601936745⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21

noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨143581253554,145911457541⟩,⟨827385093401,838165809692⟩,⟨370461229556,373781584487⟩,⟨-1043800895816,-1008615918818⟩,⟨-1397699169012,-1380937037075⟩,⟨-206601936745,-203206095544⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22

noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨445664614062,453954172742⟩,⟨1737056204820,1797351239158⟩,⟨778862247753,800479393199⟩,⟨-7501729426780,-6921246208428⟩,⟨-5336856833620,-5058320557656⟩,⟨-1485141358850,-1394747296040⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23

noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨802623210888,812805230205⟩,⟨4143394064294,4217980946260⟩,⟨778862247753,800479393199⟩,⟨-19805515118553,-19008466115485⟩,⟨-5336856833620,-5058320557656⟩,⟨-1485141358850,-1394747296040⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24

noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨90105393968,95004676592⟩,⟨-235364207822,-227633266688⟩,⟨878750308760,879609302222⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25

noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨12724908530623,13416797445489⟩,⟨30489156966148,35046002943923⟩,⟨-130974843118403,-117699651231371⟩,⟨146105363393279,183087257199125⟩,⟨-389701747018780,-236584729000864⟩,⟨2177337128459215,2557154134522288⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26

noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨9288948552334,9918260854006⟩,⟨70209003330005,77377417688244⟩,⟨-87808154286273,-76150720009428⟩,⟨94767670128209,184245466633386⟩,⟨-834059105468636,-649267798838460⟩,⟨1380585809376930,1707464064910706⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27

noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨84129718272,89776550144⟩,⟨-741104272878,-590168465551⟩,⟨640113823684,841007625729⟩,⟨6466813940170,11396488361333⟩,⟨-8379096907193,-939660174419⟩,⟨-6670048818011,4096967809529⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28

noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29

noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1183641346048,1189288177920⟩,⟨-741104272878,-590168465551⟩,⟨640113823684,841007625729⟩,⟨6466813940170,11396488361333⟩,⟨-8379096907193,-939660174419⟩,⟨-6670048818011,4096967809529⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30

noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨81066406144,86299405312⟩,⟨-688428777979,-545618044698⟩,⟨591793145939,781231296647⟩,⟨5547608831467,10315704041285⟩,⟨-7489866046586,-379581094829⟩,⟨-6751046453269,3487245041060⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31

noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨87269245420,93345863661⟩,⟨-802808303902,-630879106552⟩,⟨684269764906,911029568022⟩,⟨7034608350648,12980535802232⟩,⟨-9812236319391,-1113201557999⟩,⟨-7136742201424,5288664526475⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32

noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-89776550144,-84129718272⟩,⟨590168465551,741104272878⟩,⟨-841007625729,-640113823684⟩,⟨-11396488361333,-6466813940170⟩,⟨939660174419,8379096907193⟩,⟨-4096967809529,6670048818011⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33

noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1009735077632,1015381909504⟩,⟨590168465551,741104272878⟩,⟨-841007625729,-640113823684⟩,⟨-11396488361333,-6466813940170⟩,⟨939660174419,8379096907193⟩,⟨-4096967809529,6670048818011⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34

noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-93654321728,-87522554048⟩,⟨639067019164,806996590963⟩,⟨-915782450290,-693150612250⟩,⟨-13002063988559,-7374067091286⟩,⟨1420394540869,9796237632804⟩,⟨-5223987842214,6826115695786⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35

noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-86488311381,-80376224019⟩,⟨523760507531,698270640053⟩,⟨-794756975971,-564918526392⟩,⟨-10806392386650,-4713353133228⟩,⟨-643828588563,8227770875871⟩,⟨-4585336747191,8053733089976⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36

noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨780934039,12969639642⟩,⟨-279047796371,67391533501⟩,⟨-110487211065,346111041630⟩,⟨-3771784036002,8267182669004⟩,⟨-10456064907954,7114569317872⟩,⟨-11722078948615,13342397616451⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37

noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨390467019,6484819821⟩,⟨-139523898186,33695766751⟩,⟨-55243605533,173055520815⟩,⟨-1885892018001,4133591334502⟩,⟨-5228032453977,3557284658936⟩,⟨-5861039474308,6671198808226⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38

noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-6484819821,-390467019⟩,⟨-33695766751,139523898186⟩,⟨-173055520815,55243605533⟩,⟨-4133591334502,1885892018001⟩,⟨-3557284658936,5228032453977⟩,⟨-6671198808226,5861039474308⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39

noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨755638563795,761732935861⟩,⟨-33695766751,139523898186⟩,⟨-173055520815,55243605533⟩,⟨-4133591334502,1885892018001⟩,⟨-3557284658936,5228032453977⟩,⟨-6671198808226,5861039474308⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40

noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨6437230237,7330371733⟩,⟨-121024249740,-90314109438⟩,⟨97957300838,137338726350⟩,⟨1623175289995,2860129738320⟩,⟨-2502057684254,-830965907600⟩,⟨-343913170406,1955605444028⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41

noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-7330371733,-6437230237⟩,⟨90314109438,121024249740⟩,⟨-137338726350,-97957300838⟩,⟨-2860129738320,-1623175289995⟩,⟨830965907600,2502057684254⟩,⟨-1955605444028,343913170406⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42

noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1092181256043,1093074397539⟩,⟨90314109438,121024249740⟩,⟨-137338726350,-97957300838⟩,⟨-2860129738320,-1623175289995⟩,⟨830965907600,2502057684254⟩,⟨-1955605444028,343913170406⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43

noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-7354916480,-6456147840⟩,⟨90845978739,121836525848⟩,⟨-138260500014,-98534181698⟩,⟨-2892826681362,-1640240392574⟩,⟨844000835291,2534171297278⟩,⟨-1986116712795,337391135373⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44

noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3677458240,-3228073920⟩,⟨45422989369,60918262924⟩,⟨-69130250007,-49267090849⟩,⟨-1446413340681,-820120196287⟩,⟨422000417645,1267085648639⟩,⟨-993058356398,168695567687⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45

noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3228073920,3677458240⟩,⟨-60918262924,-45422989369⟩,⟨49267090849,69130250007⟩,⟨820120196287,1446413340681⟩,⟨-1267085648639,-422000417645⟩,⟨-168695567687,993058356398⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46

noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765351457536,765800861120⟩,⟨-60918262924,-45422989369⟩,⟨49267090849,69130250007⟩,⟨820120196287,1446413340681⟩,⟨-1267085648639,-422000417645⟩,⟨-168695567687,993058356398⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47

noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48

noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49

noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨273045314010,273268599385⟩,⟨22578527359,30256062435⟩,⟨-34334681588,-24489325209⟩,⟨-715032434580,-405793822498⟩,⟨207741476900,625514421064⟩,⟨-488901361007,85978292602⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50

noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1530702915072,1531601722240⟩,⟨-121836525848,-90845978738⟩,⟨98534181698,138260500014⟩,⟨1640240392574,2892826681362⟩,⟨-2534171297278,-844000835290⟩,⟨-337391135374,1986116712796⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51

noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1190611934582,1197270300295⟩,⟨-878747460592,-692017074483⟩,⟨750581776999,997205578883⟩,⟨8387266984108,14803055147296⟩,⟨-11399138998098,-1974340876622⟩,⟨-6962499266618,6519029612774⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52

noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1281712241388,1295028972814⟩,⟨-1757494921184,-1384034148966⟩,⟨1501163553998,1994411157765⟩,⟨16774533968224,29606110294581⟩,⟨-22798277996188,-3948681753244⟩,⟨-13920138258404,13038059225544⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53

noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨168588960256,179953727040⟩,⟨-1507659862488,-1175079223686⟩,⟨1274524985512,1710897491433⟩,⟨12174677967068,24141640720644⟩,⟨-18195288998822,-1006531019452⟩,⟨-14603579740963,9707250151376⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54

noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨57818087486,62196481952⟩,⟨-516182465847,-394200540052⟩,⟨425787550512,587154125380⟩,⟨3918713368087,8094806226599⟩,⟨-6158438282404,4460254218⟩,⟨-5430406516252,3401419061443⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55

noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380124454842,380658691440⟩,⟨1152257822,19586121692⟩,⟨-23358334940,269548495⟩,⟨-595407566184,150309071279⟩,⟨-336576197973,669347107883⟩,⟨-773520541791,608999254935⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56

noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3175878672417,3180342133256⟩,⟨-163868878339,-9613417805⟩,⟨-2255199382,195429406939⟩,⟨-1257514856336,4998412642435⟩,⟨-5620286172210,2816224505023⟩,⟨-5095518902625,6495740407213⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57

noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨167004355650,179903592737⟩,⟨-1502329643987,-1139132034257⟩,⟨1229736276567,1709400771910⟩,⟨11254746312202,23850870518885⟩,⟨-18310489661575,169543647439⟩,⟨-15998123029067,10414790194755⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58

noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨335593315906,359857319777⟩,⟨-3009989506475,-2314211257943⟩,⟨2504261262079,3420298263343⟩,⟨23429424279270,47992511239529⟩,⟨-36505778660397,-836987372013⟩,⟨-30601702770030,20122040346131⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59

noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨519312051523,527722536914⟩,⟨-46688319952,193322100292⟩,⟨-239782984750,76544663590⟩,⟨-5735990321428,2648472185236⟩,⟨-4972837392074,7257899256984⟩,⟨-9260897176919,8175438814300⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60

noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨356896828429,365601988382⟩,⟨-48517946691,200898026864⟩,⟨-249179625294,79544303828⟩,⟨-5969659765488,2789058561911⟩,⟨-5213354801952,7556892413583⟩,⟨-9641885579062,8552429034283⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61

noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨713793656858,731203976764⟩,⟨-97035893382,401796053728⟩,⟨-498359250588,159088607656⟩,⟨-11939319530976,5578117123822⟩,⟨-10426709603904,15113784827166⟩,⟨-19283771158124,17104858068566⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62

noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523372543339,1525164492003⟩,⟨-31522416410,30178271002⟩,⟨-38804544652,40303199176⟩,⟨-1219889345746,1269651391367⟩,⟨-1703205389678,1658056848964⟩,⟨-2292996579402,2330029883202⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63

noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨988960581223,1014274259226⟩,⟨-155564535156,577412307341⟩,⟨-717094617926,247479106287⟩,⟨-17395673524498,8603975708278⟩,⟨-15623726489058,22096436508976⟩,⟨-28310516612805,25311352593317⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64

noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67806234713,67917178431⟩,⟨11213998900,15039462242⟩,⟨-17066832422,-12163028242⟩,⟨-354495790845,-199879054658⟩,⟨101288614172,309920354704⟩,⟨-241928615853,44881813587⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65

noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨49497300845,50207234244⟩,⟨263706684777,271663810160⟩,⟨35415456044,40567077120⟩,⟨-1400933528342,-1202759224944⟩,⟨-313249146238,-117723379977⟩,⟨-295431846361,-70066595733⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66

noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2130992847205,2133496159849⟩,⟨-339432577350,-252945400418⟩,⟨274351912884,385189232366⟩,⟨4581986544843,8086321879722⟩,⟨-7090759577018,-2366261420458⟩,⟨-922300130778,5568027961550⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67

noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2966696195666,2971925271429⟩,⟨-709236046606,-528213052040⟩,⟨572915186430,804843455189⟩,⟨9599679151706,16952589890328⟩,⟨-14879992292687,-4975345776295⟩,⟨-1890251112803,11706912579837⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68

noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨133553343505,135707658282⟩,⟨679145921979,710514925596⟩,⟨121349015948,146402531361⟩,⟨-3704971352756,-2724541619404⟩,⟨-1414924901360,-359774054888⟩,⟨-847945143853,404912218255⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69

noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8908309486134,9052007144766⟩,⟨-48157432934034,-44581434355476⟩,⟨-9922902153641,-7965759660049⟩,⟨625061692938687,763519461484120⟩,⟨103345715199464,201482417294866⟩,⟨-13198353190334,79227379939104⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70

noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨8012618243011,8350268982455⟩,⟨-45704851708340,-35345275046365⟩,⟨-15057312190217,-5127403405817⟩,⟨368420137588129,788790715090313⟩,⟨-51721880961759,400589322755871⟩,⟨-249715567833638,294410852869728⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71

noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨16025236486022,16700537964910⟩,⟨-91409703416680,-70690550092730⟩,⟨-30114624380434,-10254806811634⟩,⟨736840275176258,1577581430180626⟩,⟨-103443761923518,801178645511742⟩,⟨-499431135667276,588821705739456⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72

noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10952333724070,10995116277821⟩,⟨-109951162778821,-109097176394608⟩,⟨0,0⟩,⟨2173453475238562,2199023255588622⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73

noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9852822096294,9895604650045⟩,⟨-109951162778820,-109097176394608⟩,⟨0,0⟩,⟨2173453475238575,2199023255588602⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74

noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2411110045440,2415874025920⟩,⟨-12269843176037,-12121908488212⟩,⟨0,0⟩,⟨104571265817406,111755106875729⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75

noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7677986271350,7777775934968⟩,⟨-49323484867982,-47877459400191⟩,⟨-22007515688402,-21425477238117⟩,⟨597096956833702,625578874954297⟩,⟨320820858663475,334144178307672⟩,⟨119575904060684,124542221536042⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76

noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6578474643574,6678264307192⟩,⟨-49323484867982,-47877459400191⟩,⟨-22007515688403,-21425477238117⟩,⟨597096956833711,625578874954288⟩,⟨320820858663479,334144178307668⟩,⟨119575904060685,124542221536041⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77

noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1966956804992,1983510230976⟩,⟨-8243817613242,-7882560632131⟩,⟨-3678287248790,-3527497605713⟩,⟨36496498068103,48046625537692⟩,⟨25241326128182,30558965809846⟩,⟨7381737332423,9498649777533⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78

noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨98913096826,99342593558⟩,⟨878750308760,879609302222⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79

noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨133174814112,135194958694⟩,⟨700073864327,707554288930⟩,⟨313473858794,315518682074⟩,⟨-1767320322048,-1753486165276⟩,⟨-1577200910340,-1569301190404⟩,⟨-351843720890,-351156861664⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80

noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4378066850432,4399384256896⟩,⟨-20513660789279,-20004469120343⟩,⟨-3678287248790,-3527497605713⟩,⟨141067763885509,159801732413421⟩,⟨25241326128182,30558965809846⟩,⟨7381737332423,9498649777533⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81

noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨671186631812,719714639554⟩,⟨-6019979012950,-4628422515886⟩,⟨5008522524158,6840596526686⟩,⟨46858848558540,95985022479058⟩,⟨-73011557320794,-1673974744026⟩,⟨-61203405540060,40244080692262⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82

noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5049253482244,5119098896450⟩,⟨-26533639802229,-24632891636229⟩,⟨1330235275368,3313098920973⟩,⟨187926612444049,255786754892479⟩,⟨-47770231192612,28884991065820⟩,⟨-53821668207637,49742730469795⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83

noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨454235576933,462518583894⟩,⟨1638102241523,1879281092255⟩,⟨119669212466,299343664232⟩,⟨-35785967240010,-26361911717507⟩,⟨-3252966055322,5260283212419⟩,⟨-4862871818991,4494333421032⟩⟩⟩
noncomputable def wholeBoxes85 := wholeStep84.proposed :: wholeBoxes84

noncomputable def wholeStep85 : Instruction 40 := ⟨.mul 88 85,⟨⟨219902325554,220761319016⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes86 := wholeStep85.proposed :: wholeBoxes85

noncomputable def wholeStep86 : Instruction 40 := ⟨.neg 0,⟨⟨-220761319016,-219902325554⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes87 := wholeStep86.proposed :: wholeBoxes86

noncomputable def wholeStep87 : Instruction 40 := ⟨.add 89 0,⟨⟨878750308760,879609302222⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes88 := wholeStep87.proposed :: wholeBoxes87

noncomputable def wholeStep88 : Instruction 40 := ⟨.mul 12 0,⟨⟨1927004356625,1932699220739⟩,⟨-14647622592683,-14510276640425⟩,⟨0,0⟩,⟨132062950305200,138483458204854⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes89 := wholeStep88.proposed :: wholeBoxes88

noncomputable def wholeStep89 : Instruction 40 := ⟨.neg 91,⟨⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes90 := wholeStep89.proposed :: wholeBoxes89

noncomputable def wholeStep90 : Instruction 40 := ⟨.add 1 0,⟨⟨827492728849,833187592963⟩,⟨-14647622592683,-14510276640425⟩,⟨0,0⟩,⟨132062950305200,138483458204854⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes91 := wholeStep90.proposed :: wholeBoxes90

noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨33906671132,35996307729⟩,⟨-722000179415,-680219757804⟩,⟨330673852191,333275037186⟩,⟨8415385086772,9118424866802⟩,⟨-6692236630045,-6625935308195⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91

noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨488142248065,498514891623⟩,⟨916102062108,1199061334451⟩,⟨450343064657,632618701418⟩,⟨-27370582153238,-17243486850705⟩,⟨-9945202685367,-1365652095776⟩,⟨-4862871818991,4494333421032⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92

noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨500409295618,501398026980⟩,⟨2510857612204,2551553037358⟩,⟨0,0⟩,⟨1957166706152,4308831445771⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93

noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨222163106187,227332187097⟩,⟨1531663353494,1703660175927⟩,⟨204959956837,288486052088⟩,⟨-7428549416319,-329098191245⟩,⟨-3506791192524,846535081825⟩,⟨-2217561209817,2049500753761⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94

noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-719714639554,-671186631812⟩,⟨4628422515886,6019979012950⟩,⟨-6840596526686,-5008522524158⟩,⟨-95985022479058,-46858848558540⟩,⟨1673974744026,73011557320794⟩,⟨-40244080692262,61203405540060⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95

noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3658352210878,3728197625084⟩,⟨-15885238273393,-13984490107393⟩,⟨-10518883775476,-8536020129871⟩,⟨45082741406451,112942883854881⟩,⟨26915300872208,103570523130640⟩,⟨-32862343359839,70702055317593⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96

noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨443106160346,458415819527⟩,⟨376087552579,705331648628⟩,⟨-250385958827,35955151477⟩,⟨-20976922917716,-9755161529200⟩,⟨-13415453642968,-1908538759749⟩,⟨-11270799194974,2657786926013⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97

noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨310866712984,314907002146⟩,⟨1963659047730,1971389988864⟩,⟨878750308760,879609302222⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98

noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-314907002146,-310866712984⟩,⟨-1971389988864,-1963659047730⟩,⟨-879609302222,-878750308760⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99

noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨784604625630,788644914792⟩,⟨-1971389988864,-1963659047730⟩,⟨-879609302222,-878750308760⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100

noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1403608082556,1422709153392⟩,⟨-9469401494528,-9137807919974⟩,⟨-4225127289939,-4089229003552⟩,⟨54199194176051,64024139581987⟩,⟨34545746687089,39076108286863⟩,⟨10906046078657,12698340656246⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101

noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1422709153392,-1403608082556⟩,⟨9137807919974,9469401494528⟩,⟨4089229003552,4225127289939⟩,⟨-64024139581987,-54199194176051⟩,⟨-39076108286863,-34545746687089⟩,⟨-12698340656246,-10906046078657⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102

noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-323197525616,-304096454780⟩,⟨9137807919974,9469401494528⟩,⟨4089229003552,4225127289939⟩,⟨-64024139581987,-54199194176051⟩,⟨-39076108286863,-34545746687089⟩,⟨-12698340656246,-10906046078657⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103

noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-13963143100,-12460409771⟩,⟨405902143038,443699971627⟩,⟨38277921886,61018908223⟩,⟨-4793086662942,-4112634032191⟩,⟨1815219520379,2272140520545⟩,⟨2719580493985,2933224530377⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104

noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨429143017246,445955409756⟩,⟨781989695617,1149031620255⟩,⟨-212108036941,96974059700⟩,⟨-25770009580658,-13867795561391⟩,⟨-11600234122589,363601760796⟩,⟨-8551218700989,5591011456390⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105

noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-99342593558,-98913096826⟩,⟨-879609302222,-878750308760⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106

noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4052982857,4291910488⟩,⟨25374198200,27762819599⟩,⟨39526600801,39737037424⟩,⟨-283296042850,-272034168828⟩,⟨251814268106,252930624064⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107

noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨8887752920,9430291420⟩,⟨7747908567,16317778736⟩,⟨86677559241,87311197222⟩,⟨-856628402366,-719800317674⟩,⟨108761645553,119972071186⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108

noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1487349951365,1506218364004⟩,⟨-7915545269682,-7581984872878⟩,⟨-1502195233939,-1425237785468⟩,⟨112084100843054,120363661956491⟩,⟨23786924195324,25804055049181⟩,⟨5283682946026,5783410924997⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109

noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨12022791336,12918533789⟩,⟨-57409167505,-38934258737⟩,⟨104367904619,108086685350⟩,⟨-502424762808,-48221054347⟩,⟨-311455815254,-222086472886⟩,⟨-195865923290,-175107756822⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110

noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-12918533789,-12022791336⟩,⟨38934258737,57409167505⟩,⟨-108086685350,-104367904619⟩,⟨48221054347,502424762808⟩,⟨222086472886,311455815254⟩,⟨175107756822,195865923290⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111

noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-112261127347,-110935888162⟩,⟨-840675043485,-821341141255⟩,⟨-108086685350,-104367904619⟩,⟨2247244309899,2701448018360⟩,⟨222086472886,311455815254⟩,⟨175107756822,195865923290⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112

noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨80596427247,85693840452⟩,⟨-568456262250,-526600176357⟩,⟨627100875690,648864210569⟩,⟨3127387294622,3840456576875⟩,⟨-3881618042986,-3402967430675⟩,⟨-2640161715161,-2408870873370⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113

noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨109025761181,117391788236⟩,⟨-1395649391967,-1268126324145⟩,⟨731224261701,784404725181⟩,⟨19709156333269,22826746518619⟩,⟨-7562454663017,-6139900443947⟩,⟨-5002453272339,-4433574767919⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114

noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-117391788236,-109025761181⟩,⟨1268126324145,1395649391967⟩,⟨-784404725181,-731224261701⟩,⟨-22826746518619,-19709156333269⟩,⟨6139900443947,7562454663017⟩,⟨4433574767919,5002453272339⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115

noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨982119839540,990485866595⟩,⟨1268126324145,1395649391967⟩,⟨-784404725181,-731224261701⟩,⟨-22826746518619,-19709156333269⟩,⟨6139900443947,7562454663017⟩,⟨4433574767919,5002453272339⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116

noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨118956110842,121789249371⟩,⟨778926659029,809002162835⟩,⟨183555431683,195665179595⟩,⟨-2783965702330,-2157231716414⟩,⟨-820363843993,-536959874174⟩,⟨-230142566058,-115515867060⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117

noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11192943277,11461962198⟩,⟨165739418642,171667357998⟩,⟨21060525240,22071495822⟩,⟨675452011469,832068481584⟩,⟨92326941650,120468791992⟩,⟨-20182542073,-14084440366⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118

noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨163135667197,174096326046⟩,⟨1462721060035,1887839891582⟩,⟨-6978360731,230851931482⟩,⟨-11198094342798,7772313102935⟩,⟨-6269469219077,7281930401631⟩,⟨-6721956851862,5540098217840⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119

noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-174096326046,-163135667197⟩,⟨-1887839891582,-1462721060035⟩,⟨-230851931482,6978360731⟩,⟨-7772313102935,11198094342798⟩,⟨-7281930401631,6269469219077⟩,⟨-5540098217840,6721956851862⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120

noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨48066780141,64196519900⟩,⟨-356176538088,240939115892⟩,⟨-25891974645,295464412819⟩,⟨-15200862519254,10868996151553⟩,⟨-10788721594155,7116004300902⟩,⟨-7757659427657,8771457605623⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121

noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨28668135162467,30127637652370⟩,⟨-290118142368746,-241348204143677⟩,⟨-110196234713705,-69758012048122⟩,⟨2863674217544383,4946453597707997⟩,⟨481587760969989,2441072707610687⟩,⟨-727582180738003,1407995038335983⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122

noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨12869855988,13490190452⟩,⟨168544076566,179220962586⟩,⟨39717706888,43346363512⟩,⟨486888251515,723718775231⟩,⟨78334273668,171746969818⟩,⟨10302221438,44644446863⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123

noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨335562409405,369643721387⟩,⟨835002878095,2085823862408⟩,⟨-316445588373,371208411134⟩,⟨-48364429401941,6527368642240⟩,⟨-21719987712143,15244740328456⟩,⟨-17346873215582,13458608363790⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124

noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-369643721387,-335562409405⟩,⟨-2085823862408,-835002878095⟩,⟨-371208411134,316445588373⟩,⟨-6527368642240,48364429401941⟩,⟨-15244740328456,21719987712143⟩,⟨-13458608363790,17346873215582⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125

noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨59499295859,110393000351⟩,⟨-1303834166791,314028742160⟩,⟨-583316448075,413419648073⟩,⟨-32297378222898,34496633840550⟩,⟨-26844974451045,22083589472939⟩,⟨-22009827064779,22937884671972⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126

noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨232087910938,234537552252⟩,⟨1578824173087,1587163591152⟩,⟨313473858794,315518682074⟩,⟨-3966343577600,-3952509420828⟩,⟨-1577200910340,-1569301190404⟩,⟨-351843720890,-351156861664⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127

noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1705139965673,-1616875890779⟩,⟨-5636690294229,-2637925416182⟩,⟨-607069242152,1553581868857⟩,⟨-22706748629898,106470286136919⟩,⟨-64193691635944,47303708933471⟩,⟨-55620239327874,59888178356979⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128

noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-188872687879,-174929725909⟩,⟨-1878970761061,-1430839878474⟩,⟨-370683687776,-97840513685⟩,⟨-7637619270757,12373208436339⟩,⟨-7770657605273,7214624869258⟩,⟨-6207062144050,7543463040069⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129

noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨43215223059,59607826343⟩,⟨-300146587974,156323712678⟩,⟨-57209828982,217678168389⟩,⟨-11603962848357,8420699015511⟩,⟨-9347858515613,5645323678854⟩,⟨-6558905864940,7192306178405⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130

noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2601099888,6445449293⟩,⟨-111886959285,42525738810⟩,⟨-36657346512,53803256099⟩,⟨-3983347967790,3950131227921⟩,⟨-3134882953261,2277187929711⟩,⟨-2377459263441,2442121949095⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131

noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1698531836,3231519224⟩,⟨-32543695296,16949555574⟩,⟨-6203033174,23601974064⟩,⟨-1343518363385,1076891819823⟩,⟨-1132395275994,673996933896⟩,⟨-733808433478,866023624771⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132

noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨3038566095,5829634977⟩,⟨-82937556427,18399838800⟩,⟨-22000891222,37128475055⟩,⟨-2621482094549,2571921971422⟩,⟨-2237502597446,1461079075928⟩,⟨-1470296501802,1631719774210⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133

noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5829634977,-3038566095⟩,⟨-18399838800,82937556427⟩,⟨-37128475055,22000891222⟩,⟨-2571921971422,2621482094549⟩,⟨-1461079075928,2237502597446⟩,⟨-1631719774210,1470296501802⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134

noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3228535089,3406883198⟩,⟨-130286798085,125463295237⟩,⟨-73785821567,75804147321⟩,⟨-6555269939212,6571613322470⟩,⟨-4595962029189,4514690527157⟩,⟨-4009179037651,3912418450897⟩⟩⟩


noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]

noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨48066780141,64196519900⟩,⟨-356176538088,240939115892⟩,⟨-25891974645,295464412819⟩,⟨-15200862519254,10868996151553⟩,⟨-10788721594155,7116004300902⟩,⟨-7757659427657,8771457605623⟩⟩

noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3228535089,3406883198⟩,⟨-130286798085,125463295237⟩,⟨-73785821567,75804147321⟩,⟨-6555269939212,6571613322470⟩,⟨-4595962029189,4514690527157⟩,⟨-4009179037651,3912418450897⟩⟩



attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (513/5120) u, BivariateJet2.affineZ (539/5120) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet


noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet























end GeneralCK.Certificates.LaneCB.RB2Cell000001


