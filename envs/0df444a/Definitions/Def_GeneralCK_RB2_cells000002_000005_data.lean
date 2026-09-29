-- Prove2me | Definitions.Def_GeneralCK_RB2_cells000002_000005_data
-- name    : GeneralCK_RB2_cells000002_000005_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-24T23:56:20.915511+00:00
-- url     : https://prove2.me/theorems/52f872d8-7e80-4c7d-9777-b69e79487012
-- title:
--   Exact certificate data for RB2 cells 000002–000005
-- statement:
--   This bundle preserves the exact numerical endpoints, logarithm enclosure proposals, center and whole-cell instruction lists, and real-valued coordinate definitions for RB2 cells 000002 through 000005. Each cell keeps its original disjoint namespace and its own complete source/type/body audit. Separate theorem proofs check the numerical proposals and establish positivity of the actual correction matrix minors on each cell's specified rectangle; the data bundle introduces no positivity assumption.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/releases/tag/v1.0

import Definitions.Def_GeneralCK_RB2_program_data

section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell000002Endpoints
open GeneralCK.Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

noncomputable def lift40 (a : DyadicInterval 40) : DyadicInterval 64 :=
  ⟨a.lo*16777216, a.hi*16777216⟩







noncomputable def sharedTwo : DyadicInterval 64 := ⟨12786308645202655420,12786308645202662926⟩

noncomputable def out_w0 : DyadicInterval 40 := ⟨-2525295488000,-2525295430144⟩



noncomputable def out_w1 : DyadicInterval 40 := ⟨-116561173120,-116561173056⟩



noncomputable def out_w2 : DyadicInterval 40 := ⟨-2152150546432,-2152150506944⟩



noncomputable def out_w3 : DyadicInterval 40 := ⟨-2152150546368,-2152150506944⟩



noncomputable def out_w4 : DyadicInterval 40 := ⟨-167404485440,-167404485376⟩



noncomputable def out_w5 : DyadicInterval 40 := ⟨-167404485440,-167404485376⟩



noncomputable def out_w6 : DyadicInterval 40 := ⟨762123383616,762123402880⟩



noncomputable def out_w7 : DyadicInterval 40 := ⟨81034764416,81034764480⟩



noncomputable def out_w8 : DyadicInterval 40 := ⟨-87485670144,-87485670080⟩



noncomputable def out_w9 : DyadicInterval 40 := ⟨81034888320,81034888384⟩



noncomputable def out_w10 : DyadicInterval 40 := ⟨-87485814592,-87485814528⟩



noncomputable def out_w11 : DyadicInterval 40 := ⟨-6450926208,-6450926144⟩



noncomputable def out_w12 : DyadicInterval 40 := ⟨-6450905728,-6450905664⟩



noncomputable def out_w13 : DyadicInterval 40 := ⟨168520434560,168520434624⟩



noncomputable def out_w14 : DyadicInterval 40 := ⟨168520702848,168520702912⟩



noncomputable def out_w15 : DyadicInterval 40 := ⟨2408734257088,2408734314944⟩



noncomputable def out_w16 : DyadicInterval 40 := ⟨2408734257088,2408734314944⟩



noncomputable def out_w17 : DyadicInterval 40 := ⟨1984746021568,1984746060160⟩



noncomputable def out_w18 : DyadicInterval 40 := ⟨1984746021568,1984746060224⟩



noncomputable def out_w19 : DyadicInterval 40 := ⟨-2527432537536,-2527432479680⟩



noncomputable def out_w20 : DyadicInterval 40 := ⟨-2523162584128,-2523162526272⟩



noncomputable def out_w21 : DyadicInterval 40 := ⟨-116799963776,-116799963712⟩



noncomputable def out_w22 : DyadicInterval 40 := ⟨-116322434304,-116322434240⟩



noncomputable def out_w23 : DyadicInterval 40 := ⟨-2159312452352,-2159312412736⟩



noncomputable def out_w24 : DyadicInterval 40 := ⟨-2145029678144,-2145029638848⟩



noncomputable def out_w25 : DyadicInterval 40 := ⟨-168579979008,-168579978944⟩



noncomputable def out_w26 : DyadicInterval 40 := ⟨-166231125504,-166231125440⟩



noncomputable def out_w27 : DyadicInterval 40 := ⟨78437057984,78437058048⟩



noncomputable def out_w28 : DyadicInterval 40 := ⟨-84465411392,-84465411328⟩



noncomputable def out_w29 : DyadicInterval 40 := ⟨83655969088,83655969152⟩



noncomputable def out_w30 : DyadicInterval 40 := ⟨-90548953600,-90548953536⟩



noncomputable def out_w31 : DyadicInterval 40 := ⟨-6892984512,-6892984448⟩



noncomputable def out_w32 : DyadicInterval 40 := ⟨-6028353344,-6028353280⟩



noncomputable def out_w33 : DyadicInterval 40 := ⟨162902469376,162902469440⟩



noncomputable def out_w34 : DyadicInterval 40 := ⟨174204922688,174204922752⟩



noncomputable def out_w35 : DyadicInterval 40 := ⟨2406362562496,2406362620352⟩



noncomputable def out_w36 : DyadicInterval 40 := ⟨2411110045440,2411110103296⟩



noncomputable def out_w37 : DyadicInterval 40 := ⟨1976449659904,1976449698496⟩



noncomputable def out_w38 : DyadicInterval 40 := ⟨1993081287360,1993081325952⟩



end LaneCBRB2Cell000002Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000002
open Set LaneCBRB2Cell000002Endpoints
open BivariateJetProgram (zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
















































noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨110595407872,110595407872⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨111883898060,111883898061⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0

noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1

noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-110595407872,-110595407872⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2

noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨439160406016,439160406016⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3

noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨44688002252,44688002253⟩,⟨-111883898061,-111883898060⟩,⟨439160406016,439160406016⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4

noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨155283410124,155283410125⟩,⟨987627729715,987627729716⟩,⟨439160406016,439160406016⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5

noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨44688002252,44688002253⟩,⟨-111883898061,-111883898060⟩,⟨439160406016,439160406016⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes7 := centerStep6.proposed :: centerBoxes6

noncomputable def centerStep7 : Instruction 40 := ⟨.log 7,⟨⟨-2525295488000,-2525295430144⟩,⟨10931067056724,10931067056725⟩,⟨0,0⟩,⟨-108673909379485,-108673909379464⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes8 := centerStep7.proposed :: centerBoxes7

noncomputable def centerStep8 : Instruction 40 := ⟨.mul 8 0,⟨⟨-254009214125,-254009208305⟩,⟨-1425783860225,-1425783802367⟩,⟨0,0⟩,⟨10931067056722,10931067056727⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes9 := centerStep8.proposed :: centerBoxes8

noncomputable def centerStep9 : Instruction 40 := ⟨.neg 0,⟨⟨254009208305,254009214125⟩,⟨1425783802367,1425783860225⟩,⟨0,0⟩,⟨-10931067056727,-10931067056722⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes10 := centerStep9.proposed :: centerBoxes9

noncomputable def centerStep10 : Instruction 40 := ⟨.add 12 7,⟨⟨988916219904,988916219904⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes11 := centerStep10.proposed :: centerBoxes10

noncomputable def centerStep11 : Instruction 40 := ⟨.log 0,⟨⟨-116561173120,-116561173056⟩,⟨-1222475468885,-1222475468884⟩,⟨0,0⟩,⟨-1359190966492,-1359190966489⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes12 := centerStep11.proposed :: centerBoxes11

noncomputable def centerStep12 : Instruction 40 := ⟨.mul 1 0,⟨⟨-104836758246,-104836758188⟩,⟨-982950454721,-982950454655⟩,⟨0,0⟩,⟨1222475468882,1222475468887⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes13 := centerStep12.proposed :: centerBoxes12

noncomputable def centerStep13 : Instruction 40 := ⟨.neg 0,⟨⟨104836758188,104836758246⟩,⟨982950454655,982950454721⟩,⟨0,0⟩,⟨-1222475468887,-1222475468882⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes14 := centerStep13.proposed :: centerBoxes13

noncomputable def centerStep14 : Instruction 40 := ⟨.add 4 0,⟨⟨358845966493,358845972371⟩,⟨2408734257022,2408734314946⟩,⟨0,0⟩,⟨-12153542525614,-12153542525604⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes15 := centerStep14.proposed :: centerBoxes14

noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2152150546432,-2152150506944⟩,⟨6993072678282,6993072678335⟩,⟨3109552865207,3109552865228⟩,⟨-44477078958586,-44477078957911⟩,⟨-27562548072033,-27562548071702⟩,⟨-8794194419942,-8794194419825⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15

noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-303947013847,-303947008267⟩,⟨-945524684950,-945524649463⟩,⟨-420438786849,-420438771070⟩,⟨6281472899789,6281472900035⟩,⟨3845770446910,3845770486515⟩,⟨1241999142433,1241999142477⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16

noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨303947008267,303947013847⟩,⟨945524649463,945524684950⟩,⟨420438771070,420438786849⟩,⟨-6281472900035,-6281472899789⟩,⟨-3845770486515,-3845770446910⟩,⟨-1241999142477,-1241999142433⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17

noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-155283410125,-155283410124⟩,⟨-987627729716,-987627729715⟩,⟨-439160406016,-439160406016⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18

noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨944228217651,944228217652⟩,⟨-987627729716,-987627729715⟩,⟨-439160406016,-439160406016⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19

noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-167404485440,-167404485376⟩,⟨-1150048423081,-1150048423077⟩,⟨-511382697369,-511382697367⟩,⟨-1202908038458,-1202908038450⟩,⟨745444876606,745444876611⟩,⟨-237844017801,-237844017798⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20

noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-143762043912,-143762043856⟩,⟨-837257958578,-837257958513⟩,⟨-372296700434,-372296700404⟩,⟨1033022011268,1033022011288⟩,⟨1391452655064,1391452655140⟩,⟨204253440645,204253440651⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21

noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨143762043856,143762043912⟩,⟨837257958513,837257958578⟩,⟨372296700404,372296700434⟩,⟨-1033022011288,-1033022011268⟩,⟨-1391452655140,-1391452655064⟩,⟨-204253440651,-204253440645⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22

noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨447709052123,447709057759⟩,⟨1782782607976,1782782643528⟩,⟨792735471474,792735487283⟩,⟨-7314494911323,-7314494911057⟩,⟨-5237223141655,-5237223101974⟩,⟨-1446252583128,-1446252583078⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23

noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨806555018616,806555030130⟩,⟨4191516864998,4191516958474⟩,⟨792735471474,792735487283⟩,⟨-19468037436937,-19468037436661⟩,⟨-5237223141655,-5237223101974⟩,⟨-1446252583128,-1446252583078⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24

noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨89376004504,89376004506⟩,⟨-223767796122,-223767796120⟩,⟨878320812032,878320812032⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25

noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨13526290711881,13526290712185⟩,⟨33865334202455,33865334204281⟩,⟨-132926311799672,-132926311793696⟩,⟨169575071994661,169575072009127⟩,⟨-332803284338263,-332803284272473⟩,⟨2612601598390133,2612601598566293⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26

noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨9922312216919,9922312358789⟩,⟨76406587047870,76406588554956⟩,⟨-87756793594852,-87756792003769⟩,⟨143095831188946,143095838756224⟩,⟨-790879316105513,-790879300270677⟩,⟨1707024865780673,1707024897100975⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27

noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨84095655936,84095789312⟩,⟨-642125710166,-642123635621⟩,⟨737511155898,737513537441⟩,⟨8562007624016,8562059727564⟩,⟨-4568603140042,-4568526347145⟩,⟨-1464810156836,-1464700314156⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28

noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29

noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1183607283712,1183607417088⟩,⟨-642125710166,-642123635621⟩,⟨737511155898,737513537441⟩,⟨8562007624016,8562059727564⟩,⟨-4568603140042,-4568526347145⟩,⟨-1464810156836,-1464700314156⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30

noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨81034764416,81034888384⟩,⟨-596502484006,-596500489640⟩,⟨685110687730,685112977268⟩,⟨7630061441831,7630112903627⟩,⟨-3872320339871,-3872246040089⟩,⟨-1787633385208,-1787528340309⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31

noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨87232672191,87232815472⟩,⟨-689450962121,-689448517563⟩,⟨791866153047,791868959483⟩,⟨9541391313700,9541457022924⟩,⟨-5305428781214,-5305336894577⟩,⟨-1113224526198,-1113096930116⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32

noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-84095789312,-84095655936⟩,⟨642123635621,642125710166⟩,⟨-737513537441,-737511155898⟩,⟨-8562059727564,-8562007624016⟩,⟨4568526347145,4568603140042⟩,⟨1464700314156,1464810156836⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33

noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1015415838464,1015415971840⟩,⟨642123635621,642125710166⟩,⟨-737513537441,-737511155898⟩,⟨-8562059727564,-8562007624016⟩,⟨4568526347145,4568603140042⟩,⟨1464700314156,1464810156836⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34

noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-87485814592,-87485670080⟩,⟨695303622766,695305960453⟩,⟨-798593718300,-798591034622⟩,⟨-9710857058062,-9710796464973⟩,⟨5451895747690,5451982945280⟩,⟨1005973216321,1006096262789⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35

noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-80794501124,-80794357052⟩,⟨591030966710,591033459408⟩,⟨-678831528520,-678828666800⟩,⟨-7474740962220,-7474673200253⟩,⟨3738621860618,3738715909120⟩,⟨1883809655916,1883939405451⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36

noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨6438171067,6438458420⟩,⟨-98419995411,-98415058155⟩,⟨113034624527,113040292683⟩,⟨2066650351480,2066783822671⟩,⟨-1566806920596,-1566620985457⟩,⟨770585129718,770842475335⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37

noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨3219085533,3219229210⟩,⟨-49209997706,-49207529077⟩,⟨56517312263,56520146342⟩,⟨1033325175740,1033391911336⟩,⟨-783403460298,-783310492728⟩,⟨385292564859,385421237668⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38

noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-3219229210,-3219085533⟩,⟨49207529077,49209997706⟩,⟨-56520146342,-56517312263⟩,⟨-1033391911336,-1033325175740⟩,⟨783310492728,783403460298⟩,⟨-385421237668,-385292564859⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39

noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨758904154406,758904317347⟩,⟨49207529077,49209997706⟩,⟨-56520146342,-56517312263⟩,⟨-1033391911336,-1033325175740⟩,⟨783310492728,783403460298⟩,⟨-385421237668,-385292564859⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40

noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨6432018696,6432039100⟩,⟨-98225552274,-98225079144⟩,⟨112816422942,112816966176⟩,⟨2059733398151,2059748291836⟩,⟨-1560286711724,-1560268291650⟩,⟨765318579837,765342127563⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41

noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-6432039100,-6432018696⟩,⟨98225079144,98225552274⟩,⟨-112816966176,-112816422942⟩,⟨-2059748291836,-2059733398151⟩,⟨1560268291650,1560286711724⟩,⟨-765342127563,-765318579837⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42

noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1093079588676,1093079609080⟩,⟨98225079144,98225552274⟩,⟨-112816966176,-112816422942⟩,⟨-2059748291836,-2059733398151⟩,⟨1560268291650,1560286711724⟩,⟨-765342127563,-765318579837⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43

noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-6450926208,-6450905664⟩,⟨98803065907,98803543666⟩,⟨-113480818237,-113480269687⟩,⟨-2080747141721,-2080732035854⟩,⟨1579646828324,1579665484690⟩,⟨-781558030145,-781534216252⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44

noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3225463104,-3225452832⟩,⟨49401532953,49401771833⟩,⟨-56740409119,-56740134843⟩,⟨-1040373570861,-1040366017927⟩,⟨789823414162,789832742345⟩,⟨-390779015073,-390767108126⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45

noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3225452832,3225463104⟩,⟨-49401771833,-49401532953⟩,⟨56740134843,56740409119⟩,⟨1040366017927,1040373570861⟩,⟨-789832742345,-789823414162⟩,⟨390767108126,390779015073⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46

noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765348836448,765348865984⟩,⟨-49401771833,-49401532953⟩,⟨56740134843,56740409119⟩,⟨1040366017927,1040373570861⟩,⟨-789832742345,-789823414162⟩,⟨390767108126,390779015073⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47

noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48

noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49

noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨273269897169,273269902270⟩,⟨24556269786,24556388069⟩,⟨-28204241544,-28204105735⟩,⟨-514937072959,-514933349537⟩,⟨390067072912,390071677931⟩,⟨-191335531891,-191329644959⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50

noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1530697672896,1530697731968⟩,⟨-98803543666,-98803065906⟩,⟨113480269686,113480818238⟩,⟨2080732035854,2080747141722⟩,⟨-1579665484690,-1579646828324⟩,⟨781534216252,781558030146⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51

noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1190571995262,1190572151646⟩,⟨-752890549292,-752887919106⟩,⟨864729483045,864732502567⟩,⟨10991141626233,10991211882756⟩,⟨-6450348090888,-6450249148257⟩,⟨-461354894038,-461217045148⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52

noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1281632362748,1281632675516⟩,⟨-1505781098584,-1505775838212⟩,⟨1729458966089,1729465005133⟩,⟨21982283252468,21982423765500⟩,⟨-12900696181770,-12900498296514⟩,⟨-922709635700,-922434242672⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53

noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨168520434560,168520702912⟩,⟨-1291808692494,-1291803864372⟩,⟨1483701437473,1483706980448⟩,⟨17340845687596,17340982180913⟩,⟨-9324315283513,-9324129789444⟩,⟨-2793741308464,-2793489896212⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54

noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨58044445411,58044549933⟩,⟨-439444042322,-439442320489⟩,⟨504721514346,504723491049⟩,⟨5773146074734,5773191605151⟩,⟨-3027414490010,-3027350079193⟩,⟨-1116342720205,-1116252752519⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55

noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380435809046,380435830830⟩,⟨9629902974,9630188163⟩,⟨-11060753365,-11060425918⟩,⟨-204148906535,-204139888636⟩,⟨155499067106,155510192053⟩,⟨-77951308977,-77937124685⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56

noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3177739112998,3177739294959⟩,⟨-80439923414,-80437532048⟩,⟨92386534594,92389280305⟩,⟨1709230485679,1709306248398⟩,⟨-1303637272225,-1303543920202⟩,⟨656372239608,656491113028⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57

noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨167756392761,167756704451⟩,⟨-1274300030104,-1274294847155⟩,⟨1463591454441,1463597404645⟩,⟨16839711619311,16839850489415⟩,⟨-8892314202556,-8892120008962⟩,⟨-3106914321248,-3106644926717⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58

noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨336276827321,336277407363⟩,⟨-2566108722598,-2566098711527⟩,⟨2947292891914,2947304385093⟩,⟨34180557306907,34180832670328⟩,⟨-18216629486069,-18216249798406⟩,⟨-5900655629712,-5900134822929⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59

noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨523810299978,523810524909⟩,⟨67927973294,67931395672⟩,⟨-78022609298,-78018680272⟩,⟨-1422129939069,-1422037066453⟩,⟨1076252794244,1076381869932⟩,⟨-526240245889,-526061924010⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60

noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨361543982557,361544215435⟩,⟨70327798038,70331356428⟩,⟨-80779084393,-80774999214⟩,⟨-1467812557768,-1467715628748⟩,⟨1109037690243,1109172092588⟩,⟨-538816387372,-538631043120⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61

noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨723087965114,723088430870⟩,⟨140655596076,140662712856⟩,⟨-161558168786,-161549998428⟩,⟨-2935625115536,-2935431257496⟩,⟨2218075380486,2218344185176⟩,⟨-1077632774744,-1077262086240⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62

noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524265633796,1524265713272⟩,⟨-578464522,-577513632⟩,⟨663303510,664395296⟩,⟨20983744018,21013743571⟩,⟨-19397193040,-19360116600⟩,⟨16192088689,16239450309⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63

noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨1002425174587,1002425872538⟩,⟨194612048558,194622550395⟩,⟨-223533743879,-223521687249⟩,⟨-4056039283250,-4055750334694⟩,⟨3062356685804,3062754172514⟩,⟨-1483481412429,-1482935960089⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64

noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67917823524,67917826061⟩,⟨12206308964,12206367988⟩,⟨-14019624962,-14019557190⟩,⟨-254865505154,-254863638987⟩,⟨192632787006,192635091804⟩,⟨-93661165959,-93658223997⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65

noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨49821629924,49821632497⟩,⟨267867801528,267867860401⟩,⟨38683782639,38683835308⟩,⟨-1296451897194,-1296450028550⟩,⟨-226845250798,-226843241259⟩,⟨-178258164275,-178255903724⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66

noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2130978251270,2130978415746⟩,⟨-275100974614,-275099633758⟩,⟨315965707572,315967247114⟩,⟨5811186803900,5811229258825⟩,⟨-4418693937012,-4418641624718⟩,⟨2199468104142,2199534720157⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67

noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2966665715767,2966666059234⟩,⟨-574477468814,-574474646611⟩,⟨659812903853,659816144253⟩,⟨12172246176403,12172335660927⟩,⟨-9269893059367,-9269783049076⟩,⟨4641938061002,4642077823431⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68

noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨134427065312,134427087819⟩,⟨696720979086,696721350840⟩,⟨134273073877,134273376447⟩,⟨-3226402256889,-3226391290097⟩,⟨-891573719264,-891562268209⟩,⟨-224204457138,-224191667033⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69

noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8993171236755,8993172742474⟩,⟨-46610669115864,-46610628637557⟩,⟨-8982890955036,-8982867705109⟩,⟨699001194725552,699002758966320⟩,⟨152759962626654,152761054952825⟩,⟨32943572916158,32944523485444⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70

noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨8199077680815,8199084762291⟩,⟨-40903215613646,-40903062958322⟩,⟨-10018047647456,-10017921828097⟩,⟨587603388464103,587608531952712⟩,⟨172204584922471,172209542350376⟩,⟨21553199732203,21558757152976⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71

noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨16398155361630,16398169524582⟩,⟨-81806431227292,-81806125916644⟩,⟨-20036095294912,-20035843656194⟩,⟨1175206776928206,1175217063905424⟩,⟨344409169844942,344419084700752⟩,⟨43106399464406,43117514305952⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72

noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10931067056724,10931067056725⟩,⟨-108673909379485,-108673909379464⟩,⟨0,0⟩,⟨2160817149603222,2160817149603840⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73

noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9831555428948,9831555428949⟩,⟨-108673909379485,-108673909379464⟩,⟨0,0⟩,⟨2160817149603232,2160817149603830⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74

noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2408734257088,2408734314944⟩,⟨-12153542525660,-12153542525558⟩,⟨0,0⟩,⟨107314718406763,107314718418708⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75

noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7785286391131,7785286391182⟩,⟨-49515686946678,-49515686945978⟩,⟨-22017738596625,-22017738596335⟩,⟨629855635503714,629855635517379⟩,⟨335197889056059,335197889062575⟩,⟨124537695478695,124537695481145⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76

noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6685774763355,6685774763406⟩,⟨-49515686946678,-49515686945978⟩,⟨-22017738596625,-22017738596334⟩,⟨629855635503716,629855635517374⟩,⟨335197889056060,335197889062574⟩,⟨124537695478695,124537695481146⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77

noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1984746021568,1984746060224⟩,⟨-8143121101504,-8143121101253⟩,⟨-3620935562636,-3620935562528⟩,⟨43274170915027,43274170924799⟩,⟨28307992946247,28307992950792⟩,⟨8556350401168,8556350403052⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78

noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨99471065088,99471065088⟩,⟨878320812032,878320812032⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79

noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨133352821260,133352821262⟩,⟨708663509727,708663509732⟩,⟨315115650662,315115650664⟩,⟨-1774257784753,-1774257784749⟩,⟨-1577889615056,-1577889615052⟩,⟨-350813683712,-350813683712⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80

noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4393480278656,4393480375168⟩,⟨-20296663627164,-20296663626811⟩,⟨-3620935562636,-3620935562528⟩,⟨150588889321790,150588889343507⟩,⟨28307992946247,28307992950792⟩,⟨8556350401168,8556350403052⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81

noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨672553654642,672554814726⟩,⟨-5132217445196,-5132197423054⟩,⟨5894585783828,5894608770186⟩,⟨68361114613814,68361665340656⟩,⟨-36433258972138,-36432499596812⟩,⟨-11801311259424,-11800269645858⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82

noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5066033933298,5066035189894⟩,⟨-25428881072360,-25428861049865⟩,⟨2273650221192,2273673207658⟩,⟨218950003935604,218950554684163⟩,⟨-8125266025891,-8124506646020⟩,⟨-3244960858256,-3243919242806⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83

noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨458316018118,458316131801⟩,⟨1746380033920,1746382849130⟩,⟨205693512852,205695592402⟩,⟨-30950623157521,-30950538829918⟩,⟨1081175871908,1081262934033⟩,⟨-293566438577,-293472205286⟩⟩⟩
noncomputable def centerBoxes85 := centerStep84.proposed :: centerBoxes84

noncomputable def centerStep85 : Instruction 40 := ⟨.mul 88 85,⟨⟨221190815744,221190815744⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes86 := centerStep85.proposed :: centerBoxes85

noncomputable def centerStep86 : Instruction 40 := ⟨.neg 0,⟨⟨-221190815744,-221190815744⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes87 := centerStep86.proposed :: centerBoxes86

noncomputable def centerStep87 : Instruction 40 := ⟨.add 89 0,⟨⟨878320812032,878320812032⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes88 := centerStep87.proposed :: centerBoxes87

noncomputable def centerStep88 : Instruction 40 := ⟨.mul 12 0,⟨⟨1924164670212,1924164716430⟩,⟨-14526060217769,-14526060101975⟩,⟨0,0⟩,⟨134340185392009,134340185401960⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes89 := centerStep88.proposed :: centerBoxes88

noncomputable def centerStep89 : Instruction 40 := ⟨.neg 91,⟨⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes90 := centerStep89.proposed :: centerBoxes89

noncomputable def centerStep90 : Instruction 40 := ⟨.add 1 0,⟨⟨824653042436,824653088654⟩,⟨-14526060217769,-14526060101975⟩,⟨0,0⟩,⟨134340185392009,134340185401960⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes91 := centerStep90.proposed :: centerBoxes90

noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨33516786986,33516788866⟩,⟨-674304841456,-674304832031⟩,⟨329378021832,329378040293⟩,⟨8416335697490,8416335721611⟩,⟨-6626565812353,-6626565719884⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91

noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨491832805104,491832920667⟩,⟨1072075192464,1072078017099⟩,⟨535071534684,535073632695⟩,⟨-22534287460031,-22534203108307⟩,⟨-5545389940445,-5545302785851⟩,⟨-293566438577,-293472205286⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92

noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨501892554988,501892567044⟩,⟨2532355881864,2532356003553⟩,⟨0,0⟩,⟨3194096148032,3194099067279⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93

noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨224506241630,224506299774⟩,⟨1622140420643,1622142042352⟩,⟨244243364835,244244328379⟩,⟨-3919083858538,-3919030217485⟩,⟨-1298938918258,-1298894182832⟩,⟨-134003870204,-133960852443⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94

noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-672554814726,-672553654642⟩,⟨5132197423054,5132217445196⟩,⟨-5894608770186,-5894585783828⟩,⟨-68361665340656,-68361114613814⟩,⟨36432499596812,36433258972138⟩,⟨11800269645858,11801311259424⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95

noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3720925463930,3720926720526⟩,⟨-15164466204110,-15164446181615⟩,⟨-9515544332822,-9515521346356⟩,⟨82227223981134,82227774729693⟩,⟨64740492543059,64741251922930⟩,⟨20356620047026,20357661662476⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96

noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨451287549652,451287702064⟩,⟨559029783699,559033022056⟩,⟨-87677866755,-87674718710⟩,⟨-15579333726203,-15579239091317⟩,⟨-7966958927785,-7966844470137⟩,⟨-4172519022888,-4172379115261⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97

noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨310566820248,310566820250⟩,⟨1975255459430,1975255459432⟩,⟨878320812032,878320812032⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98

noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-310566820250,-310566820248⟩,⟨-1975255459432,-1975255459430⟩,⟨-878320812032,-878320812032⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99

noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨788944807526,788944807528⟩,⟨-1975255459432,-1975255459430⟩,⟨-878320812032,-878320812032⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100

noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1424136888066,1424136915808⟩,⟨-9408589540861,-9408589471215⟩,⟨-4183641141780,-4183641110815⟩,⟨60308976815123,60308976823148⟩,⟨37291549397623,37291549478652⟩,⟨11924543603131,11924543604672⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101

noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1424136915808,-1424136888066⟩,⟨9408589471215,9408589540861⟩,⟨4183641110815,4183641141780⟩,⟨-60308976823148,-60308976815123⟩,⟨-37291549478652,-37291549397623⟩,⟨-11924543604672,-11924543603131⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102

noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-324625288032,-324625260290⟩,⟨9408589471215,9408589540861⟩,⟨4183641110815,4183641141780⟩,⟨-60308976823148,-60308976815123⟩,⟨-37291549478652,-37291549397623⟩,⟨-11924543604672,-11924543603131⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103

noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-13193908311,-13193907182⟩,⟨415431174594,415431180259⟩,⟨40377917762,40377930108⟩,⟨-4365962957604,-4365962943030⟩,⟨2141170893467,2141170955512⟩,⟨2857354980942,2857355005752⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104

noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨438093641341,438093794882⟩,⟨974460958293,974464202315⟩,⟨-47299948993,-47296788602⟩,⟨-19945296683807,-19945202034347⟩,⟨-5825788034318,-5825673514625⟩,⟨-1315164041946,-1315024109509⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105

noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-99471065088,-99471065088⟩,⟨-878320812032,-878320812032⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106

noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4042852361,4042852362⟩,⟨25576075057,25576075060⟩,⟨39730142208,39730142208⟩,⟨-268128013518,-268128013513⟩,⟨251342618624,251342618624⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107

noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨8856802176,8856802392⟩,⟨11342299371,11342300736⟩,⟨87038055949,87038058040⟩,⟨-758219735909,-758219721574⟩,⟨111463671483,111463684713⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108

noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1498875804444,1498875825842⟩,⟨-7789379890598,-7789379494475⟩,⟨-1473194054654,-1473193983211⟩,⟨117138692069746,117138700181759⟩,⟨25044517841322,25044519495588⟩,⟨5583573456690,5583573773060⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109

noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨12073766344,12073766811⟩,⟨-47283083727,-47283076922⟩,⟨106785089428,106785094839⟩,⟨-250749497851,-250749347681⟩,⟨-278121086606,-278120999414⟩,⟨-188261122936,-188261102375⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110

noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-12073766811,-12073766344⟩,⟨47283076922,47283083727⟩,⟨-106785094839,-106785089428⟩,⟨250749347681,250749497851⟩,⟨278120999414,278121086606⟩,⟨188261102375,188261122936⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111

noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-111544831899,-111544831432⟩,⟨-831037735110,-831037728305⟩,⟨-106785094839,-106785089428⟩,⟨2449772603233,2449772753403⟩,⟨278120999414,278121086606⟩,⟨188261102375,188261122936⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112

noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨80667027470,80667029044⟩,⟨-532928370385,-532928366431⟩,⟨645567972323,645567987771⟩,⟨3416066201379,3416066201884⟩,⟨-3718228711190,-3718228672205⟩,⟨-2544745127757,-2544745127584⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113

noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨109966873143,109966876859⟩,⟨-1297975891380,-1297975835405⟩,⟨771968212797,771968253772⟩,⟨20801827891426,20801829161456⟩,⟨-7090751533293,-7090750868617⟩,⟨-4789345006824,-4789344800566⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114

noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-109966876859,-109966873143⟩,⟨1297975835405,1297975891380⟩,⟨-771968253772,-771968212797⟩,⟨-20801829161456,-20801827891426⟩,⟨7090750868617,7090751533293⟩,⟨4789344800566,4789345006824⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115

noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨989544750917,989544754633⟩,⟨1297975835405,1297975891380⟩,⟨-771968253772,-771968212797⟩,⟨-20801829161456,-20801827891426⟩,⟨7090750868617,7090751533293⟩,⟨4789344800566,4789345006824⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116

noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨120015633272,120015633725⟩,⟨795210322207,795210331400⟩,⟨189972427941,189972433981⟩,⟨-2446571550757,-2446571318515⟩,⟨-685644400611,-685644272186⟩,⟨-177343969506,-177343919804⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117

noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11316159924,11316160020⟩,⟨168616613004,168616615092⟩,⟨21666573592,21666574782⟩,⟨759181086134,759181139262⟩,⟨104991101182,104991128614⟩,⟨-17455931788,-17455925353⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118

noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨168769609927,168769757125⟩,⟨1672803364415,1672808716926⟩,⟨116924802006,116927690458⟩,⟨-1673333666152,-1673123165540⟩,⟨425794410970,425942979358⟩,⟨-606336045782,-606211366609⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119

noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-168769757125,-168769609927⟩,⟨-1672808716926,-1672803364415⟩,⟨-116927690458,-116924802006⟩,⟨1673123165540,1673333666152⟩,⟨-425942979358,-425794410970⟩,⟨606211366609,606336045782⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120

noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨55736484505,55736689847⟩,⟨-50668296283,-50661322063⟩,⟨127315674377,127319526373⟩,⟨-2245960692998,-2245696551333⟩,⟨-1724881897616,-1724688593802⟩,⟨472207496405,472375193339⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121

noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨29600572465869,29600598608158⟩,⟨-269117001481407,-269116342587825⟩,⟨-90170284595427,-90169783010582⟩,⟨3978509933554521,3978533624000460⟩,⟨1461678591815278,1461699735231846⟩,⟨337386714534591,337408547280379⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122

noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13100136338,13100136438⟩,⟨173600111164,173600113828⟩,⟨41472342206,41472343682⟩,⟨616151049010,616151128324⟩,⟨125110070044,125110110564⟩,⟨26931001211,26931016384⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123

noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨352676156567,352676470733⟩,⟨1467190698713,1467202772865⟩,⟨42166029692,42173039824⟩,⟨-20991172143707,-20990663369531⟩,⟨-3604296504013,-3603935765335⟩,⟨-2057423492564,-2057124206200⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124

noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-352676470733,-352676156567⟩,⟨-1467202772865,-1467190698713⟩,⟨-42173039824,-42166029692⟩,⟨20990663369531,20991172143707⟩,⟨3603935765335,3604296504013⟩,⟨2057124206200,2057423492564⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125

noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨85417170608,85417638315⟩,⟨-492741814572,-492726496398⟩,⟨-89472988817,-89462818294⟩,⟨1045366685724,1045970109360⟩,⟨-2221852268983,-2221377010612⟩,⟨741960164254,742399383055⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126

noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨232823886348,232823886350⟩,⟨1586984321759,1586984321764⟩,⟨315115650662,315115650664⟩,⟨-3973281040305,-3973281040301⟩,⟨-1577889615056,-1577889615052⟩,⟨-350813683712,-350813683712⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127

noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1663585010712,-1663583566922⟩,⟨-4094951815371,-4094910000836⟩,⟨440026920258,440053913589⟩,⟨40973023712206,40974564149954⟩,⟨-7704585259077,-7703354000189⟩,⟨2325266571752,2326445991855⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128

noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-181586264549,-181586106268⟩,⟨-1650149192643,-1650143568633⟩,⟨-239401910338,-239398705141⟩,⟨2250802252398,2251034529936⟩,⟨-192865766493,-192703498863⟩,⟨674190901567,674329281124⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129

noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨51237621799,51237780082⟩,⟨-63164870884,-63159246869⟩,⟨75713740324,75716945523⟩,⟨-1722478787907,-1722246510365⟩,⟨-1770755381549,-1770593113915⟩,⟨323377217855,323515597412⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130

noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4329970403,4330010065⟩,⟨-28914440827,-28913008938⟩,⟨5355119766,5356005449⟩,⟨-76083999937,-76024077661⟩,⟨-299566980790,-299522187068⟩,⟨53574296872,53612911403⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131

noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2387690881,2387705634⟩,⟨-5887027808,-5886485458⟩,⟨7056572924,7056893452⟩,⟨-153280596107,-153257159451⟩,⟨-173735726834,-173718950730⟩,⟨40566465141,40580338234⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132

noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4310058990,4310085706⟩,⟨-28310415821,-28309327343⟩,⟨4874688595,4875316020⟩,⟨-95523308179,-95472382813⟩,⟨-285018464806,-284983636090⟩,⟨45328249324,45355519249⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133

noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4310085706,-4310058990⟩,⟨28309327343,28310415821⟩,⟨-4875316020,-4874688595⟩,⟨95472382813,95523308179⟩,⟨284983636090,285018464806⟩,⟨-45355519249,-45328249324⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134

noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨19884697,19951075⟩,⟨-605113484,-602593117⟩,⟨479803746,481316854⟩,⟨19388382876,19499230518⟩,⟨-14583344700,-14503722262⟩,⟨8218777623,8284662079⟩⟩⟩


noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]

noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨55736484505,55736689847⟩,⟨-50668296283,-50661322063⟩,⟨127315674377,127319526373⟩,⟨-2245960692998,-2245696551333⟩,⟨-1724881897616,-1724688593802⟩,⟨472207496405,472375193339⟩⟩

noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨19884697,19951075⟩,⟨-605113484,-602593117⟩,⟨479803746,481316854⟩,⟨19388382876,19499230518⟩,⟨-14583344700,-14503722262⟩,⟨8218777623,8284662079⟩⟩

noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨110380659507,110810156237⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨109951162777,113816633344⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0

noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1

noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-110810156237,-110380659507⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2

noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨438945657651,439375154381⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3

noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨43894565764,45482193716⟩,⟨-113816633344,-109951162777⟩,⟨438945657651,439375154381⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4

noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨154275225271,156292349953⟩,⟨985694994432,989560464999⟩,⟨438945657651,439375154381⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5

noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨43465069034,45911690446⟩,⟨-113816633344,-109951162777⟩,⟨438945657651,439375154381⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes7 := wholeStep6.proposed :: wholeBoxes6

noncomputable def wholeStep7 : Instruction 40 := ⟨.log 7,⟨⟨-2527432537536,-2523162526272⟩,⟨10909882818222,10952333724170⟩,⟨0,0⟩,⟨-109097176396601,-108253100831767⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes8 := wholeStep7.proposed :: wholeBoxes7

noncomputable def wholeStep8 : Instruction 40 := ⟨.mul 8 0,⟨⟨-254717810425,-253301862988⟩,⟨-1432182582740,-1419372643130⟩,⟨0,0⟩,⟨10824815827704,11037070997671⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes9 := wholeStep8.proposed :: wholeBoxes8

noncomputable def wholeStep9 : Instruction 40 := ⟨.neg 0,⟨⟨253301862988,254717810425⟩,⟨1419372643130,1432182582740⟩,⟨0,0⟩,⟨-11037070997671,-10824815827704⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes10 := wholeStep9.proposed :: wholeBoxes9

noncomputable def wholeStep10 : Instruction 40 := ⟨.add 12 7,⟨⟨988701471539,989130968269⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes11 := wholeStep10.proposed :: wholeBoxes10

noncomputable def wholeStep11 : Instruction 40 := ⟨.log 0,⟨⟨-116799963776,-116322434240⟩,⟨-1222740993531,-1222210059533⟩,⟨0,0⟩,⟨-1359781469784,-1358600847764⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes12 := wholeStep11.proposed :: wholeBoxes11

noncomputable def wholeStep12 : Instruction 40 := ⟨.mul 1 0,⟨⟨-105074342413,-104599313914⟩,⟨-983666826738,-982234238194⟩,⟨0,0⟩,⟨1221147960896,1223802630987⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes13 := wholeStep12.proposed :: wholeBoxes12

noncomputable def wholeStep13 : Instruction 40 := ⟨.neg 0,⟨⟨104599313914,105074342413⟩,⟨982234238194,983666826738⟩,⟨0,0⟩,⟨-1223802630987,-1221147960896⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes14 := wholeStep13.proposed :: wholeBoxes13

noncomputable def wholeStep14 : Instruction 40 := ⟨.add 4 0,⟨⟨357901176902,359792152838⟩,⟨2401606881324,2415849409478⟩,⟨0,0⟩,⟨-12260873628658,-12045963788600⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes15 := wholeStep14.proposed :: wholeBoxes14

noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2159312452352,-2145029638848⟩,⟨6934332410668,7052546743929⟩,⟨3087968507058,3131404218333⟩,⟨-45236825440317,-43733021795233⟩,⟨-27921784761235,-27210038887154⟩,⟨-8918225265544,-8672531749276⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15

noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-306939925814,-300974471198⟩,⟨-970407690755,-920486740286⟩,⟨-429600918373,-411216134642⟩,⟨6002759383922,6558294518489⟩,⟨3712660941676,3977931464035⟩,⟨1197850315392,1285812354063⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16

noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨300974471198,306939925814⟩,⟨920486740286,970407690755⟩,⟨411216134642,429600918373⟩,⟨-6558294518489,-6002759383922⟩,⟨-3977931464035,-3712660941676⟩,⟨-1285812354063,-1197850315392⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17

noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-156292349953,-154275225271⟩,⟨-989560464999,-985694994432⟩,⟨-439375154381,-438945657651⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18

noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨943219277823,945236402505⟩,⟨-989560464999,-985694994432⟩,⟨-439375154381,-438945657651⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19

noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-168579979008,-166231125440⟩,⟨-1153531594653,-1146573603117⟩,⟨-512180043980,-510587460734⟩,⟨-1210205609698,-1195649954175⟩,⟨741622736528,749259831458⟩,⟨-238586287607,-237104864080⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20

noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-144926100704,-142601858978⟩,⟨-842653086185,-831869550425⟩,⟨-373952199451,-370642812119⟩,⟨1015372004874,1050665047011⟩,⟨1383090624008,1399822265084⟩,⟨202562526551,205942790784⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21

noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨142601858978,144926100704⟩,⟨831869550425,842653086185⟩,⟨370642812119,373952199451⟩,⟨-1050665047011,-1015372004874⟩,⟨-1399822265084,-1383090624008⟩,⟨-205942790784,-202562526551⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22

noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨443576330176,451866026518⟩,⟨1752356290711,1813060776940⟩,⟨781858946761,803553117824⟩,⟨-7608959565500,-7018131388796⟩,⟨-5377753729119,-5095751565684⟩,⟨-1491755144847,-1400412841943⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23

noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨801477507078,811658179356⟩,⟨4153963172035,4228910186418⟩,⟨781858946761,803553117824⟩,⟨-19869833194158,-19064095177396⟩,⟨-5377753729119,-5095751565684⟩,⟨-1491755144847,-1400412841943⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24

noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨86930138068,91823380892⟩,⟨-227633266688,-219902325554⟩,⟨877891315302,878750308762⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25

noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨13165773334315,13906866438760⟩,⟨31529923487980,36416201644272⟩,⟨-140580280309839,-125873366425303⟩,⟨151018257707177,190717261582405⟩,⟨-420941363604842,-251098950846836⟩,⟨2406862699655176,2842166536799627⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26

noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨9597052840709,10266032308420⟩,⟨72723798473463,80370588939039⟩,⟨-94414059910541,-81590556914342⟩,⟨97005706530685,192635854133698⟩,⟨-897032469122269,-692990076765101⟩,⟨1530109540676538,1902298902893337⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27

noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨81302565888,86920708352⟩,⟨-721779123016,-571084515715⟩,⟨640713283140,847898444720⟩,⟨6248469338806,11186684153071⟩,⟨-8594345525121,-895302743510⟩,⟨-7041263578899,4473233836460⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28

noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29

noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1180814193664,1186432336128⟩,⟨-721779123016,-571084515715⟩,⟨640713283140,847898444720⟩,⟨6248469338806,11186684153071⟩,⟨-8594345525121,-895302743510⟩,⟨-7041263578899,4473233836460⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30

noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨78437057984,83655969152⟩,⟨-672082485713,-529245576296⟩,⟨593773183207,789518117369⟩,⟨5379878295830,10161697442836⟩,⟨-7716788923711,-347113585670⟩,⟨-7123375047632,3844580946677⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31

noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨84237027637,90269301757⟩,⟨-780129562960,-609120322857⟩,⟨683386558637,916444687884⟩,⟨6773221785811,12698537425257⟩,⟨-10017294337574,-1053459439872⟩,⟨-7530224589864,5706542864049⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32

noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-86920708352,-81302565888⟩,⟨571084515715,721779123016⟩,⟨-847898444720,-640713283140⟩,⟨-11186684153071,-6248469338806⟩,⟨895302743510,8594345525121⟩,⟨-4473233836460,7041263578899⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33

noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1012590919424,1018209061888⟩,⟨571084515715,721779123016⟩,⟨-847898444720,-640713283140⟩,⟨-11186684153071,-6248469338806⟩,⟨895302743510,8594345525121⟩,⟨-4473233836460,7041263578899⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34

noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-90548953600,-84465411328⟩,⟨616684813536,783736574385⟩,⟨-920681966686,-691873340408⟩,⟨-12705598828813,-7093281834000⟩,⟨1354843499284,9988349358539⟩,⟨-5628153793665,7210320121886⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35

noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-83853378874,-77788089143⟩,⟨508492210441,681912564369⟩,⟨-803382691260,-567350384662⟩,⟨-10645469988200,-4582289725510⟩,⟨-668810402700,8462274684090⟩,⟨-4985514683177,8465530796082⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36

noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨383648763,12481212614⟩,⟨-271637352519,72792241512⟩,⟨-119996132623,349094303222⟩,⟨-3872248202389,8116247699747⟩,⟨-10686104740274,7408815244218⟩,⟨-12515739273041,14172073660131⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37

noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨191824381,6240606307⟩,⟨-135818676260,36396120756⟩,⟨-59998066312,174547151611⟩,⟨-1936124101195,4058123849874⟩,⟨-5343052370137,3704407622109⟩,⟨-6257869636521,7086036830066⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38

noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-6240606307,-191824381⟩,⟨-36396120756,135818676260⟩,⟨-174547151611,59998066312⟩,⟨-4058123849874,1936124101195⟩,⟨-3704407622109,5343052370137⟩,⟨-7086036830066,6257869636521⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39

noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨755882777309,761931578499⟩,⟨-36396120756,135818676260⟩,⟨-174547151611,59998066312⟩,⟨-4058123849874,1936124101195⟩,⟨-3704407622109,5343052370137⟩,⟨-7086036830066,6257869636521⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40

noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨6011857494,6871423048⟩,⟨-114118943468,-84456835732⟩,⟨94754130108,134059397944⟩,⟨1517317494665,2716332552369⟩,⟨-2472046611188,-797975818036⟩,⟨-366559300856,2014982649141⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41

noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-6871423048,-6011857494⟩,⟨84456835732,114118943468⟩,⟨-134059397944,-94754130108⟩,⟨-2716332552369,-1517317494665⟩,⟨797975818036,2472046611188⟩,⟨-2014982649141,366559300856⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42

noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1092640204728,1093499770282⟩,⟨84456835732,114118943468⟩,⟨-134059397944,-94754130108⟩,⟨-2716332552369,-1517317494665⟩,⟨797975818036,2472046611188⟩,⟨-2014982649141,366559300856⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43

noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-6892984512,-6028353280⟩,⟨84921163640,114836617535⟩,⟨-134902474039,-95275070617⟩,⟨-2745409007213,-1532218338506⟩,⟨809721543309,2501682538670⟩,⟨-2044206123193,360608736356⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44

noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3446492256,-3014176640⟩,⟨42460581820,57418308768⟩,⟨-67451237020,-47637535308⟩,⟨-1372704503607,-766109169253⟩,⟨404860771654,1250841269335⟩,⟨-1022103061597,180304368178⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45

noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3014176640,3446492256⟩,⟨-57418308768,-42460581820⟩,⟨47637535308,67451237020⟩,⟨766109169253,1372704503607⟩,⟨-1250841269335,-404860771654⟩,⟨-180304368178,1022103061597⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46

noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765137560256,765569895136⟩,⟨-57418308768,-42460581820⟩,⟨47637535308,67451237020⟩,⟨766109169253,1372704503607⟩,⟨-1250841269335,-404860771654⟩,⟨-180304368178,1022103061597⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47

noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48

noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49

noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨273160051182,273374942571⟩,⟨21114208933,28529735867⟩,⟨-33514849486,-23688532527⟩,⟨-679083138093,-379329373666⟩,⟨199493954509,618011652797⟩,⟨-503745662286,91639825214⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50

noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1530275120512,1531139790272⟩,⟨-114836617536,-84921163640⟩,⟨95275070616,134902474040⟩,⟨1532218338506,2745409007214⟩,⟨-2501682538670,-809721543308⟩,⟨-360608736356,2044206123194⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51

noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1187306089550,1193893601478⟩,⟨-851012447495,-665926231198⟩,⟨747118456514,999713219265⟩,⟨8033169533623,14402851525145⟩,⟨-11558348162292,-1882063355089⟩,⟨-7361733593924,6948389214109⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52

noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1275100551324,1288275575180⟩,⟨-1702024894990,-1331852462396⟩,⟨1494236913028,1999426438530⟩,⟨16066339067248,28805703050283⟩,⟨-23116696324579,-3764126710178⟩,⟨-14718662787914,13896778428215⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53

noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨162902469376,174204922752⟩,⟨-1467645952207,-1136703432944⟩,⟨1275294581514,1724093535813⟩,⟨11753188989120,23663833275773⟩,⟨-18614957486579,-911241876087⟩,⟨-15395287107565,10503928852960⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54

noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨55893187259,60233680887⟩,⟨-503050508201,-381867261484⟩,⟨426673408454,592313585746⟩,⟨3796515728075,7952910085346⟩,⟨-6315948260207,26214281078⟩,⟨-5708789950167,3687074344103⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55

noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380177907792,380691974200⟩,⟨834092947,18631857881⟩,⟨-23001645284,572057731⟩,⟨-570965212867,151395979899⟩,⟨-340690684944,666455997037⟩,⟨-799381170984,631766180116⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56

noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3175601014849,3179894977686⟩,⟨-155841120924,-6957715393⟩,⟨-4784821708,192391022251⟩,⟨-1266280115616,4790958639977⟩,⟨-5593247894245,2850083805573⟩,⟨-5284815818036,6709487160324⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57

noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨161430272949,174201686005⟩,⟨-1463408506332,-1103259775841⟩,⟨1232052728910,1723568326242⟩,⟨10900530773153,23405653175727⟩,⟨-18744725162288,231437328732⟩,⟨-16805047044308,11238223969676⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58

noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨324332742325,348406608757⟩,⟨-2931054458539,-2239963208785⟩,⟨2507347310424,3447661862055⟩,⟨22653719762273,47069486451500⟩,⟨-37359682648867,-679804547355⟩,⟨-32200334151873,21742152822636⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59

noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨519647776884,527997808890⟩,⟨-50443038598,188237278768⟩,⟨-241912833644,83154048066⟩,⟨-5633330117457,2716916797754⟩,⟨-5177229304528,7420001901350⟩,⟨-9839909978496,8728484678308⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60

noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨357242974872,365888085045⟩,⟨-52433475535,195664952496⟩,⟨-251458496493,86435232018⟩,⟨-5864962825397,2859002291721⟩,⟨-5426342036693,7728196079232⟩,⟨-10247984998081,9130508221781⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61

noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨714485949744,731776170090⟩,⟨-104866951070,391329904992⟩,⟨-502916992986,172870464036⟩,⟨-11729925650794,5718004583442⟩,⟨-10852684073386,15456392158464⟩,⟨-20495969996162,18261016443562⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62

noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523403697464,1525127932778⟩,⟨-30379781804,29197779828⟩,⟨-38784327328,40148343932⟩,⟨-1184114213863,1228091512549⟩,⟨-1703706720634,1662325067880⟩,⟨-2375591385497,2410765424050⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63

noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨989939997112,1015043633330⟩,⟨-165679663660,562244539226⟩,⟨-723406811070,266508481957⟩,⟨-17080238520120,8769555772548⟩,⟨-16214767248750,22574035982501⟩,⟨-30047667755856,26969735283767⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64

noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67863232799,67970049009⟩,⟨10491127600,14186871166⟩,⟨-16665799292,-11770245250⟩,⟨-336874116436,-186998814198⟩,⟨97384343498,306406464856⟩,⟨-249474933162,47612551665⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65

noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨49468194125,50175409551⟩,⟨264035200031,271897190621⟩,⟨35954638778,41094570388⟩,⟨-1397730241170,-1203840351608⟩,⟨-318096144920,-122427192869⟩,⟨-300739657465,-68027264948⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66

noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2129801891404,2132209426559⟩,⟨-319834570274,-236382664158⟩,⟨265203325704,375720530082⟩,⟨4278130666792,7670300729377⟩,⟨-6995683036444,-2268621032504⟩,⟨-987829563882,5726476978893⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67

noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2964209530577,2969237079195⟩,⟨-668084935820,-493487973309⟩,⟨553655879051,784822059764⟩,⟨8958692177560,16072178419097⟩,⟨-14671761799100,-4766846858181⟩,⟨-2028958958416,12030871934509⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68

noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨133362930215,135498964031⟩,⟨681333604979,712057282053⟩,⟨121840857389,146790890015⟩,⟨-3701937175121,-2749041687334⟩,⟨-1420571195920,-366580412702⟩,⟨-868529418363,424289019272⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69

noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8922029982000,9064931444336⟩,⟨-48399884704433,-44862917549505⟩,⟨-9977655353658,-8022701800202⟩,⟨632183866913676,768465324263150⟩,⟨104819355726571,203105201452325⟩,⟨-14411680506303,81000150766697⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70

noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨8032906711936,8368534462667⟩,⟨-46047598167152,-35756682579046⟩,⟨-15175272611494,-5025969838832⟩,⟨378866172832668,796316280631473⟩,⟨-56142874042860,406961254218037⟩,⟨-265869668852354,310258925707272⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71

noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨16065813423872,16737068925334⟩,⟨-92095196334304,-71513365158092⟩,⟨-30350545222988,-10051939677664⟩,⟨757732345665336,1592632561262946⟩,⟨-112285748085720,813922508436074⟩,⟨-531739337704708,620517851414544⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72

noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10909882818222,10952333724170⟩,⟨-109097176396601,-108253100831767⟩,⟨0,0⟩,⟨2148278590145760,2173453475298114⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73

noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9810371190446,9852822096394⟩,⟨-109097176396601,-108253100831767⟩,⟨0,0⟩,⟨2148278590145775,2173453475298112⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74

noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2406362562496,2411110103296⟩,⟨-12227224809080,-12080350374972⟩,⟨0,0⟩,⟨103760055435140,110865974497594⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75

noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7735028745669,7836163048805⟩,⟨-50263139378099,-48782804268322⟩,⟨-22317357458241,-21723758589195⟩,⟨615320788203660,644801075324084⟩,⟨328427810226911,342146326764016⟩,⟨122021960811943,127119469264963⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76

noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6635517117893,6736651421029⟩,⟨-50263139378099,-48782804268322⟩,⟨-22317357458242,-21723758589194⟩,⟨615320788203658,644801075324082⟩,⟨328427810226910,342146326764016⟩,⟨122021960811942,127119469264963⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77

noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1976449659904,1993081325952⟩,⟨-8328650987236,-7962006221807⟩,⟨-3698007795114,-3545607999426⟩,⟨37340185669332,49188072559331⟩,⟨25591906072782,31018803939331⟩,⟨7478038267574,9630255892777⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78

noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨99256358666,99685855397⟩,⟨877891315302,878750308762⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79

noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨132345454918,134362579601⟩,⟨704918229809,712407433351⟩,⟨314094932785,316135765445⟩,⟨-1781208837000,-1767320322048⟩,⟨-1581836455122,-1573942774986⟩,⟨-351156861666,-350470673530⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80

noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4382812222400,4404191429248⟩,⟨-20555875796316,-20042356596779⟩,⟨-3698007795114,-3545607999426⟩,⟨141100241104472,160054047056925⟩,⟨25591906072782,31018803939331⟩,⟨7478038267574,9630255892777⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81

noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨648665484650,696813217514⟩,⟨-5862108917078,-4479926417570⟩,⟨5014694620848,6895323724110⟩,⟨45307439524546,94138972903000⟩,⟨-74719365297734,-1359609094710⟩,⟨-64400668303746,43484305645272⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82

noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5031477707050,5101004646762⟩,⟨-26417984713394,-24522283014349⟩,⟨1316686825734,3349715724684⟩,⟨186407680629018,254193019959925⟩,⟨-49127459224952,29659194844621⟩,⟨-56922630036172,53114561538049⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83

noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨454207252833,462476247410⟩,⟨1622166726642,1863115258092⟩,⟨118861444048,303697813572⟩,⟨-35601901514226,-26175881827194⟩,⟨-3402787903758,5366169658195⟩,⟨-5160819515916,4815565717724⟩⟩⟩
noncomputable def wholeBoxes85 := wholeStep84.proposed :: wholeBoxes84

noncomputable def wholeStep85 : Instruction 40 := ⟨.mul 88 85,⟨⟨220761319014,221620312474⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes86 := wholeStep85.proposed :: wholeBoxes85

noncomputable def wholeStep86 : Instruction 40 := ⟨.neg 0,⟨⟨-221620312474,-220761319014⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes87 := wholeStep86.proposed :: wholeBoxes86

noncomputable def wholeStep87 : Instruction 40 := ⟨.add 89 0,⟨⟨877891315302,878750308762⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes88 := wholeStep87.proposed :: wholeBoxes87

noncomputable def wholeStep88 : Instruction 40 := ⟨.mul 12 0,⟨⟨1921330108492,1927004402870⟩,⟨-14594447534479,-14458129877504⟩,⟨0,0⟩,⟨131167320761344,137515064791860⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes89 := wholeStep88.proposed :: wholeBoxes88

noncomputable def wholeStep89 : Instruction 40 := ⟨.neg 91,⟨⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes90 := wholeStep89.proposed :: wholeBoxes89

noncomputable def wholeStep90 : Instruction 40 := ⟨.add 1 0,⟨⟨821818480716,827492775094⟩,⟨-14594447534479,-14458129877504⟩,⟨0,0⟩,⟨131167320761344,137515064791860⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes91 := wholeStep90.proposed :: wholeBoxes90

noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨32487511814,34553151760⟩,⟨-695070593076,-653729794771⟩,⟨328085346598,330673870673⟩,⟨8076834124150,8763646159574⟩,⟨-6659570832821,-6593775017748⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91

noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨486694764647,497029399170⟩,⟨927096133566,1209385463321⟩,⟨446946790646,634371684245⟩,⟨-27525067390076,-17412235667620⟩,⟨-10062358736579,-1227605359553⟩,⟨-5160819515916,4815565717724⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92

noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨501398014948,502387228948⟩,⟨2512147284185,2552733193796⟩,⟨0,0⟩,⟨2027158573049,4364694834823⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93

noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨221941981071,227101938940⟩,⟨1534766026698,1706542441027⟩,⟨203816156151,289856172978⟩,⟨-7442968853742,-351612393942⟩,⟨-3576500927061,913007866219⟩,⟨-2358074030510,2200321174991⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94

noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-696813217514,-648665484650⟩,⟨4479926417570,5862108917078⟩,⟨-6895323724110,-5014694620848⟩,⟨-94138972903000,-45307439524546⟩,⟨1359609094710,74719365297734⟩,⟨-43484305645272,64400668303746⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95

noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3685999004886,3755525944598⟩,⟨-16075949378746,-14180247679701⟩,⟨-10593331519224,-8560302620274⟩,⟨46961268201472,114746607532379⟩,⟨26951515167492,105738169237065⟩,⟨-36006267377698,74030924196523⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96

noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨443674448551,458932985271⟩,⟨398651414377,726480056123⟩,⟨-241556099179,49420964051⟩,⟨-21263547084926,-10084951050089⟩,⟨-13644847051278,-1894073314277⟩,⟨-11691132029381,2981010801842⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97

noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨308550450542,312584699906⟩,⟨1971389988864,1979120929998⟩,⟨877891315302,878750308762⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98

noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-312584699906,-308550450542⟩,⟨-1979120929998,-1971389988864⟩,⟨-878750308762,-877891315302⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99

noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨786926927870,790961177234⟩,⟨-1979120929998,-1971389988864⟩,⟨-878750308762,-877891315302⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100

noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1414556626476,1433772878862⟩,⟨-9578969690679,-9242167078661⟩,⟨-4253162323597,-4115683988838⟩,⟨55275846815447,65367813251555⟩,⟨34983505446468,39613142798254⟩,⟨11013968670084,12838799667896⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101

noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1433772878862,-1414556626476⟩,⟨9242167078661,9578969690679⟩,⟨4115683988838,4253162323597⟩,⟨-65367813251555,-55275846815447⟩,⟨-39613142798254,-34983505446468⟩,⟨-12838799667896,-11013968670084⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102

noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-334261251086,-315044998700⟩,⟨9242167078661,9578969690679⟩,⟨4115683988838,4253162323597⟩,⟨-65367813251555,-55275846815447⟩,⟨-39613142798254,-34983505446468⟩,⟨-12838799667896,-11013968670084⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103

noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-13957559612,-12454122604⟩,⟨396858917184,434584927904⟩,⟨29124203044,51825043442⟩,⟨-4712673189109,-4033556735068⟩,⟨1910318841802,2367597243811⟩,⟨2750013876973,2963811126840⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104

noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨429716888939,446478862667⟩,⟨795510331561,1161064984027⟩,⟨-212431896135,101246007493⟩,⟨-25976220274035,-14118507785157⟩,⟨-11734528209476,473523929534⟩,⟨-8941118152408,5944821928682⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105

noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-99685855397,-99256358666⟩,⟨-878750308762,-877891315302⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106

noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨3923727928,4162526361⟩,⟨24385097430,26767847983⟩,⟨39624999436,39835402372⟩,⟨-273752155753,-262508401127⟩,⟨250784818133,251900503000⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107

noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨8587368930,9127970193⟩,⟨7078815495,15588939795⟩,⟨86722243560,87354729775⟩,⟨-825378584615,-690641981411⟩,⟨105867709348,117030113883⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108

noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1489451902737,1508371487582⟩,⟨-7958760529659,-7622825110183⟩,⟨-1512277763232,-1434768139523⟩,⟨113009299626295,121381892747130⟩,⟨24036996589902,26079614066397⟩,⟨5334043683645,5839854405058⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109

noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨11632867419,12522259548⟩,⟨-56483053123,-38149754983⟩,⟨104923478222,108632321241⟩,⟨-475358549523,-26037795912⟩,⟨-322607560161,-233418293595⟩,⟨-198637125963,-177848603156⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110

noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-12522259548,-11632867419⟩,⟨38149754983,56483053123⟩,⟨-108632321241,-104923478222⟩,⟨26037795912,475358549523⟩,⟨233418293595,322607560161⟩,⟨177848603156,198637125963⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111

noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-112208114945,-110889226085⟩,⟨-840600553779,-821408262179⟩,⟨-108632321241,-104923478222⟩,⟨2225061051464,2674381805075⟩,⟨233418293595,322607560161⟩,⟨177848603156,198637125963⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112

noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨78131525615,83223979228⟩,⟨-554089867783,-512393024433⟩,⟨634620124968,656291666767⟩,⟨3068505459041,3778209786387⟩,⟨-3955047504713,-3476995442035⟩,⟨-2659900967249,-2428821192275⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113

noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨105840762890,114171304950⟩,⟨-1362544098014,-1235792042775⟩,⟨745220294897,798382656326⟩,⟨19291969791876,22392273581976⟩,⟨-7799587092823,-6373764932288⟩,⟨-5075300937992,-4504419754583⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114

noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-114171304950,-105840762890⟩,⟨1235792042775,1362544098014⟩,⟨-798382656326,-745220294897⟩,⟨-22392273581976,-19291969791876⟩,⟨6373764932288,7799587092823⟩,⟨4504419754583,5075300937992⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115

noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨985340322826,993670864886⟩,⟨1235792042775,1362544098014⟩,⟨-798382656326,-745220294897⟩,⟨-22392273581976,-19291969791876⟩,⟨6373764932288,7799587092823⟩,⟨4504419754583,5075300937992⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116

noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨118602941505,121428620952⟩,⟨780469978244,810335632450⟩,⟨183915880602,196003730279⟩,⟨-2761548138370,-2140262411235⟩,⟨-826643099009,-543393152944⟩,⟨-234276272051,-119636931402⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117

noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11183529260,11451139526⟩,⟨165683243708,171571088798⟩,⟨21163729430,22172440348⟩,⟨681437435895,836505920279⟩,⟨90923687302,119021597972⟩,⟨-20517766063,-14407328754⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118

noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨163411181812,174312400778⟩,⟨1461777299460,1884314157980⟩,⟨-6853769868,235273092443⟩,⟨-11077443243411,7767978150785⟩,⟨-6434027553669,7397361891098⟩,⟨-7074340755284,5865056642557⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119

noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-174312400778,-163411181812⟩,⟨-1884314157980,-1461777299460⟩,⟨-235273092443,6853769868⟩,⟨-7767978150785,11077443243411⟩,⟨-7397361891098,6434027553669⟩,⟨-5865056642557,7074340755284⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120

noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨47629580293,63690757128⟩,⟨-349548131282,244765141567⟩,⟨-31456936292,296709942846⟩,⟨-15210947004527,10725830849469⟩,⟨-10973862818159,7347035419888⟩,⟨-8223130673067,9274661930275⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121

noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨28879432172919,30339233059072⟩,⟨-293721697428014,-244889336213018⟩,⟨-111308432924166,-69876686530060⟩,⟨2943397712194299,5030931673377313⟩,⟨473803198721329,2487218320512835⟩,⟨-789785645982351,1475562298184139⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122

noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨12793550680,13410417511⟩,⟨168376637112,178984807202⟩,⟨39677551156,43292789396⟩,⟨498043673006,732693333074⟩,⟨78512479010,171677639458⟩,⟨9781081643,44070785057⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123

noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨336031443215,370038635343⟩,⟨840092140088,2089343657556⟩,⟨-315437692381,381532205929⟩,⟨-48297548796030,6574702829303⟩,⟨-22109387780067,15535072978331⟩,⟨-18141316342828,14169844409721⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124

noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-370038635343,-336031443215⟩,⟨-2089343657556,-840092140088⟩,⟨-381532205929,315437692381⟩,⟨-6574702829303,48297548796030⟩,⟨-15535072978331,22109387780067⟩,⟨-14169844409721,18141316342828⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125

noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨59678253596,110447419452⟩,⟨-1293833325995,320972843939⟩,⟨-593964102064,416683699874⟩,⟨-32550923103338,34179041010873⟩,⟨-27269601187807,22582911709601⟩,⟨-23110962562129,24086138271510⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126

noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨231601813584,234048434998⟩,⟨1582809545111,1591157742113⟩,⟨314094932785,316135765445⟩,⟨-3980232092552,-3966343577600⟩,⟨-1581836455122,-1573942774986⟩,⟨-351156861666,-350470673530⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127

noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1708062840241,-1620288109733⟩,⟨-5583504107707,-2603668243711⟩,⟨-639861206420,1564236701713⟩,⟨-23169872106917,105108033760011⟩,⟨-65318525516339,48672588648530⟩,⟨-58808370316212,63286436080789⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128

noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-188636218072,-174778448035⟩,⟨-1875470284895,-1430988903083⟩,⟨-375152150932,-98274184891⟩,⟨-7634906565506,12201645906402⟩,⟨-7879839340574,7376824647929⟩,⟨-6546545934850,7910908343592⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129

noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨42965595512,59269986963⟩,⟨-292660739784,160168839030⟩,⟨-61057218147,217861580554⟩,⟨-11615138658058,8235302328802⟩,⟨-9461675795696,5802881872943⟩,⟨-6897702796516,7560437670062⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130

noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2585193370,6397822079⟩,⟨-110059693912,43179790470⟩,⟨-37566097313,53941901426⟩,⟨-3989565244540,3879943852808⟩,⟨-3163586913390,2321611394833⟩,⟨-2485329219552,2551764967249⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131

noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1678965779,3194992455⟩,⟨-31552186978,17268039304⟩,⟨-6582668946,23487979050⟩,⟨-1337510635055,1043657121548⟩,⟨-1136055165982,689090246642⟩,⟨-767847772067,901437870964⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132

noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨3018059344,5791552939⟩,⟨-81396184873,19143654476⟩,⟨-22678160854,37162406382⟩,⟨-2629088631934,2512773195855⟩,⟨-2256240737472,1495229964933⟩,⟨-1538451346800,1706296738297⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133

noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5791552939,-3018059344⟩,⟨-19143654476,81396184873⟩,⟨-37162406382,22678160854⟩,⟨-2512773195855,2629088631934⟩,⟨-1495229964933,2256240737472⟩,⟨-1706296738297,1538451346800⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134

noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3206359569,3379762735⟩,⟨-129203348388,124575975343⟩,⟨-74728503695,76620062280⟩,⟨-6502338440395,6509032484742⟩,⟨-4658816878323,4577852132305⟩,⟨-4191625957849,4090216314049⟩⟩⟩


noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]

noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨47629580293,63690757128⟩,⟨-349548131282,244765141567⟩,⟨-31456936292,296709942846⟩,⟨-15210947004527,10725830849469⟩,⟨-10973862818159,7347035419888⟩,⟨-8223130673067,9274661930275⟩⟩

noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3206359569,3379762735⟩,⟨-129203348388,124575975343⟩,⟨-74728503695,76620062280⟩,⟨-6502338440395,6509032484742⟩,⟨-4658816878323,4577852132305⟩,⟨-4191625957849,4090216314049⟩⟩



attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (103/1024) u, BivariateJet2.affineZ (521/5120) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet


noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet























end GeneralCK.Certificates.LaneCB.RB2Cell000002

end

section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell000003Endpoints
open GeneralCK.Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

noncomputable def lift40 (a : DyadicInterval 40) : DyadicInterval 64 :=
  ⟨a.lo*16777216, a.hi*16777216⟩







noncomputable def sharedTwo : DyadicInterval 64 := ⟨12786308645202655420,12786308645202662926⟩

noncomputable def out_w0 : DyadicInterval 40 := ⟨-2525295488000,-2525295430144⟩



noncomputable def out_w1 : DyadicInterval 40 := ⟨-116561173120,-116561173056⟩



noncomputable def out_w2 : DyadicInterval 40 := ⟨-2141272513280,-2141272474048⟩



noncomputable def out_w3 : DyadicInterval 40 := ⟨-2141272513280,-2141272474048⟩



noncomputable def out_w4 : DyadicInterval 40 := ⟨-169203786688,-169203786624⟩



noncomputable def out_w5 : DyadicInterval 40 := ⟨-169203786688,-169203786624⟩



noncomputable def out_w6 : DyadicInterval 40 := ⟨762123383616,762123402880⟩



noncomputable def out_w7 : DyadicInterval 40 := ⟨83432382656,83432382720⟩



noncomputable def out_w8 : DyadicInterval 40 := ⟨-90287039808,-90287039744⟩



noncomputable def out_w9 : DyadicInterval 40 := ⟨83432506304,83432506368⟩



noncomputable def out_w10 : DyadicInterval 40 := ⟨-90287184576,-90287184512⟩



noncomputable def out_w11 : DyadicInterval 40 := ⟨-6854678272,-6854678208⟩



noncomputable def out_w12 : DyadicInterval 40 := ⟨-6854657088,-6854657024⟩



noncomputable def out_w13 : DyadicInterval 40 := ⟨173719422464,173719422528⟩



noncomputable def out_w14 : DyadicInterval 40 := ⟨173719690880,173719690944⟩



noncomputable def out_w15 : DyadicInterval 40 := ⟨2408734257088,2408734314944⟩



noncomputable def out_w16 : DyadicInterval 40 := ⟨2408734257088,2408734314944⟩



noncomputable def out_w17 : DyadicInterval 40 := ⟨1972068687424,1972068726016⟩



noncomputable def out_w18 : DyadicInterval 40 := ⟨1972068687424,1972068726080⟩



noncomputable def out_w19 : DyadicInterval 40 := ⟨-2527432537536,-2527432479680⟩



noncomputable def out_w20 : DyadicInterval 40 := ⟨-2523162584128,-2523162526272⟩



noncomputable def out_w21 : DyadicInterval 40 := ⟨-116799963776,-116799963712⟩



noncomputable def out_w22 : DyadicInterval 40 := ⟨-116322434304,-116322434240⟩



noncomputable def out_w23 : DyadicInterval 40 := ⟨-2148369011648,-2148368972288⟩



noncomputable def out_w24 : DyadicInterval 40 := ⟨-2134216264576,-2134216225408⟩



noncomputable def out_w25 : DyadicInterval 40 := ⟨-170382088000,-170382087936⟩



noncomputable def out_w26 : DyadicInterval 40 := ⟨-168027626368,-168027626304⟩



noncomputable def out_w27 : DyadicInterval 40 := ⟨80835374528,80835374592⟩



noncomputable def out_w28 : DyadicInterval 40 := ⟨-87253299392,-87253299328⟩



noncomputable def out_w29 : DyadicInterval 40 := ⟨86052608640,86052608704⟩



noncomputable def out_w30 : DyadicInterval 40 := ⟨-93363710336,-93363710272⟩



noncomputable def out_w31 : DyadicInterval 40 := ⟨-7311101632,-7311101568⟩



noncomputable def out_w32 : DyadicInterval 40 := ⟨-6417924800,-6417924736⟩



noncomputable def out_w33 : DyadicInterval 40 := ⟨168088673856,168088673920⟩



noncomputable def out_w34 : DyadicInterval 40 := ⟨179416318976,179416319040⟩



noncomputable def out_w35 : DyadicInterval 40 := ⟨2406362562496,2406362620352⟩



noncomputable def out_w36 : DyadicInterval 40 := ⟨2411110045440,2411110103296⟩



noncomputable def out_w37 : DyadicInterval 40 := ⟨1963834137472,1963834176064⟩



noncomputable def out_w38 : DyadicInterval 40 := ⟨1980341345984,1980341384576⟩



end LaneCBRB2Cell000003Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000003
open Set LaneCBRB2Cell000003Endpoints
open BivariateJetProgram (zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
















































noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨110595407872,110595407872⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨115749368627,115749368628⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0

noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1

noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-110595407872,-110595407872⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2

noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨439160406016,439160406016⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3

noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨46231925555,46231925556⟩,⟨-115749368628,-115749368627⟩,⟨439160406016,439160406016⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4

noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨156827333427,156827333428⟩,⟨983762259148,983762259149⟩,⟨439160406016,439160406016⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5

noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨46231925555,46231925556⟩,⟨-115749368628,-115749368627⟩,⟨439160406016,439160406016⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes7 := centerStep6.proposed :: centerBoxes6

noncomputable def centerStep7 : Instruction 40 := ⟨.log 7,⟨⟨-2525295488000,-2525295430144⟩,⟨10931067056724,10931067056725⟩,⟨0,0⟩,⟨-108673909379485,-108673909379464⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes8 := centerStep7.proposed :: centerBoxes7

noncomputable def centerStep8 : Instruction 40 := ⟨.mul 8 0,⟨⟨-254009214125,-254009208305⟩,⟨-1425783860225,-1425783802367⟩,⟨0,0⟩,⟨10931067056722,10931067056727⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes9 := centerStep8.proposed :: centerBoxes8

noncomputable def centerStep9 : Instruction 40 := ⟨.neg 0,⟨⟨254009208305,254009214125⟩,⟨1425783802367,1425783860225⟩,⟨0,0⟩,⟨-10931067056727,-10931067056722⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes10 := centerStep9.proposed :: centerBoxes9

noncomputable def centerStep10 : Instruction 40 := ⟨.add 12 7,⟨⟨988916219904,988916219904⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes11 := centerStep10.proposed :: centerBoxes10

noncomputable def centerStep11 : Instruction 40 := ⟨.log 0,⟨⟨-116561173120,-116561173056⟩,⟨-1222475468885,-1222475468884⟩,⟨0,0⟩,⟨-1359190966492,-1359190966489⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes12 := centerStep11.proposed :: centerBoxes11

noncomputable def centerStep12 : Instruction 40 := ⟨.mul 1 0,⟨⟨-104836758246,-104836758188⟩,⟨-982950454721,-982950454655⟩,⟨0,0⟩,⟨1222475468882,1222475468887⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes13 := centerStep12.proposed :: centerBoxes12

noncomputable def centerStep13 : Instruction 40 := ⟨.neg 0,⟨⟨104836758188,104836758246⟩,⟨982950454655,982950454721⟩,⟨0,0⟩,⟨-1222475468887,-1222475468882⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes14 := centerStep13.proposed :: centerBoxes13

noncomputable def centerStep14 : Instruction 40 := ⟨.add 4 0,⟨⟨358845966493,358845972371⟩,⟨2408734257022,2408734314946⟩,⟨0,0⟩,⟨-12153542525614,-12153542525604⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes15 := centerStep14.proposed :: centerBoxes14

noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2141272513280,-2141272474048⟩,⟨6897127045758,6897127045810⟩,⟨3078940145947,3078940145968⟩,⟨-43264991732981,-43264991732328⟩,⟨-27022527519858,-27022527519535⟩,⟨-8621893741704,-8621893741591⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15

noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-305417468918,-305417463319⟩,⟨-932091136043,-932091100923⟩,⟨-416093947436,-416093931759⟩,⟨6171042772678,6171042772918⟩,⟨3796570379149,3796570418496⟩,⟨1229771991870,1229771991912⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16

noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨305417463319,305417468918⟩,⟨932091100923,932091136043⟩,⟨416093931759,416093947436⟩,⟨-6171042772918,-6171042772678⟩,⟨-3796570418496,-3796570379149⟩,⟨-1229771991912,-1229771991870⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17

noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-156827333428,-156827333427⟩,⟨-983762259149,-983762259148⟩,⟨-439160406016,-439160406016⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18

noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨942684294348,942684294349⟩,⟨-983762259149,-983762259148⟩,⟨-439160406016,-439160406016⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19

noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-169203786688,-169203786624⟩,⟨-1147423426260,-1147423426255⟩,⟨-512220237220,-512220237217⟩,⟨-1197423006607,-1197423006597⟩,⟨747888647440,747888647448⟩,⟨-238623735111,-238623735108⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20

noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-145069636579,-145069636523⟩,⟨-832371136784,-832371136719⟩,⟨-371578034213,-371578034182⟩,⟨1026630217895,1026630217918⟩,⟨1388604893169,1388604893249⟩,⟨204587965839,204587965846⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21

noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨145069636523,145069636579⟩,⟨832371136719,832371136784⟩,⟨371578034182,371578034213⟩,⟨-1026630217918,-1026630217895⟩,⟨-1388604893249,-1388604893169⟩,⟨-204587965846,-204587965839⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22

noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨450487099842,450487105497⟩,⟨1764462237642,1764462272827⟩,⟨787671965941,787671981649⟩,⟨-7197672990836,-7197672990573⟩,⟨-5185175311745,-5185175272318⟩,⟨-1434359957758,-1434359957709⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23

noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨809333066335,809333077868⟩,⟨4173196494664,4173196587773⟩,⟨787671965941,787671981649⟩,⟨-19351215516450,-19351215516177⟩,⟨-5185175311745,-5185175272318⟩,⟨-1434359957758,-1434359957709⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24

noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨92463851110,92463851112⟩,⟨-231498737256,-231498737254⟩,⟨878320812032,878320812032⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25

noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨13074577849350,13074577849634⟩,⟨32734395397258,32734395398964⟩,⟨-124196361021184,-124196361015787⟩,⟨163912082572873,163912082586388⟩,⟨-310946390450081,-310946390390667⟩,⟨2359500439294195,2359500439447967⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26

noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨9623989337205,9623989474557⟩,⟨73719830699341,73719832152217⟩,⟨-82052560798579,-82052559304893⟩,⟨139029564613112,139029571907603⟩,⟨-738477903690456,-738477888908388⟩,⟨1541790049507056,1541790077926835⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27

noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨86679471104,86679604480⟩,⟨-658028021976,-658025958148⟩,⟨732404204444,732406500449⟩,⟨8704933888147,8704985504767⟩,⟨-4478503982753,-4478430249712⟩,⟨-1440703042432,-1440600861185⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28

noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29

noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1186191098880,1186191232256⟩,⟨-658028021976,-658025958148⟩,⟨732404204444,732406500449⟩,⟨8704933888147,8704985504767⟩,⟨-4478503982753,-4478430249712⟩,⟨-1440703042432,-1440600861185⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30

noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨83432382656,83432506368⟩,⟨-609943425009,-609941443409⟩,⟨678884582114,678886786677⟩,⟨7730470323062,7730521273672⟩,⟨-3774639331656,-3774568073322⟩,⟨-1754599950146,-1754502363138⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31

noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨90009734471,90009878058⟩,⟨-707960198317,-707957755864⟩,⟨787979912560,787982629904⟩,⟨9730504705611,9730570168460⟩,⟨-5224637744473,-5224549124446⟩,⟨-1097811671751,-1097692490620⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32

noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-86679604480,-86679471104⟩,⟨658025958148,658028021976⟩,⟨-732406500449,-732404204444⟩,⟨-8704985504767,-8704933888147⟩,⟨4478430249712,4478503982753⟩,⟨1440600861185,1440703042432⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33

noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1012832023296,1012832156672⟩,⟨658025958148,658028021976⟩,⟨-732406500449,-732404204444⟩,⟨-8704985504767,-8704933888147⟩,⟨4478430249712,4478503982753⟩,⟨1440600861185,1440703042432⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34

noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-90287184576,-90287039744⟩,⟨714340661081,714342995605⟩,⟨-795086890008,-795084292805⟩,⟨-9914072876422,-9914012564510⟩,⟨5378257593261,5378341652238⟩,⟨988940277921,989055166142⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35

noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-83169437743,-83169293376⟩,⟨603991429314,603993922603⟩,⟨-672264797717,-672262023801⟩,⟨-7562666455669,-7562598834622⟩,⟨3634832953331,3634923776052⟩,⟨1851912674254,1852033986425⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36

noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨6840296728,6840584682⟩,⟨-103968769003,-103963833261⟩,⟨115715114843,115720606103⟩,⟨2167838249942,2167971333838⟩,⟨-1589804791142,-1589625348394⟩,⟨754101002503,754341495805⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37

noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨3420148364,3420292341⟩,⟨-51984384502,-51981916630⟩,⟨57857557421,57860303052⟩,⟨1083919124971,1083985666919⟩,⟨-794902395571,-794812674197⟩,⟨377050501251,377170747903⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38

noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-3420292341,-3420148364⟩,⟨51981916630,51984384502⟩,⟨-57860303052,-57857557421⟩,⟨-1083985666919,-1083919124971⟩,⟨794812674197,794902395571⟩,⟨-377170747903,-377050501251⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39

noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨758703091275,758703254516⟩,⟨51981916630,51984384502⟩,⟨-57860303052,-57857557421⟩,⟨-1083985666919,-1083919124971⟩,⟨794812674197,794902395571⟩,⟨-377170747903,-377050501251⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40

noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨6833334474,6833355504⟩,⟨-103750805796,-103750320748⟩,⟨115477467398,115478007098⟩,⟨2160117632259,2160132823089⟩,⟨-1582773538142,-1582755328492⟩,⟨748580257633,748602835632⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41

noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-6833355504,-6833334474⟩,⟨103750320748,103750805796⟩,⟨-115478007098,-115477467398⟩,⟨-2160132823089,-2160117632259⟩,⟨1582755328492,1582773538142⟩,⟨-748602835632,-748580257633⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42

noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1092678272272,1092678293302⟩,⟨103750320748,103750805796⟩,⟨-115478007098,-115477467398⟩,⟨-2160132823089,-2160117632259⟩,⟨1582755328492,1582773538142⟩,⟨-748602835632,-748580257633⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43

noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-6854678272,-6854657024⟩,⟨104399149088,104399639179⟩,⟨-116200179668,-116199634355⟩,⟨-2183554632471,-2183539211733⟩,⟨1603686691386,1603705149143⟩,⟨-765564859085,-765542010128⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44

noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3427339136,-3427328512⟩,⟨52199574544,52199819590⟩,⟨-58100089834,-58099817177⟩,⟨-1091777316236,-1091769605866⟩,⟨801843345693,801852574572⟩,⟨-382782429543,-382771005064⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45

noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3427328512,3427339136⟩,⟨-52199819590,-52199574544⟩,⟨58099817177,58100089834⟩,⟨1091769605866,1091777316236⟩,⟨-801852574572,-801843345693⟩,⟨382771005064,382782429543⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46

noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765550712128,765550742016⟩,⟨-52199819590,-52199574544⟩,⟨58099817177,58100089834⟩,⟨1091769605866,1091777316236⟩,⟨-801852574572,-801843345693⟩,⟨382771005064,382782429543⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47

noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48

noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49

noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨273169568068,273169573326⟩,⟨25937580187,25937701449⟩,⟨-28869501775,-28869366849⟩,⟨-540033205773,-540029408064⟩,⟨395688832123,395693384536⟩,⟨-187150708908,-187145064408⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50

noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1531101424256,1531101484032⟩,⟨-104399639180,-104399149088⟩,⟨116199634354,116200179668⟩,⟨2183539211732,2183554632472⟩,⟨-1603705149144,-1603686691386⟩,⟨765542010128,765564859086⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51

noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1193609238856,1193609396039⟩,⟨-775477484739,-775474848303⟩,⟨863128623278,863131556418⟩,⟨11266283951881,11266354202045⟩,⟨-6399396727680,-6399300967690⟩,⟨-449550151499,-449420965351⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52

noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1287706849936,1287707164302⟩,⟨-1550954969478,-1550949696606⟩,⟨1726257246557,1726263112835⟩,⟨22532567903769,22532708404079⟩,⟨-12798793455354,-12798601935382⟩,⟨-899100151571,-898842082130⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53

noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨173719422464,173719690944⟩,⟨-1324286675329,-1324281849777⟩,⟨1473968591414,1473973960191⟩,⟨17644470375075,17644606662612⟩,⟨-9152992891738,-9152813758766⟩,⟨-2743666346206,-2743431411189⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54

noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨59811993811,59812098716⟩,⟨-449965443110,-449963720436⟩,⟨500824194924,500826111460⟩,⟨5859043483719,5859088919821⟩,⟨-2958420787673,-2958358570474⟩,⟨-1100955726071,-1100871578573⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55

noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380396445263,380396467437⟩,⟨10181121138,10181413672⟩,⟨-11332243126,-11331917629⟩,⟨-214445165333,-214435959734⟩,⟨158055770733,158066776404⟩,⟨-76518727373,-76505119514⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56

noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3178067945162,3178068130418⟩,⟨-85061852488,-85059398559⟩,⟨94673865970,94676596413⟩,⟨1796084108259,1796161488867⟩,⟨-1325656099140,-1325563704909⟩,⟨644811826256,644925914313⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57

noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨172882737630,172883050930⟩,⟨-1305223634023,-1305218437322⟩,⟨1452750396069,1452756177645⟩,⟨17102513941927,17102652915078⟩,⟨-8700731531106,-8700543513436⟩,⟨-3060917969977,-3060665476272⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58

noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨346602160094,346602741874⟩,⟨-2629510309352,-2629500287099⟩,⟨2926718987483,2926730137836⟩,⟨34746984317002,34747259577690⟩,⟨-17853724422844,-17853357272202⟩,⟨-5804584316183,-5804096887461⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59

noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨523532781435,523533006720⟩,⟨71738833570,71742254852⟩,⟨-79851452452,-79847646100⟩,⟨-1491064419832,-1490971798511⟩,⟨1091428204118,1091552781540⟩,⟨-514434172133,-514267533065⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60

noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨361256697632,361256930815⟩,⟨74253614175,74257171368⟩,⟨-82650635960,-82646678392⟩,⟨-1538246087268,-1538149402183⟩,⟨1124024843370,1124154570488⟩,⟨-526165092007,-525991896451⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61

noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨722513395264,722513861630⟩,⟨148507228350,148514342736⟩,⟨-165301271920,-165293356784⟩,⟨-3076492174536,-3076298804366⟩,⟨2248049686740,2248309140976⟩,⟨-1052330184014,-1051983792902⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62

noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524268068752,1524268149558⟩,⟨-649318432,-648343292⟩,⟨721627256,722712270⟩,⟨23406388643,23437000213⟩,⟨-20949820652,-20913153244⟩,⟨16939174496,16984601453⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63

noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨1001630241850,1001630941480⟩,⟨205450928282,205461443032⟩,⟨-228685238209,-228673539904⟩,⟨-4249778131345,-4249489436220⟩,⟨3102930488554,3103314745110⟩,⟨-1447946062717,-1447435583725⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64

noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67867961587,67867964200⟩,⟨12888190350,12888250856⟩,⟨-14345040622,-14344973300⟩,⟨-267114741905,-267112838242⟩,⟨195252757916,195255036498⟩,⟨-91477775565,-91474954892⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65

noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨49956529853,49956532489⟩,⟨267079647537,267079707877⟩,⟨38060329505,38060382054⟩,⟨-1293249166816,-1293247255266⟩,⟨-221549078106,-221547083805⟩,⟨-176425103807,-176422926313⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66

noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2132102573667,2132102740148⟩,⟨-290758985068,-290757608780⟩,⟨323622636018,323624167386⟩,⟨6101107245434,6101150616641⟩,⟨-4488477480908,-4488425693474⟩,⟨2156638978809,2156702928232⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67

noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2969013882831,2969014230575⟩,⟨-607335341829,-607332443336⟩,⟨675980680528,675983905630⟩,⟨12785361159287,12785452640727⟩,⟨-9421593101755,-9421484128011⟩,⟨4556074387484,4556208623984⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68

noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨134897737254,134897760172⟩,⟨693601408440,693601788998⟩,⟨133487715840,133488017931⟩,⟨-3206311516696,-3206300283993⟩,⟨-883144112598,-883132733618⟩,⟨-222595993186,-222583659616⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69

noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8961793124461,8961794646995⟩,⟨-46078732870698,-46078691931937⟩,⟨-8868141370523,-8868118288173⟩,⟨686851219531266,686852799615295⟩,⟨149864100813283,149865179592325⟩,⟨32337960341047,32338873116372⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70

noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨8163990982815,8163998072287⟩,⟨-40302143926048,-40301991324294⟩,⟨-9942627851855,-9942505515386⟩,⟨573846144405492,573851276441913⟩,⟨169740044962477,169744847216211⟩,⟨21346106010086,21351319180400⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71

noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨16327981965630,16327996144574⟩,⟨-80604287852096,-80603982648588⟩,⟨-19885255703710,-19885011030772⟩,⟨1147692288810984,1147702552883826⟩,⟨339480089924954,339489694432422⟩,⟨42692212020172,42702638360800⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72

noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10931067056724,10931067056725⟩,⟨-108673909379485,-108673909379464⟩,⟨0,0⟩,⟨2160817149603222,2160817149603840⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73

noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9831555428948,9831555428949⟩,⟨-108673909379485,-108673909379464⟩,⟨0,0⟩,⟨2160817149603232,2160817149603830⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74

noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2408734257088,2408734314944⟩,⟨-12153542525660,-12153542525558⟩,⟨0,0⟩,⟨107314718406763,107314718418708⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75

noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7708642321395,7708642321445⟩,⟨-48355546315829,-48355546315150⟩,⟨-21586354991454,-21586354991173⟩,⟨606659061855020,606659061868072⟩,⟨324863169314189,324863169320442⟩,⟨120895665508221,120895665510577⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76

noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6609130693619,6609130693669⟩,⟨-48355546315829,-48355546315150⟩,⟨-21586354991454,-21586354991172⟩,⟨606659061855020,606659061868067⟩,⟨324863169314188,324863169320440⟩,⟨120895665508221,120895665510577⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77

noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1972068687424,1972068726080⟩,⟨-8044550472158,-8044550471912⟩,⟨-3591160383227,-3591160383120⟩,⟨42067568721153,42067568730513⟩,⟨27770416164849,27770416169221⟩,⟨8383270005584,8383270007402⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78

noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨99471065088,99471065088⟩,⟨878320812032,878320812032⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79

noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨134458481758,134458481760⟩,⟨703127097259,703127097263⟩,⟨313882321304,313882321306⟩,⟨-1760396448892,-1760396448888⟩,⟨-1571713921844,-1571713921840⟩,⟨-350813683712,-350813683712⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80

noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4380802944512,4380803041024⟩,⟨-20198092997818,-20198092997470⟩,⟨-3591160383227,-3591160383120⟩,⟨149382287127916,149382287149221⟩,⟨27770416164849,27770416169221⟩,⟨8383270005584,8383270007402⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81

noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨693204320188,693205483748⟩,⟨-5259020618704,-5259000574198⟩,⟨5853437974966,5853460275672⟩,⟨69493968634004,69494519155380⟩,⟨-35707448845688,-35706714544404⟩,⟨-11609168632366,-11608193774922⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82

noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5074007264700,5074008524772⟩,⟨-25457113616522,-25457093571668⟩,⟨2262277591739,2262299892552⟩,⟨218876255761920,218876806304601⟩,⟨-7937032680839,-7936298375183⟩,⟨-3225898626782,-3224923767520⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83

noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨459037352706,459037466703⟩,⟨1750195202007,1750198022016⟩,⟨204664649186,204666666706⟩,⟨-31018347607679,-31018263256028⟩,⟨1089120266457,1089204512438⟩,⟨-291841908868,-291753714903⟩⟩⟩
noncomputable def centerBoxes85 := centerStep84.proposed :: centerBoxes84

noncomputable def centerStep85 : Instruction 40 := ⟨.mul 88 85,⟨⟨221190815744,221190815744⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes86 := centerStep85.proposed :: centerBoxes85

noncomputable def centerStep86 : Instruction 40 := ⟨.neg 0,⟨⟨-221190815744,-221190815744⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes87 := centerStep86.proposed :: centerBoxes86

noncomputable def centerStep87 : Instruction 40 := ⟨.add 89 0,⟨⟨878320812032,878320812032⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes88 := centerStep87.proposed :: centerBoxes87

noncomputable def centerStep88 : Instruction 40 := ⟨.mul 12 0,⟨⟨1924164670212,1924164716430⟩,⟨-14526060217769,-14526060101975⟩,⟨0,0⟩,⟨134340185392009,134340185401960⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes89 := centerStep88.proposed :: centerBoxes88

noncomputable def centerStep89 : Instruction 40 := ⟨.neg 91,⟨⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes90 := centerStep89.proposed :: centerBoxes89

noncomputable def centerStep90 : Instruction 40 := ⟨.add 1 0,⟨⟨824653042436,824653088654⟩,⟨-14526060217769,-14526060101975⟩,⟨0,0⟩,⟨134340185392009,134340185401960⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes91 := centerStep90.proposed :: centerBoxes90

noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨34674756595,34674758540⟩,⟨-697601361899,-697601352148⟩,⟨329378021832,329378040293⟩,⟨8707111211124,8707111236074⟩,⟨-6626565812353,-6626565719884⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91

noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨493712109301,493712225243⟩,⟨1052593840108,1052596669868⟩,⟨534042671018,534044706999⟩,⟨-22311236396555,-22311152019954⟩,⟨-5537445545896,-5537361207446⟩,⟨-291841908868,-291753714903⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92

noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨501892554988,501892567044⟩,⟨2532355881864,2532356003553⟩,⟨0,0⟩,⟨3194096148032,3194099067279⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93

noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨225364085022,225364143361⟩,⟨1617576140881,1617577765796⟩,⟨243773720858,243774656076⟩,⟨-3901546149807,-3901492474456⟩,⟨-1297682193380,-1297638886499⟩,⟨-133216676489,-133176415511⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94

noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-693205483748,-693204320188⟩,⟨5259000574198,5259020618704⟩,⟨-5853460275672,-5853437974966⟩,⟨-69494519155380,-69493968634004⟩,⟨35706714544404,35707448845688⟩,⟨11608193774922,11609168632366⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95

noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3687597460764,3687598720836⟩,⟨-14939092423620,-14939072378766⟩,⟨-9444620658899,-9444598358086⟩,⟨79887767972536,79888318515217⟩,⟨63477130709253,63477865014909⟩,⟨19991463780506,19992438639768⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96

noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨450953626485,450953780586⟩,⟨531292255157,531295512275⟩,⟨-102261495682,-102258408788⟩,⟨-15241502372742,-15241407392557⟩,⟨-7813193717963,-7813082135385⟩,⟨-4124228449475,-4124096099907⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97

noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨313654666854,313654666856⟩,⟨1967524518296,1967524518298⟩,⟨878320812032,878320812032⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98

noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-313654666856,-313654666854⟩,⟨-1967524518298,-1967524518296⟩,⟨-878320812032,-878320812032⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99

noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨785856960920,785856960922⟩,⟨-1967524518298,-1967524518296⟩,⟨-878320812032,-878320812032⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100

noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1409502060982,1409502088615⟩,⟨-9278628164217,-9278628094847⟩,⟨-4142063871605,-4142063840641⟩,⟨58857760716646,58857760724325⟩,⟨36644989415278,36644989496162⟩,⟨11729237391444,11729237392932⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101

noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1409502088615,-1409502060982⟩,⟨9278628094847,9278628164217⟩,⟨4142063840641,4142063871605⟩,⟨-58857760724325,-58857760716646⟩,⟨-36644989496162,-36644989415278⟩,⟨-11729237392932,-11729237391444⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102

noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-309990460839,-309990433206⟩,⟨9278628094847,9278628164217⟩,⟨4142063840641,4142063871605⟩,⟨-58857760724325,-58857760716646⟩,⟨-36644989496162,-36644989415278⟩,⟨-11729237392932,-11729237391444⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103

noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-13034383218,-13034382055⟩,⟨422778648732,422778654568⟩,⟨50349672602,50349684947⟩,⟨-4428419120527,-4428419105526⟩,⟨2039118465173,2039118527214⟩,⟨2815609737827,2815609762637⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104

noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨437919243267,437919398531⟩,⟨954070903889,954074166843⟩,⟨-51911823080,-51908723841⟩,⟨-19669921493269,-19669826498083⟩,⟨-5774075252790,-5773963608171⟩,⟨-1308618711648,-1308486337270⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105

noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-99471065088,-99471065088⟩,⟨-878320812032,-878320812032⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106

noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4182528642,4182528643⟩,⟨26459701452,26459701455⟩,⟨39730142208,39730142208⟩,⟨-277391553335,-277391553330⟩,⟨251342618624,251342618624⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107

noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨9162795341,9162795565⟩,⟨11734163847,11734165258⟩,⟨87038055949,87038058040⟩,⟨-784415427415,-784415412590⟩,⟨111463671483,111463684713⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108

noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1493730891117,1493730912404⟩,⟨-7702184682666,-7702184291292⟩,⟨-1453752523856,-1453752453429⟩,⟨115145380705290,115145388664004⟩,⟨24562008287119,24562009907078⟩,⟨5476988405633,5476988715018⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109

noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨12448027018,12448027501⟩,⟨-48244929197,-48244922220⟩,⟨106129842329,106129847740⟩,⟨-270492300898,-270492147664⟩,⟨-269108918815,-269108831930⟩,⟨-184517438583,-184517418208⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110

noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-12448027501,-12448027018⟩,⟨48244922220,48244929197⟩,⟨-106129847740,-106129842329⟩,⟨270492147664,270492300898⟩,⟨269108831930,269108918815⟩,⟨184517418208,184517438583⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111

noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-111919092589,-111919092106⟩,⟨-830075889812,-830075882835⟩,⟨-106129847740,-106129842329⟩,⟨2469515403216,2469515556450⟩,⟨269108831930,269108918815⟩,⟨184517418208,184517438583⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112

noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨82920935480,82920937108⟩,⟨-545861229054,-545861224962⟩,⟨636671962605,636671978054⟩,⟨3462599107860,3462599108360⟩,⟨-3639439625585,-3639439586605⟩,⟨-2516222765852,-2516222765681⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113

noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨112651435162,112651438980⟩,⟨-1322443643755,-1322443586706⟩,⟨755308116321,755308157102⟩,⟨21035522367585,21035523651942⟩,⟨-6830174998286,-6830174341105⟩,⟨-4688926961144,-4688926758337⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114

noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-112651438980,-112651435162⟩,⟨1322443586706,1322443643755⟩,⟨-755308157102,-755308116321⟩,⟨-21035523651942,-21035522367585⟩,⟨6830174341105,6830174998286⟩,⟨4688926758337,4688926961144⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115

noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨986860188796,986860192614⟩,⟨1322443586706,1322443643755⟩,⟨-755308157102,-755308116321⟩,⟨-21035523651942,-21035522367585⟩,⟨6830174341105,6830174998286⟩,⟨4688926758337,4688926961144⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116

noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨120682418758,120682419228⟩,⟨792808256689,792808266115⟩,⟨189357141422,189357147504⟩,⟨-2461072573243,-2461072337047⟩,⟨-680914127637,-680913999421⟩,⟨-172707443004,-172707393686⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117

noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11392224385,11392224484⟩,⟨168986551554,168986553706⟩,⟨21605875370,21605876566⟩,⟨750587843961,750587898397⟩,⟨105460269996,105460297440⟩,⟨-17075728212,-17075721810⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118

noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨169176959667,169177108049⟩,⟨1674331747038,1674337127716⟩,⟨114817381921,114820215194⟩,⟨-1738707194109,-1738496124837⟩,⟨443396511667,443541552025⟩,⟨-592744914704,-592626907401⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119

noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-169177108049,-169176959667⟩,⟨-1674337127716,-1674331747038⟩,⟨-114820215194,-114817381921⟩,⟨1738496124837,1738707194109⟩,⟨-443541552025,-443396511667⟩,⟨592626907401,592744914704⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120

noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨56186976973,56187183694⟩,⟨-56760986835,-56753981242⟩,⟨128953505664,128957274155⟩,⟨-2163050024970,-2162785280347⟩,⟨-1741223745405,-1741035398166⟩,⟨459410230912,459568499193⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121

noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨29285640233176,29285666238384⟩,⟨-264034119350341,-264033465364197⟩,⟨-88995460623909,-88994974770807⟩,⟨3862671421562827,3862694880103723⟩,⟨1430035548531533,1430055932154416⟩,⟨330960013933921,330980422385643⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122

noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13246104751,13246104855⟩,⟨174037300946,174037303694⟩,⟨41567687432,41567688930⟩,⟨603061816653,603061897797⟩,⟨123599495002,123599535752⟩,⟨27309169974,27309185141⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123

noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨352811783367,352812099429⟩,⟨1454618679822,1454630772995⟩,⟨35009303624,35016188285⟩,⟨-20988564538427,-20988056783710⟩,⟨-3548600153337,-3548248232281⟩,⟨-2014506851000,-2014222925416⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124

noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-352812099429,-352811783367⟩,⟨-1454630772995,-1454618679822⟩,⟨-35016188285,-35009303624⟩,⟨20988056783710,20988564538427⟩,⟨3548248232281,3548600153337⟩,⟨2014222925416,2014506851000⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125

noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨85107143838,85107615164⟩,⟨-500559869106,-500544512979⟩,⟨-86928011365,-86918027465⟩,⟨1318135290441,1318738040344⟩,⟨-2225827020509,-2225363454834⟩,⟨705604213768,706020513730⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126

noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨233929546846,233929546848⟩,⟨1581447909291,1581447909295⟩,⟨313882321304,313882321306⟩,⟨-3959419704444,-3959419704440⟩,⟨-1571713921844,-1571713921840⟩,⟨-350813683712,-350813683712⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127

noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1662023816878,-1662022366432⟩,⟨-4122149557949,-4122107647931⟩,⟨448039496730,448065859652⟩,⟨41552283438073,41553824691512⟩,⟨-7767829023137,-7766631774075⟩,⟨2232211692134,2233323117897⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128

noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-182423768852,-182423608940⟩,⟨-1650857667823,-1650852005916⟩,⟨-237055791226,-237052638449⟩,⟨2336345325960,2336578624876⟩,⟨-210179834137,-210021075204⟩,⟨660394302057,660525680876⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129

noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨51505777994,51505937908⟩,⟨-69409758532,-69404096621⟩,⟨76826530078,76829682857⟩,⟨-1623074378484,-1622841079564⟩,⟨-1781893755981,-1781734997044⟩,⟨309580618345,309711997164⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130

noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4349124657,4349164744⟩,⟨-29973163273,-29971717839⟩,⟨5539390633,5540264151⟩,⟨-48398036684,-48337603535⟩,⟨-302745542543,-302701523862⟩,⟨51227163135,51263954969⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131

noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2412748623,2412763606⟩,⟨-6502913882,-6502363234⟩,⟨7197759626,7198077356⟩,⟨-143301876107,-143278116926⟩,⟨-176643586912,-176627005416⟩,⟨39740382496,39753662465⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132

noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4327472206,4327499165⟩,⟨-29316462771,-29315365283⟩,⟨5029374098,5029993166⟩,⟨-69563158204,-69511908146⟩,⟨-287313493938,-287279245789⟩,⟨42654016065,42680025978⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133

noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4327499165,-4327472206⟩,⟨29315365283,29316462771⟩,⟨-5029993166,-5029374098⟩,⟨69511908146,69563158204⟩,⟨287279245789,287313493938⟩,⟨-42680025978,-42654016065⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134

noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨21625492,21692538⟩,⟨-657797990,-655255068⟩,⟨509397467,510890053⟩,⟨21113871462,21225554669⟩,⟨-15466296754,-15388029924⟩,⟨8547137157,8609938904⟩⟩⟩


noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]

noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨56186976973,56187183694⟩,⟨-56760986835,-56753981242⟩,⟨128953505664,128957274155⟩,⟨-2163050024970,-2162785280347⟩,⟨-1741223745405,-1741035398166⟩,⟨459410230912,459568499193⟩⟩

noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨21625492,21692538⟩,⟨-657797990,-655255068⟩,⟨509397467,510890053⟩,⟨21113871462,21225554669⟩,⟨-15466296754,-15388029924⟩,⟨8547137157,8609938904⟩⟩

noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨110380659507,110810156237⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨113816633344,117682103911⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0

noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1

noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-110810156237,-110380659507⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2

noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨438945657651,439375154381⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3

noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨45437734092,47026871993⟩,⟨-117682103911,-113816633344⟩,⟨438945657651,439375154381⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4

noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨155818393599,157837028230⟩,⟨981829523865,985694994432⟩,⟨438945657651,439375154381⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5

noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨45008237362,47456368723⟩,⟨-117682103911,-113816633344⟩,⟨438945657651,439375154381⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes7 := wholeStep6.proposed :: wholeBoxes6

noncomputable def wholeStep7 : Instruction 40 := ⟨.log 7,⟨⟨-2527432537536,-2523162526272⟩,⟨10909882818222,10952333724170⟩,⟨0,0⟩,⟨-109097176396601,-108253100831767⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes8 := wholeStep7.proposed :: wholeBoxes7

noncomputable def wholeStep8 : Instruction 40 := ⟨.mul 8 0,⟨⟨-254717810425,-253301862988⟩,⟨-1432182582740,-1419372643130⟩,⟨0,0⟩,⟨10824815827704,11037070997671⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes9 := wholeStep8.proposed :: wholeBoxes8

noncomputable def wholeStep9 : Instruction 40 := ⟨.neg 0,⟨⟨253301862988,254717810425⟩,⟨1419372643130,1432182582740⟩,⟨0,0⟩,⟨-11037070997671,-10824815827704⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes10 := wholeStep9.proposed :: wholeBoxes9

noncomputable def wholeStep10 : Instruction 40 := ⟨.add 12 7,⟨⟨988701471539,989130968269⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes11 := wholeStep10.proposed :: wholeBoxes10

noncomputable def wholeStep11 : Instruction 40 := ⟨.log 0,⟨⟨-116799963776,-116322434240⟩,⟨-1222740993531,-1222210059533⟩,⟨0,0⟩,⟨-1359781469784,-1358600847764⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes12 := wholeStep11.proposed :: wholeBoxes11

noncomputable def wholeStep12 : Instruction 40 := ⟨.mul 1 0,⟨⟨-105074342413,-104599313914⟩,⟨-983666826738,-982234238194⟩,⟨0,0⟩,⟨1221147960896,1223802630987⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes13 := wholeStep12.proposed :: wholeBoxes12

noncomputable def wholeStep13 : Instruction 40 := ⟨.neg 0,⟨⟨104599313914,105074342413⟩,⟨982234238194,983666826738⟩,⟨0,0⟩,⟨-1223802630987,-1221147960896⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes14 := wholeStep13.proposed :: wholeBoxes13

noncomputable def wholeStep14 : Instruction 40 := ⟨.add 4 0,⟨⟨357901176902,359792152838⟩,⟨2401606881324,2415849409478⟩,⟨0,0⟩,⟨-12260873628658,-12045963788600⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes15 := wholeStep14.proposed :: wholeBoxes14

noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2148369011648,-2134216225408⟩,⟨6839541963563,6955424727378⟩,⟨3057747981961,3100391937303⟩,⟨-43999473871929,-42545556672254⟩,⟨-27371393931630,-26680134009529⟩,⟨-8742454306133,-8503614227435⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15

noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-308402541432,-302452593892⟩,⟨-956706698398,-907323675501⟩,⟨-425176574555,-406951853527⟩,⟨5898784601822,6441472924422⟩,⟨3665946287399,3926272905524⟩,⟨1186424370305,1272793145731⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16

noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨302452593892,308402541432⟩,⟨907323675501,956706698398⟩,⟨406951853527,425176574555⟩,⟨-6441472924422,-5898784601822⟩,⟨-3926272905524,-3665946287399⟩,⟨-1272793145731,-1186424370305⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17

noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-157837028230,-155818393599⟩,⟨-985694994432,-981829523865⟩,⟨-439375154381,-438945657651⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18

noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨941674599546,943693234177⟩,⟨-985694994432,-981829523865⟩,⟨-439375154381,-438945657651⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19

noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-170382088000,-168027626304⟩,⟨-1150910418888,-1143944810544⟩,⟨-513020199792,-511422395615⟩,⟨-1204711945596,-1190173615732⟩,⟨744055737320,751714347831⟩,⟨-239369660808,-237880946530⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20

noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-146236219435,-143906934420⟩,⟨-837764574607,-826984433014⟩,⟨-373237248468,-369920438398⟩,⟨1009028951681,1044224531953⟩,⟨1380231438743,1396985954789⟩,⟨202891669859,206282687855⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21

noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨143906934420,146236219435⟩,⟨826984433014,837764574607⟩,⟨369920438398,373237248468⟩,⟨-1044224531953,-1009028951681⟩,⟨-1396985954789,-1380231438743⟩,⟨-206282687855,-202891669859⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22

noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨446359528312,454638760867⟩,⟨1734308108515,1794471273005⟩,⟨776872291925,798413823023⟩,⟨-7485697456375,-6907813553503⟩,⟨-5323258860313,-5046177726142⟩,⟨-1479075833586,-1389316040164⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23

noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨804260705214,814430913705⟩,⟨4135914989839,4210320682483⟩,⟨776872291925,798413823023⟩,⟨-19746571085033,-18953777342103⟩,⟨-5323258860313,-5046177726142⟩,⟨-1479075833586,-1389316040164⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24

noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨90016474724,94912737446⟩,⟨-235364207822,-227633266688⟩,⟨877891315302,878750308762⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25

noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨12737234771070,13430050702623⟩,⟨30548253453971,35115274779691⟩,⟨-131105569706048,-117812509546959⟩,⟨146530358568506,183630360027213⟩,⟨-390490367009952,-237025214691944⟩,⟨2179403560540092,2559732764760164⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26

noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨9316915947653,9947915227569⟩,⟨70257447154938,77437821859236⟩,⟨-88112960073090,-76424143013713⟩,⟨95807188145029,185381091294405⟩,⟨-834719196828798,-649497833509046⟩,⟨1385698472268415,1713468828939861⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27

noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨83881035264,89509632256⟩,⟨-737297530537,-587106213089⟩,⟨638638194389,838937179667⟩,⟨6405675381843,11303775730047⟩,⟨-8345503196173,-940393521906⟩,⟨-6646203322088,4092115812368⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28

noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29

noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1183392663040,1189021260032⟩,⟨-737297530537,-587106213089⟩,⟨638638194389,838937179667⟩,⟨6405675381843,11303775730047⟩,⟨-8345503196173,-940393521906⟩,⟨-6646203322088,4092115812368⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30

noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨80835374528,86052608704⟩,⟨-685036533752,-542908802163⟩,⟨590561451065,779471778749⟩,⟨5496652362792,10234469908616⟩,⟨-7462355563713,-383960774172⟩,⟨-6727695664806,3484861219201⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31

noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨87002253285,93058025623⟩,⟨-798508497996,-627490629815⟩,⟨682567266172,908586343373⟩,⟨6966723510945,12871053682470⟩,⟨-9768388710056,-1113074194889⟩,⟨-7109507453384,5278313465218⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32

noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-89509632256,-83881035264⟩,⟨587106213089,737297530537⟩,⟨-838937179667,-638638194389⟩,⟨-11303775730047,-6405675381843⟩,⟨940393521906,8345503196173⟩,⟨-4092115812368,6646203322088⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33

noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1010001995520,1015630592512⟩,⟨587106213089,737297530537⟩,⟨-838937179667,-638638194389⟩,⟨-11303775730047,-6405675381843⟩,⟨940393521906,8345503196173⟩,⟨-4092115812368,6646203322088⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34

noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-93363710336,-87253299328⟩,⟨635595375710,802639214133⟩,⟨-913286496571,-691383388654⟩,⟨-12891476275502,-7302139788677⟩,⟨1417729148512,9751804180704⟩,⟨-5213374764529,6800462819478⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35

noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-86241052894,-80150135942⟩,⟨521245751530,694815741077⟩,⟨-792932420254,-563861535171⟩,⟨-10720884700617,-4671388063962⟩,⟨-631176254596,8194863089055⟩,⟨-4576840569792,8022828472707⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36

noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨761200391,12907889681⟩,⟨-277262746466,67325111262⟩,⟨-110365154082,344724808202⟩,⟨-3754161189672,8199665618508⟩,⟨-10399564964652,7081788894166⟩,⟨-11686348023176,13301141937925⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37

noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨380600195,6453944841⟩,⟨-138631373233,33662555631⟩,⟨-55182577041,172362404101⟩,⟨-1877080594836,4099832809254⟩,⟨-5199782482326,3540894447083⟩,⟨-5843174011588,6650570968963⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38

noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-6453944841,-380600195⟩,⟨-33662555631,138631373233⟩,⟨-172362404101,55182577041⟩,⟨-4099832809254,1877080594836⟩,⟨-3540894447083,5199782482326⟩,⟨-6650570968963,5843174011588⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39

noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨755669438775,761742802685⟩,⟨-33662555631,138631373233⟩,⟨-172362404101,55182577041⟩,⟨-4099832809254,1877080594836⟩,⟨-3540894447083,5199782482326⟩,⟨-6650570968963,5843174011588⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40

noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨6399230257,7286848147⟩,⟨-120044625550,-89579911152⟩,⟨97442594604,136593295680⟩,⟨1604363911686,2829264225944⟩,⟨-2483919584712,-825511295286⟩,⟨-340224636469,1946499420124⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41

noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-7286848147,-6399230257⟩,⟨89579911152,120044625550⟩,⟨-136593295680,-97442594604⟩,⟨-2829264225944,-1604363911686⟩,⟨825511295286,2483919584712⟩,⟨-1946499420124,340224636469⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42

noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1092224779629,1093112397519⟩,⟨89579911152,120044625550⟩,⟨-136593295680,-97442594604⟩,⟨-2829264225944,-1604363911686⟩,⟨825511295286,2483919584712⟩,⟨-1946499420124,340224636469⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43

noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-7311101632,-6417924736⟩,⟨90104324267,120845511022⟩,⟨-137504586673,-98013036949⟩,⟨-2861421775890,-1621140074402⟩,⟨838376062011,2515604117134⟩,⟨-1976681898103,333757355853⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44

noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3655550816,-3208962368⟩,⟨45052162133,60422755511⟩,⟨-68752293337,-49006518474⟩,⟨-1430710887945,-810570037201⟩,⟨419188031005,1257802058567⟩,⟨-988340949052,166878677927⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45

noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3208962368,3655550816⟩,⟨-60422755511,-45052162133⟩,⟨49006518474,68752293337⟩,⟨810570037201,1430710887945⟩,⟨-1257802058567,-419188031005⟩,⟨-166878677927,988340949052⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46

noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765332345984,765778953696⟩,⟨-60422755511,-45052162133⟩,⟨49006518474,68752293337⟩,⟨810570037201,1430710887945⟩,⟨-1257802058567,-419188031005⟩,⟨-166878677927,988340949052⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47

noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48

noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49

noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨273056194907,273278099380⟩,⟨22394977788,30011156388⟩,⟨-34148323920,-24360648651⟩,⟨-707316056486,-401090977921⟩,⟨206377823821,620979896178⟩,⟨-486624855031,85056159118⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50

noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1530664691968,1531557907392⟩,⟨-120845511022,-90104324266⟩,⟨98013036948,137504586674⟩,⟨1621140074402,2861421775890⟩,⟨-2515604117134,-838376062010⟩,⟨-333757355854,1976681898104⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51

noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1190320406383,1196953892148⟩,⟨-873771688336,-688089263267⟩,⟨748484813948,994224889580⟩,⟨8302988457700,14671810390393⟩,⟨-11341820803510,-1967496630397⟩,⟨-6935110260113,6501233094096⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52

noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1281129184990,1294396156520⟩,⟨-1747543376672,-1376178526534⟩,⟨1496969627896,1988449779160⟩,⟨16605976915405,29343620780775⟩,⟨-22683641607011,-3934993260795⟩,⟨-13865401792016,13002466188188⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53

noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨168088673856,179416319040⟩,⟨-1499805238385,-1168980828780⟩,⟨1271585599205,1706559868476⟩,⟨12059946198646,23940922591561⟩,⟨-18115998883369,-1014681488390⟩,⟨-14548555529051,9688599832879⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54

noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨57649535703,62012366600⟩,⟨-513540917655,-392219025623⟩,⟨424889795365,585708886042⟩,⟨3882790638657,8029224079624⟩,⟨-6132720865526,-1646766528⟩,⟨-5408937946287,3394915944146⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55

noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380130110413,380661034817⟩,⟨1141206854,19427061441⟩,⟨-23225828594,262850644⟩,⟨-589249417562,149150162169⟩,⟨-333943047941,664291507055⟩,⟨-769335950147,605429689087⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56

noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3175859121477,3180294816165⟩,⟨-162533251384,-9521101098⟩,⟨-2199095830,194314999668⟩,⟨-1247782729653,4946469389073⟩,⟨-5577544943445,2794103279657⟩,⟨-5065494683675,6460265368680⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57

noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨166516478030,179368369606⟩,⟨-1494564084967,-1133395250870⟩,⟨1227139147063,1705099627595⟩,⟨11151575400149,23655026726846⟩,⟨-18230569378136,150178462166⟩,⟨-15933180006694,10391044240218⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58

noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨334605151886,358784688646⟩,⟨-2994369323352,-2302376079650⟩,⟨2498724746268,3411659496071⟩,⟨23211521598795,47595949318407⟩,⟨-36346568261505,-864503026224⟩,⟨-30481735535745,20079644073097⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59

noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨519354490005,527736208317⟩,⟨-46642907314,192087919980⟩,⟨-238825706724,76461093878⟩,⟨-5689225546987,2635845322986⟩,⟨-4949735188180,7218744791088⟩,⟨-9232346148560,8150354090525⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60

noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨356940578046,365616195634⟩,⟨-48471382265,199618067010⟩,⟨-248188048127,79458488400⟩,⟨-5921073511986,2775503547908⟩,⟨-5188940882111,7516191720439⟩,⟨-9612247934265,8526019165537⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61

noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨713881156092,731232391268⟩,⟨-96942764530,399236134020⟩,⟨-496376096254,158916976800⟩,⟨-11842147023972,5551007095816⟩,⟨-10377881764222,15032383440878⟩,⟨-19224495868530,17052038331074⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62

noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523377843821,1525158677135⟩,⟨-31265599870,29940301284⟩,⟨-38580258732,40061992070⟩,⟨-1208124151542,1257057864204⟩,⟨-1690092821848,1645543522702⟩,⟨-2280256775978,2316906534573⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63

noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨989085252796,1014309806619⟩,⟨-155264859011,573701774675⟩,⟨-714192942881,247080817983⟩,⟨-17252693866105,8557685366485⟩,⟨-15546930919108,21974809405187⟩,⟨-28219415919833,25228984637162⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64

noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67811638998,67921900701⟩,⟨11123279218,14918244740⟩,⟨-16974789212,-12099601054⟩,⟨-350687428269,-197578095565⟩,⟨100640886730,307690515176⟩,⟨-240816869867,44401701474⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65

noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨49602237233,50311151107⟩,⟨263216125500,271141164386⟩,⟨35339499226,40471196126⟩,⟨-1395915613599,-1199232262018⟩,⟨-312368036124,-117987750330⟩,⟨-294399940649,-69894094005⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66

noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2130886422708,2133374094861⟩,⟨-336662011212,-250874123134⟩,⟨272894058086,383072323572⟩,⟨4528448083641,7998163318522⟩,⟨-7038416132690,-2350323548256⟩,⟨-912336258074,5541206160701⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67

noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2966473957561,2971670223278⟩,⟨-703426892947,-523874626755⟩,⟨569856591974,800397328391⟩,⟨9487130820680,16766990985911⟩,⟨-14769331466013,-4941484173354⟩,⟨-1869767180695,11649743528457⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68

noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨133826456466,135976869973⟩,⟨677967877710,709184651891⟩,⟨121053622924,146006604485⟩,⟨-3691706227203,-2719124637446⟩,⟨-1409525741389,-360713840826⟩,⟨-844604786238,403414625797⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69

noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8890672508160,9033533813412⟩,⟨-47871278235917,-44328056477315⟩,⟨-9855716376470,-7914935220653⟩,⟨619817498542236,756564189839287⟩,⟨102511054256721,199602116997447⟩,⟨-13138667710015,78517847208427⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70

noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7997762682189,8333519813613⟩,⟨-45437352422586,-35162586360892⟩,⟨-14959765276876,-5090016911424⟩,⟨365864142860402,781767150097389⟩,⟨-51417255871408,397165553289502⟩,⟨-248399414284850,292517210602636⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71

noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15995525364378,16667039627226⟩,⟨-90874704845172,-70325172721784⟩,⟨-29919530553752,-10180033822848⟩,⟨731728285720804,1563534300194778⟩,⟨-102834511742816,794331106579004⟩,⟨-496798828569700,585034421205272⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72

noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10909882818222,10952333724170⟩,⟨-109097176396601,-108253100831767⟩,⟨0,0⟩,⟨2148278590145760,2173453475298114⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73

noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9810371190446,9852822096394⟩,⟨-109097176396601,-108253100831767⟩,⟨0,0⟩,⟨2148278590145775,2173453475298112⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74

noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2406362562496,2411110103296⟩,⟨-12227224809080,-12080350374972⟩,⟨0,0⟩,⟨103760055435140,110865974497594⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75

noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7659329582998,7758556558643⟩,⟨-49080023142543,-47645067839474⟩,⟨-21877500511915,-21300638377931⟩,⟨592754878825722,620952790242680⟩,⟨318358206399436,331537936236802⟩,⟨118474388754478,123379916104533⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76

noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6559817955222,6659044930867⟩,⟨-49080023142544,-47645067839474⟩,⟨-21877500511915,-21300638377931⟩,⟨592754878825727,620952790242673⟩,⟨318358206399438,331537936236800⟩,⟨118474388754478,123379916104533⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77

noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1963834137472,1980341384576⟩,⟨-8226456359793,-7866939874927⟩,⟨-3666956364302,-3517065858345⟩,⟨36323350794800,47792357666682⟩,⟨25130010382049,30405715946390⟩,⟨7332376375186,9429869934227⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78

noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨99256358666,99685855397⟩,⟨877891315302,878750308762⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79

noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨133450360767,135468995399⟩,⟨699387560457,706865283074⟩,⟨312861000334,314903039183⟩,⟨-1767320322048,-1753486165276⟩,⟨-1575660761910,-1567767081776⟩,⟨-351156861666,-350470673530⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80

noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4370196699968,4391451487872⟩,⟨-20453681168873,-19947290249899⟩,⟨-3666956364302,-3517065858345⟩,⟨140083406229940,158658332164276⟩,⟨25130010382049,30405715946390⟩,⟨7332376375186,9429869934227⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81

noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨669210303772,717569377292⟩,⟨-5988738646704,-4604752159300⟩,⟨4997449492536,6823318992142⟩,⟨46423043197590,95191898636814⟩,⟨-72693136523010,-1729006052448⟩,⟨-60963471071490,40159288146194⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82

noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5039407003740,5109020865164⟩,⟨-26442419815577,-24552042409199⟩,⟨1330493128234,3306253133797⟩,⟨186506449427530,253850230801090⟩,⟨-47563126140961,28676709893942⟩,⟨-53631094696304,49589158080421⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83

noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨454923055283,463203027889⟩,⟨1626282396293,1866835496353⟩,⟨120107782221,299757331779⟩,⟨-35648075765859,-26270341007336⟩,⟨-3249936119003,5242357763491⟩,⟨-4862396554635,4495939394168⟩⟩⟩
noncomputable def wholeBoxes85 := wholeStep84.proposed :: wholeBoxes84

noncomputable def wholeStep85 : Instruction 40 := ⟨.mul 88 85,⟨⟨220761319014,221620312474⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes86 := wholeStep85.proposed :: wholeBoxes85

noncomputable def wholeStep86 : Instruction 40 := ⟨.neg 0,⟨⟨-221620312474,-220761319014⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes87 := wholeStep86.proposed :: wholeBoxes86

noncomputable def wholeStep87 : Instruction 40 := ⟨.add 89 0,⟨⟨877891315302,878750308762⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes88 := wholeStep87.proposed :: wholeBoxes87

noncomputable def wholeStep88 : Instruction 40 := ⟨.mul 12 0,⟨⟨1921330108492,1927004402870⟩,⟨-14594447534479,-14458129877504⟩,⟨0,0⟩,⟨131167320761344,137515064791860⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes89 := wholeStep88.proposed :: wholeBoxes88

noncomputable def wholeStep89 : Instruction 40 := ⟨.neg 91,⟨⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes90 := wholeStep89.proposed :: wholeBoxes89

noncomputable def wholeStep90 : Instruction 40 := ⟨.add 1 0,⟨⟨821818480716,827492775094⟩,⟨-14594447534479,-14458129877504⟩,⟨0,0⟩,⟨131167320761344,137515064791860⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes91 := wholeStep90.proposed :: wholeBoxes90

noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨33640936861,35715677087⟩,⟨-718483146784,-676911035071⟩,⟨328085346598,330673870673⟩,⟨8362586632920,9059455080463⟩,⟨-6659570832821,-6593775017748⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91

noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨488563992144,498918704976⟩,⟨907799249509,1189924461282⟩,⟨448193128819,630431202452⟩,⟨-27285489132939,-17210885926873⟩,⟨-9909506951824,-1351417254257⟩,⟨-4862396554635,4495939394168⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92

noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨501398014948,502387228948⟩,⟨2512147284185,2552733193796⟩,⟨0,0⟩,⟨2027158573049,4364694834823⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93

noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨222794384022,227965197759⟩,⟨1530237066335,1702036744936⟩,⟨204384509837,288055693857⟩,⟨-7418233283127,-342658316890⟩,⟨-3503812501018,847398703858⟩,⟨-2221719051822,2054277987331⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94

noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-717569377292,-669210303772⟩,⟨4604752159300,5988738646704⟩,⟨-6823318992142,-4997449492536⟩,⟨-95191898636814,-46423043197590⟩,⟨1729006052448,72693136523010⟩,⟨-40159288146194,60963471071490⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95

noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3652627322676,3722241184100⟩,⟨-15848929009573,-13958551603195⟩,⟨-10490275356444,-8514515350881⟩,⟨44891507593126,112235288966686⟩,⟨26859016434497,103098852469400⟩,⟨-32826911771008,70393341005717⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96

noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨443328130093,458611133439⟩,⟨370676954286,698809636595⟩,⟨-253150961705,32632593607⟩,⟨-20912666501401,-9754607471341⟩,⟨-13357504321348,-1893389203525⟩,⟨-11242226242271,2663234091252⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97

noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨311636787198,315674056460⟩,⟨1963659047730,1971389988864⟩,⟨877891315302,878750308762⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98

noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-315674056460,-311636787198⟩,⟨-1971389988864,-1963659047730⟩,⟨-878750308762,-877891315302⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99

noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨783837571316,787874840578⟩,⟨-1971389988864,-1963659047730⟩,⟨-878750308762,-877891315302⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100

noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1400009733318,1419049251729⟩,⟨-9445505541481,-9115595928541⟩,⟨-4210349528950,-4075301416872⟩,⟨53994501646003,63746032174577⟩,⟨34405274738457,38897921963244⟩,⟨10843537197318,12618543538152⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101

noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1419049251729,-1400009733318⟩,⟨9115595928541,9445505541481⟩,⟨4075301416872,4210349528950⟩,⟨-63746032174577,-53994501646003⟩,⟨-38897921963244,-34405274738457⟩,⟨-12618543538152,-10843537197318⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102

noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-319537623953,-300498105542⟩,⟨9115595928541,9445505541481⟩,⟨4075301416872,4210349528950⟩,⟨-63746032174577,-53994501646003⟩,⟨-38897921963244,-34405274738457⟩,⟨-12618543538152,-10843537197318⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103

noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-13791664336,-12300815852⟩,⟨404250920788,441880960005⟩,⟨39131228402,61759748078⟩,⟨-4773291163251,-4097464830326⟩,⟨1810090446167,2263821379057⟩,⟨2709240530944,2921112766255⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104

noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨429536465757,446310317587⟩,⟨774927875074,1140690596600⟩,⟨-214019733303,94392341685⟩,⟨-25685957664652,-13852072301667⟩,⟨-11547413875181,370432175532⟩,⟨-8532985711327,5584346857507⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105

noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-99685855397,-99256358666⟩,⟨-878750308762,-877891315302⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106

noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4063034567,4302572698⟩,⟨25266762807,27653435689⟩,⟨39624999436,39835402372⟩,⟨-283020225417,-271767411095⟩,⟨250784818133,251900503000⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107

noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨8892251819,9435076666⟩,⟨7451006657,16000373786⟩,⟨86722243560,87354729775⟩,⟨-852252726745,-716158596200⟩,⟨105867709348,117030113883⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108

noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1484381055865,1503151666838⟩,⟨-7869028675367,-7538114966259⟩,⟨-1492223928291,-1415926745356⟩,⟨111106579906440,119295097951105⟩,⟨23578127499010,25572737586103⟩,⟨5233424776280,5727122682435⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109

noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨12004866352,12898773291⟩,⟨-57466200552,-39089925842⟩,⟨104273211305,107972146445⟩,⟨-495576586925,-45317344971⟩,⟨-313286677583,-224715741982⟩,⟨-194785302533,-174212661079⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110

noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-12898773291,-12004866352⟩,⟨39089925842,57466200552⟩,⟨-107972146445,-104273211305⟩,⟨45317344971,495576586925⟩,⟨224715741982,313286677583⟩,⟨174212661079,194785302533⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111

noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-112584628688,-111261225018⟩,⟨-839660382920,-820425114750⟩,⟨-107972146445,-104273211305⟩,⟨2244340600523,2694599842477⟩,⟨224715741982,313286677583⟩,⟨174212661079,194785302533⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112

noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨80389066169,85474140128⟩,⟨-567023095658,-525318762061⟩,⟨625728747467,647392759316⟩,⟨3115589804039,3823756862292⟩,⟨-3874948420136,-3399634405590⟩,⟨-2630551262907,-2401151675965⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113

noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨108528190066,116852421530⟩,⟨-1386906816192,-1260337050103⟩,⟨728753858948,781532868535⟩,⟨19532583911830,22617472876529⟩,⟨-7530389509362,-6122022530231⟩,⟨-4970859043006,-4408025516681⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114

noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-116852421530,-108528190066⟩,⟨1260337050103,1386906816192⟩,⟨-781532868535,-728753858948⟩,⟨-22617472876529,-19532583911830⟩,⟨6122022530231,7530389509362⟩,⟨4408025516681,4970859043006⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115

noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨982659206246,990983437710⟩,⟨1260337050103,1386906816192⟩,⟨-781532868535,-728753858948⟩,⟨-22617472876529,-19532583911830⟩,⟨6122022530231,7530389509362⟩,⟨4408025516681,4970859043006⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116

noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨119267702379,122097417956⟩,⟨778029115318,807972047661⟩,⟨183319816352,195369676412⟩,⟨-2776162898660,-2154590342459⟩,⟨-820906048209,-539682029247⟩,⟨-229149181474,-115499711366⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117

noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11258689658,11528116936⟩,⟨166040087246,171954256868⟩,⟨21103124210,22111642496⟩,⟨672529215414,828224936549⟩,⟨91453506830,119430815350⟩,⟨-20112435531,-14051929023⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118

noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨163789678476,174749931648⟩,⟨1462725961634,1886473108671⟩,⟨-6694143236,230940513744⟩,⟨-11147517282690,7708029857152⟩,⟨-6254432279042,7251697257331⟩,⟨-6717081920143,5538746514216⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119

noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-174749931648,-163789678476⟩,⟨-1886473108671,-1462725961634⟩,⟨-230940513744,6694143236⟩,⟨-7708029857152,11147517282690⟩,⟨-7251697257331,6254432279042⟩,⟨-5538746514216,6717081920143⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120

noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨48044452374,64175519283⟩,⟨-356236042336,239310783302⟩,⟨-26556003907,294749837093⟩,⟨-15126263140279,10804858965800⟩,⟨-10755509758349,7101830982900⟩,⟨-7760465566038,8771359907474⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121

noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨28569555758954,30019171692551⟩,⟨-288376771055791,-240054588379357⟩,⟨-109474232520199,-69348256226725⟩,⟨2841708807684030,4900396004108821⟩,⟨478161616299303,2418514964737475⟩,⟨-722992234791246,1396222721768604⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122

noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨12937366437,13558546445⟩,⟨168790838812,179445670802⟩,⟨39770626784,43390415226⟩,⟨484518718677,720039297611⟩,⟨77120868200,170051138156⟩,⟨10236602397,44372291562⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123

noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨336162713025,370179198976⟩,⟨829740599347,2074681312064⟩,⟨-316579031899,368673246985⟩,⟨-48102459504558,6383924714582⟩,⟨-21616873652762,15137511590421⟩,⟨-17289979426121,13412066279151⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124

noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-370179198976,-336162713025⟩,⟨-2074681312064,-829740599347⟩,⟨-368673246985,316579031899⟩,⟨-6383924714582,48102459504558⟩,⟨-15137511590421,21616873652762⟩,⟨-13412066279151,17289979426121⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125

noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨59357266781,110147604562⟩,⟨-1299753436990,310949997253⟩,⟨-582692980288,410971373584⟩,⟨-32069882379234,34250387202891⟩,⟨-26684925465602,21987305828294⟩,⟨-21945051990478,22874326283628⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126

noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨232706719433,235154850796⟩,⟨1577278875759,1585615591836⟩,⟨312861000334,314903039183⟩,⟨-3966343577600,-3952509420828⟩,⟨-1575660761910,-1567767081776⟩,⟨-351156861666,-350470673530⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127

noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1706623577556,-1618611119599⟩,⟨-5611753303049,-2630291265114⟩,⟨-606572038653,1546663444661⟩,⟨-22498575914367,105597606162104⟩,⟨-63801089096462,47051187913963⟩,⟨-55439386784389,59698648212638⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128

noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-189515351160,-175576159817⟩,⟨-1877274130541,-1430667337629⟩,⟨-370603971377,-98116179424⟩,⟨-7574138867143,12312897288819⟩,⟨-7733317567654,7197088499782⟩,⟨-6201906606418,7534676543866⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129

noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨43191368273,59578690979⟩,⟨-299995254782,154948254207⟩,⟨-57742971043,216786859759⟩,⟨-11540482444743,8360387867991⟩,⟨-9308978329564,5629321418006⟩,⟨-6553063468084,7184205870336⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130

noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2593685509,6429017704⟩,⟨-111550342336,42123144405⟩,⟨-36670557902,53514931835⟩,⟨-3952948674961,3923745460194⟩,⟨-3116581423423,2266938410837⟩,⟨-2370715375581,2434156650352⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131

noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1696657175,3228360965⟩,⟨-32511388018,16792208326⟩,⟨-6257779438,23493843994⟩,⟨-1335230223637,1069744245150⟩,⟨-1127140007984,671167702676⟩,⟨-732945155863,864060210084⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132

noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨3030393854,5814633208⟩,⟨-82710919519,18105133771⟩,⟨-22037782750,36887810457⟩,⟨-2600121782977,2553548993959⟩,⟨-2223107339099,1453371619151⟩,⟨-1465507827840,1625695608773⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133

noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5814633208,-3030393854⟩,⟨-18105133771,82710919519⟩,⟨-36887810457,22037782750⟩,⟨-2553548993959,2600121782977⟩,⟨-1453371619151,2223107339099⟩,⟨-1625695608773,1465507827840⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134

noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3220947699,3398623850⟩,⟨-129655476107,124834063924⟩,⟨-73558368359,75552714585⟩,⟨-6506497668920,6523867243171⟩,⟨-4569953042574,4490045749936⟩,⟨-3996410984354,3899664478192⟩⟩⟩


noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]

noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨48044452374,64175519283⟩,⟨-356236042336,239310783302⟩,⟨-26556003907,294749837093⟩,⟨-15126263140279,10804858965800⟩,⟨-10755509758349,7101830982900⟩,⟨-7760465566038,8771359907474⟩⟩

noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3220947699,3398623850⟩,⟨-129655476107,124834063924⟩,⟨-73558368359,75552714585⟩,⟨-6506497668920,6523867243171⟩,⟨-4569953042574,4490045749936⟩,⟨-3996410984354,3899664478192⟩⟩



attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (103/1024) u, BivariateJet2.affineZ (539/5120) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet


noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet























end GeneralCK.Certificates.LaneCB.RB2Cell000003

end

section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell000004Endpoints
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



noncomputable def out_w4 : DyadicInterval 40 := ⟨-2133161707584,-2133161668480⟩



noncomputable def out_w5 : DyadicInterval 40 := ⟨-2133161707584,-2133161668480⟩



noncomputable def out_w6 : DyadicInterval 40 := ⟨-170558944576,-170558944512⟩



noncomputable def out_w7 : DyadicInterval 40 := ⟨-170558944576,-170558944512⟩



noncomputable def out_w8 : DyadicInterval 40 := ⟨762123383616,762123402880⟩



noncomputable def out_w9 : DyadicInterval 40 := ⟨86052289792,86052289856⟩



noncomputable def out_w10 : DyadicInterval 40 := ⟨-93363334912,-93363334848⟩



noncomputable def out_w11 : DyadicInterval 40 := ⟨86052413568,86052413632⟩



noncomputable def out_w12 : DyadicInterval 40 := ⟨-93363480704,-93363480640⟩



noncomputable def out_w13 : DyadicInterval 40 := ⟨-7311067072,-7311067008⟩



noncomputable def out_w14 : DyadicInterval 40 := ⟨-7311045120,-7311045056⟩



noncomputable def out_w15 : DyadicInterval 40 := ⟨179415624704,179415624768⟩



noncomputable def out_w16 : DyadicInterval 40 := ⟨179415894272,179415894336⟩



noncomputable def out_w17 : DyadicInterval 40 := ⟨2413489943680,2413490001536⟩



noncomputable def out_w18 : DyadicInterval 40 := ⟨2413489943680,2413490001536⟩



noncomputable def out_w19 : DyadicInterval 40 := ⟨1962602723904,1962602762560⟩



noncomputable def out_w20 : DyadicInterval 40 := ⟨1962602723968,1962602762560⟩



noncomputable def out_w21 : DyadicInterval 40 := ⟨-2531719137984,-2531719080128⟩



noncomputable def out_w22 : DyadicInterval 40 := ⟨-2527432537536,-2527432479680⟩



noncomputable def out_w23 : DyadicInterval 40 := ⟨-116322434304,-116322434240⟩



noncomputable def out_w24 : DyadicInterval 40 := ⟨-115845112128,-115845112064⟩



noncomputable def out_w25 : DyadicInterval 40 := ⟨-2140216458112,-2140216418880⟩



noncomputable def out_w26 : DyadicInterval 40 := ⟨-2126146712960,-2126146673920⟩



noncomputable def out_w27 : DyadicInterval 40 := ⟨-171740465088,-171740465024⟩



noncomputable def out_w28 : DyadicInterval 40 := ⟨-169379573120,-169379573056⟩



noncomputable def out_w29 : DyadicInterval 40 := ⟨83448312512,83448312576⟩



noncomputable def out_w30 : DyadicInterval 40 := ⟨-90305696512,-90305696448⟩



noncomputable def out_w31 : DyadicInterval 40 := ⟨88679327232,88679327296⟩



noncomputable def out_w32 : DyadicInterval 40 := ⟨-96464069120,-96464069056⟩



noncomputable def out_w33 : DyadicInterval 40 := ⟨-7784741888,-7784741824⟩



noncomputable def out_w34 : DyadicInterval 40 := ⟨-6857383936,-6857383872⟩



noncomputable def out_w35 : DyadicInterval 40 := ⟨173754009024,173754009088⟩



noncomputable def out_w36 : DyadicInterval 40 := ⟨185143396352,185143396416⟩



noncomputable def out_w37 : DyadicInterval 40 := ⟨2411110045440,2411110103296⟩



noncomputable def out_w38 : DyadicInterval 40 := ⟨2415873968064,2415874025920⟩



noncomputable def out_w39 : DyadicInterval 40 := ⟨1954406208960,1954406247552⟩



noncomputable def out_w40 : DyadicInterval 40 := ⟨1970836845824,1970836884416⟩



end LaneCBRB2Cell000004Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000004
open Set LaneCBRB2Cell000004Endpoints
open BivariateJetProgram (zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
















































noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨110165911142,110165911143⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨119614839193,119614839194⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0

noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1

noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-110165911143,-110165911142⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2

noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨439589902745,439589902746⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3

noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨47822573403,47822573405⟩,⟨-119614839194,-119614839193⟩,⟨439589902745,439589902746⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4

noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨157988484545,157988484548⟩,⟨979896788582,979896788583⟩,⟨439589902745,439589902746⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5

noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨47822573402,47822573406⟩,⟨-119614839194,-119614839193⟩,⟨439589902745,439589902746⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2133161707584,-2133161668480⟩,⟨6819534449923,6819534450061⟩,⟨3059300245228,3059300245295⟩,⟨-42297006180486,-42297006178783⟩,⟨-26626778004771,-26626778003836⟩,⟨-8512250124893,-8512250124528⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15

noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-306513343710,-306513338084⟩,⟨-921200256694,-921200221802⟩,⟨-413258147153,-413258131497⟩,⟨6077643690181,6077643690802⟩,⟨3760131880211,3760131919649⟩,⟨1223122578457,1223122578593⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16

noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨306513338084,306513343710⟩,⟨921200221802,921200256694⟩,⟨413258131497,413258147153⟩,⟨-6077643690802,-6077643690181⟩,⟨-3760131919649,-3760131880211⟩,⟨-1223122578593,-1223122578457⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17

noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-157988484548,-157988484545⟩,⟨-979896788583,-979896788582⟩,⟨-439589902746,-439589902745⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18

noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨941523143228,941523143231⟩,⟨-979896788583,-979896788582⟩,⟨-439589902746,-439589902745⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19

noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-170558944576,-170558944512⟩,⟨-1144324407550,-1144324407542⟩,⟨-513353509151,-513353509146⟩,⟨-1190963621152,-1190963621135⟩,⟨749734480412,749734480427⟩,⟨-239680798912,-239680798907⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20

noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-146051382766,-146051382710⟩,⟨-827892791751,-827892791682⟩,⟨-371399637239,-371399637205⟩,⟨1019834428035,1019834428071⟩,⟨1386458945344,1386458945434⟩,⟨205241139296,205241139308⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21

noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨146051382710,146051382766⟩,⟨827892791682,827892791751⟩,⟨371399637205,371399637239⟩,⟨-1019834428071,-1019834428035⟩,⟨-1386458945434,-1386458945344⟩,⟨-205241139308,-205241139296⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22

noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨452564720794,452564726476⟩,⟨1749093013484,1749093048445⟩,⟨784657768702,784657784392⟩,⟨-7097478118873,-7097478118216⟩,⟨-5146590865083,-5146590825555⟩,⟨-1428363717901,-1428363717753⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23

noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨810468847121,810468858662⟩,⟨4162582957151,4162583050058⟩,⟨784657768702,784657784392⟩,⟨-19293106187086,-19293106185909⟩,⟨-5146590865083,-5146590825555⟩,⟨-1428363717901,-1428363717753⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24

noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨95645146804,95645146812⟩,⟨-239229678388,-239229678386⟩,⟨879179805490,879179805492⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25

noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨12639698509647,12639698510705⟩,⟨31614683129739,31614683135297⟩,⟨-116185379493348,-116185379473631⟩,⟨158150637632850,158150637675210⟩,⟨-290605345952046,-290605345751256⟩,⟨2135975378388803,2135975378934911⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26

noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨9316938193542,9316938326995⟩,⟨71155690773628,71155692181610⟩,⟨-76622013040415,-76622011625218⟩,⟨134163748768626,134163755876839⟩,⟨-690672572607759,-690672558602827⟩,⟨1392214372335480,1392214398505390⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27

noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨89509287424,89509421312⟩,⟨-677086135026,-677084069168⟩,⟨729099006066,729101229667⟩,⟨8917765098239,8917816631094⟩,⟨-4405498907784,-4405427615113⟩,⟨-1426816433481,-1426720868839⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28

noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29

noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1189020915200,1189021049088⟩,⟨-677086135026,-677084069168⟩,⟨729099006066,729101229667⟩,⟨8917765098239,8917816631094⟩,⟨-4405498907784,-4405427615113⟩,⟨-1426816433481,-1426720868839⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30

noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨86052289792,86052413632⟩,⟨-626115208699,-626113227854⟩,⟨674212483945,674214616074⟩,⟨7889896021609,7889946859637⟩,⟨-3689925667806,-3689856854532⟩,⟨-1732830716950,-1732739583020⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31

noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨93057653760,93057798162⟩,⟨-730077825624,-730075369333⟩,⟨786161202682,786163846634⟩,⟨10001265835968,10001331603422⟩,⟨-5165480470180,-5165394370262⟩,⟨-1091409913924,-1091297955267⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32

noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-89509421312,-89509287424⟩,⟨677084069168,677086135026⟩,⟨-729101229667,-729099006066⟩,⟨-8917816631094,-8917765098239⟩,⟨4405427615113,4405498907784⟩,⟨1426720868839,1426816433481⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33

noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1010002206464,1010002340352⟩,⟨677084069168,677086135026⟩,⟨-729101229667,-729099006066⟩,⟨-8917816631094,-8917765098239⟩,⟨4405427615113,4405498907784⟩,⟨1426720868839,1426816433481⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34

noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-93363480704,-93363334848⟩,⟨737089190082,737091536734⟩,⟨-793716364890,-793713839009⟩,⟨-10202272306025,-10202211772949⟩,⟨5327938034416,5328019668308⟩,⟨980192313388,980300199910⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35

noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-85762925678,-85762780326⟩,⟨619590164242,619592674854⟩,⟨-667191008210,-667188305771⟩,⟨-7706679680915,-7706611614591⟩,⟨3542561686821,3542650055455⟩,⟨1831882212145,1831996299409⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36

noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨7294728082,7295017836⟩,⟨-110487661382,-110482694479⟩,⟨118970194472,118975540863⟩,⟨2294586155053,2294719988831⟩,⟨-1622918783359,-1622744314807⟩,⟨740472298221,740698344142⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37

noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨3647364041,3647508918⟩,⟨-55243830691,-55241347239⟩,⟨59485097236,59487770432⟩,⟨1147293077526,1147359994416⟩,⟨-811459391680,-811372157403⟩,⟨370236149110,370349172071⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38

noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-3647508918,-3647364041⟩,⟨55241347239,55243830691⟩,⟨-59487770432,-59485097236⟩,⟨-1147359994416,-1147293077526⟩,⟨811372157403,811459391680⟩,⟨-370349172071,-370236149110⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39

noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨758475874698,758476038839⟩,⟨55241347239,55243830691⟩,⟨-59487770432,-59485097236⟩,⟨-1147359994416,-1147293077526⟩,⟨811372157403,811459391680⟩,⟨-370349172071,-370236149110⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40

noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨7286792001,7286813801⟩,⟨-110240922596,-110240421340⟩,⟨118709308470,118709848076⟩,⟨2285861475827,2285877126743⟩,⟨-1615258936844,-1615240777898⟩,⟨734638610749,734660415729⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41

noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-7286813801,-7286792001⟩,⟨110240421340,110240922596⟩,⟨-118709848076,-118709308470⟩,⟨-2285877126743,-2285861475827⟩,⟨1615240777898,1615258936844⟩,⟨-734660415729,-734638610749⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42

noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1092224813975,1092224835775⟩,⟨110240421340,110240922596⟩,⟨-118709848076,-118709308470⟩,⟨-2285877126743,-2285861475827⟩,⟨1615240777898,1615258936844⟩,⟨-734660415729,-734638610749⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43

noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-7311067072,-7311045056⟩,⟨110975891724,110976398541⟩,⟨-119501824736,-119501279144⟩,⟨-2312328550652,-2312312647080⟩,⟨1638078378843,1638096801547⟩,⟨-752549935238,-752527851425⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44

noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3655533536,-3655522528⟩,⟨55487945862,55488199271⟩,⟨-59750912368,-59750639572⟩,⟨-1156164275326,-1156156323540⟩,⟨819039189421,819048400774⟩,⟨-376274967619,-376263925712⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45

noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3655522528,3655533536⟩,⟨-55488199271,-55487945862⟩,⟨59750639572,59750912368⟩,⟨1156156323540,1156164275326⟩,⟨-819048400774,-819039189421⟩,⟨376263925712,376274967619⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46

noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765778906144,765778936416⟩,⟨-55488199271,-55487945862⟩,⟨59750639572,59750912368⟩,⟨1156156323540,1156164275326⟩,⟨-819048400774,-819039189421⟩,⟨376263925712,376274967619⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47

noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48

noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49

noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨273056203493,273056208944⟩,⟨27560105335,27560230649⟩,⟨-29677462019,-29677327117⟩,⟨-571469281686,-571465368956⟩,⟨403810194474,403814734211⟩,⟨-183665103933,-183659652687⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50

noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1531557812288,1531557872832⟩,⟨-110976398542,-110975891724⟩,⟨119501279144,119501824736⟩,⟨2312312647080,2312328550652⟩,⟨-1638096801548,-1638078378842⟩,⟨752527851424,752549935238⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51

noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1196953483487,1196953642158⟩,⟨-802414796907,-802412135917⟩,⟨864055022697,864057886970⟩,⟨11644280886936,11644351753366⟩,⟨-6379452591506,-6379359189816⟩,⟨-443434652356,-443312845147⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52

noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1294395339198,1294395656540⟩,⟨-1604829593813,-1604824271834⟩,⟨1728110045394,1728115773941⟩,⟨23288561773877,23288703506728⟩,⟨-12758905183010,-12758718379634⟩,⟨-886869152804,-886625842203⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53

noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨179415624704,179415894336⟩,⟨-1363207009144,-1363202154227⟩,⟨1467926038986,1467931264934⟩,⟨18092094839083,18092232121170⟩,⟨-9017957260717,-9017782964376⟩,⟨-2713141814924,-2712920998388⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54

noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨61746172898,61746278621⟩,⟨-462577187155,-462575452083⟩,⟨498111412944,498113280560⟩,⟨5990296349852,5990342083588⟩,⟨-2899730310661,-2899669756307⟩,⟨-1093304517633,-1093225349329⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55

noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380351922697,380351945327⟩,⟨10829444331,10829746821⟩,⟨-11661709328,-11661383695⟩,⟨-227340965493,-227331472099⟩,⟨161665494664,161676478369⟩,⟨-75401075711,-75387925445⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56

noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3178439954014,3178440143125⟩,⟨-90499613600,-90497075049⟩,⟨97449239607,97451972381⟩,⟨1904866029207,1904945876356⟩,⟨-1356611439650,-1356519181760⟩,⟨635960412990,636070713960⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57

noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨178494249618,178494565860⟩,⟨-1342288592518,-1342283345992⟩,⟨1445400206692,1445405854060⟩,⟨17499713879029,17499854204074⟩,⟨-8540649150985,-8540465684575⟩,⟨-3036487841225,-3036249732941⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58

noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨357909874322,357910460196⟩,⟨-2705495601662,-2705485500219⟩,⟨2913326245678,2913337118994⟩,⟨35591808718112,35592086325244⟩,⟨-17558606411702,-17558248648951⟩,⟨-5749629656149,-5749170731329⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59

noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨523219252953,523219479413⟩,⟨76214253870,76217696684⟩,⟨-82072890068,-82069184204⟩,⟨-1577415709550,-1577322545348⟩,⟨1113439565366,1113560698594⟩,⟨-504519441579,-504362819283⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60

noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨360932227106,360932461435⟩,⟨78862294051,78865873553⟩,⟨-84924505093,-84920652090⟩,⟨-1626479171897,-1626381898987⟩,⟨1145940169080,1146066318646⟩,⟨-515388839426,-515226061349⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61

noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨721864454212,721864922870⟩,⟨157724588102,157731747106⟩,⟨-169849010186,-169841304180⟩,⟨-3252958343794,-3252763797974⟩,⟨2291880338160,2292132637292⟩,⟨-1030777678852,-1030452122698⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62

noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524270998487,1524271080831⟩,⟨-735977202,-734969128⟩,⟨791431068,792516266⟩,⟨26435520337,26467074825⟩,⟨-22856023650,-22819441998⟩,⟨17867435695,17911324489⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63

noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨1000732529422,1000733233193⟩,⟨218172989903,218183588509⟩,⟨-234944880848,-234933472359⟩,⟨-4492485133665,-4492194161373⟩,⟨3162492635932,3162866922490⟩,⟨-1417498384519,-1417017815088⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64

noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67811643262,67811645971⟩,⟨13688727868,13688790384⟩,⟨-14740390308,-14740323008⟩,⟨-282459361515,-282457399882⟩,⟨199079224212,199081496574⟩,⟨-89621886675,-89619162728⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65

noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨49985123347,49985126056⟩,⟨266814711751,266814773963⟩,⟨37527848130,37527900795⟩,⟨-1294448222443,-1294446250250⟩,⟨-216703866092,-216701873040⟩,⟨-175193933467,-175191824650⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66

noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2133373829911,2133373998580⟩,⟨-309167766110,-309166341950⟩,⟨332917111610,332918644732⟩,⟨6464244775327,6464289540163⟩,⟨-4587676694430,-4587624970136⟩,⟨2122434062638,2122495905731⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67

noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2971669669687,2971670022108⟩,⟨-645979970903,-645976969703⟩,⟨695602197717,695605428544⟩,⟨13553300864280,13553395359937⟩,⟨-9635966950866,-9635858036094⟩,⟨4488921818463,4489051707439⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68

noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨135095683604,135095706948⟩,⟨691757846708,691758238401⟩,⟨133050097892,133050400852⟩,⟨-3195894862246,-3195883258096⟩,⟨-877000982327,-876989594321⟩,⟨-221944303194,-221932344347⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69

noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8948662003596,8948663549891⟩,⟨-45821684069950,-45821642288805⟩,⟨-8813185148779,-8813162035112⟩,⟨680953098825774,680954715313642⟩,⟨148346915658518,148347993478141⟩,⟨32060098563406,32060983846459⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70

noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨8144722561884,8144729697087⟩,⟨-39929478320768,-39929324397481⟩,⟨-9933582951039,-9933463091396⟩,⟨565028222006544,565033403571177⟩,⟨168800222124320,168804922655806⟩,⟨21409396978963,21414329251514⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71

noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨16289445123768,16289459394174⟩,⟨-79858956641536,-79858648794962⟩,⟨-19867165902078,-19866926182792⟩,⟨1130056444013088,1130066807142354⟩,⟨337600444248640,337609845311612⟩,⟨42818793957926,42828658503028⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72

noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10973683302499,10973683302600⟩,⟨-109522921071186,-109522921069169⟩,⟨0,0⟩,⟨2186188521914400,2186188521974786⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73

noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9874171674723,9874171674824⟩,⟨-109522921071186,-109522921069170⟩,⟨0,0⟩,⟨2186188521914418,2186188521974777⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74

noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2413489943680,2413490001536⟩,⟨-12195628068220,-12195628067696⟩,⟨0,0⟩,⟨108164909937337,108164909975027⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75

noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7651986934828,7651986934974⟩,⟨-47460151576584,-47460151574723⟩,⟨-21291021318715,-21291021317853⟩,⟨588727086619464,588727086654377⟩,⟨317361455702733,317361455720761⟩,⟨118481014831342,118481014838667⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76

noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6552475307052,6552475307198⟩,⟨-47460151576585,-47460151574723⟩,⟨-21291021318716,-21291021317852⟩,⟨588727086619467,588727086654374⟩,⟨317361455702733,317361455720761⟩,⟨118481014831341,118481014838667⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77

noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1962602723904,1962602762560⟩,⟨-7963858857825,-7963858857253⟩,⟨-3572653754542,-3572653754280⟩,⟨41106042548124,41106042567358⟩,⟨27376512479712,27376512489065⟩,⟨8272569323664,8272569327621⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78

noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨99127803248,99127803250⟩,⟨879179805490,879179805492⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79

noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨135287168234,135287168238⟩,⟨698294657724,698294657733⟩,⟨313260829357,313260829362⟩,⟨-1746589471214,-1746589471210⟩,⟨-1567069317372,-1567069317360⟩,⟨-351500207392,-351500207389⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80

noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4376092667584,4376092764096⟩,⟨-20159486926045,-20159486924949⟩,⟨-3572653754542,-3572653754280⟩,⟨149270952485461,149270952542385⟩,⟨27376512479712,27376512489065⟩,⟨8272569323664,8272569327621⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81

noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨715819748644,715820920392⟩,⟨-5410991203324,-5410971000438⟩,⟨5826652491356,5826674237988⟩,⟨71183617436224,71184172650488⟩,⟨-35117212823404,-35116497297902⟩,⟨-11499259312298,-11498341462658⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82

noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5091912416228,5091913684488⟩,⟨-25570478129369,-25570457925387⟩,⟨2253998736814,2254020483708⟩,⟨220454569921685,220455125192873⟩,⟨-7740700343692,-7739984808837⟩,⟨-3226689988634,-3225772135037⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83

noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨459067534531,459067648883⟩,⟨1766203461242,1766206296927⟩,⟨203211987631,203213948254⟩,⟨-31201266530267,-31201181621517⟩,⟨1104446301105,1104528200057⟩,⟨-290906146204,-290823395994⟩⟩⟩
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

noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨36115014881,36115016897⟩,⟨-724423931876,-724423921735⟩,⟨331972847757,331972866257⟩,⟨9055589793453,9055589820657⟩,⟨-6658977614141,-6658977521421⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91

noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨495182549412,495182665780⟩,⟨1041779529366,1041782375192⟩,⟨535184835388,535186814511⟩,⟨-22145676736814,-22145591800860⟩,⟨-5554531313036,-5554449321364⟩,⟨-290906146204,-290823395994⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92

noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨500903595558,500903607567⟩,⟨2531120470889,2531120592376⟩,⟨0,0⟩,⟨3131155626176,3131158552760⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93

noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨225589901181,225589959604⟩,⟨1614532993408,1614534623858⟩,⟨243813709252,243814616725⟩,⟨-3882284325342,-3882230407206⟩,⟨-1298456009394,-1298413980692⟩,⟨-132527873664,-132490172041⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94

noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-715820920392,-715819748644⟩,⟨5410971000438,5410991203324⟩,⟨-5826674237988,-5826652491356⟩,⟨-71184172650488,-71183617436224⟩,⟨35116497297902,35117212823404⟩,⟨11498341462658,11499259312298⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95

noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3660271747192,3660273015452⟩,⟨-14748515925607,-14748495721625⟩,⟨-9399327992530,-9399306245636⟩,⟨78086779834973,78087335106161⟩,⟨62493009777614,62493725312469⟩,⟨19770910786322,19771828639919⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96

noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨450370680159,450370836224⟩,⟨509920256802,509923548312⟩,⟨-113676564299,-113673527106⟩,⟨-14939791754711,-14939695754401⟩,⟨-7698901811334,-7698792394165⟩,⟨-4093379861958,-4093254129141⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97

noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨315976969090,315976969096⟩,⟨1959793577164,1959793577166⟩,⟨879179805490,879179805492⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98

noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-315976969096,-315976969090⟩,⟨-1959793577166,-1959793577164⟩,⟨-879179805492,-879179805490⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99

noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨783534658680,783534658686⟩,⟨-1959793577166,-1959793577164⟩,⟨-879179805492,-879179805490⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100

noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1398591171344,1398591198903⟩,⟨-9173396138598,-9173396069240⟩,⟨-4115262304563,-4115262273442⟩,⟨57682926029337,57682926045337⟩,⟨36170225171236,36170225256312⟩,⟨11608658357513,11608658360812⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101

noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1398591198903,-1398591171344⟩,⟨9173396069240,9173396138598⟩,⟨4115262273442,4115262304563⟩,⟨-57682926045337,-57682926029337⟩,⟨-36170225256312,-36170225171236⟩,⟨-11608658360812,-11608658357513⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102

noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-299079571127,-299079543568⟩,⟨9173396069240,9173396138598⟩,⟨4115262273442,4115262304563⟩,⟨-57682926045337,-57682926029337⟩,⟨-36170225256312,-36170225171236⟩,⟨-11608658360812,-11608658357513⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103

noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-13008279661,-13008278461⟩,⟨431527731394,431527737444⟩,⟨59417354854,59417367244⟩,⟨-4504813271560,-4504813255544⟩,⟨1945749345821,1945749408341⟩,⟨2785690929612,2785690954692⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104

noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨437362400498,437362557763⟩,⟨941447988196,941451285756⟩,⟨-54259209445,-54256159862⟩,⟨-19444605026271,-19444509009945⟩,⟨-5753152465513,-5753042985824⟩,⟨-1307688932346,-1307563174449⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105

noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-99127803250,-99127803248⟩,⟨-879179805492,-879179805490⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106

noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4311502058,4311502060⟩,⟨27455357244,27455357251⟩,⟨39631760400,39631760401⟩,⟨-286935440430,-286935440419⟩,⟨252372404139,252372404144⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107

noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨9463989826,9463990058⟩,⟨12443481926,12443483413⟩,⟨86993946002,86993948090⟩,⟨-814755581627,-814755565976⟩,⟨114381737068,114381750391⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108

noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1491637595564,1491637616806⟩,⟨-7661078501174,-7661078111980⟩,⟨-1444133320704,-1444133250695⟩,⟨114203115761327,114203123649771⟩,⟨24306297605673,24306299209682⟩,⟨5425133517398,5425133823841⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109

noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨12839193940,12839194438⟩,⟨-49061059425,-49061052200⟩,⟨105588857925,105588863348⟩,⟨-295734894195,-295734735691⟩,⟨-258102647390,-258102560080⟩,⟨-181824643606,-181824623258⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110

noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-12839194438,-12839193940⟩,⟨49061052200,49061059425⟩,⟨-105588863348,-105588857925⟩,⟨295734735691,295734894195⟩,⟨258102560080,258102647390⟩,⟨181824623258,181824643606⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111

noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-111966997688,-111966997188⟩,⟨-830118753292,-830118746065⟩,⟨-105588863348,-105588857925⟩,⟨2494757991243,2494758149747⟩,⟨258102560080,258102647390⟩,⟨181824623258,181824643606⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112

noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨85362183038,85362184727⟩,⟨-559892795236,-559892790973⟩,⟨629267418932,629267434415⟩,⟨3520643195002,3520643196128⟩,⟨-3567200853534,-3567200814101⟩,⟨-2496917185732,-2496917185311⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113

noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨115805452386,115805456328⟩,⟨-1354349981720,-1354349923134⟩,⟨741569751380,741569792197⟩,⟨21444899023951,21444900337137⟩,⟨-6601512515465,-6601511859309⟩,⟨-4619220362034,-4619220160290⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114

noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-115805456328,-115805452386⟩,⟨1354349923134,1354349981720⟩,⟨-741569792197,-741569751380⟩,⟨-21444900337137,-21444899023951⟩,⟨6601511859309,6601512515465⟩,⟨4619220160290,4619220362034⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115

noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨983706171448,983706175390⟩,⟨1354349923134,1354349981720⟩,⟨-741569792197,-741569751380⟩,⟨-21444900337137,-21444899023951⟩,⟨6601511859309,6601512515465⟩,⟨4619220160290,4619220362034⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116

noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨121038121787,121038122277⟩,⟨791390384793,791390394520⟩,⟨189021860818,189021866972⟩,⟨-2480992458401,-2480992216039⟩,⟨-674849946630,-674849817610⟩,⟨-168676020617,-168675971247⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117

noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11401978971,11401979074⟩,⟨169067613216,169067615446⟩,⟨21504942848,21504944050⟩,⟨745361017075,745361073456⟩,⟨106869832626,106869860222⟩,⟨-16751714671,-16751708277⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118

noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨168922188777,168922338289⟩,⟨1676623883386,1676629310592⟩,⟨112575959553,112578744232⟩,⟨-1797825049892,-1797611972068⟩,⟨467395403272,467537729539⟩,⟨-581296235357,-581184202874⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119

noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-168922338289,-168922188777⟩,⟨-1676629310592,-1676623883386⟩,⟨-112578744232,-112575959553⟩,⟨1797611972068,1797825049892⟩,⟨-467537729539,-467395403272⟩,⟨581184202874,581296235357⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120

noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨56667562892,56667770827⟩,⟨-62096317184,-62089259528⟩,⟨131234965020,131238657172⟩,⟨-2084672353274,-2084405357314⟩,⟨-1765993738933,-1765809383964⟩,⟨448656329210,448806063316⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121

noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨29076281289955,29076307334995⟩,⟨-260532364705170,-260531709028274⟩,⟨-88391928282101,-88391453317412⟩,⟨3782963626323472,3782987157395681⟩,⟨1411579839139691,1411599723768705⟩,⟨328097614794761,328116889565436⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122

noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13324303768,13324303877⟩,⟨174238095088,174238097936⟩,⟨41616387552,41616389078⟩,⟨592997953560,592998037140⟩,⟨123523046218,123523087432⟩,⟨27854248506,27854263761⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123

noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨352357532711,352357851219⟩,⟨1450447113783,1450459287993⟩,⟨29366563492,29373354218⟩,⟨-21047340443591,-21046829494802⟩,⟨-3495868719841,-3495522919608⟩,⟨-1978638017794,-1978367142902⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124

noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-352357851219,-352357532711⟩,⟨-1450459287993,-1450447113783⟩,⟨-29373354218,-29366563492⟩,⟨21046829494802,21047340443591⟩,⟨3495522919608,3495868719841⟩,⟨1978367142902,1978638017794⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125

noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨85004549279,85005025052⟩,⟨-509011299797,-508995828027⟩,⟨-83632563663,-83622723354⟩,⟨1602224468531,1602831433646⟩,⟨-2257629545905,-2257174265983⟩,⟨670678210556,671074843345⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126

noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨234414971482,234414971488⟩,⟨1577474463214,1577474463225⟩,⟨313260829357,313260829362⟩,⟨-3945612726766,-3945612726762⟩,⟨-1567069317372,-1567069317360⟩,⟨-351500207392,-351500207389⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127

noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1658810890446,-1658809429834⟩,⟨-4166079287670,-4166037021229⟩,⟨458798755115,458824626344⟩,⟨42466452771876,42468009216862⟩,⟨-7887794625283,-7886621413171⟩,⟨2148115533930,2149168992486⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128

noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-182607759955,-182607598426⟩,⟨-1652571353826,-1652565633156⟩,⟨-234667269860,-234664161273⟩,⟨2420677177389,2420913114273⟩,⟨-236166461706,-236010300921⟩,⟨648698142108,648823310469⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129

noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨51807211527,51807373062⟩,⟨-75096890612,-75091169931⟩,⟨78593559497,78596668089⟩,⟨-1524935549377,-1524699612489⟩,⟨-1803235779078,-1803079618281⟩,⟨297197934716,297323103080⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130

noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4381036562,4381077160⟩,⟨-31034719253,-31033253087⟩,⟨5835589126,5836454335⟩,⟨-21106754183,-21045342975⟩,⟨-308921755495,-308878198627⟩,⟨49287225938,49322475878⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131

noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2441072107,2441087330⟩,⟨-7076910384,-7076349218⟩,⟨7406403094,7406719134⟩,⟨-133448740783,-133424495941⟩,⟨-180667983136,-180651494730⟩,⟨39242775280,39255546938⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132

noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4357257027,4357284286⟩,⟨-30313129925,-30312017743⟩,⟨5288408894,5289022745⟩,⟨-44432418358,-44380438862⟩,⟨-292362676184,-292328746839⟩,⟨40280274370,40305241237⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133

noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4357284286,-4357257027⟩,⟨30312017743,30313129925⟩,⟨-5289022745,-5288408894⟩,⟨44380438862,44432418358⟩,⟨292328746839,292362676184⟩,⟨-40305241237,-40280274370⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134

noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨23752276,23820133⟩,⟨-722701510,-720123162⟩,⟨546566381,548045441⟩,⟨23273684679,23387075383⟩,⟨-16593008656,-16515522443⟩,⟨8981984701,9042201508⟩⟩⟩


noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]

noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨56667562892,56667770827⟩,⟨-62096317184,-62089259528⟩,⟨131234965020,131238657172⟩,⟨-2084672353274,-2084405357314⟩,⟨-1765993738933,-1765809383964⟩,⟨448656329210,448806063316⟩⟩

noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨23752276,23820133⟩,⟨-722701510,-720123162⟩,⟨546566381,548045441⟩,⟨23273684679,23387075383⟩,⟨-16593008656,-16515522443⟩,⟨8981984701,9042201508⟩⟩

noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨109951162777,110380659508⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨117682103910,121547574477⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0

noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1

noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-110380659508,-109951162777⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2

noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨439375154380,439804651111⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3

noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨47026871992,48619029791⟩,⟨-121547574477,-117682103910⟩,⟨439375154380,439804651111⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4

noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨156978034769,158999689299⟩,⟨977964053299,981829523866⟩,⟨439375154380,439804651111⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5

noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨46597375261,49048526522⟩,⟨-121547574477,-117682103910⟩,⟨439375154380,439804651111⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2140216458112,-2126146673920⟩,⟨6762798423630,6876968357854⟩,⟨3038358712061,3080496762227⟩,⟨-43012454439053,-41596142653965⟩,⟨-26968413097871,-26291443961105⟩,⟨-8630613867433,-8396112810403⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15

noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-309495364375,-303551429626⟩,⟨-945617011857,-896633707195⟩,⟨-422298010671,-404159432042⟩,⟨5810380229593,6343125650416⟩,⟨3631216613693,3888143524869⟩,⟨1180245574655,1265678582826⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16

noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨303551429626,309495364375⟩,⟨896633707195,945617011857⟩,⟨404159432042,422298010671⟩,⟨-6343125650416,-5810380229593⟩,⟨-3888143524869,-3631216613693⟩,⟨-1265678582826,-1180245574655⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17

noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-158999689299,-156978034769⟩,⟨-981829523866,-977964053299⟩,⟨-439804651111,-439375154380⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18

noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨940511938477,942533593007⟩,⟨-981829523866,-977964053299⟩,⟨-439804651111,-439375154380⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19

noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-171740465088,-169379573056⟩,⟨-1147814220980,-1140842996076⟩,⟨-514156501437,-512552650410⟩,⟨-1198238793117,-1183728037810⟩,⟨745890312156,753571410517⟩,⟨-240431207176,-238933552684⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20

noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-147220960229,-144885698858⟩,⟨-833284801042,-822507535004⟩,⟨-373064357162,-369736545943⟩,⟨1002287323247,1037374594192⟩,⟨1378070228475,1394855303313⟩,⟨203537010959,206943680188⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21

noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨144885698858,147220960229⟩,⟨822507535004,833284801042⟩,⟨369736545943,373064357162⟩,⟨-1037374594192,-1002287323247⟩,⟨-1394855303313,-1378070228475⟩,⟨-206943680188,-203537010959⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22

noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨448437128484,456716324604⟩,⟨1719141242199,1778901812899⟩,⟨773895977985,795362367833⟩,⟨-7380500244608,-6812667552840⟩,⟨-5282998828182,-5009286842168⟩,⟨-1472622263014,-1383782585614⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23

noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨805395725310,815567382067⟩,⟨4125479101673,4199531520001⟩,⟨773895977985,795362367833⟩,⟨-19684285936381,-18899887459897⟩,⟨-5282998828182,-5009286842168⟩,⟨-1472622263014,-1383782585614⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24

noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨93194750522,98097053044⟩,⟨-243095148954,-235364207820⟩,⟨878750308760,879609302222⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25

noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨12323773060464,12972037725765⟩,⟨29568422228019,33837093028512⟩,⟨-122435276541292,-110395970581427⟩,⟨141886999827875,176525676046412⟩,⟨-362476303765133,-223657797056477⟩,⟨1977847248699119,2311186146486254⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26

noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨9027202525056,9622063633357⟩,⟨67899008246342,74644877428012⟩,⟨-82142741627048,-71481710762368⟩,⟨93584912346361,177579328913986⟩,⟨-778020903621812,-609716032186065⟩,⟨1254271396605375,1543416708201904⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27

noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨86696656896,92353583872⟩,⟨-756367659398,-605941354736⟩,⟨637913951572,832342624997⟩,⟨6618410069944,11508038787500⟩,⟨-8141843674471,-978373690903⟩,⟨-6309687741189,3754108883368⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28

noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29

noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1186208284672,1191865211648⟩,⟨-756367659398,-605941354736⟩,⟨637913951572,832342624997⟩,⟨6618410069944,11508038787500⟩,⟨-8141843674471,-978373690903⟩,⟨-6309687741189,3754108883368⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30

noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨83448312512,88679327296⟩,⟨-701086855596,-558989018868⟩,⟨588484167856,771509022745⟩,⟨5658534607481,10382759663685⟩,⟨-7247595106471,-410621852788⟩,⟨-6389885302797,3164761131165⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31

noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨90028224479,96127955837⟩,⟨-820978319783,-649053789634⟩,⟨683301221301,903443241212⟩,⟨7223138626701,13147595409669⟩,⟨-9574485959995,-1165881681098⟩,⟨-6752649225067,4901449061605⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32

noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-92353583872,-86696656896⟩,⟨605941354736,756367659398⟩,⟨-832342624997,-637913951572⟩,⟨-11508038787500,-6618410069944⟩,⟨978373690903,8141843674471⟩,⟨-3754108883368,6309687741189⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33

noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1007158043904,1012814970880⟩,⟨605941354736,756367659398⟩,⟨-832342624997,-637913951572⟩,⟨-11508038787500,-6618410069944⟩,⟨978373690903,8141843674471⟩,⟨-3754108883368,6309687741189⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34

noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-96464069120,-90305696448⟩,⟨657809752459,825724464414⟩,⟨-908666122480,-692519193969⟩,⟨-13183406338843,-7578494772034⟩,⟨1476438748462,9570829045354⟩,⟨-4849296438029,6452090464060⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35

noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-88857862790,-82720460875⟩,⟨536198132404,710848456342⟩,⟨-784624161233,-561326596883⟩,⟨-10875267354372,-4796245012031⟩,⟨-612053141234,7972516128738⟩,⟨-4216929368282,7648444375758⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36

noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨1170361689,13407494962⟩,⟨-284780187379,61794666708⟩,⟨-101322939932,342116644329⟩,⟨-3652128727671,8351350397638⟩,⟨-10186539101229,6806634447640⟩,⟨-10969578593349,12549893437363⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37

noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨585180844,6703747481⟩,⟨-142390093690,30897333354⟩,⟨-50661469966,171058322165⟩,⟨-1826064363836,4175675198819⟩,⟨-5093269550615,3403317223820⟩,⟨-5484789296675,6274946718682⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38

noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-6703747481,-585180844⟩,⟨-30897333354,142390093690⟩,⟨-171058322165,50661469966⟩,⟨-4175675198819,1826064363836⟩,⟨-3403317223820,5093269550615⟩,⟨-6274946718682,5484789296675⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39

noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨755419636135,761538222036⟩,⟨-30897333354,142390093690⟩,⟨-171058322165,50661469966⟩,⟨-4175675198819,1826064363836⟩,⟨-3403317223820,5093269550615⟩,⟨-6274946718682,5484789296675⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40

noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨6836044410,7757248072⟩,⟨-127062347148,-95557133554⟩,⟨100599221674,139825396088⟩,⟨1711594363604,2973866979205⟩,⟨-2512907459732,-857399158514⟩,⟨-319756630057,1890838857457⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41

noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-7757248072,-6836044410⟩,⟨95557133554,127062347148⟩,⟨-139825396088,-100599221674⟩,⟨-2973866979205,-1711594363604⟩,⟨857399158514,2512907459732⟩,⟨-1890838857457,319756630057⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42

noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1091754379704,1092675583366⟩,⟨95557133554,127062347148⟩,⟨-139825396088,-100599221674⟩,⟨-2973866979205,-1711594363604⟩,⟨857399158514,2512907459732⟩,⟨-1890838857457,319756630057⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43

noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-7784741888,-6857383872⟩,⟨96154962240,127965163905⟩,⟨-140818898203,-101228594890⟩,⟨-3009890263109,-1730711499528⟩,⟨871615942819,2547151449931⟩,⟨-1922309090086,312708798545⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44

noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3892370944,-3428691936⟩,⟨48077481120,63982581953⟩,⟨-70409449102,-50614297445⟩,⟨-1504945131555,-865355749764⟩,⟨435807971409,1273575724966⟩,⟨-961154545043,156354399273⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45

noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3428691936,3892370944⟩,⟨-63982581953,-48077481120⟩,⟨50614297445,70409449102⟩,⟨865355749764,1504945131555⟩,⟨-1273575724966,-435807971409⟩,⟨-156354399273,961154545043⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46

noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765552075552,766015773824⟩,⟨-63982581953,-48077481120⟩,⟨50614297445,70409449102⟩,⟨865355749764,1504945131555⟩,⟨-1273575724966,-435807971409⟩,⟨-156354399273,961154545043⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47

noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48

noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49

noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272938594926,273168895842⟩,⟨23889283388,31765586787⟩,⟨-34956349022,-25149805418⟩,⟨-743466744802,-427898590901⟩,⟨214349789628,628226864933⟩,⟨-472709714365,79939157515⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50

noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1531104151104,1532031547648⟩,⟨-127965163906,-96154962240⟩,⟨101228594890,140818898204⟩,⟨1730711499528,3009890263110⟩,⟨-2547151449932,-871615942818⟩,⟨-312708798546,1922309090086⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51

noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1193629492427,1200333777735⟩,⟨-901441095028,-714118069428⟩,⟨751798628691,991988271832⟩,⟨8654450265184,15069263008190⟩,⟨-11193422659321,-2052603398411⟩,⟨-6572874010742,6113769313134⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52

noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1287747357078,1301155927694⟩,⟨-1802882190056,-1428236138856⟩,⟨1503597257383,1983976543663⟩,⟨17308900530373,30138526016364⟩,⟨-22386845318631,-4105206796822⟩,⟨-13140875606615,12227538626261⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53

noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨173754009024,185143396416⟩,⟨-1539346922813,-1206897811751⟩,⟨1270579976463,1693969913434⟩,⟨12471356204412,24408272209525⟩,⟨-17719787158350,-1097404665637⟩,⟨-13829841703567,8971921076332⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54

noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨59564951704,63965475475⟩,⟨-526466794338,-404352033231⟩,⟨423910820316,580748284011⟩,⟨4000539623448,8166529799526⟩,⟨-5983265112842,-18918102657⟩,⟨-5156235118104,3137550042536⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55

noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380075485452,380626594294⟩,⟨1474180345,20392217992⟩,⟨-23578685648,-36041945⟩,⟨-613696392795,147753730486⟩,⟨-329941157591,667125400719⟩,⟨-745306844343,584343619161⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56

noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3176146485131,3180751892422⟩,⟨-170657115367,-12301328365⟩,⟨300752755,197323826099⟩,⟨-1236416868764,5154176451614⟩,⟨-5604171285187,2761188543123⟩,⟨-4890218185509,6261759886150⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57

noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨172064585050,185044252400⟩,⟨-1532931870240,-1168713440285⟩,⟨1224562562382,1691512912429⟩,⟨11493430070019,24088044547798⟩,⟨-17819501027145,101133806851⟩,⟨-15200616650329,9649280064512⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58

noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨345818594074,370187648816⟩,⟨-3072278793053,-2375611252036⟩,⟨2495142538845,3385482825863⟩,⟨23964786274431,48496316757323⟩,⟨-35539288185495,-996270858786⟩,⟨-29030458353896,18621201140844⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59

noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨519011179365,527452779008⟩,⟨-42799911732,197243023258⟩,⟨-236955112134,70177785828⟩,⟨-5792272970029,2566398957681⟩,⟨-4758682113194,7068471185232⟩,⟨-8708007651089,7650919794860⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60

noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨356586712101,365321695003⟩,⟨-44465789894,204920208363⟩,⟨-246177989717,72909278396⟩,⟨-6026036602525,2704604892409⟩,⟨-4989931371257,7357225877624⟩,⟨-9063321829288,8004009489144⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61

noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨713173424202,730643390006⟩,⟨-88931579788,409840416726⟩,⟨-492355979434,145818556792⟩,⟨-12052073205050,5409209784818⟩,⟨-9979862742514,14714451755248⟩,⟨-18126643658576,16008018978288⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62

noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523346903032,1525195503238⟩,⟨-32408030352,30907384908⟩,⟨-38596801198,40219676530⟩,⟨-1243155479677,1298295899506⟩,⟨-1689752291418,1641291516914⟩,⟨-2203547656003,2242065720143⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63

noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨988084618332,1013517260534⟩,⟨-144897747986,589051557765⟩,⟨-708623359511,228999895548⟩,⟨-17568377581796,8389204547842⟩,⟨-14994733724183,21531427031860⟩,⟨-26644818465449,23730095373621⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64

noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67753241273,67867627564⟩,⟨11860370144,15784044570⟩,⟨-17369506650,-12486184556⟩,⟨-368384083981,-210604389697⟩,⟨104398934970,311067611992⟩,⟨-233734823297,41943781491⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65

noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨49629462316,50341098668⟩,⟨262904788866,270925004817⟩,⟨34804504911,39947769703⟩,⟨-1399265248827,-1198329596195⟩,⟨-307615881732,-113374226608⟩,⟨-289401196914,-71735295335⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66

noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2132110168102,2134693807411⟩,⟨-356606811882,-267797553232⟩,⟨281927935878,392426945026⟩,⟨4836957192408,8417595238311⟩,⟨-7131050172254,-2445210011384⟩,⟨-852801378965,5393063715809⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67

noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2969029746047,2974428077799⟩,⟨-745330297709,-559374637408⟩,⟨588890133624,820196591932⟩,⟨10138549395778,17655549585778⟩,⟨-14972844123938,-5144529453144⟩,⟨-1743481165808,11347226356230⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68

noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨134015272029,136184078061⟩,⟨675801304590,707664620512⟩,⟨120564355776,145620438536⟩,⟨-3695004414310,-2695015605080⟩,⟨-1403971497007,-353965036587⟩,⟨-825438968740,385423541091⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69

noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8877145087938,9020806370136⟩,⟨-47634164524575,-44052038365128⟩,⟨-9801970773028,-7858975101170⟩,⟨612882913501587,751779582702130⟩,⟨101072096195391,198021990155559⟩,⟨-12028374630182,76863326965533⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70

noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7977515011673,8315276281854⟩,⟨-45097424358414,-34754904363697⟩,⟨-14849156906365,-5183727532130⟩,⟨355595411414950,774364834200984⟩,⟨-47365475218640,391177767868446⟩,⟨-233774711900402,278176880792631⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71

noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15955030023346,16630552563708⟩,⟨-90194848716828,-69509808727394⟩,⟨-29698313812730,-10367455064260⟩,⟨711190822829900,1548729668401968⟩,⟨-94730950437280,782355535736892⟩,⟨-467549423800804,556353761585262⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72

noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10952333724070,10995116277821⟩,⟨-109951162778821,-109097176394608⟩,⟨0,0⟩,⟨2173453475238562,2199023255588622⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73

noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9852822096294,9895604650045⟩,⟨-109951162778820,-109097176394608⟩,⟨0,0⟩,⟨2173453475238575,2199023255588602⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74

noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2411110045440,2415874025920⟩,⟨-12269843176037,-12121908488212⟩,⟨0,0⟩,⟨104571265817406,111755106875729⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75

noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7603321899209,7701241905555⟩,⟨-48167927980722,-46765975052338⟩,⟨-21576534668551,-21010800385799⟩,⟨575289709310752,602538996803206⟩,⟨311041839595064,323845069272822⟩,⟨116121279278690,120901759485661⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76

noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6503810271433,6601730277779⟩,⟨-48167927980722,-46765975052337⟩,⟨-21576534668552,-21010800385799⟩,⟨575289709310758,602538996803203⟩,⟨311041839595067,323845069272822⟩,⟨116121279278691,120901759485662⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77

noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1954406208960,1970836884416⟩,⟨-8143102995103,-7788826745524⟩,⟨-3647654185037,-3499327958128⟩,⟨35505221679289,46687911157118⟩,⟨24788785181819,29959247610515⟩,⟨7238710279160,9302200537803⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78

noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨98913096826,99342593558⟩,⟨878750308760,879609302222⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79

noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨134277539272,136299193803⟩,⟨694559528974,702028440800⟩,⟨312237512194,314283542842⟩,⟨-1753486165281,-1739706366688⟩,⟨-1571019177332,-1563119457398⟩,⟨-351843720890,-351156861664⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80

noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4365516254400,4386710910336⟩,⟨-20412946171140,-19910735233736⟩,⟨-3647654185037,-3499327958128⟩,⟨140076487496695,158443018032847⟩,⟨24788785181819,29959247610515⟩,⟨7238710279160,9302200537803⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81

noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨691637188148,740375297632⟩,⟨-6144557586106,-4751222504072⟩,⟨4990285077690,6770965651726⟩,⟨47929572548862,96992633514646⟩,⟨-71078576370990,-1992541717572⟩,⟨-58060916707792,37242402281688⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82

noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5057153442548,5127086207968⟩,⟨-26557503757246,-24661957737808⟩,⟨1342630892653,3271637693598⟩,⟨188006060045557,255435651547493⟩,⟨-46289791189171,27966705892943⟩,⟨-50822206428632,46544602819491⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83

noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨454946264768,463240249970⟩,⟨1642259892300,1883056127722⟩,⟨120784333818,295597577555⟩,⟨-35832977010359,-26455894720676⟩,⟨-3109299178070,5144145730327⟩,⟨-4591865760595,4205377590748⟩⟩⟩
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

noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨35069196393,37167977782⟩,⟨-745527573809,-703514061620⟩,⟨330673852191,333275037186⟩,⟨8702942632379,9416158326176⟩,⟨-6692236630045,-6625935308195⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91

noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨490015461161,500408227752⟩,⟨896732318491,1179542066102⟩,⟨451458186009,628872614741⟩,⟨-27130034377980,-17039736394500⟩,⟨-9801535808115,-1481789577868⟩,⟨-4591865760595,4205377590748⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92

noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨500409295618,501398026980⟩,⟨2510857612204,2551553037358⟩,⟨0,0⟩,⟨1957166706152,4308831445771⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93

noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨223015642187,228195584059⟩,⟨1527125494800,1699152742843⟩,⟨205467470424,286777765953⟩,⟨-7403986662167,-319541410426⟩,⟨-3438729884357,784985378540⟩,⟨-2093977338991,1917731448618⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94

noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-740375297632,-691637188148⟩,⟨4751222504072,6144557586106⟩,⟨-6770965651726,-4990285077690⟩,⟨-96992633514646,-47929572548862⟩,⟨1992541717572,71078576370990⟩,⟨-37242402281688,58060916707792⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95

noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3625140956768,3695073722188⟩,⟨-15661723667068,-13766177647630⟩,⟨-10418619836763,-8489613035818⟩,⟨43083853982049,110513445483985⟩,⟨26781326899391,101037823981505⟩,⟨-30003692002528,67363117245595⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96

noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨442719289993,458053881973⟩,⟨348514628066,678081400223⟩,⟨-262065887544,19405445211⟩,⟨-20630993866646,-9428410525461⟩,⟨-13137915125403,-1900855846078⟩,⟨-10857883377030,2371047361138⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97

noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨313956069538,317999378598⟩,⟨1955928106598,1963659047732⟩,⟨878750308760,879609302222⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98

noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-317999378598,-313956069538⟩,⟨-1963659047732,-1955928106598⟩,⟨-879609302222,-878750308760⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99

noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨781512249178,785555558238⟩,⟨-1963659047732,-1955928106598⟩,⟨-879609302222,-878750308760⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100

noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1389155288208,1408081397070⟩,⟨-9337701611727,-9012857430358⟩,⟨-4182767476123,-4049254787545⟩,⟨52947631002215,62442726501006⟩,⟨33978168886410,38375281210111⟩,⟨10738596573654,12482284038208⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101

noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1408081397070,-1389155288208⟩,⟨9012857430358,9337701611727⟩,⟨4049254787545,4182767476123⟩,⟨-62442726501006,-52947631002215⟩,⟨-38375281210111,-33978168886410⟩,⟨-12482284038208,-10738596573654⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102

noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-308569769294,-289643660432⟩,⟨9012857430358,9337701611727⟩,⟨4049254787545,4182767476123⟩,⟨-62442726501006,-52947631002215⟩,⟨-38375281210111,-33978168886410⟩,⟨-12482284038208,-10738596573654⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103

noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-13765104553,-12275117421⟩,⟨412966415023,450660456565⟩,⟨48179777090,70846320770⟩,⟨-4850038468324,-4173238885670⟩,⟨1716976801505,2170256575389⟩,⟨2679413460190,2891111550262⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104

noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨428954185440,445778764552⟩,⟨761481043089,1128741856788⟩,⟨-213886110454,90251765981⟩,⟨-25481032334970,-13601649411131⟩,⟨-11420938323898,269400729311⟩,⟨-8178469916840,5262158911400⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105

noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-99342593558,-98913096826⟩,⟨-879609302222,-878750308760⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106

noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4191943563,4431611010⟩,⟨26259482736,28652028824⟩,⟨39526600801,39737037424⟩,⟨-292573172208,-281302238490⟩,⟨251814268106,252930624064⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107

noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨9192478714,9737244848⟩,⟨8130273729,16739555547⟩,⟨86677559241,87311197222⟩,⟨-883642208912,-745445126376⟩,⟨108761645553,119972071186⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108

noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1482312615973,1501033320173⟩,⟨-7826757136335,-7498153866624⟩,⟨-1482333936241,-1406573873405⟩,⟨110208546533795,118307302443859⟩,⟨23334566512838,25304546334069⟩,⟨5184466917293,5672292762608⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109

noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨12392890466,13293109954⟩,⟨-58352673735,-39835858089⟩,⟨103727316945,107435986014⟩,⟨-523250084598,-68139007394⟩,⟨-302366863161,-213621084930⟩,⟨-192076731339,-171534590661⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110

noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-13293109954,-12392890466⟩,⟨39835858089,58352673735⟩,⟨-107435986014,-103727316945⟩,⟨68139007394,523250084598⟩,⟨213621084930,302366863161⟩,⟨171534590661,192076731339⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111

noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-112635703512,-111305987292⟩,⟨-839773444133,-820397635025⟩,⟨-107435986014,-103727316945⟩,⟨2267162262946,2722273340150⟩,⟨213621084930,302366863161⟩,⟨171534590661,192076731339⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112

noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨82827863963,87917801644⟩,⟨-581128593893,-539273530438⟩,⟨618279470240,640033004240⟩,⟨3172009360352,3883107714673⟩,⟨-3802990286952,-3327194314056⟩,⟨-2611346329254,-2381763164399⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113

noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨111664837919,120023787262⟩,⟨-1419179774683,-1291871763957⟩,⟨715008280127,767802117421⟩,⟨19933722621806,23034496510812⟩,⟨-7300075286497,-5895117271041⟩,⟨-4900161743695,-4339320708351⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114

noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-120023787262,-111664837919⟩,⟨1291871763957,1419179774683⟩,⟨-767802117421,-715008280127⟩,⟨-23034496510812,-19933722621806⟩,⟨5895117271041,7300075286497⟩,⟨4339320708351,4900161743695⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115

noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨979487840514,987846789857⟩,⟨1291871763957,1419179774683⟩,⟨-767802117421,-715008280127⟩,⟨-23034496510812,-19933722621806⟩,⟨5895117271041,7300075286497⟩,⟨4339320708351,4900161743695⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116

noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨119619668995,122456841435⟩,⟨776510182424,806657772759⟩,⟨182973996690,195045173758⟩,⟨-2798692817830,-2171930942085⟩,⟨-814900438803,-533557879207⟩,⟨-225108599547,-111477305937⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117

noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11267750603,11538578934⟩,⟨166101324318,172055429486⟩,⟨21001090174,22011823362⟩,⟨666527024322,823767010741⟩,⟨92841839718,120861991008⟩,⟨-19782130917,-13733980953⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118

noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨163506501090,174525615396⟩,⟨1463769181146,1890073394622⟩,⟨-6915173696,226692361497⟩,⟨-11267772933552,7711148585477⟩,⟨-6099867664642,7144483807610⟩,⟨-6394904426726,5243191478691⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119

noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-174525615396,-163506501090⟩,⟨-1890073394622,-1463769181146⟩,⟨-226692361497,6915173696⟩,⟨-7711148585477,11267772933552⟩,⟨-7144483807610,6099867664642⟩,⟨-5243191478691,6394904426726⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120

noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨48490026791,64689082969⟩,⟨-362947899822,235383561697⟩,⟨-21224891073,293692939649⟩,⟨-15115135247644,10948231523126⟩,⟨-10583213691967,6884853043182⟩,⟨-7337168817682,8312635875344⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121

noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨28360418347593,29809695116251⟩,⟨-284838858558210,-236579004496812⟩,⟨-108405435572038,-69207181861356⟩,⟨2764174816872678,4818203888609668⟩,⟨484573764817511,2374663412648979⟩,⟨-667033927273015,1334994164110868⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122

noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13013837097,13638489704⟩,⟨168958451454,179681161120⟩,⟨39812746614,43445863260⟩,⟨473390138339,711026772443⟩,⟨76926949492,170094951594⟩,⟨10756403542,44943119739⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123

noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨335674362193,369763456477⟩,⟨824875793888,2071319619090⟩,⟨-317759502076,358756503518⟩,⟨-48168922636561,6334149420559⟩,⟨-21250925900628,14865966399791⟩,⟨-16563548984754,12766021307916⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124

noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-369763456477,-335674362193⟩,⟨-2071319619090,-824875793888⟩,⟨-358756503518,317759502076⟩,⟨-6334149420559,48168922636561⟩,⟨-14865966399791,21250925900628⟩,⟨-12766021307916,16563548984754⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125

noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨59190728963,110104402359⟩,⟨-1309838576001,303866062900⟩,⟨-572642613972,408011268057⟩,⟨-31815181755529,34567273225430⟩,⟨-26286904723689,21520326629939⟩,⟨-20944491224756,21825707896154⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126

noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨233190636098,235641787361⟩,⟨1573309837734,1581637743022⟩,⟨312237512194,314283542842⟩,⟨-3952509420833,-3938729622240⟩,⟨-1571019177332,-1563119457398⟩,⟨-351843720890,-351156861664⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127

noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1703660007303,-1615162881555⟩,⟨-5665277528697,-2665100200398⟩,⟨-575491859316,1537153378485⟩,⟨-22026368601724,106956204661425⟩,⟨-62752709494778,45773634191322⟩,⟨-52548494931161,56605527523135⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128

noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-189743171517,-175719150560⟩,⟨-1880855578790,-1430625004659⟩,⟨-366311339816,-97586835374⟩,⟨-7575306513005,12484256454264⟩,⟨-7632411994575,7044873779730⟩,⟨-5892945886573,7198533532749⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129

noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨43447464581,59922636801⟩,⟨-307545741056,151012738363⟩,⟨-54073827622,216696707468⟩,⟨-11527815933838,8545526832024⟩,⟨-9203431171907,5481754322332⟩,⟨-6244789607463,6847376671085⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130

noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2610395343,6477924053⟩,⟨-113408912437,41448932589⟩,⟨-35816519370,53415315388⟩,⟨-3946267319234,3994846351784⟩,⟨-3090928070341,2225775075111⟩,⟨-2272915211136,2334493630303⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131

noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1716836939,3265743000⟩,⟨-33522067936,16460183312⟩,⟨-5893973746,23619646706⟩,⟨-1340996189978,1103498804642⟩,⟨-1124386495432,657028315762⟩,⟨-701987810232,831769881787⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132

noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨3051715587,5853732327⟩,⟨-84273605841,17342418622⟩,⟨-21398920559,36873366686⟩,⟨-2592061730885,2613191253447⟩,⟨-2206254382914,1421546575006⟩,⟨-1403703563421,1557654936429⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133

noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5853732327,-3051715587⟩,⟨-17342418622,84273605841⟩,⟨-36873366686,21398920559⟩,⟨-2613191253447,2592061730885⟩,⟨-1421546575006,2206254382914⟩,⟨-1557654936429,1403703563421⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134

noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3243336984,3426208466⟩,⟨-130751331059,125722538430⟩,⟨-72689886056,74814235947⟩,⟨-6559458572681,6586908082669⟩,⟨-4512474645347,4432029458025⟩,⟨-3830570147565,3738197193724⟩⟩⟩


noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]

noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨48490026791,64689082969⟩,⟨-362947899822,235383561697⟩,⟨-21224891073,293692939649⟩,⟨-15115135247644,10948231523126⟩,⟨-10583213691967,6884853043182⟩,⟨-7337168817682,8312635875344⟩⟩

noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3243336984,3426208466⟩,⟨-130751331059,125722538430⟩,⟨-72689886056,74814235947⟩,⟨-6559458572681,6586908082669⟩,⟨-4512474645347,4432029458025⟩,⟨-3830570147565,3738197193724⟩⟩



attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (513/5120) u, BivariateJet2.affineZ (557/5120) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet


noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet























end GeneralCK.Certificates.LaneCB.RB2Cell000004

end

section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell000005Endpoints
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



noncomputable def out_w4 : DyadicInterval 40 := ⟨-2122458618560,-2122458579584⟩



noncomputable def out_w5 : DyadicInterval 40 := ⟨-2122458618560,-2122458579584⟩



noncomputable def out_w6 : DyadicInterval 40 := ⟨-172365185856,-172365185792⟩



noncomputable def out_w7 : DyadicInterval 40 := ⟨-172365185856,-172365185792⟩



noncomputable def out_w8 : DyadicInterval 40 := ⟨762123383616,762123402880⟩



noncomputable def out_w9 : DyadicInterval 40 := ⟨88411928640,88411928704⟩



noncomputable def out_w10 : DyadicInterval 40 := ⟨-96147715136,-96147715072⟩



noncomputable def out_w11 : DyadicInterval 40 := ⟨88412052224,88412052288⟩



noncomputable def out_w12 : DyadicInterval 40 := ⟨-96147861248,-96147861184⟩



noncomputable def out_w13 : DyadicInterval 40 := ⟨-7735809024,-7735808960⟩



noncomputable def out_w14 : DyadicInterval 40 := ⟨-7735786432,-7735786368⟩



noncomputable def out_w15 : DyadicInterval 40 := ⟨184559643776,184559643840⟩



noncomputable def out_w16 : DyadicInterval 40 := ⟨184559913472,184559913536⟩



noncomputable def out_w17 : DyadicInterval 40 := ⟨2413489943680,2413490001536⟩



noncomputable def out_w18 : DyadicInterval 40 := ⟨2413489943680,2413490001536⟩



noncomputable def out_w19 : DyadicInterval 40 := ⟨1950093393792,1950093432384⟩



noncomputable def out_w20 : DyadicInterval 40 := ⟨1950093393856,1950093432448⟩



noncomputable def out_w21 : DyadicInterval 40 := ⟨-2531719137984,-2531719080128⟩



noncomputable def out_w22 : DyadicInterval 40 := ⟨-2527432537536,-2527432479680⟩



noncomputable def out_w23 : DyadicInterval 40 := ⟨-116322434304,-116322434240⟩



noncomputable def out_w24 : DyadicInterval 40 := ⟨-115845112128,-115845112064⟩



noncomputable def out_w25 : DyadicInterval 40 := ⟨-2129450047360,-2129450008320⟩



noncomputable def out_w26 : DyadicInterval 40 := ⟨-2115506194688,-2115506155776⟩



noncomputable def out_w27 : DyadicInterval 40 := ⟨-173549533952,-173549533888⟩



noncomputable def out_w28 : DyadicInterval 40 := ⟨-171182994240,-171182994176⟩



noncomputable def out_w29 : DyadicInterval 40 := ⟨85808923584,85808923648⟩



noncomputable def out_w30 : DyadicInterval 40 := ⟨-93076902208,-93076902144⟩



noncomputable def out_w31 : DyadicInterval 40 := ⟨91037721472,91037721536⟩



noncomputable def out_w32 : DyadicInterval 40 := ⟨-99261530752,-99261530688⟩



noncomputable def out_w33 : DyadicInterval 40 := ⟨-8223809280,-8223809216⟩



noncomputable def out_w34 : DyadicInterval 40 := ⟨-7267978560,-7267978496⟩



noncomputable def out_w35 : DyadicInterval 40 := ⟨178885825728,178885825792⟩



noncomputable def out_w36 : DyadicInterval 40 := ⟨190299252160,190299252224⟩



noncomputable def out_w37 : DyadicInterval 40 := ⟨2411110045440,2411110103296⟩



noncomputable def out_w38 : DyadicInterval 40 := ⟨2415873968064,2415874025920⟩



noncomputable def out_w39 : DyadicInterval 40 := ⟨1941956621888,1941956660480⟩



noncomputable def out_w40 : DyadicInterval 40 := ⟨1958267014144,1958267052736⟩



end LaneCBRB2Cell000005Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell000005
open Set LaneCBRB2Cell000005Endpoints
open BivariateJetProgram (zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
















































noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨110165911142,110165911143⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨123480309760,123480309760⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0

noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1

noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-110165911143,-110165911142⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2

noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨439589902745,439589902746⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3

noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨49368006655,49368006657⟩,⟨-123480309760,-123480309760⟩,⟨439589902745,439589902746⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4

noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨159533917797,159533917800⟩,⟨976031318016,976031318016⟩,⟨439589902745,439589902746⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5

noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨49368006654,49368006658⟩,⟨-123480309760,-123480309760⟩,⟨439589902745,439589902746⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2122458618560,-2122458579584⟩,⟨6726831497847,6726831497975⟩,⟨3029664263162,3029664263227⟩,⟨-41154873544786,-41154873543229⟩,⟨-26113400091504,-26113400090617⟩,⟨-8348129584079,-8348129583724⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15

noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-307958670226,-307958664564⟩,⟨-908065248674,-908065214037⟩,⟨-408979001990,-408978986386⟩,⟨5971376788390,5971376788957⟩,⟨3712365716536,3712365755830⟩,⟨1211273973909,1211273974042⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16

noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨307958664564,307958670226⟩,⟨908065214037,908065248674⟩,⟨408978986386,408979001990⟩,⟨-5971376788957,-5971376788390⟩,⟨-3712365755830,-3712365716536⟩,⟨-1211273974042,-1211273973909⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17

noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-159533917800,-159533917797⟩,⟨-976031318016,-976031318016⟩,⟨-439589902746,-439589902745⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18

noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨939977709976,939977709979⟩,⟨-976031318016,-976031318016⟩,⟨-439589902746,-439589902745⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19

noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-172365185856,-172365185792⟩,⟨-1141684288727,-1141684288722⟩,⟨-514197522338,-514197522334⟩,⟨-1185474516321,-1185474516308⟩,⟨752201809317,752201809329⟩,⟨-240469573308,-240469573304⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20

noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-147355815608,-147355815552⟩,⟨-823023550556,-823023550489⟩,⟨-370677493507,-370677493474⟩,⟨1013467791443,1013467791468⟩,⟨1383597172186,1383597172272⟩,⟨205578579726,205578579736⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21

noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨147355815552,147355815608⟩,⟨823023550489,823023550556⟩,⟨370677493474,370677493507⟩,⟨-1013467791468,-1013467791443⟩,⟨-1383597172272,-1383597172186⟩,⟨-205578579736,-205578579726⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22

noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨455314480116,455314485834⟩,⟨1731088764526,1731088799230⟩,⟨779656479860,779656495497⟩,⟨-6984844580425,-6984844579833⟩,⟨-5095962928102,-5095962888722⟩,⟨-1416852553778,-1416852553635⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23

noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨813218606443,813218618020⟩,⟨4144578708193,4144578800843⟩,⟨779656479860,779656495497⟩,⟨-19180472648638,-19180472647526⟩,⟨-5095962928102,-5095962888722⟩,⟨-1416852553778,-1416852553635⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24

noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨98736013308,98736013316⟩,⟨-246960619520,-246960619520⟩,⟨879179805490,879179805492⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25

noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨12244020991059,12244020992052⟩,⟨30625006092662,30625006097631⟩,⟨-109025021707663,-109025021689729⟩,⟨153199835064067,153199835101344⟩,⟨-272695706536180,-272695706358003⟩,⟨1941593429662667,1941593430143915⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26

noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨9055898488084,9055898617739⟩,⟨68804305082443,68804306444059⟩,⟨-71954716238439,-71954714902388⟩,⟨130598294172659,130598301041687⟩,⟨-647689477737799,-647689464597979⟩,⟨1265641729374598,1265641753303368⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27

noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨92063760384,92063894272⟩,⟨-692421674713,-692419619179⟩,⟨724124111583,724126260350⟩,⟨9048424119960,9048475183815⟩,⟨-4319161892615,-4319093276258⟩,⟨-1403541376451,-1403452071444⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28

noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29

noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1191575388160,1191575522048⟩,⟨-692421674713,-692419619179⟩,⟨724124111583,724126260350⟩,⟨9048424119960,9048475183815⟩,⟨-4319161892615,-4319093276258⟩,⟨-1403541376451,-1403452071444⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30

noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨88411928640,88412052288⟩,⟨-638923638602,-638921670091⟩,⟨668176599725,668178657553⟩,⟨7978044808300,7978095152795⟩,⟨-3597179189020,-3597113034235⟩,⟨-1701156130073,-1701071078356⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31

noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨95814792245,95814937013⟩,⟨-748099582349,-748097128054⟩,⟨782350980859,782353546574⟩,⟨10178368271031,10178433794344⟩,⟨-5087258075300,-5087174849907⟩,⟨-1076350967222,-1076245925823⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32

noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-92063894272,-92063760384⟩,⟨692419619179,692421674713⟩,⟨-724126260350,-724124111583⟩,⟨-9048475183815,-9048424119960⟩,⟨4319093276258,4319161892615⟩,⟨1403452071444,1403541376451⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33

noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1007447733504,1007447867392⟩,⟨692419619179,692421674713⟩,⟨-724126260350,-724124111583⟩,⟨-9048475183815,-9048424119960⟩,⟨4319093276258,4319161892615⟩,⟨1403452071444,1403541376451⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34

noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-96147861248,-96147715072⟩,⟨755695105651,755697449459⟩,⟨-790299304625,-790296854465⟩,⟨-10394747661363,-10394687396892⟩,⟨5256957205545,5257036087415⟩,⟨963658117635,963759309404⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35

noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-88097256384,-88097110738⟩,⟨631870041890,631872553274⟩,⟨-660804717236,-660802091824⟩,⟨-7781331828339,-7781263898267⟩,⟨3443702287246,3443787819709⟩,⟨1801193957560,1801301105923⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36

noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨7717535861,7717826275⟩,⟨-116229540459,-116224574780⟩,⟨121546263623,121551454750⟩,⟨2397036442692,2397169896077⟩,⟨-1643555788054,-1643387030198⟩,⟨724842990338,725055180100⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37

noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨3858767930,3858913138⟩,⟨-58114770230,-58112287390⟩,⟨60773131811,60775727375⟩,⟨1198518221346,1198584948039⟩,⟨-821777894027,-821693515099⟩,⟨362421495169,362527590050⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38

noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-3858913138,-3858767930⟩,⟨58112287390,58114770230⟩,⟨-60775727375,-60773131811⟩,⟨-1198584948039,-1198518221346⟩,⟨821693515099,821777894027⟩,⟨-362527590050,-362421495169⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39

noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨758264470478,758264634950⟩,⟨58112287390,58114770230⟩,⟨-60775727375,-60773131811⟩,⟨-1198584948039,-1198518221346⟩,⟨821693515099,821777894027⟩,⟨-362527590050,-362421495169⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40

noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨7708636963,7708659386⟩,⟨-115955182724,-115954669864⟩,⟨121263999420,121264535616⟩,⟨2387381535402,2387397468299⟩,⟨-1635343472520,-1635325516038⟩,⟨718755916909,718776874625⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41

noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-7708659386,-7708636963⟩,⟨115954669864,115955182724⟩,⟨-121264535616,-121263999420⟩,⟨-2387397468299,-2387381535402⟩,⟨1635325516038,1635343472520⟩,⟨-718776874625,-718755916909⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42

noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1091802968390,1091802990813⟩,⟨115954669864,115955182724⟩,⟨-121264535616,-121263999420⟩,⟨-2387397468299,-2387381535402⟩,⟨1635325516038,1635343472520⟩,⟨-718776874625,-718755916909⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43

noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-7735809024,-7735786368⟩,⟨116773363769,116773882649⟩,⟨-122120722152,-122120179661⟩,⟨-2416655651075,-2416639446087⟩,⟨1659841418686,1659859651022⟩,⟨-737415511222,-737394270159⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44

noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-3867904512,-3867893184⟩,⟨58386681884,58386941325⟩,⟨-61060361076,-61060089830⟩,⟨-1208327825538,-1208319723043⟩,⟨829920709343,829929825511⟩,⟨-368707755611,-368697135079⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45

noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3867893184,3867904512⟩,⟨-58386941325,-58386681884⟩,⟨61060089830,61060361076⟩,⟨1208319723043,1208327825538⟩,⟨-829929825511,-829920709343⟩,⟨368697135079,368707755611⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46

noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765991276800,765991307392⟩,⟨-58386941325,-58386681884⟩,⟨61060089830,61060361076⟩,⟨1208319723043,1208327825538⟩,⟨-829929825511,-829920709343⟩,⟨368697135079,368707755611⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47

noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48

noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49

noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272950742097,272950747704⟩,⟨28988667466,28988795681⟩,⟨-30316133904,-30315999855⟩,⟨-596849367075,-596845383850⟩,⟨408831379009,408835868130⟩,⟨-179694218657,-179688979227⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50

noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1531982553600,1531982614784⟩,⟨-116773882650,-116773363768⟩,⟨122120179660,122120722152⟩,⟨2416639446086,2416655651076⟩,⟨-1659859651022,-1659841418686⟩,⟨737394270158,737415511222⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51

noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1199988464657,1199988624135⟩,⟨-824755573048,-824752905445⟩,⟨862516671089,862519459781⟩,⟨11911439927647,11911510798540⟩,⟨-6330253433982,-6330162825846⟩,⟨-431879094499,-431764424462⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52

noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1300465301538,1300465620494⟩,⟨-1649511146095,-1649505810890⟩,⟨1725033342178,1725038919562⟩,⟨23822879855302,23823021597069⟩,⟨-12660506867960,-12660325651697⟩,⟨-863758038012,-863528999909⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53

noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨184559643776,184559913536⟩,⟨-1394621358321,-1394616505485⟩,⟨1458473171558,1458478244813⟩,⟨18372718964749,18372856054639⟩,⟨-8854227113778,-8854058402470⟩,⟨-2664925959903,-2664718675615⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54

noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨63490623249,63490729356⟩,⟨-472654239918,-472652503797⟩,⟨494294304999,494296119922⟩,⟨6066577291668,6066622938267⟩,⟨-2833311103723,-2833252475052⟩,⟨-1078342476415,-1078268094392⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55

noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380310461773,380310484775⟩,⟨11401984218,11402293885⟩,⟨-11924381785,-11924058027⟩,⟨-237841588628,-237831915702⟩,⟨164020829955,164031699214⟩,⟨-74051569786,-74038923039⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56

noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3178786460041,3178786652302⟩,⟨-95304923873,-95302324024⟩,⟨99666024793,99668742949⟩,⟨1993608314627,1993689716712⟩,⟨-1377018865511,-1376927524410⟩,⟨625096552724,625202674667⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57

noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨183557070634,183557388502⟩,⟨-1371989099548,-1371983838292⟩,⟨1434804200504,1434809700620⟩,⟨17736073416099,17736213874418⟩,⟨-8356562064788,-8356384009352⟩,⟨-2991877594471,-2991653399569⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58

noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨368116714410,368117302038⟩,⟨-2766610457869,-2766600343777⟩,⟨2893277372062,2893287945433⟩,⟨36108792380848,36109069929057⟩,⟨-17210789178566,-17210442411822⟩,⟨-5656803554374,-5656372075184⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59

noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨522927627743,522927854596⟩,⟨80152827332,80156269240⟩,⟨-83826461800,-83822863620⟩,⟨-1647035860764,-1646942942803⟩,⟨1126916742012,1127033918464⟩,⟨-493307156248,-493160139895⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60

noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨360630511521,360630746191⟩,⟨82914595406,82918173895⟩,⟨-86714828453,-86711087482⟩,⟨-1697432501595,-1697335467166⟩,⟨1159100116730,1159222153691⟩,⟨-503355104020,-503202315185⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61

noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨721261023042,721261492382⟩,⟨165829190812,165836347790⟩,⟨-173429656906,-173422174964⟩,⟨-3394865003190,-3394670934332⟩,⟨2318200233460,2318444307382⟩,⟨-1006710208040,-1006404630370⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62

noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524273894214,1524273977821⟩,⟨-819212786,-818181044⟩,⟨855644044,856722732⟩,⟨29241977787,29274115674⟩,⟨-24534134984,-24497946166⟩,⟨18617395533,18659594313⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63

noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨999897882445,999898587945⟩,⟨229354773015,229365384637⟩,⟨-239867559055,-239856465539⟩,⟨-4687431095842,-4687140380055⟩,⟨3197929210822,3198291837743⟩,⟨-1383679167552,-1383227421272⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64

noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67759272143,67759274928⟩,⟨14392714178,14392778134⟩,⟨-15051794284,-15051727418⟩,⟨-294803863961,-294801866700⟩,⟨201383954990,201386202128⟩,⟨-87545434315,-87542816348⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65

noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨50115978288,50115981062⟩,⟨266061815248,266061878912⟩,⟨36915076861,36915129416⟩,⟨-1291565637818,-1291563624263⟩,⟨-211631730477,-211629752121⟩,⟨-173412388174,-173410352100⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66

noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2134557275471,2134557445971⟩,⟨-325409124492,-325407665546⟩,⟨340307423686,340308949020⟩,⟨6759156327882,6759201975070⟩,⟨-4651404450170,-4651353227622⟩,⟨2081994344347,2082053859055⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67

noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2974142722161,2974143078505⟩,⟨-680103477971,-680100401619⟩,⟨711240821985,711244038332⟩,⟨14178442851158,14178539280518⟩,⟨-9775626425747,-9775518498726⟩,⟨4408053540764,4408178605981⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68

noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨135562069853,135562093600⟩,⟨688689177370,688689577747⟩,⟨132272577298,132272879820⟩,⟨-3176531833082,-3176519969247⟩,⟨-868758651399,-868747332144⟩,⟨-220396322452,-220384763148⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69

noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8917875104391,8917876666575⟩,⟨-45305067431941,-45305025220790⟩,⟨-8701499098138,-8701476148339⟩,⟨669287166072577,669288796875627⟩,⟨145561377685461,145562442406782⟩,⟨31478542653168,31479394752123⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70

noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨8109931907519,8109939050316⟩,⟨-39340298582473,-39340144731441⟩,⟨-9858673337657,-9858556566111⟩,⟨551730462823553,551735632020940⟩,⟨166379438397883,166384000862216⟩,⟨21200374800940,21205021472014⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71

noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨16219863815038,16219878100632⟩,⟨-78680597164946,-78680289462882⟩,⟨-19717346675314,-19717113132222⟩,⟨1103460925647106,1103471264041880⟩,⟨332758876795766,332768001724432⟩,⟨42400749601880,42410042944028⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72

noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10973683302499,10973683302600⟩,⟨-109522921071186,-109522921069169⟩,⟨0,0⟩,⟨2186188521914400,2186188521974786⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73

noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9874171674723,9874171674824⟩,⟨-109522921071186,-109522921069170⟩,⟨0,0⟩,⟨2186188521914418,2186188521974777⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74

noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2413489943680,2413490001536⟩,⟨-12195628068220,-12195628067696⟩,⟨0,0⟩,⟨108164909937337,108164909975027⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75

noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7577860785254,7577860785397⟩,⟨-46361485709417,-46361485707665⟩,⟨-20880519526351,-20880519525514⟩,⟨567280771693431,567280771725560⟩,⟨307721572382424,307721572399448⟩,⟨115071022815253,115071022822295⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76

noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6478349157478,6478349157621⟩,⟨-46361485709418,-46361485707665⟩,⟨-20880519526351,-20880519525513⟩,⟨567280771693433,567280771725561⟩,⟨307721572382425,307721572399450⟩,⟨115071022815253,115071022822297⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77

noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1950093393792,1950093432448⟩,⟨-7868515786899,-7868515786390⟩,⟨-3543861785654,-3543861785416⟩,⟨39969399018893,39969399036562⟩,⟨26865601896065,26865601904755⟩,⟨8107660008741,8107660012477⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78

noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨99127803248,99127803250⟩,⟨879179805490,879179805492⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79

noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨136386303633,136386303637⟩,⟨692796295984,692796295990⟩,⟨312025086441,312025086446⟩,⟨-1732836851712,-1732836851712⟩,⟨-1560887584362,-1560887584354⟩,⟨-351500207392,-351500207389⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80

noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4363583337472,4363583433984⟩,⟨-20064143855119,-20064143854086⟩,⟨-3543861785654,-3543861785416⟩,⟨148134308956230,148134309011589⟩,⟨26865601896065,26865601904755⟩,⟨8107660008741,8107660012477⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81

noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨736233428820,736234604076⟩,⟨-5533220915738,-5533200687554⟩,⟨5786554744124,5786575890866⟩,⟨72217584761696,72218139858114⟩,⟨-34421578357132,-34420884823644⟩,⟨-11313607108748,-11312744150368⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82

noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5099816766292,5099818038060⟩,⟨-25597364770857,-25597344541640⟩,⟨2242692958470,2242714105450⟩,⟨220351893717926,220352448869703⟩,⟨-7555976461067,-7555282918889⟩,⟨-3205947100007,-3205084137891⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83

noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨459780160790,459780275458⟩,⟨1770099855910,1770102696675⟩,⟨202192701483,202194608020⟩,⟨-31269329756182,-31269244810825⟩,⟨1112060100246,1112139536725⟩,⟨-289036045942,-288958244540⟩⟩⟩
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

noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨37282106924,37282109005⟩,⟨-747834400053,-747834389587⟩,⟨331972847757,331972866257⟩,⟨9348230038170,9348230066209⟩,⟨-6658977614141,-6658977521421⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91

noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨497062267714,497062384463⟩,⟨1022265455857,1022268307088⟩,⟨534165549240,534167474277⟩,⟨-21921099718012,-21921014744616⟩,⟨-5546917513895,-5546837984696⟩,⟨-289036045942,-288958244540⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92

noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨500903595558,500903607567⟩,⟨2531120470889,2531120592376⟩,⟨0,0⟩,⟨3131155626176,3131158552760⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93

noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨226446242881,226446301498⟩,⟨1609970171167,1609971804949⟩,⟨243349353911,243350236734⟩,⟨-3864465334548,-3864411375146⟩,⟨-1297333835339,-1297293053167⟩,⟨-131675913626,-131640466548⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94

noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-736234604076,-736233428820⟩,⟨5533200687554,5533220915738⟩,⟨-5786575890866,-5786554744124⟩,⟨-72218139858114,-72217584761696⟩,⟨34420884823644,34421578357132⟩,⟨11312744150368,11313607108748⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95

noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3627348733396,3627350005164⟩,⟨-14530943167565,-14530922938348⟩,⟨-9330437676520,-9330416529540⟩,⟨75916169098116,75916724249893⟩,⟨61286486719709,61287180261887⟩,⟨19420404159109,19421267121225⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96

noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨449945842534,449946000301⟩,⟨483116436730,483119747424⟩,⟨-127984188955,-127981204867⟩,⟨-14611621082803,-14611524722931⟩,⟨-7550042629286,-7549935729351⟩,⟨-4046340460237,-4046221007019⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97

noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨319067835594,319067835600⟩,⟨1952062636032,1952062636032⟩,⟨879179805490,879179805492⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98

noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-319067835600,-319067835594⟩,⟨-1952062636032,-1952062636032⟩,⟨-879179805492,-879179805490⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99

noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨780443792176,780443792182⟩,⟨-1952062636032,-1952062636032⟩,⟨-879179805492,-879179805490⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100

noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1384194805130,1384194832580⟩,⟨-9047324807239,-9047324738203⟩,⟨-4074779731669,-4074779700566⟩,⟨56310037213351,56310037227920⟩,⟨35553124056102,35553124140575⟩,⟨11422304263093,11422304266184⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101

noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1384194832580,-1384194805130⟩,⟨9047324738203,9047324807239⟩,⟨4074779700566,4074779731669⟩,⟨-56310037227920,-56310037213351⟩,⟨-35553124140575,-35553124056102⟩,⟨-11422304266184,-11422304263093⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102

noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-284683204804,-284683177354⟩,⟨9047324738203,9047324807239⟩,⟨4074779700566,4074779731669⟩,⟨-56310037227920,-56310037213351⟩,⟨-35553124140575,-35553124056102⟩,⟨-11422304266184,-11422304263093⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103

noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-12782258955,-12782257721⟩,⟨438195597598,438195603815⟩,⟨69139686326,69139698715⟩,⟨-4560431291043,-4560431274676⟩,⟨1847895994384,1847896056861⟩,⟨2745371267787,2745371292847⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104

noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨437163583579,437163742580⟩,⟨921312034328,921315351239⟩,⟨-58844502629,-58841506152⟩,⟨-19172052373846,-19171955997607⟩,⟨-5702146634902,-5702039672490⟩,⟨-1300969192450,-1300849714172⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105

noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-99127803250,-99127803248⟩,⟨-879179805492,-879179805490⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106

noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4450832466,4450832468⟩,⟨28342603978,28342603983⟩,⟨39631760400,39631760401⟩,⟨-296208039941,-296208039931⟩,⟨252372404139,252372404144⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107

noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨9769827918,9769828158⟩,⟨12845605219,12845606748⟩,⟨86993946002,86993948090⟩,⟨-841085205380,-841085189281⟩,⟨114381737068,114381750391⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108

noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1486593878726,1486593899890⟩,⟨-7576444407614,-7576444022515⟩,⟨-1425241111104,-1425241041936⟩,⟨112289498007630,112289505759203⟩,⟨23843126755624,23843128329472⟩,⟨5322899728051,5322900028407⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109

noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨13209288571,13209289085⟩,⟨-49953416078,-49953408686⟩,⟨104955967684,104955973108⟩,⟨-316459694560,-316459533143⟩,⟨-249593051873,-249592964818⟩,⟨-178234484432,-178234464241⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110

noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-13209289085,-13209288571⟩,⟨49953408686,49953416078⟩,⟨-104955973108,-104955967684⟩,⟨316459533143,316459694560⟩,⟨249592964818,249593051873⟩,⟨178234464241,178234484432⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111

noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-112337092335,-112337091819⟩,⟨-829226396806,-829226389412⟩,⟨-104955973108,-104955967684⟩,⟨2515482788695,2515482950112⟩,⟨249592964818,249593051873⟩,⟨178234464241,178234484432⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112

noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨87559077329,87559079072⟩,⟨-572300524124,-572300519729⟩,⟨620537296609,620537312091⟩,⟨3561966050283,3561966051339⟩,⟨-3491706711036,-3491706671652⟩,⟨-2469671655620,-2469671655225⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113

noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨118384185392,118384189435⟩,⟨-1377125011494,-1377124951856⟩,⟨725498600801,725498641446⟩,⟨21645216720053,21645218046806⟩,⟨-6356338395873,-6356337746557⟩,⟨-4523973262082,-4523973063440⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114

noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-118384189435,-118384185392⟩,⟨1377124951856,1377125011494⟩,⟨-725498641446,-725498600801⟩,⟨-21645218046806,-21645216720053⟩,⟨6356337746557,6356338395873⟩,⟨4523973063440,4523973262082⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115

noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨981127438341,981127442384⟩,⟨1377124951856,1377125011494⟩,⟨-725498641446,-725498600801⟩,⟨-21645218046806,-21645216720053⟩,⟨6356337746557,6356338395873⟩,⟨4523973063440,4523973262082⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116

noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨121701618543,121701619050⟩,⟨789025250010,789025259967⟩,⟨188436657259,188436663458⟩,⟨-2495754358920,-2495754112723⟩,⟨-670695474580,-670695345719⟩,⟨-164260280369,-164260231339⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117

noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11477479527,11477479634⟩,⟨169444103532,169444105822⟩,⟨21446700300,21446701508⟩,⟨736753217030,736753274682⟩,⟨107308915930,107308943548⟩,⟨-16382889194,-16382882828⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118

noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨169314403017,169314553720⟩,⟨1678295422605,1678300877589⟩,⟨110555550458,110558286737⟩,⟨-1863499924944,-1863286308456⟩,⟨483252497291,483391704202⟩,⟨-568269413206,-568162937684⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119

noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-169314553720,-169314403017⟩,⟨-1678300877589,-1678295422605⟩,⟨-110558286737,-110555550458⟩,⟨1863286308456,1863499924944⟩,⟨-483391704202,-483252497291⟩,⟨568162937684,568269413206⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120

noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨57131689161,57131898481⟩,⟨-68330706422,-68323617656⟩,⟨132791067174,132794686276⟩,⟨-2001179026092,-2000911450202⟩,⟨-1780725539541,-1780545550458⟩,⟨436487024058,436628946658⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121

noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨28767544130379,28767570037553⟩,⟨-255623383681131,-255622732934107⟩,⟨-87249349622313,-87248888669418⟩,⟨3672852717227421,3672876015900106⟩,⟨1381198470393583,1381217678356417⟩,⟨321906564192317,321924659231634⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122

noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13470784284,13470784397⟩,⟨174669639814,174669642746⟩,⟨41714967994,41714969542⟩,⟨579936566138,579936651526⟩,⟨121975163816,121975205274⟩,⟨28226407687,28226422946⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123

noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨352448643171,352448963533⟩,⟨1438246802704,1438258994030⟩,⟨22482713688,22489393478⟩,⟨-21045464373261,-21044954530697⟩,⟨-3445513208940,-3445175270747⟩,⟨-1938014620003,-1937756606927⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124

noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-352448963533,-352448643171⟩,⟨-1438258994030,-1438246802704⟩,⟨-22489393478,-22482713688⟩,⟨21044954530697,21045464373261⟩,⟨3445175270747,3445513208940⟩,⟨1937756606927,1938014620003⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125

noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨84714620046,84715099409⟩,⟨-516946959702,-516931451465⟩,⟨-81333896107,-81324219840⟩,⟨1872902156851,1873508375654⟩,⟨-2256971364155,-2256526463550⟩,⟨636787414477,637164905831⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126

noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨235514106881,235514106887⟩,⟨1571976101474,1571976101482⟩,⟨312025086441,312025086446⟩,⟨-3931860107264,-3931860107264⟩,⟨-1560887584362,-1560887584354⟩,⟨-351500207392,-351500207389⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127

noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1657184788067,-1657183320896⟩,⟨-4193894867315,-4193852509530⟩,⟨466197942473,466223256496⟩,⟨43044182968883,43045740006349⟩,⟨-7936168355462,-7935025352468⟩,⟨2060528644918,2061525560228⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128

noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-183428775720,-183428612559⟩,⟨-1653429038648,-1653423280387⟩,⟨-232409845955,-232406783016⟩,⟨2506831923638,2507068857685⟩,⟨-251767237536,-251614176202⟩,⟨635442621025,635561942605⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129

noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨52085331161,52085494328⟩,⟨-81452937174,-81447178905⟩,⟨79615240486,79618303430⟩,⟨-1425028183626,-1424791249579⟩,⟨-1812654821898,-1812501760556⟩,⟨283942413633,284061735216⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130

noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨4401853711,4401894748⟩,⟨-32125902917,-32124422716⟩,⟨6005015989,6005871001⟩,⟨7375308461,7437246452⟩,⟨-311857406259,-311814514859⟩,⟨47071948382,47105682333⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131

noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2467351552,2467367012⟩,⟨-7717092554,-7716522822⟩,⟨7542960094,7543273918⟩,⟨-122944865189,-122920288222⟩,⟨-183532696816,-183516369656⟩,⟨38431282813,38443559133⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132

noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨4376093749,4376121257⟩,⟨-31344432313,-31343310924⟩,⟨5425562434,5426169129⟩,⟨-17917274978,-17864964476⟩,⟨-294337134376,-294303710140⟩,⟨37729840078,37753751707⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133

noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-4376121257,-4376093749⟩,⟨31343310924,31344432313⟩,⟨-5426169129,-5425562434⟩,⟨17864964476,17917274978⟩,⟨294303710140,294337134376⟩,⟨-37753751707,-37729840078⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134

noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨25732454,25800999⟩,⟨-782591993,-779990403⟩,⟨578846860,580308567⟩,⟨25240272937,25354521430⟩,⟨-17553696119,-17477380483⟩,⟨9318196675,9375842255⟩⟩⟩


noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]

noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨57131689161,57131898481⟩,⟨-68330706422,-68323617656⟩,⟨132791067174,132794686276⟩,⟨-2001179026092,-2000911450202⟩,⟨-1780725539541,-1780545550458⟩,⟨436487024058,436628946658⟩⟩

noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨25732454,25800999⟩,⟨-782591993,-779990403⟩,⟨578846860,580308567⟩,⟨25240272937,25354521430⟩,⟨-17553696119,-17477380483⟩,⟨9318196675,9375842255⟩⟩

noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨109951162777,110380659508⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨121547574476,125413045044⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0

noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1

noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-110380659508,-109951162777⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2

noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨439375154380,439804651111⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3

noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨48571550269,50165218018⟩,⟨-125413045044,-121547574476⟩,⟨439375154380,439804651111⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4

noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨158522713046,160545877526⟩,⟨974098582732,977964053300⟩,⟨439375154380,439804651111⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5

noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨48142053538,50594714749⟩,⟨-125413045044,-121547574476⟩,⟨439375154380,439804651111⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
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

noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-2129450047360,-2115506155776⟩,⟨6671194145987,6783146890998⟩,⟨3009096830395,3050479761259⟩,⟨-41846835069778,-40476908301072⟩,⟨-26445329447701,-25787537127732⟩,⟨-8463236348549,-8235168693043⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15

noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-310932979575,-305004300825⟩,⟨-932222796418,-883760802115⟩,⟨-417941775383,-399958383821⟩,⟨5710230350367,6230801169023⟩,⟨3585818294453,3838034757100⟩,⟨1169161862444,1253073688196⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16

noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨305004300825,310932979575⟩,⟨883760802115,932222796418⟩,⟨399958383821,417941775383⟩,⟨-6230801169023,-5710230350367⟩,⟨-3838034757100,-3585818294453⟩,⟨-1253073688196,-1169161862444⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17

noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-160545877526,-158522713046⟩,⟨-977964053300,-974098582732⟩,⟨-439804651111,-439375154380⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18

noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨938965750250,940988914730⟩,⟨-977964053300,-974098582732⟩,⟨-439804651111,-439375154380⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19

noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-173549533952,-171182994176⟩,⟨-1145177923545,-1138199081357⟩,⟨-515003159294,-513394030082⟩,⟨-1192740889178,-1178247792997⟩,⟨748346787480,756049568322⟩,⟨-241223691849,-239718638225⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20

noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-148527931384,-146187602291⟩,⟨-828413812484,-817640055799⟩,⟨-372345957161,-369010666326⟩,⟨995969702826,1030958960462⟩,⟨1375196976686,1392005037319⟩,⟨203869005826,207286555996⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21

noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨146187602291,148527931384⟩,⟨817640055799,828413812484⟩,⟨369010666326,372345957161⟩,⟨-1030958960462,-995969702826⟩,⟨-1392005037319,-1375196976686⟩,⟨-207286555996,-203869005826⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22

noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨451191903116,459460910959⟩,⟨1701400857914,1760636608902⟩,⟨768969050147,790287732544⟩,⟨-7261760129485,-6706200053193⟩,⟨-5230039794419,-4961015271139⟩,⟨-1460360244192,-1373030868270⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23

noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨808150499942,818311968422⟩,⟨4107738717388,4181266316004⟩,⟨768969050147,790287732544⟩,⟨-19565545821258,-18793419960250⟩,⟨-5230039794419,-4961015271139⟩,⟨-1460360244192,-1373030868270⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24

noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨96284107076,101189429498⟩,⟨-250826090088,-243095148952⟩,⟨878750308760,879609302222⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25

noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨11947155207931,12555818985375⟩,⟨28701569810530,32708689726631⟩,⟨-114704446164047,-103751611011703⟩,⟨137903977181426,170416343988256⟩,⟨-337991864222473,-211739833909253⟩,⟨1802001664861280,2095778855226556⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26

noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8781261798662,9344673298140⟩,⟨65730073403539,72091220561649⟩,⟨-77013308814509,-67233674228837⟩,⟨92389032527025,171397290556846⟩,⟨-727404257153686,-573639140721040⟩,⟨1142919694876623,1399742861365092⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27

noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨89246138368,94912815360⟩,⟨-771331516289,-621413948880⟩,⟨635629033057,823994819335⟩,⟨6763696229285,11613835495262⟩,⟨-7916663274254,-1011437312147⟩,⟨-5980999298712,3445459352796⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28

noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29

noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1188757766144,1194424443136⟩,⟨-771331516289,-621413948880⟩,⟨635629033057,823994819335⟩,⟨6763696229285,11613835495262⟩,⟨-7916663274254,-1011437312147⟩,⟨-5980999298712,3445459352796⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30

noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨85808923584,91037721536⟩,⟨-713423705976,-572034393956⟩,⟨585119901735,762133304942⟩,⟨5763322534148,10444317437857⟩,⟨-7017902989254,-436551176816⟩,⟨-6060252454072,2875411633931⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31

noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨92773938663,98896343707⟩,⟨-838873326323,-666962651275⟩,⟨682219679618,896148102821⟩,⟨7405578996832,13308470023919⟩,⟨-9348500254427,-1212308494539⟩,⟨-6402089472120,4551217442531⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32

noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-94912815360,-89246138368⟩,⟨621413948880,771331516289⟩,⟨-823994819335,-635629033057⟩,⟨-11613835495262,-6763696229285⟩,⟨1011437312147,7916663274254⟩,⟨-3445459352796,5980999298712⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33

noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨1004598812416,1010265489408⟩,⟨621413948880,771331516289⟩,⟨-823994819335,-635629033057⟩,⟨-11613835495262,-6763696229285⟩,⟨1011437312147,7916663274254⟩,⟨-3445459352796,5980999298712⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34

noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-99261530752,-93076902144⟩,⟨676309217348,844205627708⟩,⟨-901844471534,-691780052001⟩,⟨-13359272787443,-7777193930337⟩,⟨1526300636324,9357053055154⟩,⟨-4510693958442,6110826650398⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35

noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-91204582482,-85042252391⟩,⟨548294237477,723077870432⟩,⟨-774834884483,-557675258818⟩,⟨-10937885604877,-4872916072985⟩,⟨-585480334651,7729979901993⟩,⟨-3884679803587,7277584873860⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36

noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨1569356181,13854091316⟩,⟨-290579088846,56115219157⟩,⟨-92615204865,338472844003⟩,⟨-3532306608045,8435553950934⟩,⟨-9933980589078,6517671407454⟩,⟨-10286769275707,11828802316391⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37

noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨784678090,6927045658⟩,⟨-145289544423,28057609579⟩,⟨-46307602433,169236422002⟩,⟨-1766153304023,4217776975467⟩,⟨-4966990294539,3258835703727⟩,⟨-5143384637854,5914401158196⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38

noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-6927045658,-784678090⟩,⟨-28057609579,145289544423⟩,⟨-169236422002,46307602433⟩,⟨-4217776975467,1766153304023⟩,⟨-3258835703727,4966990294539⟩,⟨-5914401158196,5143384637854⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39

noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨755196337958,761338724790⟩,⟨-28057609579,145289544423⟩,⟨-169236422002,46307602433⟩,⟨-4217776975467,1766153304023⟩,⟨-3258835703727,4966990294539⟩,⟨-5914401158196,5143384637854⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40

noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨7244009988,8193130743⟩,⟨-133166842328,-100878960920⟩,⟨103186606128,142258919634⟩,⟨1800415821745,3087287281241⟩,⟨-2522876408020,-882674833998⟩,⟨-297676186971,1829877346016⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41

noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-8193130743,-7244009988⟩,⟨100878960920,133166842328⟩,⟨-142258919634,-103186606128⟩,⟨-3087287281241,-1800415821745⟩,⟨882674833998,2522876408020⟩,⟨-1829877346016,297676186971⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42

noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1091318497033,1092267617788⟩,⟨100878960920,133166842328⟩,⟨-142258919634,-103186606128⟩,⟨-3087287281241,-1800415821745⟩,⟨882674833998,2522876408020⟩,⟨-1829877346016,297676186971⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43

noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-8223809280,-7267978496⟩,⟨101547998606,134166599368⟩,⟨-143326935920,-103870948310⟩,⟨-3126836771916,-1821735035458⟩,⟨898122054416,2559306333698⟩,⟨-1862298641445,290098310026⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44

noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-4111904640,-3633989248⟩,⟨50773999303,67083299684⟩,⟨-71663467960,-51935474155⟩,⟨-1563418385958,-910867517729⟩,⟨449061027208,1279653166849⟩,⟨-931149320723,145049155013⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45

noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨3633989248,4111904640⟩,⟨-67083299684,-50773999303⟩,⟨51935474155,71663467960⟩,⟨910867517729,1563418385958⟩,⟨-1279653166849,-449061027208⟩,⟨-145049155013,931149320723⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46

noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨765757372864,766235307520⟩,⟨-67083299684,-50773999303⟩,⟨51935474155,71663467960⟩,⟨910867517729,1563418385958⟩,⟨-1279653166849,-449061027208⟩,⟨-145049155013,931149320723⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47

noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48

noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49

noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272829624258,273066904447⟩,⟨25219740230,33291710582⟩,⟨-35564729909,-25796651532⟩,⟨-771821820311,-450103955436⟩,⟨220668708499,630719102005⟩,⟨-457469336504,74419046743⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50

noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1531514745728,1532470615040⟩,⟨-134166599368,-101547998606⟩,⟨103870948310,143326935920⟩,⟨1821735035458,3126836771916⟩,⟨-2559306333698,-898122054416⟩,⟨-290098310026,1862298641446⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51

noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1196641706847,1203391647167⟩,⟨-923964763275,-736053894982⟩,⟨752891412220,987049228650⟩,⟨8916972231340,15330855183130⟩,⟨-10998948712155,-2124236198468⟩,⟨-6217142420104,5746457029551⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52

noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1293771785918,1307271666558⟩,⟨-1847929526549,-1472107789965⟩,⟨1505782824440,1974098457300⟩,⟨17833944462690,30661710366248⟩,⟨-21997897424301,-4248472396937⟩,⟨-12429402149901,11492914059098⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53

noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨178885825728,190299252224⟩,⟨-1570462444666,-1238150932061⟩,⟨1266474113017,1677687078821⟩,⟨12756524726071,24663575360937⟩,⟨-17268741605810,-1176991571834⟩,⟨-13123018950528,8308460029260⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54

noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨61298448483,65720816395⟩,⟨-536517818292,-414274562759⟩,⟨421970992456,574559044168⟩,⟨4077687414711,8233634367032⟩,⟨-5816587355535,-38332931202⟩,⟨-4905649542790,2899150054358⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55

noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380025624165,380593525738⟩,⟨1808026422,21203291807⟩,⟨-23794956832,-336612625⟩,⟨-631829830714,144948685254⟩,⟨-323475688148,664901913536⟩,⟨-718927668012,561356575594⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56

noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3176422450356,3181169223184⟩,⟨-177491345419,-15089735713⟩,⟨2809359137,199186000964⟩,⟨-1213212434352,5308811524936⟩,⟨-5588076609962,2707766778132⟩,⟨-4699073587280,6043039389282⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57

noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨177087502318,190147182765⟩,⟨-1562892837105,-1197655364326⟩,⟨1219205244699,1674252612073⟩,⟨11719045801604,24312556169825⟩,⟨-17352838524601,44259453013⟩,⟨-14472022814135,8957366521953⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58

noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨355973328046,380446434989⟩,⟨-3133355281771,-2435806296387⟩,⟨2485679357716,3351939690894⟩,⟨24475570527675,48976131530762⟩,⟨-34621580130411,-1132732118821⟩,⟨-27595041764663,17265826551213⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59

noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨518704390620,527176465644⟩,⟨-38856059652,201206706110⟩,⟨-234369948368,64129873836⟩,⟨-5848475523207,2484284697836⟩,⟨-4557780087688,6890859490068⟩,⟨-8204914717908,7175001642866⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60

noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨356270589944,365034664440⟩,⟨-40357858197,208983406605⟩,⟨-243428418280,66608512999⟩,⟨-6082222547790,2620184260922⟩,⟨-4780394169112,7169904497957⟩,⟨-8536843441203,7506428845729⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61

noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨712541179888,730069328880⟩,⟨-80715716394,417966813210⟩,⟨-486856836560,133217025998⟩,⟨-12164445095580,5240368521844⟩,⟨-9560788338224,14339808995914⟩,⟨-17073686882406,15012857691458⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62

noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1523321614985,1525226605052⟩,⟨-33287638448,31618843722⟩,⟨-38387971324,40140329792⟩,⟨-1265552245783,1326420950171⟩,⟨-1676631499700,1624754353604⟩,⟨-2119975656042,2159974828417⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63

noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨987192271068,1012741598916⟩,⟨-134070471134,600792237996⟩,⟨-700850141980,211449674617⟩,⟨-17739969217053,8174138199496⟩,⟨-14404454050935,21000801236860⟩,⟨-25127570435676,22293825381725⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64

noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67699151143,67816958385⟩,⟨12515906292,16536185928⟩,⟨-17665207824,-12802212484⟩,⟨-382211437610,-221358923308⟩,⟨107358482874,312098432752⟩,⟨-226017197508,39265121342⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65

noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨49759458162,50472798383⟩,⟨262121066235,270204075248⟩,⟨34199639196,39334550685⟩,⟨-1397729515600,-1194080603898⟩,⟨-302099736792,-109123392413⟩,⟨-283681367156,-73224251431⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66

noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2133253853009,2135917553425⟩,⟨-373995810244,-282893337978⟩,⟨289364632388,399530686340⟩,⟨5093763439861,8748950035395⟩,⟨-7169167363590,-2521183081108⟩,⟨-789037515798,5228613290467⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67

noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2971418991605,2976986149199⟩,⟨-781898401348,-591065125147⟩,⟨604585968260,835283167302⟩,⟨10681880310157,18359541974500⟩,⟨-15061425973548,-5307738499162⟩,⟨-1608613931406,11009378432565⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68

noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨134474429609,136657783240⟩,⟨672486670685,704842667897⟩,⟨119785297652,144843844711⟩,⟨-3685309912573,-2666017794655⟩,⟨-1393182130687,-348226249712⟩,⟨-804314825920,367258674271⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69

noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨8846373700438,8990005186338⟩,⟨-47120774249583,-43532598410398⟩,⟨-9683230625684,-7754154075415⟩,⟨601025218606329,740337177764370⟩,⟨98857670110423,194646840091730⟩,⟨-10958735098143,74630598484378⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70

noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨7942682481417,8280542012176⟩,⟨-44498358407975,-34173280577994⟩,⟨-14649464790431,-5233148204263⟩,⟨343084543076943,760238263647845⟩,⟨-43370046966526,382212511531347⟩,⟨-219270429963469,263367932857201⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71

noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨15885364962834,16561084024352⟩,⟨-88996716815950,-68346561155988⟩,⟨-29298929580862,-10466296408526⟩,⟨686169086153886,1520476527295690⟩,⟨-86740093933052,764425023062694⟩,⟨-438540859926938,526735865714402⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72

noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨10952333724070,10995116277821⟩,⟨-109951162778821,-109097176394608⟩,⟨0,0⟩,⟨2173453475238562,2199023255588622⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73

noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨9852822096294,9895604650045⟩,⟨-109951162778820,-109097176394608⟩,⟨0,0⟩,⟨2173453475238575,2199023255588602⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74

noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2411110045440,2415874025920⟩,⟨-12269843176037,-12121908488212⟩,⟨0,0⟩,⟨104571265817406,111755106875729⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75

noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨7530095685071,7626199403135⟩,⟨-47047825111350,-45688221010066⟩,⟨-21158090871343,-20608046778329⟩,⟨554418861689413,580498287731141⟩,⟨301645653127676,313953745683781⟩,⟨112798458287802,117401810693797⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76

noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨6430584057295,6526687775359⟩,⟨-47047825111350,-45688221010066⟩,⟨-21158090871344,-20608046778328⟩,⟨554418861689422,580498287731135⟩,⟨301645653127680,313953745683778⟩,⟨112798458287803,117401810693796⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77

noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1941956621888,1958267052736⟩,⟨-8044312975429,-7696818352853⟩,⟨-3617644482584,-3471713040105⟩,⟨34545307998123,45375145731297⟩,⟨24348791635525,29377578031609⟩,⟨7099597321493,9111600886675⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78

noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨98913096826,99342593558⟩,⟨878750308760,879609302222⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79

noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨135375920023,137399084504⟩,⟨689066936889,696524314709⟩,⟨311001165592,313048403610⟩,⟨-1739706366693,-1725980926276⟩,⟨-1564837444326,-1556937724390⟩,⟨-351843720890,-351156861664⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80

noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨4353066667328,4374141078656⟩,⟨-20314156151466,-19818726841065⟩,⟨-3617644482584,-3471713040105⟩,⟨139116573815529,157130252607026⟩,⟨24348791635525,29377578031609⟩,⟨7099597321493,9111600886675⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81

noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨711946656092,760892869978⟩,⟨-6266710563542,-4871612592774⟩,⟨4971358715432,6703879381788⟩,⟨48951141055350,97952263061524⟩,⟨-69243160260822,-2265464237642⟩,⟨-55190083529326,34531653102426⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82

noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨5065013323420,5135033948634⟩,⟨-26580866715008,-24690339433839⟩,⟨1353714232848,3232166341683⟩,⟨188067714870879,255082515668550⟩,⟨-44894368625297,27112113793967⟩,⟨-48090486207833,43643253989101⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83

noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨455653347020,463958340757⟩,⟨1646430776727,1886861076272⟩,⟨121781401493,292031279236⟩,⟨-35880706698223,-26548887228108⟩,⟨-2974362555777,5035354917351⟩,⟨-4345050570329,3943236190560⟩⟩⟩
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

noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨36231721655,38339647835⟩,⟨-769054968218,-726808365435⟩,⟨330673852191,333275037186⟩,⟨8990500177985,9713891785703⟩,⟨-6692236630045,-6625935308195⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91

noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨491885068675,502297988592⟩,⟨877375808509,1160052710837⟩,⟨452455253684,625306316422⟩,⟨-26890206520238,-16834995442405⟩,⟨-9666599185822,-1590580390844⟩,⟨-4345050570329,3943236190560⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92

noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨500409295618,501398026980⟩,⟨2510857612204,2551553037358⟩,⟨0,0⟩,⟨1957166706152,4308831445771⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93

noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨223866537217,229057350622⟩,⟨1522585425245,1694650653788⟩,⟨205921255469,285151466699⟩,⟨-7379698181060,-309409012523⟩,⟨-3374919325765,727196509561⟩,⟨-1981424960006,1798190029025⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94

noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-760892869978,-711946656092⟩,⟨4871612592774,6266710563542⟩,⟨-6703879381788,-4971358715432⟩,⟨-97952263061524,-48951141055350⟩,⟨2265464237642,69243160260822⟩,⟨-34531653102426,55190083529326⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95

noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨3592173797350,3662194422564⟩,⟨-15442543558692,-13552016277523⟩,⟨-10321523864372,-8443071755537⟩,⟨41164310754005,108179111551676⟩,⟨26614255873167,98620738292431⟩,⟨-27432055780933,64301684416001⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96

noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨442281664344,457641509398⟩,⟨321467130502,651371727847⟩,⟨-273755805817,3142768917⟩,⟨-20291464035592,-9106593332473⟩,⟨-12870501024177,-1887134380124⟩,⟨-10477317664254,2111815573971⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97

noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨317045426092,321091755052⟩,⟨1948197165464,1955928106600⟩,⟨878750308760,879609302222⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98

noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-321091755052,-317045426092⟩,⟨-1955928106600,-1948197165464⟩,⟨-879609302222,-878750308760⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99

noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨778419872724,782466201684⟩,⟨-1955928106600,-1948197165464⟩,⟨-879609302222,-878750308760⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100

noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨1374844602146,1393598524953⟩,⟨-9208299695926,-8890011257629⟩,⟨-4141106231284,-4009912485248⟩,⟨51732598559600,60911328205369⟩,⟨33424979907784,37693954921416⟩,⟨10575609353713,12272491599183⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101

noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-1393598524953,-1374844602146⟩,⟨8890011257629,9208299695926⟩,⟨4009912485248,4141106231284⟩,⟨-60911328205369,-51732598559600⟩,⟨-37693954921416,-33424979907784⟩,⟨-12272491599183,-10575609353713⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102

noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨-294086897177,-275332974370⟩,⟨8890011257629,9208299695926⟩,⟨4009912485248,4141106231284⟩,⟨-60911328205369,-51732598559600⟩,⟨-37693954921416,-33424979907784⟩,⟨-12272491599183,-10575609353713⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103

noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨-13532592379,-12055438485⟩,⟨419685832753,457269952424⟩,⟨57939029227,80529953628⟩,⟨-4903516205215,-4230634786266⟩,⟨1621008992754,2070612653776⟩,⟨2640070872795,2849832536253⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104

noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨428749071965,445586070913⟩,⟨741152963255,1108641680271⟩,⟨-215816776590,83672722545⟩,⟨-25194980240807,-13337228118739⟩,⟨-11249492031423,183478273652⟩,⟨-7837246791459,4961648110224⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105

noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-99342593558,-98913096826⟩,⟨-879609302222,-878750308760⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106

noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨4330904269,4571311532⟩,⟨27144767273,29541238050⟩,⟨39526600801,39737037424⟩,⟨-301850301569,-290570308152⟩,⟨251814268106,252930624064⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107

noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨9497204508,10044198275⟩,⟨8512638892,17161332362⟩,⟨86677559241,87311197222⟩,⟨-910656015488,-771089935100⟩,⟨108761645553,119972071186⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108

noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1477340997402,1495916688416⟩,⟨-7739679751822,-7415913548855⟩,⟨-1462852040367,-1388259670337⟩,⟨108381110908754,116304761309523⟩,⟨22893869290683,24818213605470⟩,⟨5087903383026,5564217685654⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109

noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨12760765075,13665416029⟩,⟨-59265228248,-40707640537⟩,⟨103099533480,106798043827⟩,⟨-544418425365,-88432606460⟩,⟨-293547963116,-205421890770⟩,⟨-188379878692,-168050804817⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110

noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-13665416029,-12760765075⟩,⟨40707640537,59265228248⟩,⟨-106798043827,-103099533480⟩,⟨88432606460,544418425365⟩,⟨205421890770,293547963116⟩,⟨168050804817,188379878692⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111

noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-113008009587,-111673861901⟩,⟨-838901661685,-819485080512⟩,⟨-106798043827,-103099533480⟩,⟨2287455862012,2743441680917⟩,⟨205421890770,293547963116⟩,⟨168050804817,188379878692⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112

noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨85028459270,90110882353⟩,⟨-593528924981,-551681985909⟩,⟨609555900047,631298064824⟩,⟨3214282761359,3923074587912⟩,⟨-3726094770679,-3253212205388⟩,⟨-2583260124688,-2355382146697⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113

noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨114247112674,122598405797⟩,⟨-1441821219036,-1314752915686⟩,⟨699131335966,751540692091⟩,⟨20142144788280,23225188683690⟩,⟨-7046277383196,-5658768256462⟩,⟨-4800964843420,-4248022187591⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114

noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-122598405797,-114247112674⟩,⟨1314752915686,1441821219036⟩,⟨-751540692091,-699131335966⟩,⟨-23225188683690,-20142144788280⟩,⟨5658768256462,7046277383196⟩,⟨4248022187591,4800964843420⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115

noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨976913221979,985264515102⟩,⟨1314752915686,1441821219036⟩,⟨-751540692091,-699131335966⟩,⟨-23225188683690,-20142144788280⟩,⟨5658768256462,7046277383196⟩,⟨4248022187591,4800964843420⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116

noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨120281152892,123122338091⟩,⟨774111401404,804325833727⟩,⟨182408391680,194440813870⟩,⟨-2813326394624,-2186759863132⟩,⟨-809718151846,-530444089589⟩,⟨-220203627529,-107559506159⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117

noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨11342355202,11614984243⟩,⟨166464931154,172444937610⟩,⟨20942976450,21953445614⟩,⟨657609986597,815465624218⟩,⟨93341911384,121240737954⟩,⟨-19388464961,-13389690508⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118

noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨163870437901,174947426777⟩,⟨1464887392464,1892353000465⟩,⟨-6930150542,222699241861⟩,⟨-11336777255163,7649482025181⟩,⟨-5939865479071,7014942561409⟩,⟨-6094673235102,4972151020078⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119

noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-174947426777,-163870437901⟩,⟨-1892353000465,-1464887392464⟩,⟨-222699241861,6930150542⟩,⟨-7649482025181,11336777255163⟩,⟨-7014942561409,5939865479071⟩,⟨-4972151020078,6094673235102⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120

noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨48919110440,65186912721⟩,⟨-369767575220,229763261324⟩,⟨-16777986392,292081617241⟩,⟨-15029180206241,11027368242640⟩,⟨-10389861887174,6667061988632⟩,⟨-6953575980084,7892863264127⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121

noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨28056719821218,29495845594721⟩,⟨-279671331960905,-231914623880449⟩,⟨-106672125843890,-68643678155673⟩,⟨2667891347677745,4693716233888227⟩,⟨486366846716110,2311136191669800⟩,⟨-612388673549681,1268175493433881⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122

noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨13158165294,13787130354⟩,⟨169367943868,180135388720⟩,⟨39909158018,43546620190⟩,⟨459959007027,698335587668⟩,⟨75506293180,168422671936⟩,⟨11206495177,45237991243⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123

noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨335762667432,369857905859⟩,⟨814947123015,2056981117417⟩,⟨-319216668992,346717135232⟩,⟨-47973946370492,6141881594298⟩,⟨-20805611575552,14506576068545⟩,⟨-15842566492349,12132487288489⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124

noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-369857905859,-335762667432⟩,⟨-2056981117417,-814947123015⟩,⟨-346717135232,319216668992⟩,⟨-6141881594298,47973946370492⟩,⟨-14506576068545,20805611575552⟩,⟨-12132487288489,15842566492349⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125

noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨58891166106,109823403481⟩,⟨-1315828154162,293694557256⟩,⟨-562533911822,402889391537⟩,⟨-31336861835105,34636718251753⟩,⟨-25756068099968,20989089849204⟩,⟨-19969734079948,20804214602573⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126

noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨234289016849,236741678062⟩,⟨1567817245649,1576133616931⟩,⟨311001165592,313048403610⟩,⟨-3938729622245,-3925004181828⟩,⟨-1564837444326,-1556937724390⟩,⟨-351843720890,-351156861664⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127

noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1702151296009,-1613425459351⟩,⟨-5693979324308,-2692538835964⟩,⟨-545587352204,1521802913100⟩,⟨-21346732342628,107435156377062⟩,⟨-61390416070415,44335496407305⟩,⟨-49747252743774,53602472174456⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128

noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-190605394300,-176500793128⟩,⟨-1882781641820,-1430483024519⟩,⟨-362107742842,-97256279660⟩,⟨-7512166934668,12594432329695⟩,⟨-7502123062273,6884726188132⟩,⟨-5605786758120,6881494105535⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129

noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨43683622549,60240884934⟩,⟨-314964396171,145650592412⟩,⟨-51106577250,215792123950⟩,⟨-11450896556913,8669428147867⟩,⟨-9066960506599,5327788463742⟩,⟨-5957630479010,6530337243871⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130

noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨2620166431,6511116788⟩,⟨-114945495306,40361942251⟩,⟨-35026882490,53060387384⟩,⟨-3908978156014,4039998214836⟩,⟨-3049820594321,2177514933208⟩,⟨-2177368808102,2235844293413⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131

noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1735551340,3300523729⟩,⟨-34513020998,15960032358⟩,⟨-5600132572,23645968230⟩,⟨-1338206662272,1130422959897⟩,⟨-1117166103718,640977200400⟩,⟨-672882977631,800281732606⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132

noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨3065329490,5878343359⟩,⟨-85616336738,16276119025⟩,⟨-20833500972,36634250407⟩,⟨-2562397504939,2654541156961⟩,⟨-2176788518633,1384315497124⟩,⟨-1342821872462,1489531298110⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133

noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5878343359,-3065329490⟩,⟨-16276119025,85616336738⟩,⟨-36634250407,20833500972⟩,⟨-2654541156961,2562397504939⟩,⟨-1384315497124,2176788518633⟩,⟨-1489531298110,1342821872462⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134

noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-3258176928,3445787298⟩,⟨-131221614331,125978278989⟩,⟨-71661132897,73893888356⟩,⟨-6563519312975,6602395719775⟩,⟨-4434136091445,4354303451841⟩,⟨-3666900106212,3578666165875⟩⟩⟩


noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]

noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨48919110440,65186912721⟩,⟨-369767575220,229763261324⟩,⟨-16777986392,292081617241⟩,⟨-15029180206241,11027368242640⟩,⟨-10389861887174,6667061988632⟩,⟨-6953575980084,7892863264127⟩⟩

noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-3258176928,3445787298⟩,⟨-131221614331,125978278989⟩,⟨-71661132897,73893888356⟩,⟨-6563519312975,6602395719775⟩,⟨-4434136091445,4354303451841⟩,⟨-3666900106212,3578666165875⟩⟩



attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (513/5120) u, BivariateJet2.affineZ (115/1024) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet


noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet























end GeneralCK.Certificates.LaneCB.RB2Cell000005

end


